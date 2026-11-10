import Final.MacroLink
import Final.OutputInjective
import FL.Typed.Fn

/-!
# Assembly.Spec: the component bundle (the contract for the remaining transcriptions)

`Components hD hd A density` collects exactly the facts that the FL transcription packages
must provide so that `Assembly.main_of_components` can build the top-level machine:

* one FL program `P` (fixed once the SAT density is known), seven function indices
  (`Indices`: `init`, `step`, `isDone`, `isInvoke`, `query`, `resume`, `output`), and three
  polynomial envelopes (`Budget`: value size `m`, cost `t`, call depth `d`) in the input
  length `L = paperL rows a b c d`;
* for every positive instance (`n = k+1`, every SAT machine with the right density, every
  precision, every coin string) SOME encoding `enc : Config → Val` of the macro controller
  states such that (`PositiveFacts`), all with the budget at `L`:
  - `init` maps the FL encoding of the raw machine input to `enc (initial …)`;
  - at every reachable state: `isDone` decides `pc = .done`; `isInvoke` decides
    `pc = .invoke` (if not done); `query` returns the query bits (at `.invoke`);
    `step` follows every non-invoke controller edge; `resume` follows the invoke edge given
    the actual SAT answer bit; `output` returns the raw output word (at `.done`);
* for `n = 0` (`ZeroFacts`): `init` produces some value on which `isDone` answers `true` and
  `output` returns the output word of the zero-length vector.

Nothing else is assumed. The budget envelopes are evaluated at `L` only: in particular the
cost of a single FL call may not depend on the cell budget `B` (`1/ε`).
-/

set_option autoImplicit false
set_option linter.constructorNameAsVariable false

noncomputable section
namespace QecReliability.Assembly
open OracleCost OracleCost.MultiTape OracleCost.WholeWrapperCandidate
open SharedCircuit SharedCircuit.LatentEncoding RationalOutput QecPhysical QecPhysical.Stabilizer
open FL Final

/-! ## Raw words and their FL encodings -/

/-- FL encoding of a raw bit string (`encBits w = (bitsVal w).bits`). -/
abbrev bitsVal (w : List Bool) : Val := Enc.list Enc.bool w

/-- Raw output word of a list of ratios; `outputWord v = ratioWord v.entries.toList`. -/
def ratioWord (xs : List Ratio) : List Bool :=
  xs.flatMap (fun x => QueryCodec.natHeader x.num ++ QueryCodec.natHeader x.den)

theorem outputWord_eq_ratioWord {r : ℕ} (v : RationalOutput.Vector r) :
    outputWord v = ratioWord v.entries.toList := rfl

/-! ## Program interface -/

/-- Indices of the seven top-level FL functions in the program. -/
structure Indices where
  init : ℕ
  step : ℕ
  isDone : ℕ
  isInvoke : ℕ
  query : ℕ
  resume : ℕ
  output : ℕ

/-- Polynomial resource envelopes (in the input length `L`) for every top-level FL call:
value-size budget `m`, evaluation cost `t`, call depth `d`. -/
structure Budget where
  value : PolynomialEnvelope
  cost : PolynomialEnvelope
  depth : PolynomialEnvelope

/-- `P` computes `f x = y` within the budget at input length `L` (argument included in the
value budget, as `FL.Computes` requires). -/
def Budget.Computes (Bd : Budget) (P : Program) (L f : ℕ) (x y : Val) : Prop :=
  FL.Computes P f x y (Bd.value.eval L) (Bd.cost.eval L) (Bd.depth.eval L)

/-- How a typed transcription discharges a `Budget.Computes` fact. -/
theorem Budget.computes_of_validAt {Bd : Budget} {P : Program} {L : ℕ} {a b : Ty}
    {F : FnSig a b} {x : a.den} (h : F.ValidAt P x) (hm : F.msize x ≤ Bd.value.eval L)
    (harg : (a.enc x).size ≤ Bd.value.eval L) (ht : F.cost x ≤ Bd.cost.eval L)
    (hdep : F.depth x ≤ Bd.depth.eval L) :
    Bd.Computes P L F.idx (a.enc x) (b.enc (F.den x)) := by
  obtain ⟨harg', t, d, ht', hd', e⟩ := h.computes hm harg
  exact ⟨harg', t, d, ht'.trans ht, hd'.trans hdep, e⟩

/-! ## The macro controller of one positive instance -/

section Instance
variable {D t : ℕ} (hD : D = 16^384) (hd : D = 256*t)
    (A : FiniteLocalSelectorCandidate.CertifiedParity (512*t) (64*t) t)
variable {kE : ℕ} {ΓE ΛE : Type} [Fintype ΓE] [Inhabited ΓE] [Fintype ΛE]
    {E : Machine kE ΓE ΛE} {density : ℕ} {PtE PsE : PolynomialEnvelope} {T : ℕ → ℕ}

/-- The concrete external interface of the instance whose coins are `coins`. -/
abbrev instExt (spec : EncodedSAT E density PtE PsE T) (c d k : ℕ)
    (rows : List (List (PauliCoord (k+1))))
    (coins : Fin (coinBits hD hd A c d (k+1)) → Bool) : External :=
  macroExternal hD hd A spec c d k rows (coinWord hD hd A c d (k+1) coins)

/-- One controller step of the instance (parameters `q = keySize (k+1) (k+1)`, `r = k+1`,
`B = rationalCellBudget a b`, `m = macroM c d k`, `shape = true`). -/
abbrev instStep (spec : EncodedSAT E density PtE PsE T) (a b c d k : ℕ)
    (rows : List (List (PauliCoord (k+1))))
    (coins : Fin (coinBits hD hd A c d (k+1)) → Bool) (s : Config) : Option Edge :=
  step (keySize (k+1) (k+1)) (k+1) (rationalCellBudget a b) (macroM c d k) true
    (instExt hD hd A spec c d k rows coins) s

/-- Reachable controller states of the instance. -/
abbrev InstReachable (spec : EncodedSAT E density PtE PsE T) (a b c d k : ℕ)
    (rows : List (List (PauliCoord (k+1))))
    (coins : Fin (coinBits hD hd A c d (k+1)) → Bool) (s : Config) : Prop :=
  Reachable (keySize (k+1) (k+1)) (k+1) (rationalCellBudget a b) (macroM c d k) true
    (instExt hD hd A spec c d k rows coins) s

/-- The initial controller state of the instance. -/
abbrev instInitial (c d k : ℕ) : Config :=
  initial (keySize (k+1) (k+1)) (k+1) (macroM c d k)

/-- For discharging the contract: what the macro layer already proves at every reachable
state of an instance (fixed-slot field bounds, represented bits, query length, all
polynomial in `L = paperL`, none depending on the cell budget). -/
theorem instReachable_bounds (spec : EncodedSAT E density PtE PsE T) (hT : Monotone T)
    {a b c d k : ℕ} (rows : List (List (PauliCoord (k+1))))
    (coins : Fin (coinBits hD hd A c d (k+1)) → Bool)
    (ha : 0 < a) (hab : a ≤ b) (hc : 0 < c) (hd' : 0 < d) {s : Config}
    (hs : InstReachable hD hd A spec a b c d k rows coins s) :
    MultiTape.FixedSlot.Fits (slotWidth (paperL rows a b c d))
        (fieldPolynomial (paperL rows a b c d)) (configFields s) ∧
      (representedBits s).length ≤ InputEncoding.retainedPolynomial
        (SharedCircuit.FixedLocalEmitter.AllLength.gateConstant hD hd A) density
        (paperL rows a b c d) ∧
      s.query.length ≤ InputEncoding.queryPolynomial
        (SharedCircuit.FixedLocalEmitter.AllLength.gateConstant hD hd A) density
        (paperL rows a b c d) := by
  obtain ⟨final, totals, PR⟩ := (macro_main hD hd A spec hT a b c d ha
    (lt_of_lt_of_le ha hab) hc hd' hab).positive k rows (coinWord hD hd A c d (k+1) coins)
  exact ⟨(PR.fields s hs).1, PR.represented s hs, PR.query s hs⟩

/-- **The per-instance contract, `n = k+1`.** With `L = paperL rows a b c d` and
`input = machineInput rows a b c d (List.ofFn coins)`, the encoding `enc` of controller
states satisfies, within the budget at `L`: -/
structure PositiveFacts (P : Program) (I : Indices) (Bd : Budget)
    (spec : EncodedSAT E density PtE PsE T) (a b c d k : ℕ)
    (rows : List (List (PauliCoord (k+1))))
    (coins : Fin (coinBits hD hd A c d (k+1)) → Bool) (enc : Config → Val) : Prop where
  /-- Parse the raw input (problem encoding and coins) into the initial state. -/
  init : Bd.Computes P (paperL rows a b c d) I.init
    (bitsVal (machineInput rows a b c d (List.ofFn coins))) (enc (instInitial c d k))
  /-- Termination test. -/
  isDone : ∀ s, InstReachable hD hd A spec a b c d k rows coins s →
    Bd.Computes P (paperL rows a b c d) I.isDone (enc s) (Enc.bool (decide (s.pc = .done)))
  /-- SAT-call test. -/
  isInvoke : ∀ s, InstReachable hD hd A spec a b c d k rows coins s → s.pc ≠ .done →
    Bd.Computes P (paperL rows a b c d) I.isInvoke (enc s) (Enc.bool (decide (s.pc = .invoke)))
  /-- The SAT query buffer. -/
  query : ∀ s, InstReachable hD hd A spec a b c d k rows coins s → s.pc = .invoke →
    Bd.Computes P (paperL rows a b c d) I.query (enc s) (bitsVal s.query)
  /-- The invoke edge, given the actual answer bit (argument `(answer, state)`). -/
  resume : ∀ s edge, InstReachable hD hd A spec a b c d k rows coins s → s.pc = .invoke →
    instStep hD hd A spec a b c d k rows coins s = some edge →
    Bd.Computes P (paperL rows a b c d) I.resume
      (Val.cons (Enc.bool ((instExt hD hd A spec c d k rows coins).sat s.query).value) (enc s))
      (enc edge.next)
  /-- Every other edge (including query compilation and the endpoints). -/
  step : ∀ s edge, InstReachable hD hd A spec a b c d k rows coins s → s.pc ≠ .invoke →
    instStep hD hd A spec a b c d k rows coins s = some edge →
    Bd.Computes P (paperL rows a b c d) I.step (enc s) (enc edge.next)
  /-- The raw output word, at `.done`. -/
  output : ∀ s, InstReachable hD hd A spec a b c d k rows coins s → s.pc = .done →
    Bd.Computes P (paperL rows a b c d) I.output (enc s) (bitsVal (ratioWord s.output))

end Instance

/-- **The per-instance contract, `n = 0`.** -/
def ZeroFacts (P : Program) (I : Indices) (Bd : Budget) (rows : List (List (PauliCoord 0)))
    (a b c d : ℕ) : Prop :=
  ∃ v : Val,
    Bd.Computes P (paperL rows a b c d) I.init (bitsVal (machineInput rows a b c d [])) v ∧
    Bd.Computes P (paperL rows a b c d) I.isDone v (Enc.bool true) ∧
    Bd.Computes P (paperL rows a b c d) I.output v
      (bitsVal (outputWord ZeroLengthDispatch.zeroVector))

/-- **The component bundle** for the fixed hash certificate `A` and SAT density `density`:
the FL program, its function indices, the polynomial budget, and the per-instance facts. -/
structure Components {D t : ℕ} (hD : D = 16^384) (hd : D = 256*t)
    (A : FiniteLocalSelectorCandidate.CertifiedParity (512*t) (64*t) t) (density : ℕ) where
  P : Program
  idx : Indices
  budget : Budget
  positive : ∀ {kE : ℕ} {ΓE ΛE : Type} [Fintype ΓE] [Inhabited ΓE] [Fintype ΛE]
    (E : Machine kE ΓE ΛE) (PtE PsE : PolynomialEnvelope) (T : ℕ → ℕ)
    (spec : EncodedSAT E density PtE PsE T), Monotone T →
    ∀ (a b c d k : ℕ) (rows : List (List (PauliCoord (k+1))))
      (coins : Fin (coinBits hD hd A c d (k+1)) → Bool),
      0 < a → a ≤ b → 0 < c → 0 < d →
      ∃ enc : Config → Val, PositiveFacts hD hd A P idx budget spec a b c d k rows coins enc
  zero : ∀ (rows : List (List (PauliCoord 0))) (a b c d : ℕ),
    0 < a → a ≤ b → 0 < c → 0 < d → ZeroFacts P idx budget rows a b c d

end QecReliability.Assembly

end
