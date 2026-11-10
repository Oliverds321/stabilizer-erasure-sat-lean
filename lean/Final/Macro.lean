import Final.ConcreteExternal
import WholeWrapperFixedProbability
import WholeWrapperFixedSlots
import WholeWrapperFactoryInputRun

/-!
# Closed macro-level theorem

`macro_main` packages, for the fixed all-length hash factory (certificate `A`) and the
external SAT machine `E` (premise `EncodedSAT E density PtE PsE T`), everything the
first-order controller `WholeWrapperCandidate.step` does when its `External` interface is
`concreteExternal` (`Final/ConcreteExternal.lean`):

* positive length `n = k+1`, for EVERY stored random word `w`: the controller trace from
  `initial` halts at `pc = .done` with `output` equal to the stored-dispatch coefficient
  vector, with exact/capped call counts and SAT time, a polynomial dispatch count, and
  polynomial (in `paperLength`) fixed-slot / represented-bit / query-buffer bounds on
  EVERY reachable state; every SAT invocation is on a canonical padded query on which
  `E` has a completed run whose observations are the reply;
* `n = 0`: the zero-length dispatch (no controller run, constant vector, no calls);
* for all `n`: deterministic `ShapeStructure` (proved here WITHOUT a `Lift`, i.e. for
  arbitrary, possibly non-isotropic, `rows`), call/time caps, physical target optimality and
  the `1 - c/d` confidence bound.

`macro_main_closed` removes the certificate parameter using
`exists_one_fixed_all_length_factory`; it is a single hypothesis-free statement.
-/

set_option autoImplicit false
-- The linter traverses huge elaborated factory terms and hits the recursion limit.
set_option linter.constructorNameAsVariable false

noncomputable section
namespace QecReliability.Final
open OracleCost OracleCost.MultiTape OracleCost.MultiTape.FixedSlot OracleCost.WholeWrapperCandidate
open Binary SharedCircuit SharedCircuit.LatentEncoding SharedCircuit.ConcreteQuantum
open RationalOutput QecPhysical QecPhysical.Stabilizer
open OracleCost.StoredCodeHashConfidence
open SharedCircuit.FixedLocalEmitter.AllLength FiniteLocalSelectorCandidate

/-! ## Generic controller facts -/

/-- Only the `compile` edge enters `invoke`, and it installs the compiled query of the
current request. -/
theorem step_invoke_query {q r B m : ℕ} {shape : Bool} {ext : External} {s : Config}
    {edge : Edge} (he : step q r B m shape ext s = some edge) :
    edge.next.pc = .invoke → edge.next.query = (ext.compileQuery edge.next.request).bits := by
  cases hp : s.pc <;> simp only [step, hp] at he
  all_goals try contradiction
  all_goals repeat' first
    | (simp only [localEdge, Option.some.injEq] at he; subst edge)
    | split at he
  all_goals first
    | (intro _; rfl)
    | (intro h; simp only at h; exact absurd h (by decide))

theorem reachable_invoke_query {q r B m : ℕ} {shape : Bool} {ext : External} {s : Config}
    (h : Reachable q r B m shape ext s) :
    s.pc = .invoke → s.query = (ext.compileQuery s.request).bits := by
  obtain ⟨totals, events, h⟩ := h
  exact h.preserves (fun s => s.pc = .invoke → s.query = (ext.compileQuery s.request).bits)
    (fun _ _ _ he => step_invoke_query he) (by intro hpc; cases hpc)

theorem trace_reachable_end {q r B m : ℕ} {shape : Bool} {ext : External}
    {final : Config} {totals : Totals} {events : List RequestKey}
    (h : Trace q r B m shape ext (initial q r m) totals events final) :
    Reachable q r B m shape ext final := ⟨totals, events, h⟩

/-- Determinism: a reachable state lies on the path to any terminal state reached from
the same start. -/
theorem trace_reaches_terminal {q r B m : ℕ} {shape : Bool} {ext : External}
    {s t u : Config} {T₁ T₂ : Totals} {E₁ E₂ : List RequestKey}
    (h₂ : Trace q r B m shape ext s T₂ E₂ u) (h₁ : Trace q r B m shape ext s T₁ E₁ t)
    (ht : step q r B m shape ext t = none) :
    ∃ T₃ E₃, Trace q r B m shape ext u T₃ E₃ t := by
  induction h₂ generalizing T₁ E₁ with
  | nil => exact ⟨T₁, E₁, h₁⟩
  | @cons s edge v totals events he tail ih =>
      cases h₁ with
      | nil => rw [ht] at he; cases he
      | cons he' tail' =>
          have hedge := Option.some.inj (he.symm.trans he')
          subst hedge
          exact ih tail'

/-! ## Polynomial bounds -/

/-- The cell budget is quadratic in `⌊b/a⌋`, i.e. in `1/ε`. -/
theorem rationalCellBudget_le {a : ℕ} (b : ℕ) (ha : 0 < a) :
    rationalCellBudget a b ≤ 144 * (b / a + 1) ^ 2 := by
  have hb : b < a * (b / a + 1) := Nat.lt_mul_div_succ b ha
  have hb' : b * b ≤ (a * (b / a + 1)) * (a * (b / a + 1)) :=
    Nat.mul_le_mul hb.le hb.le
  apply (ceilDiv_le_iff (Nat.mul_pos ha ha)).mpr
  calc 144 * b * b = 144 * (b * b) := by ring
    _ ≤ 144 * ((a * (b / a + 1)) * (a * (b / a + 1))) := Nat.mul_le_mul_left _ hb'
    _ = a * a * (144 * (b / a + 1) ^ 2) := by ring

theorem totalCallCap_mono {q q' r r' B m m' : ℕ} (hq : q ≤ q') (hr : r ≤ r') (hm : m ≤ m') :
    totalCallCap q r B m ≤ totalCallCap q' r' B m' := by
  unfold totalCallCap trialCallCap prefixCallCap
  gcongr

theorem macroDispatchBound_mono {q q' r r' B m m' : ℕ} (hq : q ≤ q') (hr : r ≤ r')
    (hm : m ≤ m') : macroDispatchBound q r B m ≤ macroDispatchBound q' r' B m' := by
  have ht := totalCallCap_mono (B := B) hq hr hm
  unfold macroDispatchBound coefficientLocalBound
  gcongr

/-- The established dispatch bound is below the controller's original candidate
`dispatchBound` as soon as `q ≥ 2` (here `q = keySize (k+1) (k+1) = 3(k+1)`). -/
theorem macroDispatchBound_le_dispatchBound {q r B m : ℕ} (hq : 2 ≤ q) :
    macroDispatchBound q r B m ≤ dispatchBound q r B m := by
  have hp := program_length q r m
  have key : 2*(r+1)*(2*m+1)*(5*q+28) ≤ 2*(r+1)*(2*m+1)*(9*q+23) :=
    Nat.mul_le_mul_left _ (by omega)
  unfold macroDispatchBound dispatchBound totalCallCap trialCallCap coefficientLocalBound
  simp only [hp, coefficientCodeLength]
  ring_nf
  ring_nf at key
  omega

/-- Explicit dispatch polynomial in the input length `L` and the cell budget `B`. -/
def dispatchPoly (L B : ℕ) : ℕ := macroDispatchBound (2 * L) L B (3 * L + 2)

/-- Explicit call-cap polynomial in `L` and `B`. -/
def callPoly (L B : ℕ) : ℕ := 2 * (L + 1) * (6 * L + 5) * trialCallBound (2 * L) B

/-- Linear-in-`(n + incidences)` SAT variable constant (fixed by the factory and the
SAT density, independent of the instance). -/
def variableConstant (G density : ℕ) : ℕ := (density + 1) * (12 * G + 105)

theorem engineVariables_iid_le {n : ℕ} (rows : List (List (PauliCoord n))) (G density : ℕ) :
    QuantumService.engineVariables rows (ZeroLengthDispatch.iidProgram n) density
        (G * keySize n n) ≤
      variableConstant G density * (n + rowIncidences rows + 1) := by
  unfold QuantumService.engineVariables QuantumService.variableBound
    QuantumService.clauseBound variableConstant
  simp only [ZeroLengthDispatch.iidProgram_gates, keySize]
  set I := rowIncidences rows
  apply max_le
  · nlinarith [Nat.zero_le density, Nat.zero_le G, Nat.zero_le (G * n), Nat.zero_le I,
      Nat.zero_le (density * (G * n)), Nat.zero_le (density * n), Nat.zero_le (density * I)]
  · nlinarith [Nat.zero_le density, Nat.zero_le G, Nat.zero_le (G * n), Nat.zero_le I,
      Nat.zero_le (density * (G * n)), Nat.zero_le (density * n), Nat.zero_le (density * I)]

theorem trialCallBound_two_le (L B : ℕ) :
    trialCallBound (2 * L) B ≤ 32 * (L + 1) ^ 2 * (B + 1) := by
  unfold trialCallBound
  have h1 : 1 + 2 * (2 * L) * (4 * B + 1) ≤ 16 * (L + 1) * (B + 1) := by
    ring_nf; omega
  have h2 : (2 * L + 1) * (1 + 2 * (2 * L) * (4 * B + 1)) ≤
      (2 * L + 1) * (16 * (L + 1) * (B + 1)) := Nat.mul_le_mul_left _ h1
  have h3 : 1 ≤ 16 * (L + 1) * (B + 1) := Nat.succ_le_of_lt (by positivity)
  calc 1 + (2 * L + 1) * (1 + 2 * (2 * L) * (4 * B + 1))
      ≤ 1 + (2 * L + 1) * (16 * (L + 1) * (B + 1)) := by omega
    _ ≤ 16 * (L + 1) * (B + 1) + (2 * L + 1) * (16 * (L + 1) * (B + 1)) := by omega
    _ = 32 * (L + 1) ^ 2 * (B + 1) := by ring

theorem callPoly_le (L B : ℕ) : callPoly L B ≤ 384 * (L + 1) ^ 4 * (B + 1) := by
  unfold callPoly
  have h := trialCallBound_two_le L B
  calc 2 * (L + 1) * (6 * L + 5) * trialCallBound (2 * L) B
      ≤ 2 * (L + 1) * (6 * (L + 1)) * (32 * (L + 1) ^ 2 * (B + 1)) := by
        gcongr; omega
    _ = 384 * (L + 1) ^ 4 * (B + 1) := by ring

theorem dispatchPoly_le (L B : ℕ) : dispatchPoly L B ≤ 4096 * (L + 1) ^ 4 * (B + 1) := by
  have ht : totalCallCap (2 * L) L B (3 * L + 2) ≤ 384 * (L + 1) ^ 4 * (B + 1) := by
    have h := trialCallBound_two_le L B
    unfold totalCallCap
    have heq : trialCallCap (2 * L) B = trialCallBound (2 * L) B := by
      unfold trialCallCap prefixCallCap trialCallBound; rfl
    rw [heq]
    calc 2 * (L + 1) * (2 * (3 * L + 2) + 1) * trialCallBound (2 * L) B
        ≤ 2 * (L + 1) * (6 * (L + 1)) * (32 * (L + 1) ^ 2 * (B + 1)) := by
          gcongr; omega
      _ = 384 * (L + 1) ^ 4 * (B + 1) := by ring
  have hc : coefficientLocalBound (2 * L) (3 * L + 2) ≤ 231 * (L + 1) ^ 2 := by
    unfold coefficientLocalBound
    ring_nf; omega
  unfold dispatchPoly macroDispatchBound
  have hc' : 2 * (L + 1) * coefficientLocalBound (2 * L) (3 * L + 2) ≤
      2 * (L + 1) * (231 * (L + 1) ^ 2) := Nat.mul_le_mul_left _ hc
  have hpow : (L + 1) ^ 3 ≤ (L + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have hpow1 : (L + 1) ≤ (L + 1) ^ 4 := by
    calc L + 1 = (L + 1) ^ 1 := (pow_one _).symm
      _ ≤ (L + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have hB : (L + 1) ^ 4 ≤ (L + 1) ^ 4 * (B + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have e1 : 2 * (L + 1) * (231 * (L + 1) ^ 2) = 462 * (L + 1) ^ 3 := by ring
  have e2 : 4096 * (L + 1) ^ 4 * (B + 1) = 3072 * ((L + 1) ^ 4 * (B + 1)) +
      1024 * ((L + 1) ^ 4 * (B + 1)) := by ring
  have e3 : 384 * (L + 1) ^ 4 * (B + 1) = 384 * ((L + 1) ^ 4 * (B + 1)) := by ring
  rw [e2]
  rw [e3] at ht
  rw [e1] at hc'
  omega

/-! ## SAT runs on padded queries -/

section SATRuns
variable {kE : ℕ} {ΓE ΛE : Type*} [Fintype ΓE] [Inhabited ΓE] [Fintype ΛE]
    {E : Machine kE ΓE ΛE} {density : ℕ} {PtE PsE : PolynomialEnvelope} {T : ℕ → ℕ}

/-- On a canonical padded query, `E` has a completed run within its space envelope whose
observations are exactly `satReply`. -/
theorem padded_run (spec : EncodedSAT E density PtE PsE T) {bits : List Bool}
    (hbits : IsPaddedQuery density bits) :
    ∃ run : Completed E bits, run.cells ≤ PsE.eval bits.length ∧
      (satReply spec bits).value = run.output ∧ (satReply spec bits).time = run.time ∧
      (satReply spec bits).workspace = machineCellBits ΓE * run.cells + machineControlBits ΛE := by
  obtain ⟨req, rfl⟩ := hbits
  exact ⟨spec.run req, (spec.run_spec req).2.2, satReply_of_completed spec ⟨req, rfl⟩ _⟩

end SATRuns

/-! ## Shape structure without a lift -/

/-- `ShapeStructure` of the stored dispatcher's output for ARBITRARY rows: the endpoint
order `score S univ ≤ score S ∅ = 1` holds without isotropy. -/
theorem storedRun_structure {length width : ℕ → ℕ}
    (S : ∀ k, CodeHash.System (CoefficientKey (k+1) (k+1)) (length k) (width k)
      (keySize (k+1) (k+1)))
    (K : ∀ k, SuppliedHashCircuits (actualCodeHash (S k)) (keyBits (k+1) (k+1)))
    (service : SATService) (a b c d n : ℕ) (rows : List (List (PauliCoord n)))
    (w : StoredBitDispatch.RawInput length width c d n) :
    ShapeStructure (rowSpace rows) (circuitMap (ZeroLengthDispatch.iidProgram n))
      (StoredBitDispatch.run S K service a b c d n rows w).curve := by
  rw [StoredBitDispatch.run_eq_source_dispatch]
  cases n with
  | zero => exact ZeroLengthDispatch.zeroVector_structure rows _
  | succ k =>
    simp only [ZeroLengthDispatch.run, LinearRepair.prepare_coefficients, ↓reduceIte,
      shapeVector_curve]
    apply cachedShape_structural
    simp only [ZeroLengthDispatch.iidProgram_map, id_eq, score_empty]
    exact (score_range _ _).2

/-! ## The fixed factory instantiation -/

variable {D t : ℕ} (hD : D = 16^384) (hd : D = 256*t)
    (A : CertifiedParity (512*t) (64*t) t)

/-- Repetition budget for `n = k+1`. -/
abbrev macroM (c d k : ℕ) : ℕ := rationalRepetitionBudget (2*((k+1)+1)) c d

/-- Stored random word for `n` qubits (`Unit` for `n = 0`). -/
abbrev Word (c d n : ℕ) : Type :=
  StoredBitDispatch.RawInput (positiveLength hD hd A) (positiveWidth hD hd A) c d n

/-- Hash seeds decoded from a stored word. -/
def macroSeeds (c d k : ℕ) (w : Word hD hd A c d (k+1)) :
    Fin (2*macroM c d k+1) → CodeHash.Seed (positiveLength hD hd A k) (positiveWidth hD hd A k) :=
  actualCodeHashSeedTuple (positiveLength hD hd A k) (positiveWidth hD hd A k) (macroM c d k) w

/-! ## Coins on the input tape -/

/-- Number of coin bits read after the problem encoding (`0` for `n = 0`). -/
abbrev coinBits (c d n : ℕ) : ℕ :=
  StoredBitDispatch.randomBits (positiveLength hD hd A) (positiveWidth hD hd A) c d n

/-- The stored word determined by the coin string (`Unit` for `n = 0`). -/
def coinWord : (c d n : ℕ) → (Fin (coinBits hD hd A c d n) → Bool) → Word hD hd A c d n
  | _, _, 0, _ => ()
  | c, d, k+1, coins =>
      CodeHash.FiniteRandomTape.InputWord.ofTape (coinBits hD hd A c d (k+1)) coins

theorem inputWord_cells_ofTape (N : ℕ) (f : Fin N → Bool) :
    (CodeHash.FiniteRandomTape.InputWord.ofTape N f).cells = List.ofFn f := by
  induction N with
  | zero => rfl
  | succ N ih =>
      change f 0 :: (CodeHash.FiniteRandomTape.InputWord.ofTape N (fun i => f i.succ)).cells = _
      rw [ih, List.ofFn_succ]

/-- The stored word's cells are literally the coin bits on the tape. -/
theorem coinWord_cells (c d k : ℕ) (coins : Fin (coinBits hD hd A c d (k+1)) → Bool) :
    (show CodeHash.FiniteRandomTape.InputWord (coinBits hD hd A c d (k+1)) from
      coinWord hD hd A c d (k+1) coins).cells = List.ofFn coins :=
  inputWord_cells_ofTape _ coins

theorem coinWord_succ (c d k : ℕ) (coins : Fin (coinBits hD hd A c d (k+1)) → Bool) :
    coinWord hD hd A c d (k+1) coins =
      CodeHash.FiniteRandomTape.InputWord.ofTape (coinBits hD hd A c d (k+1)) coins := rfl

theorem coinWord_bijective (c d n : ℕ) : Function.Bijective (coinWord hD hd A c d n) := by
  cases n with
  | zero =>
      exact ⟨fun _ _ _ => funext (fun i => Fin.elim0 i), fun _ => ⟨fun i => Fin.elim0 i, rfl⟩⟩
  | succ k =>
      constructor
      · intro x y h
        rw [coinWord_succ, coinWord_succ] at h
        have h' : CodeHash.FiniteRandomTape.InputWord.ofTape (coinBits hD hd A c d (k+1)) x =
            CodeHash.FiniteRandomTape.InputWord.ofTape (coinBits hD hd A c d (k+1)) y := h
        have := congrArg CodeHash.FiniteRandomTape.InputWord.denote h'
        simpa only [CodeHash.FiniteRandomTape.InputWord.denote_ofTape] using this
      · intro w
        let w' : CodeHash.FiniteRandomTape.InputWord (coinBits hD hd A c d (k+1)) := w
        refine ⟨CodeHash.FiniteRandomTape.InputWord.denote w', ?_⟩
        rw [coinWord_succ]
        exact CodeHash.FiniteRandomTape.InputWord.ofTape_denote w'

open scoped Classical in
/-- The input law is the uniform law on coin strings, transported by `coinWord`. -/
theorem inputLaw_prob_coins (c d n : ℕ) (P : Word hD hd A c d n → Prop) :
    (StoredBitDispatch.inputLaw (positiveLength hD hd A) (positiveWidth hD hd A) c d n).prob P =
      ((Finset.univ.filter (fun coins : Fin (coinBits hD hd A c d n) → Bool =>
        P (coinWord hD hd A c d n coins))).card : ℝ) / 2 ^ coinBits hD hd A c d n := by
  cases n with
  | zero =>
      have hcard : (Finset.univ.filter (fun coins : Fin (coinBits hD hd A c d 0) → Bool =>
          P (coinWord hD hd A c d 0 coins))).card = if P () then 1 else 0 := by
        by_cases h : P ()
        · rw [if_pos h, Finset.card_eq_one]
          refine ⟨fun i => Fin.elim0 i, ?_⟩
          ext x
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
          exact ⟨fun _ => funext (fun i => Fin.elim0 i), fun _ => h⟩
        · rw [if_neg h, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
          intro x _
          exact h
      have hbits : coinBits hD hd A c d 0 = 0 := rfl
      change ZeroLengthDispatch.unitLaw.prob P = _
      rw [hcard, hbits]
      by_cases h : P ()
      · simp [FiniteProbability.prob, FiniteProbability.expect, average, indicator,
          ZeroLengthDispatch.unitLaw, h]
      · simp [FiniteProbability.prob, FiniteProbability.expect, average, indicator,
          ZeroLengthDispatch.unitLaw, h]
  | succ k =>
      let N := coinBits hD hd A c d (k+1)
      let Q : CodeHash.FiniteRandomTape.InputWord N → Prop := P
      have h1 : (uniformLaw (CodeHash.FiniteRandomTape.InputWord N)).prob Q =
          ((Finset.univ.filter Q).card : ℝ) /
            Fintype.card (CodeHash.FiniteRandomTape.InputWord N) :=
        uniformLaw_prob Q
      have h3 : (Fintype.card (CodeHash.FiniteRandomTape.InputWord N) : ℝ) = 2 ^ N := by
        rw [CodeHash.FiniteRandomTape.inputWord_card]
        push_cast
        rfl
      have h2 : (Finset.univ.filter Q).card = (Finset.univ.filter (fun coins : Fin N → Bool =>
            P (coinWord hD hd A c d (k+1) coins))).card := by
        apply Finset.card_nbij' (fun w => CodeHash.FiniteRandomTape.InputWord.denote w)
          (fun coins => CodeHash.FiniteRandomTape.InputWord.ofTape N coins)
        · intro w hw
          simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hw ⊢
          rw [coinWord_succ, CodeHash.FiniteRandomTape.InputWord.ofTape_denote]
          exact hw
        · intro coins hc
          simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hc ⊢
          rw [coinWord_succ] at hc
          exact hc
        · intro w _
          exact CodeHash.FiniteRandomTape.InputWord.ofTape_denote w
        · intro coins _
          exact CodeHash.FiniteRandomTape.InputWord.denote_ofTape N coins
      exact h1.trans (congrArg₂ (· / ·) (congrArg Nat.cast h2) h3)

open scoped Classical in
/-- Counting form of a probability lower bound over the coin strings. -/
theorem coins_count_of_prob (c d n : ℕ) (P : Word hD hd A c d n → Prop) (p : ℝ)
    (h : p ≤ (StoredBitDispatch.inputLaw (positiveLength hD hd A) (positiveWidth hD hd A)
      c d n).prob P) :
    p * 2 ^ coinBits hD hd A c d n ≤
      ((Finset.univ.filter (fun coins : Fin (coinBits hD hd A c d n) → Bool =>
        P (coinWord hD hd A c d n coins))).card : ℝ) := by
  rw [inputLaw_prob_coins] at h
  have hpos : (0:ℝ) < 2 ^ coinBits hD hd A c d n := by positivity
  exact (le_div_iff₀ hpos).mp h

section Main
variable {kE : ℕ} {ΓE ΛE : Type*} [Fintype ΓE] [Inhabited ΓE] [Fintype ΛE]
    {E : Machine kE ΓE ΛE} {density : ℕ} {PtE PsE : PolynomialEnvelope} {T : ℕ → ℕ}

/-- The concrete external interface for `n = k+1` and stored word `w`. -/
def macroExternal (spec : EncodedSAT E density PtE PsE T) (c d k : ℕ)
    (rows : List (List (PauliCoord (k+1)))) (w : Word hD hd A c d (k+1)) : External :=
  concreteExternal rows (ZeroLengthDispatch.iidProgram (k+1))
    (actualCodeHash (positiveSystem hD hd A k)) (positiveCircuits hD hd A k)
    (macroM c d k) (macroSeeds hD hd A c d k w) density spec

/-- Input length `L` of the manuscript (`= Final.paperL rows a b c d`, definitionally). -/
abbrev macroL {n : ℕ} (rows : List (List (PauliCoord n))) (a b c d : ℕ) : ℕ :=
  InputEncoding.paperLength rows (ZeroLengthDispatch.iidProgram n) a b c d

/-- Stored-dispatch coefficient vector (the semantic target of the machine). -/
abbrev macroRun (spec : EncodedSAT E density PtE PsE T) (a b c d n : ℕ)
    (rows : List (List (PauliCoord n))) (w : Word hD hd A c d n) : RationalOutput.Vector n :=
  StoredBitDispatch.run (positiveSystem hD hd A) (positiveCircuits hD hd A) spec.service
    a b c d n rows w

/-- Everything known about the controller run for `n = k+1` and one stored word.
Controller parameters: `q = keySize (k+1) (k+1)`, `r = k+1`, `B = rationalCellBudget a b`,
`m = macroM c d k`, `shape = true`. `L = macroL rows a b c d`, `G = gateConstant`. -/
structure PositiveRun (spec : EncodedSAT E density PtE PsE T) (a b c d k : ℕ)
    (rows : List (List (PauliCoord (k+1)))) (w : Word hD hd A c d (k+1))
    (final : Config) (totals : Totals) : Prop where
  trace : ∃ events, Trace (keySize (k+1) (k+1)) (k+1) (rationalCellBudget a b) (macroM c d k)
    true (macroExternal hD hd A spec c d k rows w)
    (initial (keySize (k+1) (k+1)) (k+1) (macroM c d k)) totals events final
  done : final.pc = .done
  halted : step (keySize (k+1) (k+1)) (k+1) (rationalCellBudget a b) (macroM c d k) true
    (macroExternal hD hd A spec c d k rows w) final = none
  drive : ∀ fuel, totals.dispatches < fuel →
    drive (keySize (k+1) (k+1)) (k+1) (rationalCellBudget a b) (macroM c d k) true
      (macroExternal hD hd A spec c d k rows w) fuel
      (initial (keySize (k+1) (k+1)) (k+1) (macroM c d k)) = some final
  output : final.output = (macroRun hD hd A spec a b c d (k+1) rows w).entries.toList
  calls_eq : totals.calls = StoredBitDispatch.calls (positiveSystem hD hd A)
    (positiveCircuits hD hd A) spec.service a b c d (k+1) rows w
  calls_le : totals.calls ≤ StoredBitDispatch.callCap a b c d (k+1)
  calls_poly : totals.calls ≤ callPoly (macroL rows a b c d) (rationalCellBudget a b)
  oracleTime_eq : totals.oracleTime = StoredBitDispatch.oracleTime (positiveSystem hD hd A)
    (positiveCircuits hD hd A) spec.service a b c d (k+1) rows w
  oracleTime_le : totals.oracleTime ≤ StoredBitDispatch.timeCap PtE T density
    (fun k => gateConstant hD hd A * keySize (k+1) (k+1)) a b c d (k+1) rows
  oracleTime_poly : totals.oracleTime ≤
    callPoly (macroL rows a b c d) (rationalCellBudget a b) *
      PtE.eval (InputEncoding.queryPolynomial (gateConstant hD hd A) density
        (macroL rows a b c d)) *
      T (variableConstant (gateConstant hD hd A) density * ((k+1) + rowIncidences rows + 1))
  endpointTime : totals.endpointTime = 0
  dispatches_le : totals.dispatches ≤
    macroDispatchBound (keySize (k+1) (k+1)) (k+1) (rationalCellBudget a b) (macroM c d k)
  dispatches_poly : totals.dispatches ≤
    dispatchPoly (macroL rows a b c d) (rationalCellBudget a b)
  dispatches_le_candidate : totals.dispatches ≤
    dispatchBound (keySize (k+1) (k+1)) (k+1) (rationalCellBudget a b) (macroM c d k)
  on_path : ∀ s, Reachable (keySize (k+1) (k+1)) (k+1) (rationalCellBudget a b) (macroM c d k)
      true (macroExternal hD hd A spec c d k rows w) s →
    ∃ rest events, Trace (keySize (k+1) (k+1)) (k+1) (rationalCellBudget a b) (macroM c d k)
      true (macroExternal hD hd A spec c d k rows w) s rest events final
  fields : ∀ s, Reachable (keySize (k+1) (k+1)) (k+1) (rationalCellBudget a b) (macroM c d k)
      true (macroExternal hD hd A spec c d k rows w) s →
    Fits (slotWidth (macroL rows a b c d)) (fieldPolynomial (macroL rows a b c d))
        (configFields s) ∧
      (fixedFieldsBits (macroL rows a b c d) s).length =
        fixedFieldsCapacity (macroL rows a b c d) ∧
      (∀ suffix, readFields (slotWidth (macroL rows a b c d))
        (fieldPolynomial (macroL rows a b c d)) 22
          (fixedFieldsBits (macroL rows a b c d) s ++ suffix) = some (configFields s, suffix))
  represented : ∀ s, Reachable (keySize (k+1) (k+1)) (k+1) (rationalCellBudget a b)
      (macroM c d k) true (macroExternal hD hd A spec c d k rows w) s →
    (representedBits s).length ≤
      InputEncoding.retainedPolynomial (gateConstant hD hd A) density (macroL rows a b c d)
  query : ∀ s, Reachable (keySize (k+1) (k+1)) (k+1) (rationalCellBudget a b)
      (macroM c d k) true (macroExternal hD hd A spec c d k rows w) s →
    s.query.length ≤
      InputEncoding.queryPolynomial (gateConstant hD hd A) density (macroL rows a b c d)
  invoke : ∀ s, Reachable (keySize (k+1) (k+1)) (k+1) (rationalCellBudget a b)
      (macroM c d k) true (macroExternal hD hd A spec c d k rows w) s → s.pc = .invoke →
    IsPaddedQuery density s.query ∧
    ∃ run : Completed E s.query,
      run.cells ≤ PsE.eval
        (InputEncoding.queryPolynomial (gateConstant hD hd A) density (macroL rows a b c d)) ∧
      ((macroExternal hD hd A spec c d k rows w).sat s.query).value = run.output ∧
      ((macroExternal hD hd A spec c d k rows w).sat s.query).time = run.time ∧
      ((macroExternal hD hd A spec c d k rows w).sat s.query).workspace =
        machineCellBits ΓE * run.cells + machineControlBits ΛE

theorem positive_run (spec : EncodedSAT E density PtE PsE T) (hT : Monotone T)
    (a b c d : ℕ) (ha : 0 < a) (hc : 0 < c) (k : ℕ)
    (rows : List (List (PauliCoord (k+1)))) (w : Word hD hd A c d (k+1)) :
    ∃ final totals, PositiveRun hD hd A spec a b c d k rows w final totals := by
  let C := ZeroLengthDispatch.iidProgram (k+1)
  let H := actualCodeHash (positiveSystem hD hd A k)
  let Kc := positiveCircuits hD hd A k
  let m := macroM c d k
  let B := rationalCellBudget a b
  let ω := macroSeeds hD hd A c d k w
  let ext := macroExternal hD hd A spec c d k rows w
  let G := gateConstant hD hd A
  let L := macroL rows a b c d
  have hboundary : BoundaryCorrect rows C H Kc spec.service m ω density ext :=
    concreteExternal_boundary rows C H Kc m ω density spec
  have hg : ∀ scale seed, (Kc.program scale seed).gates ≤ G * keySize (k+1) (k+1) :=
    fun scale seed => positiveCircuits_gates hD hd A k scale seed
  obtain ⟨final, totals, events, htrace, hout, -, hcalls, htime, hendpoint, hcap, hdispatch,
      hall, -, -⟩ :=
    initial_output_with_input_representation rows C H Kc spec.service a b c d ha hc ω
      G density true ext hboundary hg
  obtain ⟨-, hq, hr, hR, -⟩ := InputEncoding.budget_parameters rows C a b c d ha hc
  have hq : keySize (k+1) (k+1) ≤ 2 * L := hq
  have hr : k + 1 ≤ L := hr
  have hR : 2 * m + 1 ≤ 6 * L + 5 := hR
  have hterminal : step (keySize (k+1) (k+1)) (k+1) B m true ext final = none := by
    simp only [step, hout.1]
  have hcallsEq : totals.calls = StoredBitDispatch.calls (positiveSystem hD hd A)
      (positiveCircuits hD hd A) spec.service a b c d (k+1) rows w := by
    simpa only [StoredBitDispatch.calls, rawBitOutput, QuantumService.output_eq,
      LinearRepair.prepare, prepareRational, C, H, Kc, ω, macroSeeds, macroM] using hcalls
  have htimeEq : totals.oracleTime = StoredBitDispatch.oracleTime (positiveSystem hD hd A)
      (positiveCircuits hD hd A) spec.service a b c d (k+1) rows w := htime
  have hcallsLe : totals.calls ≤ StoredBitDispatch.callCap a b c d (k+1) := by
    rw [hcallsEq]
    exact StoredBitDispatch.run_calls_le (positiveSystem hD hd A) (positiveCircuits hD hd A)
      spec.service a b c d (k+1) rows w
  have hcallCapPoly : StoredBitDispatch.callCap a b c d (k+1) ≤ callPoly L B := by
    change 2*((k+1)+1)*(2*m+1)*trialCallBound (keySize (k+1) (k+1)) B ≤
      2 * (L + 1) * (6 * L + 5) * trialCallBound (2 * L) B
    have htr : trialCallBound (keySize (k+1) (k+1)) B ≤ trialCallBound (2 * L) B := by
      unfold trialCallBound
      gcongr
    have h1 : 2*((k+1)+1) ≤ 2 * (L + 1) := by omega
    exact Nat.mul_le_mul (Nat.mul_le_mul h1 hR) htr
  have htimeLe : totals.oracleTime ≤ StoredBitDispatch.timeCap PtE T density
      (fun k => G * keySize (k+1) (k+1)) a b c d (k+1) rows := by
    rw [htimeEq]
    exact StoredBitDispatch.run_engine_time_le (positiveSystem hD hd A)
      (positiveCircuits hD hd A) spec hT (fun k => G * keySize (k+1) (k+1))
      (fun k scale seed => positiveCircuits_gates hD hd A k scale seed) a b c d (k+1) rows w
  have hquery : ∀ s, Reachable (keySize (k+1) (k+1)) (k+1) B m true ext s →
      s.query.length ≤ InputEncoding.queryPolynomial G density L := fun s hs =>
    (reachable_concrete_query_bound rows C H Kc spec.service m ω B density
      (G * keySize (k+1) (k+1)) true ext hboundary hg hs).trans
      (InputEncoding.engineInputBound_input_polynomial rows C a b c d G density)
  refine ⟨final, totals, ⟨events, htrace⟩, hout.1, hterminal,
    htrace.drive_of_terminal hterminal, ?_, hcallsEq, hcallsLe,
    hcallsLe.trans hcallCapPoly, htimeEq, htimeLe, ?_, ?_, hdispatch, ?_,
    hdispatch.trans (macroDispatchBound_le_dispatchBound (by simp only [keySize]; omega)),
    ?_, ?_, hall, hquery, ?_⟩
  · -- output
    simpa only [StoredBitDispatch.run, rawBitOutput, QuantumService.output_eq,
      LinearRepair.prepare, prepareRational, C, H, Kc, ω, macroSeeds, macroM,
      Array.toArray_toList] using hout.2.2.2.1
  · -- oracle time, polynomial form
    refine htimeLe.trans ?_
    change StoredBitDispatch.callCap a b c d (k+1) *
        PtE.eval (QuantumService.engineInputBound rows C density (G * keySize (k+1) (k+1))) *
        T (QuantumService.engineVariables rows C density (G * keySize (k+1) (k+1))) ≤ _
    have hp := PtE.monotone
      (InputEncoding.engineInputBound_input_polynomial rows C a b c d G density)
    have ht := hT (engineVariables_iid_le rows G density)
    exact Nat.mul_le_mul (Nat.mul_le_mul hcallCapPoly hp) ht
  · -- endpoint time
    rw [hendpoint]
    rfl
  · -- dispatch polynomial
    have hm : macroM c d k ≤ 3 * L + 2 := by omega
    exact hdispatch.trans (macroDispatchBound_mono hq hr hm)
  · -- every reachable state is on the path to `final`
    intro s ⟨T₂, E₂, hs⟩
    exact trace_reaches_terminal hs htrace hterminal
  · -- fixed fields
    intro s hs
    exact reachable_fixed_fields_input rows C H Kc spec.service a b c d ha hc ω density true ext
      hboundary hs
  · -- invocations
    intro s hs hpc
    have hq' := reachable_invoke_query hs hpc
    have hvalid := (reachable_request_invariant hs).request
    have hpad : IsPaddedQuery density s.query := by
      rw [hq']
      exact concreteQuery_padded rows C H Kc m ω density s.request hvalid
    obtain ⟨run, hcells, hv, ht, hw⟩ := padded_run spec hpad
    exact ⟨hpad, run, hcells.trans (PsE.monotone (hquery s hs)), hv, ht, hw⟩

open scoped Classical in
/-- The closed macro statement for fixed factory parameters and SAT machine. -/
structure MacroMain (spec : EncodedSAT E density PtE PsE T) (a b c d : ℕ) : Prop where
  positive : ∀ (k : ℕ) (rows : List (List (PauliCoord (k+1)))) (w : Word hD hd A c d (k+1)),
    ∃ final totals, PositiveRun hD hd A spec a b c d k rows w final totals
  zero : ∀ (rows : List (List (PauliCoord 0))) (w : Word hD hd A c d 0),
    macroRun hD hd A spec a b c d 0 rows w = ZeroLengthDispatch.zeroVector ∧
    StoredBitDispatch.calls (positiveSystem hD hd A) (positiveCircuits hD hd A)
      spec.service a b c d 0 rows w = 0 ∧
    StoredBitDispatch.oracleTime (positiveSystem hD hd A) (positiveCircuits hD hd A)
      spec.service a b c d 0 rows w = 0 ∧
    StoredBitDispatch.randomBits (positiveLength hD hd A) (positiveWidth hD hd A) c d 0 = 0
  shape : ∀ (n : ℕ) (rows : List (List (PauliCoord n))) (w : Word hD hd A c d n),
    ShapeStructure (rowSpace rows) (circuitMap (ZeroLengthDispatch.iidProgram n))
      (macroRun hD hd A spec a b c d n rows w).curve
  calls_le : ∀ (n : ℕ) (rows : List (List (PauliCoord n))) (w : Word hD hd A c d n),
    StoredBitDispatch.calls (positiveSystem hD hd A) (positiveCircuits hD hd A)
      spec.service a b c d n rows w ≤ StoredBitDispatch.callCap a b c d n
  time_le : ∀ (n : ℕ) (rows : List (List (PauliCoord n))) (w : Word hD hd A c d n),
    StoredBitDispatch.oracleTime (positiveSystem hD hd A) (positiveCircuits hD hd A)
      spec.service a b c d n rows w ≤
    StoredBitDispatch.timeCap PtE T density
      (fun k => gateConstant hD hd A * keySize (k+1) (k+1)) a b c d n rows
  randomBits_le : ∀ (n : ℕ) (rows : List (List (PauliCoord n))),
    StoredBitDispatch.randomBits (positiveLength hD hd A) (positiveWidth hD hd A) c d n ≤
      (6 * macroL rows a b c d + 5) * (seedConstant hD hd A * (2 * macroL rows a b c d))
  cellBudget_le : rationalCellBudget a b ≤ 144 * (b / a + 1) ^ 2
  optimality : ∀ (n : ℕ) (rows : List (List (PauliCoord n))) (lift : Lift (rowSpace rows)),
    PhysicalTargetOptimality rows (ZeroLengthDispatch.iidProgram n) lift
  confidence : ∀ (n : ℕ) (rows : List (List (PauliCoord n))) (lift : Lift (rowSpace rows)),
    1 - (c:ℝ)/d ≤
      (StoredBitDispatch.inputLaw (positiveLength hD hd A) (positiveWidth hD hd A) c d n).prob
        (fun w => AllPhysicalTails rows (ZeroLengthDispatch.iidProgram n) lift ((a:ℝ)/b)
          (macroRun hD hd A spec a b c d n rows w).curve)
  /-- The same bound counted over coin strings (the `MainTheorem` form). -/
  confidence_coins : ∀ (n : ℕ) (rows : List (List (PauliCoord n))) (lift : Lift (rowSpace rows)),
    (1 - (c:ℝ)/d) * 2 ^ coinBits hD hd A c d n ≤
      ((Finset.univ.filter (fun coins : Fin (coinBits hD hd A c d n) → Bool =>
        AllPhysicalTails rows (ZeroLengthDispatch.iidProgram n) lift ((a:ℝ)/b)
          (macroRun hD hd A spec a b c d n rows (coinWord hD hd A c d n coins)).curve)).card : ℝ)

theorem macro_main (spec : EncodedSAT E density PtE PsE T) (hT : Monotone T)
    (a b c d : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd' : 0 < d) (hab : a ≤ b) :
    MacroMain hD hd A spec a b c d where
  positive k rows w := positive_run hD hd A spec hT a b c d ha hc k rows w
  zero _ _ := ⟨rfl, rfl, rfl, rfl⟩
  shape n rows w := storedRun_structure (positiveSystem hD hd A) (positiveCircuits hD hd A)
    spec.service a b c d n rows w
  calls_le n rows w := StoredBitDispatch.run_calls_le (positiveSystem hD hd A)
    (positiveCircuits hD hd A) spec.service a b c d n rows w
  time_le n rows w := StoredBitDispatch.run_engine_time_le (positiveSystem hD hd A)
    (positiveCircuits hD hd A) spec hT (fun k => gateConstant hD hd A * keySize (k+1) (k+1))
    (fun k scale seed => positiveCircuits_gates hD hd A k scale seed) a b c d n rows w
  randomBits_le n rows := randomBits_input_polynomial hD hd A a b c d ha hc n rows
  cellBudget_le := rationalCellBudget_le b ha
  optimality n rows lift := StoredBitDispatch.target_optimality n rows lift
  confidence n rows lift := (fixed_factory_dispatch_confidence hD hd A spec hT
    a b c d ha hb hc hd' hab n rows lift).2.2
  confidence_coins n rows lift := coins_count_of_prob hD hd A c d n
    (fun w => AllPhysicalTails rows (ZeroLengthDispatch.iidProgram n) lift ((a:ℝ)/b)
      (macroRun hD hd A spec a b c d n rows w).curve) (1 - (c:ℝ)/d)
    (fixed_factory_dispatch_confidence hD hd A spec hT a b c d ha hb hc hd' hab n rows lift).2.2

end Main

/-- Hypothesis-free packaging: one fixed hash certificate serves every SAT machine,
precision and instance. -/
theorem macro_main_closed :
    ∃ (t : ℕ) (hd : (16:ℕ)^384 = 256*t) (A : CertifiedParity (512*t) (64*t) t),
      ∀ {kE : ℕ} {ΓE ΛE : Type} [Fintype ΓE] [Inhabited ΓE] [Fintype ΛE]
        (E : Machine kE ΓE ΛE) (density : ℕ) (PtE PsE : PolynomialEnvelope) (T : ℕ → ℕ)
        (spec : EncodedSAT E density PtE PsE T), Monotone T →
      ∀ (a b c d : ℕ), 0 < a → 0 < b → 0 < c → 0 < d → a ≤ b →
        MacroMain rfl hd A spec a b c d := by
  obtain ⟨A, -⟩ := exists_one_fixed_all_length_factory
  refine ⟨2^1528, FiniteLocalCountingCandidate.fixed_degree_reparametrization, A, ?_⟩
  intro kE ΓE ΛE _ _ _ E density PtE PsE T spec hT a b c d ha hb hc hd' hab
  exact macro_main rfl _ A spec hT a b c d ha hb hc hd' hab

end QecReliability.Final
