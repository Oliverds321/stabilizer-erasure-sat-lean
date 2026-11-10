import Trans.Wire.Compile
import Assembly.Spec

/-!
# Trans.Wire.Agree: the wire functions agree with the concrete instance

For the fixed certificate `A`, SAT density `density`, and a positive instance
(`n = k+1`, coin string `coins`), with `base = (data hD hd A).base`, `den = (data hD hd A).den`:

* `instX`: the context data `X = wireX base den rows (List.ofFn coins)`;
* `seedB_positive`: `SB = seedB base den q` is the seed length `seedBits L t` of the
  algorithm's hash system (`positiveLength`, `positiveWidth`);
* `seed_slice`: the seed `macroSeeds … rep` is decoded from the slice
  `take SB (drop (rep·SB) coins)` that `sliceF` cuts;
* **`compile_agrees`**: for every valid key,
  `(compileF …).den (X, encKey key) = ((instExt …).compileQuery key).bits`, given that the
  query function means `Query.queryBits` and the hash function means `Hash.hashPlain` with
  oracles `encProg ∘ (data hD hd A).program`, `gNbr actualMGG` (true for
  `Query.queryFnF _` and `Hash.hashF C _ _ _` by definition, see `compile_agrees_std`);
* **`endpoint_agrees`**: `(endpointWF …).den (X, b) = toR ((instExt …).endpoint b).value`;
* **`extAgrees`**: Control's hypothesis `ExtAgrees x X (instExt …) s` at every reachable state
  (`step_correct` then gives every non-invoke edge, `wire_step_correct`);
* **`init_pos`**, **`init_zero`**, **`zero_isDone`**: the init function on the machine input.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace QecReliability.Trans.Wire
open QecReliability.FL QecReliability.FL.Lib
open QecReliability.Trans.Control (TKey TR encKey encCfg encCtx IxR TArg ExtAgrees step_correct
  isDone_correct step_none_iff)
open QecReliability.Trans.Hash (THashArg hashPlain gNbr seedOfBits outputSeeds_slice params)
open QecReliability.OracleCost QecReliability.OracleCost.WholeWrapperCandidate
open QecReliability.SharedCircuit QecReliability.SharedCircuit.LatentEncoding
open QecReliability.SharedCircuit.FixedLocalEmitter.AllLength
open QecReliability.UniformAdapter FiniteLocalSelectorCandidate
open QecReliability.Final

noncomputable section

/-! ## The seed length -/

theorem seedB_walk (X : DyadicXorData) (hb : 8 ≤ X.base) (G : MGGInput) (q : ℕ) :
    seedB X.base X.den q =
      CodeHash.seedBits (X.walkCode hb G q).L ((X.walkCode hb G q).steps + 1) := by
  have hL : (X.walkCode hb G q).L = (params X.base X.den q).L :=
    (X.walkCode_length hb G q).trans rfl
  rw [CodeHash.seedBits, hL, DyadicXorData.walkCode_steps]
  rfl

variable {D t : ℕ} (hD : D = 16^384) (hd : D = 256*t)
    (A : CertifiedParity (512*t) (64*t) t)

theorem seedB_positive (k : ℕ) :
    seedB (data hD hd A).base (data hD hd A).den (keySize (k+1) (k+1)) =
      CodeHash.seedBits (positiveLength hD hd A k) (positiveWidth hD hd A k) :=
  seedB_walk (data hD hd A) (base_ge_eight hD hd A) actualMGG _

/-! ## Seeds from the coins -/

theorem macroSeeds_slice (c d k : ℕ) (coins : Fin (coinBits hD hd A c d (k+1)) → Bool)
    (r : Fin (2 * macroM c d k + 1)) :
    macroSeeds hD hd A c d k (coinWord hD hd A c d (k+1) coins) r =
      seedOfBits (positiveLength hD hd A k) (positiveWidth hD hd A k)
        (((List.ofFn coins).drop
          (r.val * CodeHash.seedBits (positiveLength hD hd A k) (positiveWidth hD hd A k))).take
          (CodeHash.seedBits (positiveLength hD hd A k) (positiveWidth hD hd A k))) := by
  unfold macroSeeds StoredCodeHashConfidence.actualCodeHashSeedTuple
  rw [outputSeeds_slice, CodeHash.FiniteRandomTape.sample_exact]
  simp only
  rw [coinWord_cells]

theorem slice_length (c d k : ℕ) (coins : Fin (coinBits hD hd A c d (k+1)) → Bool)
    (rep : ℕ) (hrep : rep < 2 * macroM c d k + 1) :
    (((List.ofFn coins).drop
        (rep * CodeHash.seedBits (positiveLength hD hd A k) (positiveWidth hD hd A k))).take
        (CodeHash.seedBits (positiveLength hD hd A k) (positiveWidth hD hd A k))).length =
      CodeHash.seedBits (positiveLength hD hd A k) (positiveWidth hD hd A k) := by
  set SB := CodeHash.seedBits (positiveLength hD hd A k) (positiveWidth hD hd A k)
  have hlen : (List.ofFn coins).length = (2 * macroM c d k + 1) * SB := by
    rw [List.length_ofFn]; rfl
  have hle : (rep + 1) * SB ≤ (2 * macroM c d k + 1) * SB := Nat.mul_le_mul_right _ hrep
  rw [List.length_take, List.length_drop, hlen]
  have : rep * SB + SB ≤ (2 * macroM c d k + 1) * SB := by rw [Nat.succ_mul] at hle; exact hle
  omega

/-! ## The instance -/

/-- The context data of an instance. -/
def instX (c d k : ℕ) (rows : List (List (PauliCoord (k+1))))
    (coins : Fin (coinBits hD hd A c d (k+1)) → Bool) : TX.den :=
  wireX (data hD hd A).base (data hD hd A).den rows (List.ofFn coins)

/-- The hash oracle of the algorithm on plain data. -/
abbrev instHashDen (x : THashArg.den) : WProg.den :=
  hashPlain x.1 x.2.1 x.2.2.1 (fun ell => Query.encProg ((data hD hd A).program ell))
    (gNbr actualMGG) x.2.2.2.1 x.2.2.2.2

section Agree
variable {kE : ℕ} {ΓE ΛE : Type} [Fintype ΓE] [Inhabited ΓE] [Fintype ΛE]
    {E : MultiTape.Machine kE ΓE ΛE} {density : ℕ} {PtE PsE : PolynomialEnvelope} {T : ℕ → ℕ}
    (spec : EncodedSAT E density PtE PsE T)
    (L : Lib) (cI : CIx) (Q : FnSig WQArg (.list .bool)) (H : FnSig THashArg WProg) (y : IxR)

/-- **The compile wrapper computes the instance's query bits** at every valid key. -/
theorem compile_agrees (hQd : ∀ p, Q.den p = Query.queryBits p)
    (hHd : ∀ x, H.den x = instHashDen hD hd A x) (c d k : ℕ) (rows : List (List (PauliCoord (k+1))))
    (coins : Fin (coinBits hD hd A c d (k+1)) → Bool) (key : RequestKey)
    (valid : ValidKey (keySize (k+1) (k+1)) (k+1) (macroM c d k) key) :
    (compileF L cI Q H (data hD hd A).base (data hD hd A).den density).den
        (instX hD hd A c d k rows coins, encKey key) =
      ((Assembly.instExt hD hd A spec c d k rows coins).compileQuery key).bits := by
  change _ = Final.concreteQuery rows (ZeroLengthDispatch.iidProgram (k+1))
    (StoredCodeHashConfidence.actualCodeHash (positiveSystem hD hd A k)) (positiveCircuits hD hd A k)
    (macroM c d k) (macroSeeds hD hd A c d k (coinWord hD hd A c d (k+1) coins)) density key
  cases key with
  | base side j rep =>
    rw [← Query.queryFn_base rows (ZeroLengthDispatch.iidProgram (k+1)) _ _ _ _ density side j rep
      valid]
    unfold instX wireX
    rw [compileF_den_base, hQd]
    rfl
  | cell side j rep scale pre =>
    rw [← Query.queryFn_cell rows (ZeroLengthDispatch.iidProgram (k+1)) _ _ _ _ density side j rep
      scale pre valid]
    unfold instX wireX
    rw [compileF_den_cell, hQd, hHd, seedB_positive, macroSeeds_slice,
      Hash.encProg_positiveProgram hD hd A k ⟨scale, valid.2.2.1⟩ _
        (slice_length hD hd A c d k coins rep valid.2.1)]
    simp only [Query.queryFnF_den, Query.cellArg, instHashDen]

/-- **The endpoint wrapper computes the instance's endpoints.** -/
theorem endpoint_agrees (c d k : ℕ) (rows : List (List (PauliCoord (k+1))))
    (coins : Fin (coinBits hD hd A c d (k+1)) → Bool) (b : Bool) :
    (endpointWF cI y).den (instX hD hd A c d k rows coins, b) =
      Control.toR ((Assembly.instExt hD hd A spec c d k rows coins).endpoint b).value := by
  unfold instX wireX
  rw [endpointWF_den]
  rfl

/-- **Control's external hypothesis at every reachable state of the instance.** -/
theorem extAgrees (hQd : ∀ p, Q.den p = Query.queryBits p)
    (hHd : ∀ x, H.den x = instHashDen hD hd A x) (x : Control.Ix TX)
    (hxc : x.compile = compileF L cI Q H (data hD hd A).base (data hD hd A).den density)
    (hxe : x.endpoint = endpointWF cI y)
    {a b c d k : ℕ} (rows : List (List (PauliCoord (k+1))))
    (coins : Fin (coinBits hD hd A c d (k+1)) → Bool) {s : Config}
    (hs : Assembly.InstReachable hD hd A spec a b c d k rows coins s) :
    ExtAgrees x (instX hD hd A c d k rows coins) (Assembly.instExt hD hd A spec c d k rows coins) s where
  query := by
    rw [hxc]
    exact compile_agrees hD hd A spec L cI Q H hQd hHd c d k rows coins s.request
      (reachable_request_invariant hs).request
  endpoint b := by
    rw [hxe]
    exact endpoint_agrees hD hd A spec cI y c d k rows coins b

/-- The encoded controller state of an instance (the `enc` of `Assembly.PositiveFacts`). -/
def instEnc (a b c d k : ℕ) (rows : List (List (PauliCoord (k+1))))
    (coins : Fin (coinBits hD hd A c d (k+1)) → Bool) (s : Config) : Val :=
  (TArg TX).enc (encCtx (keySize (k+1) (k+1)) (k+1) (rationalCellBudget a b) (macroM c d k)
    (instX hD hd A c d k rows coins), encCfg s)

/-- **One FL call of `stepF` is one controller edge of the instance** (every non-invoke edge). -/
theorem wire_step_correct (hQd : ∀ p, Q.den p = Query.queryBits p)
    (hHd : ∀ x, H.den x = instHashDen hD hd A x) (x : Control.Ix TX)
    (hxc : x.compile = compileF L cI Q H (data hD hd A).base (data hD hd A).den density)
    (hxe : x.endpoint = endpointWF cI y)
    {a b c d k : ℕ} (rows : List (List (PauliCoord (k+1))))
    (coins : Fin (coinBits hD hd A c d (k+1)) → Bool) {s : Config} (e : Edge)
    (hs : Assembly.InstReachable hD hd A spec a b c d k rows coins s) (hpc : s.pc ≠ .invoke)
    (he : Assembly.instStep hD hd A spec a b c d k rows coins s = some e) :
    (Control.stepF x).den (encCtx (keySize (k+1) (k+1)) (k+1) (rationalCellBudget a b)
        (macroM c d k) (instX hD hd A c d k rows coins), encCfg s) =
      (encCtx (keySize (k+1) (k+1)) (k+1) (rationalCellBudget a b) (macroM c d k)
        (instX hD hd A c d k rows coins), encCfg e.next) :=
  step_correct x _ _ _ _ _ _ s hpc (extAgrees hD hd A spec L cI Q H y hQd hHd x hxc hxe rows coins hs)
    e he

end Agree

/-- The hypotheses `hQd`, `hHd` hold for the concrete query and hash transcriptions. -/
theorem queryFn_den_std (qx : Query.Ix) (p : WQArg.den) :
    (Query.queryFnF qx).den p = Query.queryBits p := rfl

theorem hashF_den_std (C : Hash.HashCallees) (i : ℕ) (x : THashArg.den) :
    (Hash.hashF C (fun ell => Query.encProg ((data hD hd A).program ell)) (gNbr actualMGG) i).den x =
      instHashDen hD hd A x := rfl

/-! ## Init on the machine input -/

section Init
variable (L : Lib) (h : HIx) (p : PIx) (aI : AIx) (yI : Control.IxI)
  (Fp : FnSig (.prod .nat (.prod .nat .nat)) Hash.TParams)

/-- **Init, positive instance**: the machine input is mapped to the encoded initial state. -/
theorem init_pos (hFp : ∀ x, Fp.den x = (params x.1 x.2.1 x.2.2).tuple) (a b c d k : ℕ) (rows : List (List (PauliCoord (k+1))))
    (coins : Fin (coinBits hD hd A c d (k+1)) → Bool) :
    (initTopF L h p aI yI Fp (data hD hd A).base (data hD hd A).den).den
        (machineInput rows a b c d (List.ofFn coins)) =
      (encCtx (keySize (k+1) (k+1)) (k+1) (rationalCellBudget a b) (macroM c d k)
        (instX hD hd A c d k rows coins), encCfg (Assembly.instInitial c d k)) :=
  initTopF_den_pos L h p aI yI Fp _ _ hFp rows a b c d (List.ofFn coins)

/-- The same, as an equation of encodings (`instEnc` of the initial state). -/
theorem init_pos_enc (hFp : ∀ x, Fp.den x = (params x.1 x.2.1 x.2.2).tuple) (a b c d k : ℕ) (rows : List (List (PauliCoord (k+1))))
    (coins : Fin (coinBits hD hd A c d (k+1)) → Bool) :
    (TArg TX).enc ((initTopF L h p aI yI Fp (data hD hd A).base (data hD hd A).den).den
        (machineInput rows a b c d (List.ofFn coins))) =
      instEnc hD hd A a b c d k rows coins (Assembly.instInitial c d k) := by
  rw [init_pos hD hd A L h p aI yI Fp hFp]
  rfl

/-- **Init, `n = 0`.** -/
theorem init_zero (hFp : ∀ x, Fp.den x = (params x.1 x.2.1 x.2.2).tuple) (rows : List (List (PauliCoord 0))) (a b c d : ℕ) :
    (initTopF L h p aI yI Fp (data hD hd A).base (data hD hd A).den).den
        (machineInput rows a b c d []) =
      (encCtx (keySize 0 0) 0 (rationalCellBudget a b) (rationalRepetitionBudget (2 * (0 + 1)) c d)
        (wireX (data hD hd A).base (data hD hd A).den rows []), encCfg zeroCfg) := by
  have e : machineInput rows a b c d [] =
      InputEncoding.problemBits rows (ZeroLengthDispatch.iidProgram 0) a b c d ++ [] := rfl
  rw [e, initTopF_den_zero L h p aI yI Fp _ _ hFp]

end Init

/-- At the zero-length state the termination test answers `true`. -/
theorem zero_isDone {TX' : Ty} (x : Control.Ix TX') (q r B m : ℕ) (X : TX'.den) (ext : External) :
    (Control.isDoneF x).den (encCtx q r B m X, encCfg zeroCfg) = true := by
  rw [isDone_correct x q r B m X ext zeroCfg, step_none_iff]
  exact .inl rfl

/-- The output word of the zero-length state is the zero vector's output word. -/
theorem zero_output_word :
    Assembly.ratioWord zeroCfg.output = outputWord ZeroLengthDispatch.zeroVector := rfl

/-- The FL encoding of the raw input word (`Assembly.bitsVal`). -/
theorem bitsVal_eq (w : List Bool) : Assembly.bitsVal w = Ty.enc (.list .bool) w := rfl

end

end QecReliability.Trans.Wire
