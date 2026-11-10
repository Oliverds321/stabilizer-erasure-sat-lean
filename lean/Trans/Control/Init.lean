import Trans.Control.StepA
import Trans.Hash.FLBase

/-!
# Trans.Control.Init: the initial configuration `initial q r m` as an FL function

`program q r m` is built from library functions only (no new recursion):
* `cellsTail q = (range (q+1)).map cell ++ [select]` (`cellsTailF`);
* the trial block `T = (range (2m+1)).flatMap (trialCode q)` = flatten of
  `mapEnv (ct, rep) ↦ base rep :: ct` (`trialsF`);
* a coefficient half `(range (r+1)).flatMap (coefficientCode q m side)` = flatten of
  `mapEnv ((side, T'), j) ↦ begin side j :: T'` with `T' = T ++ [median, store]` (`coefsF`);
* `programF (q, r, m) = coefs true ++ (coefs false ++ [finish])`, `initF (q, r, m)` = the default
  configuration with `code := programF (q, r, m)`.

`initF_den : (initF y).den (q, r, m) = encCfg (initial q r m)`, `init_valid`.
Program length: `program_length` (`= 2 (r+1) ((2m+1)(q+3)+3) + 1`, controller file).
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace QecReliability.Trans.Control
open QecReliability.FL QecReliability.FL.Lib Tm
open QecReliability.OracleCost QecReliability.OracleCost.WholeWrapperCandidate
open QecReliability.Trans.Hash (mapEnvF mapEnvBody mapEnv_valid mapEnvF_den)

/-- Indices of the initialisation functions. -/
structure IxI where
  succ : ℕ
  rangeFrom : ℕ
  range : ℕ
  appendOp : ℕ
  cellOp : ℕ
  mapCell : ℕ
  cellsTail : ℕ
  trialOp : ℕ
  mapTrial : ℕ
  coefOp : ℕ
  mapCoef : ℕ
  idOps : ℕ
  flatten : ℕ
  trials : ℕ
  coefs : ℕ
  program : ℕ
  init : ℕ

variable (y : IxI)

def cellOpBody : Tm [.nat] TOp := .pair (.lit (2 : ℕ)) (.pair .ff v0)
def cellOpF : FnSig .nat TOp := bodySig y.cellOp cellOpBody

def cellsTailBody : Tm [.nat] (.list TOp) :=
  .app (appendF TOp y.appendOp)
    (.pair (.app (mapF (cellOpF y) y.mapCell) (.app (rangeF y.range) (.app (succF y.succ) v0)))
      (.lit [encOp .select]))
def cellsTailF : FnSig .nat (.list TOp) := bodySig y.cellsTail (cellsTailBody y)

/-- `(ct, rep) ↦ base rep :: ct`. -/
def trialOpBody : Tm [.prod (.list TOp) .nat] (.list TOp) :=
  .lcons (.pair (.lit (1 : ℕ)) (.pair .ff (.snd v0))) (.fst v0)
def trialOpF : FnSig (.prod (.list TOp) .nat) (.list TOp) := bodySig y.trialOp trialOpBody

/-- `((side, T'), j) ↦ begin side j :: T'`. -/
def coefOpBody : Tm [.prod (.prod .bool (.list TOp)) .nat] (.list TOp) :=
  .lcons (.pair .zero (.pair (.fst (.fst v0)) (.snd v0))) (.snd (.fst v0))
def coefOpF : FnSig (.prod (.prod .bool (.list TOp)) .nat) (.list TOp) := bodySig y.coefOp coefOpBody

def idOpsBody : Tm [.list TOp] (.list TOp) := v0
def idOpsF : FnSig (.list TOp) (.list TOp) := bodySig y.idOps idOpsBody
def flattenF : FnSig (.list (.list TOp)) (.list TOp) := flatMapF (idOpsF y) y.flatten

/-- `(q, m) ↦ (range (2m+1)).flatMap (trialCode q)`. -/
def trialsBody : Tm [.prod .nat .nat] (.list TOp) :=
  .app (flattenF y) (.app (mapEnvF (trialOpF y) y.mapTrial)
    (.pair (.app (cellsTailF y) (.fst v0))
      (.app (rangeF y.range) (.bit .tt (.snd v0)))))
def trialsF : FnSig (.prod .nat .nat) (.list TOp) := bodySig y.trials (trialsBody y)

/-- `(side, T, r) ↦ (range (r+1)).flatMap (fun j => begin side j :: T ++ [median, store])`. -/
def coefsBody : Tm [.prod .bool (.prod (.list TOp) .nat)] (.list TOp) :=
  .app (flattenF y) (.app (mapEnvF (coefOpF y) y.mapCoef)
    (.pair (.pair (.fst v0) (.app (appendF TOp y.appendOp)
        (.pair (.fst (.snd v0)) (.lit [encOp .median, encOp .store]))))
      (.app (rangeF y.range) (.app (succF y.succ) (.snd (.snd v0))))))
def coefsF : FnSig (.prod .bool (.prod (.list TOp) .nat)) (.list TOp) := bodySig y.coefs (coefsBody y)

/-- `(q, r, m) ↦ program q r m` (encoded). -/
def programBody : Tm [.prod .nat (.prod .nat .nat)] (.list TOp) :=
  .letE (.app (trialsF y) (.pair (.fst v0) (.snd (.snd v0)))) <|
    .app (appendF TOp y.appendOp) (.pair (.app (coefsF y) (.pair .tt (.pair v0 (.fst (.snd v1)))))
      (.app (appendF TOp y.appendOp) (.pair (.app (coefsF y) (.pair .ff (.pair v0 (.fst (.snd v1)))))
        (.lit [encOp .finish]))))
def programF : FnSig (.prod .nat (.prod .nat .nat)) (.list TOp) := bodySig y.program (programBody y)

/-- `(q, r, m) ↦ initial q r m` (encoded). -/
def initBody : Tm [.prod .nat (.prod .nat .nat)] TCfg :=
  .letE (.lit (encCfg ({} : Config))) <|
    F.cfgWith v0 (g0 := F.g0With v0 (code := .app (programF y) v1))
def initF : FnSig (.prod .nat (.prod .nat .nat)) TCfg := bodySig y.init (initBody y)

/-! ## Meaning -/

theorem flatMap_eq_flatten {α β : Type} (f : α → List β) (xs : List α) :
    (xs.map f).flatMap id = xs.flatMap f := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ih]

theorem bodySig_den_fun {a b : Ty} (i : ℕ) (body : Tm [a] b) :
    (bodySig i body).den = fun x => body.den (Env.one x) := rfl

theorem cellsTail_den (q : ℕ) :
    (cellsTailF y).den q = ((List.range (q + 1)).map Opcode.cell ++ [Opcode.select]).map encOp := by
  simp [cellsTailF, bodySig_den, bodySig_den_fun, cellsTailBody, tm_simp, cellOpF, cellOpBody, encOp]

theorem trials_den (q m : ℕ) :
    (trialsF y).den (q, m) = ((List.range (2 * m + 1)).flatMap (trialCode q)).map encOp := by
  simp only [trialsF, bodySig_den, trialsBody, tm_simp, flattenF, flatMapF_den, mapEnvF_den,
    rangeF_den, cellsTail_den, bitNat_true, List.flatMap_map, List.map_flatMap]
  all_goals simp [idOpsF, idOpsBody, trialOpF, trialOpBody, bodySig_den, tm_simp, trialCode, encOp]

theorem coefs_den (side : Bool) (q m r : ℕ) :
    (coefsF y).den (side, ((List.range (2 * m + 1)).flatMap (trialCode q)).map encOp, r) =
      ((List.range (r + 1)).flatMap (coefficientCode q m side)).map encOp := by
  simp only [coefsF, bodySig_den, coefsBody, tm_simp, flattenF, flatMapF_den, mapEnvF_den,
    rangeF_den, succF_den, appendF_den, List.flatMap_map, List.map_flatMap]
  all_goals (try (congr 1; funext j))
  all_goals simp [idOpsF, idOpsBody, coefOpF, coefOpBody, bodySig_den, tm_simp, coefficientCode,
    encOp, List.map_flatMap]

theorem program_den (q r m : ℕ) : (programF y).den (q, r, m) = (program q r m).map encOp := by
  simp only [programF, bodySig_den, programBody, tm_simp, appendF_den]
  rw [trials_den, coefs_den, coefs_den]
  simp [program, encOp]

theorem initF_den (q r m : ℕ) : (initF y).den (q, r, m) = encCfg (initial q r m) := by
  simp only [initF, bodySig_den, initBody, tm_simp]
  rw [program_den]
  simp [encCfg, initial]

/-! ## Validity -/

/-- The library functions used by the initialisation, valid everywhere. -/
structure LibI (P : Program) : Prop where
  succ : ∀ n, (succF y.succ).ValidAt P n
  range : ∀ n, (rangeF y.range).ValidAt P n
  append : ∀ p, (appendF TOp y.appendOp).ValidAt P p
  mapCell : P[y.mapCell]? = some (mapBody (cellOpF y) y.mapCell).compile
  mapTrial : P[y.mapTrial]? = some (mapEnvBody (trialOpF y) y.mapTrial).compile
  mapCoef : P[y.mapCoef]? = some (mapEnvBody (coefOpF y) y.mapCoef).compile
  flatten : P[y.flatten]? = some (flatMapBody (idOpsF y) y.appendOp y.flatten).compile
  cellOp : P[y.cellOp]? = some cellOpBody.compile
  trialOp : P[y.trialOp]? = some trialOpBody.compile
  coefOp : P[y.coefOp]? = some coefOpBody.compile
  idOps : P[y.idOps]? = some idOpsBody.compile
  cellsTail : P[y.cellsTail]? = some (cellsTailBody y).compile
  trials : P[y.trials]? = some (trialsBody y).compile
  coefs : P[y.coefs]? = some (coefsBody y).compile
  program : P[y.program]? = some (programBody y).compile
  init : P[y.init]? = some (initBody y).compile

section Valid
variable {y} {P : Program} (h : LibI y P)
include h

theorem flatten_valid : ∀ xs, (flattenF y).ValidAt P xs := fun xs =>
  flatMap_valid h.append h.flatten xs (fun _ _ => bodySig_valid h.idOps (by simp [tm_simp, idOpsBody]))

theorem cellsTail_valid : ∀ q, (cellsTailF y).ValidAt P q := fun q => by
  apply bodySig_valid h.cellsTail
  have hc : ∀ s, (cellOpF y).ValidAt P s := fun s => bodySig_valid h.cellOp (by simp [tm_simp, cellOpBody])
  simp [tm_simp, cellsTailBody, h.succ, h.range, h.append,
    map_valid h.mapCell _ (fun s _ => hc s)]

theorem trials_valid : ∀ p, (trialsF y).ValidAt P p := fun p => by
  apply bodySig_valid h.trials
  have ht : ∀ a, (trialOpF y).ValidAt P a := fun a => bodySig_valid h.trialOp (by simp [tm_simp, trialOpBody])
  simp [tm_simp, trialsBody, h.range, cellsTail_valid h, flatten_valid h,
    mapEnv_valid h.mapTrial _ (fun a _ => ht _)]

theorem coefs_valid : ∀ p, (coefsF y).ValidAt P p := fun p => by
  apply bodySig_valid h.coefs
  have ht : ∀ a, (coefOpF y).ValidAt P a := fun a => bodySig_valid h.coefOp (by simp [tm_simp, coefOpBody])
  simp [tm_simp, coefsBody, h.range, h.succ, h.append, flatten_valid h,
    mapEnv_valid h.mapCoef _ (fun a _ => ht _)]

theorem program_valid : ∀ p, (programF y).ValidAt P p := fun p => by
  apply bodySig_valid h.program
  simp [tm_simp, programBody, h.append, trials_valid h, coefs_valid h]

theorem init_valid : ∀ p, (initF y).ValidAt P p := fun p => by
  apply bodySig_valid h.init
  simp [tm_simp, initBody, program_valid h]

end Valid

end QecReliability.Trans.Control
