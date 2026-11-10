import LatentProgramParser

/-! Actual FL transcription of the four-tag latent gate reader. One fixed
compiled body handles every gate/address and has no dimension specialization.
Validity is over all bit lists, including malformed/truncated lists. Resource
bounds and installation into the final uniform program are separate stages.
-/
set_option autoImplicit false
namespace QecReliability.LatentMachine.ParserFL
open FL FL.Lib FL.Tm
open Trans.Wire
open Trans.Control (bodySig bodySig_den bodySig_valid)

abbrev GateTy : Ty := .prod .bool (.prod .bool (.prod .nat .nat))
abbrev ResultTy : Ty := .prod GateTy (.list .bool)

def gateTm {Γ : List Ty} (u s : Tm Γ .bool) (x y : Tm Γ .nat) : Tm Γ GateTy :=
  .pair u (.pair s (.pair x y))

def defaultGate {Γ : List Ty} : Tm Γ ResultTy :=
  .lit (((true, true, 0, 0), []) : ResultTy.den)

variable (L : Lib) (h : HIx) (idx : ℕ)

def gateBody : Tm [.list .bool] ResultTy :=
  .lcase v0 defaultGate <|
    .lcase v1 defaultGate <|
      .ite v2
        (.ite v0
          (.lcase v1 defaultGate
            (.pair (gateTm (.lit true) (.lit true) (.ite v0 (.lit (1:ℕ)) .zero) .zero) v1))
          (.letE (.app (hdrF L h) v1)
            (.pair (gateTm (.lit true) (.lit false) (.fst v0) .zero) (.snd v0))))
        (.letE (.app (hdrF L h) v1) <|
          .letE (.app (hdrF L h) (.snd v0)) <|
            .pair (gateTm (.lit false) v2 (.fst v1) (.fst v0)) (.snd v0))

def gateF : FnSig (.list .bool) ResultTy := bodySig idx (gateBody L h)

theorem gateF_den (bs : List Bool) :
    (gateF L h idx).den bs = Parser.gateR bs := by
  cases bs with
  | nil => rfl
  | cons u bs =>
    cases bs with
    | nil => cases u <;> rfl
    | cons s bs =>
      cases u <;> cases s <;> cases bs <;>
        simp [gateF, bodySig_den, gateBody, defaultGate, gateTm, tm_simp,
          Parser.gateR, Trans.Query.Plain.constGate, hdrF_den]

theorem gateF_gateBits {v : ℕ} (g : SharedCircuit.Gate v) (rest : List Bool) :
    (gateF L h idx).den
      (OracleCost.WholeWrapperCandidate.InputEncoding.gateBits g ++ rest) =
      (Trans.Query.encGate g, rest) := by
  rw [gateF_den, Parser.gateR_gateBits]

/-- Validity of the actual compiled syntax, not an assumed evaluator contract. -/
theorem gate_valid {P : FL.Program} (hL : L.OK P) (hH : h.OK L P)
    (hg : P[idx]? = some (gateBody L h).compile) :
    ∀ bs, (gateF L h idx).ValidAt P bs := by
  intro bs
  apply bodySig_valid hg
  cases bs with
  | nil => simp [tm_simp, gateBody, defaultGate]
  | cons u bs =>
    cases bs with
    | nil => simp [tm_simp, gateBody, defaultGate]
    | cons s bs =>
      cases u <;> cases s <;> cases bs <;>
        simp [tm_simp, gateBody, defaultGate, gateTm, hdr_valid hL hH]

end QecReliability.LatentMachine.ParserFL
