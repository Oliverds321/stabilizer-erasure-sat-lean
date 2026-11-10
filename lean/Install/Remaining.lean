import Install.Table

/-!
# Install.Remaining: the instance program and the remaining bounds

For a certificate `A` and a SAT density, the installed program is
`theProg = prog base den density (encConsts D A) pg nb` with the instance's literals and oracles
(`base = (data hD hd A).base`, `den = (data hD hd A).den`, `pg = encProg ∘ (data hD hd A).program`,
`nb = gNbr actualMGG`).

`RemainingBounds hD hd A density` collects exactly the polynomial-budget facts that are not
proved in this package, in the form consumed by
`Trans.BoundsStep.step_budget` (`hcomp`, `hend`) and `Trans.BoundsStep.init_budget`:

* `compile`: cost/depth/size budget of the compile wrapper `theCompile` at
  `(instX …, encKey s.request)` for every reachable state `s` of every positive instance;
* `endpoint`: the same for the endpoint wrapper `endpointFn` at `(instX …, side)`;
* `init`: the same for the init function `theInit` at the machine input (and its encoded size),
  for every positive instance;
* `initZero`: the same at the `n = 0` machine input.

The envelopes `Cc Cd Cm` (callees) and `Ci Di Mi` (init) are polynomials in `L = paperL`.
-/

set_option autoImplicit false

noncomputable section
namespace QecReliability.Install
open QecReliability.FL QecReliability.FL.Lib
open QecReliability.Trans.Query.Plain (ProgP)
open QecReliability.Trans.Control (encKey)
open QecReliability.Trans.Hash (gNbr)
open QecReliability.OracleCost QecReliability.OracleCost.WholeWrapperCandidate
open QecReliability.SharedCircuit QecReliability.SharedCircuit.LatentEncoding
open QecReliability.SharedCircuit.FixedLocalEmitter.AllLength
open QecReliability.UniformAdapter FiniteLocalSelectorCandidate
open QecReliability.Final

variable {D t : ℕ} (hD : D = 16^384) (hd : D = 256*t) (A : CertifiedParity (512*t) (64*t) t)
  (density : ℕ)

/-- The encoder-family meaning of the instance. -/
def thePg : ℕ → ProgP := fun ell => Trans.Query.encProg ((data hD hd A).program ell)

/-- **The installed FL program of the instance.** -/
def theProg : Program :=
  prog (data hD hd A).base (data hD hd A).den density (Trans.HashCallees.encConsts D A)
    (thePg hD hd A) (gNbr actualMGG)

/-- The controller index table of the instance. -/
def theCX : Trans.Control.Ix Trans.Wire.TX :=
  cX (data hD hd A).base (data hD hd A).den density (Trans.HashCallees.encConsts D A)
    (thePg hD hd A) (gNbr actualMGG)

/-- The hash program of the instance. -/
def theHash : FnSig Trans.Hash.THashArg Trans.Hash.TProg :=
  hashFn (Trans.HashCallees.encConsts D A) (thePg hD hd A) (gNbr actualMGG)

/-- The compile wrapper of the instance (`= (theCX …).compile`). -/
def theCompile : FnSig (.prod Trans.Wire.TX Trans.Control.TKey) (.list .bool) :=
  compileFn (data hD hd A).base (data hD hd A).den density (Trans.HashCallees.encConsts D A)
    (thePg hD hd A) (gNbr actualMGG)

/-- The init function of the instance. -/
def theInit : FnSig (.list .bool) (Trans.Control.TArg Trans.Wire.TX) :=
  Trans.Wire.initTopF wL wH wP wA yI paramsFn (data hD hd A).base (data hD hd A).den

/-- Compile-wrapper budget at every reachable state of every positive instance. -/
def CompileBound (Cc Cd Cm : PolynomialEnvelope) : Prop :=
  ∀ {kE : ℕ} {ΓE ΛE : Type} [Fintype ΓE] [Inhabited ΓE] [Fintype ΛE]
    (E : MultiTape.Machine kE ΓE ΛE) (PtE PsE : PolynomialEnvelope) (T : ℕ → ℕ)
    (spec : EncodedSAT E density PtE PsE T), Monotone T →
    ∀ (a b c d k : ℕ) (rows : List (List (PauliCoord (k+1))))
      (coins : Fin (coinBits hD hd A c d (k+1)) → Bool),
      0 < a → a ≤ b → 0 < c → 0 < d →
      ∀ s, Assembly.InstReachable hD hd A spec a b c d k rows coins s →
        (theCompile hD hd A density).cost (Trans.Wire.instX hD hd A c d k rows coins,
            encKey s.request) ≤ Cc.eval (paperL rows a b c d) ∧
        (theCompile hD hd A density).depth (Trans.Wire.instX hD hd A c d k rows coins,
            encKey s.request) ≤ Cd.eval (paperL rows a b c d) ∧
        (theCompile hD hd A density).msize (Trans.Wire.instX hD hd A c d k rows coins,
            encKey s.request) ≤ Cm.eval (paperL rows a b c d)

/-- Endpoint-wrapper budget at both sides, for every positive instance. -/
def EndpointBound (Cc Cd Cm : PolynomialEnvelope) : Prop :=
  ∀ (a b c d k : ℕ) (rows : List (List (PauliCoord (k+1))))
    (coins : Fin (coinBits hD hd A c d (k+1)) → Bool) (side : Bool),
    0 < a → a ≤ b → 0 < c → 0 < d →
      endpointFn.cost (Trans.Wire.instX hD hd A c d k rows coins, side) ≤
        Cc.eval (paperL rows a b c d) ∧
      endpointFn.depth (Trans.Wire.instX hD hd A c d k rows coins, side) ≤
        Cd.eval (paperL rows a b c d) ∧
      endpointFn.msize (Trans.Wire.instX hD hd A c d k rows coins, side) ≤
        Cm.eval (paperL rows a b c d)

/-- Init budget at the machine input of every positive instance (and the input's size). -/
def InitBound (Ci Di Mi : PolynomialEnvelope) : Prop :=
  ∀ (a b c d k : ℕ) (rows : List (List (PauliCoord (k+1))))
    (coins : Fin (coinBits hD hd A c d (k+1)) → Bool),
    0 < a → a ≤ b → 0 < c → 0 < d →
      (theInit hD hd A).cost (machineInput rows a b c d (List.ofFn coins)) ≤
        Ci.eval (paperL rows a b c d) ∧
      (theInit hD hd A).depth (machineInput rows a b c d (List.ofFn coins)) ≤
        Di.eval (paperL rows a b c d) ∧
      (theInit hD hd A).msize (machineInput rows a b c d (List.ofFn coins)) ≤
        Mi.eval (paperL rows a b c d) ∧
      (Ty.enc (.list .bool) (machineInput rows a b c d (List.ofFn coins))).size ≤
        Mi.eval (paperL rows a b c d)

/-- Init budget at the `n = 0` machine input (and the input's size). -/
def InitZeroBound (Ci Di Mi : PolynomialEnvelope) : Prop :=
  ∀ (rows : List (List (PauliCoord 0))) (a b c d : ℕ),
    0 < a → a ≤ b → 0 < c → 0 < d →
      (theInit hD hd A).cost (machineInput rows a b c d []) ≤ Ci.eval (paperL rows a b c d) ∧
      (theInit hD hd A).depth (machineInput rows a b c d []) ≤ Di.eval (paperL rows a b c d) ∧
      (theInit hD hd A).msize (machineInput rows a b c d []) ≤ Mi.eval (paperL rows a b c d) ∧
      (Ty.enc (.list .bool) (machineInput rows a b c d [])).size ≤ Mi.eval (paperL rows a b c d)

/-- **The polynomial-budget facts not proved in `Install`** (see the module docstring). -/
def RemainingBounds : Prop :=
  ∃ Cc Cd Cm Ci Di Mi : PolynomialEnvelope,
    CompileBound hD hd A density Cc Cd Cm ∧ EndpointBound hD hd A Cc Cd Cm ∧
      InitBound hD hd A Ci Di Mi ∧ InitZeroBound hD hd A Ci Di Mi

end QecReliability.Install

end
