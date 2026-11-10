import DispatchedHashStagesCandidate
import ActualMGGInstantiationCandidate
import QecReliability.FixedLocalDyadicDataCandidate

/-!
Actual all-length semantic/circuit factory from ONE supplied
finite local certificate, followed by an existential theorem removing that
certificate as a caller premise. The data family and all circuit equalities
are constructed, not assumed. This is NOT a physical generator-time theorem.
The q=0 branch is Unit/no randomness/empty Program, with its own trivial law.
-/
set_option autoImplicit false
noncomputable section
namespace QecReliability.SharedCircuit.FixedLocalEmitter.AllLength
open CodeHash UniformAdapter ExpanderWalk FiniteLocalSelectorCandidate

variable {D t : Nat} (hD : D = 16 ^ 384) (hd : D = 256 * t)
    (A : CertifiedParity (512 * t) (64 * t) t)

/-- Shift the SAME actually compiled dyadic encoder exactly once. -/
def data : DyadicXorData := (concreteDyadicData hD hd A).shift

theorem base_ge_eight : 8 ≤ (data hD hd A).base :=
  (concreteDyadicData hD hd A).shift_base_ge_eight

abbrev Seed (q : Nat) : Type :=
  (data hD hd A).dispatchedSeed (base_ge_eight hD hd A) actualMGG q

instance seedFintype (q : Nat) : Fintype (Seed hD hd A q) :=
  DyadicXorData.dispatchedSeedFintype _ _ _ _

def seedBits (q : Nat) : Nat :=
  (data hD hd A).dispatchedSeedBits (base_ge_eight hD hd A) actualMGG q

def stages (q : Nat) : HashStages (Seed hD hd A q) (BitModels q) q :=
  (data hD hd A).dispatchedStages (base_ge_eight hD hd A) actualMGG q

/-- Actual Program-valued factory matching the derived CodeHash stages. -/
def circuits (q : Nat) : SuppliedHashCircuits (stages hD hd A q) (Equiv.refl (BitModels q)) :=
  (data hD hd A).dispatchedCircuits (base_ge_eight hD hd A) actualMGG q

/-- This is the exact fixed-seed adapter program, not a dense matrix surrogate. -/
@[simp] theorem program_eq (q : Nat) (r : Fin (q + 1)) (seed : Seed hD hd A q) :
    (circuits hD hd A q).program r seed =
      (data hD hd A).dispatchedProgram (base_ge_eight hD hd A) actualMGG q r seed := rfl

@[simp] theorem seed_zero : Seed hD hd A 0 = Unit := rfl
@[simp] theorem seedBits_zero : seedBits hD hd A 0 = 0 := rfl
@[simp] theorem gates_zero (r : Fin (0 + 1)) (seed : Seed hD hd A 0) :
    ((circuits hD hd A 0).program r seed).gates = 0 := rfl
@[simp] theorem stages_zero : stages hD hd A 0 = emptyStages := rfl

/-- The zero circuit actually has no input or output coordinates. -/
theorem eval_zero (r : Fin (0 + 1)) (seed : Seed hD hd A 0) (x : BitModels 0) :
    ((circuits hD hd A 0).program r seed).eval x = fun _ => false := by
  have hr : r = 0 := Fin.ext (by have h := r.isLt; omega)
  subst r
  funext i
  exact Fin.elim0 i

/-- The finite seed space and bit budget are for exactly the dispatched family. -/
theorem seed_card (q : Nat) : Fintype.card (Seed hD hd A q) = 2 ^ seedBits hD hd A q :=
  (data hD hd A).dispatchedSeed_card (base_ge_eight hD hd A) actualMGG q

def seedConstant : Nat := (data hD hd A).Cseed
def gateConstant : Nat := (data hD hd A).Cfixed
def wireConstant : Nat := (data hD hd A).Cwire

/-- These global constants do not even depend on which good local matrix was
fixed, much less on q, seed, or confidence/accuracy parameters. -/
theorem constants_independent (B : CertifiedParity (512 * t) (64 * t) t) :
    seedConstant hD hd A = seedConstant hD hd B ∧
    gateConstant hD hd A = gateConstant hD hd B ∧
    wireConstant hD hd A = wireConstant hD hd B := by
  have numeric (X Y : DyadicXorData) (hb : X.base = Y.base)
      (hd : X.den = Y.den) (hg : X.gateConstant = Y.gateConstant) :
      X.Cseed = Y.Cseed ∧ X.Cfixed = Y.Cfixed ∧ X.Cwire = Y.Cwire := by
    simp only [DyadicXorData.Cseed, DyadicXorData.Cfixed, DyadicXorData.Cwire,
      DyadicXorData.B, DyadicXorData.A, DyadicXorData.steps, hb, hd, hg, and_self]
  exact numeric (data hD hd A) (data hD hd B) rfl rfl rfl

theorem seed_linear (q : Nat) : seedBits hD hd A q ≤ seedConstant hD hd A * q :=
  (data hD hd A).dispatchedSeedBits_bound (base_ge_eight hD hd A) actualMGG q

theorem gates_linear (q : Nat) (r : Fin (q + 1)) (seed : Seed hD hd A q) :
    ((circuits hD hd A q).program r seed).gates ≤ gateConstant hD hd A * q :=
  (data hD hd A).dispatchedProgram_gates (base_ge_eight hD hd A) actualMGG q r seed

/-- Shared-DAG metric with every gate input and output occurrence charged.
This theorem is deliberately NOT called a fanout-two theorem. -/
theorem resources_linear (q : Nat) (r : Fin (q + 1)) (seed : Seed hD hd A q) :
    seedBits hD hd A q + q + ((circuits hD hd A q).program r seed).gates +
      ((circuits hD hd A q).program r seed).circuit.edges + 2 * r.val ≤
        wireConstant hD hd A * q :=
  (data hD hd A).dispatchedProgram_resources (base_ge_eight hD hd A) actualMGG q r seed

theorem uniform (q : Nat) (r : Fin (q + 1)) (a : BitModels q) (c : Fin (2 ^ r.val)) :
    (uniformLaw (Seed hD hd A q)).prob
      (fun seed => (stages hD hd A q).hash r seed a = c) = 1 / (2 : Real) ^ r.val :=
  (data hD hd A).dispatched_uniform (base_ge_eight hD hd A) actualMGG q r a c

theorem pairwise (q : Nat) (r : Fin (q + 1)) (a b : BitModels q) (hab : a ≠ b)
    (c d : Fin (2 ^ r.val)) :
    (uniformLaw (Seed hD hd A q)).prob
      (fun seed => (stages hD hd A q).hash r seed a = c ∧
        (stages hD hd A q).hash r seed b = d) = (1 / (2 : Real) ^ r.val) ^ 2 :=
  (data hD hd A).dispatched_pairwise (base_ge_eight hD hd A) actualMGG q r a b hab c d

/-- Direct entrypoint for e.g. the existing quantum `keyBits` equivalence. -/
def stagesFor {B : Type} {q : Nat} (e : B ≃ BitModels q) : HashStages (Seed hD hd A q) B q :=
  UniformAdapter.stagesOn (stages hD hd A q) e

def circuitsFor {B : Type} {q : Nat} (e : B ≃ BitModels q) :
    SuppliedHashCircuits (stagesFor hD hd A e) e :=
  UniformAdapter.circuitsOn (circuits hD hd A q) e

/-- Concrete property of the DEFINED family, not an assumed family interface. -/
def AllLengths : Prop :=
  ∀ q, Fintype.card (Seed hD hd A q) = 2 ^ seedBits hD hd A q ∧
    seedBits hD hd A q ≤ seedConstant hD hd A * q ∧
    ∀ (r : Fin (q + 1)) (seed : Seed hD hd A q),
      ((circuits hD hd A q).program r seed).gates ≤ gateConstant hD hd A * q ∧
      seedBits hD hd A q + q + ((circuits hD hd A q).program r seed).gates +
        ((circuits hD hd A q).program r seed).circuit.edges + 2 * r.val ≤
          wireConstant hD hd A * q

theorem allLengths : AllLengths hD hd A := by
  intro q
  exact ⟨seed_card hD hd A q, seed_linear hD hd A q,
    fun r seed => ⟨gates_linear hD hd A q r seed, resources_linear hD hd A q r seed⟩⟩

/-- Quantify ONE finite certificate before EVERY length and seed. The symbolic
lemma avoids normalizing giant closed matrix dimensions during elaboration. -/
theorem exists_allLengths (ht : 0 < t) :
    ∃ A : CertifiedParity (512 * t) (64 * t) t, AllLengths hD hd A := by
  obtain ⟨A⟩ := ExpanderWalk.FixedWitnessSparseAmplifier.exists_certificate t ht
  exact ⟨A, allLengths hD hd A⟩

/-- Unconditional semantic/circuit existence; no supplied GoodCode, encoder
family, compiler equality, spectral graph, or EfficientFactory premise. -/
theorem exists_one_fixed_all_length_factory :
    ∃ A : CertifiedParity (512 * 2 ^ 1528) (64 * 2 ^ 1528) (2 ^ 1528),
      AllLengths (D := 16 ^ 384) rfl
        FiniteLocalCountingCandidate.fixed_degree_reparametrization A :=
  exists_allLengths (D := 16 ^ 384) (t := 2 ^ 1528) rfl
    FiniteLocalCountingCandidate.fixed_degree_reparametrization
    (pow_pos (by decide : 0 < (2 : Nat)) _)

end QecReliability.SharedCircuit.FixedLocalEmitter.AllLength
