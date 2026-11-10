import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Pi
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring

namespace QecReliability.Binary
abbrev Bit := ZMod 2
end QecReliability.Binary

noncomputable section
namespace QecReliability.CodeHash
open scoped BigOperators

abbrev F := Binary.Bit
abbrev Word (k : ℕ) := Fin k → F
abbrev LocalSeed (t : ℕ) := Word t × F
abbrev Seed (m t : ℕ) := Fin m → LocalSeed t

def truncate {q r : ℕ} (h : r ≤ q) : Word q →ₗ[F] Word r where
  toFun a i := a (Fin.castLE h i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def weight {m : ℕ} (v : Word m) : ℕ := (Finset.univ.filter (fun i => v i ≠ 0)).card

def DistanceAtLeast {k m : ℕ} (G : Word k →ₗ[F] Word m) (d : ℕ) : Prop :=
  ∀ a, a ≠ 0 → d ≤ weight (G a)

end QecReliability.CodeHash
