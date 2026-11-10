import LatentInitializerInstalled
import LatentWrappersFL

/-! Concrete latent query and endpoint callback installation, slots298–301.
Hash slicing remains at original slots243–244. This alone does not retarget the
old controller, whose callback calls and true-mode repair require replacement. -/
set_option autoImplicit false
namespace QecReliability.LatentMachine.WrappersInstalled
open FL FL.Lib Trans.Wire
open Trans.Query.Plain (ProgP)
open Trans.Control (bodySig_valid)

abbrev indices : CIx := ⟨243,244,298,299,300,301⟩

variable (base den density : ℕ) (E : ℕ × ℕ × ℕ)
  (pg : ℕ → ProgP) (nb : ℕ → ℕ → ℕ → ℕ)

def segment : FL.Program :=
  [(WrappersFL.cellQBody Install.wL indices Install.queryFn (Install.hashFn E pg nb)
      base den density).compile,
   (WrappersFL.baseQBody Install.wL Install.queryFn density).compile,
   (WrappersFL.compileBody Install.wL indices Install.queryFn (Install.hashFn E pg nb)
      base den density).compile,
   (WrappersFL.endpointWBody Install.wL Install.yR).compile]

def program : FL.Program :=
  InitializerInstalled.program base den density E pg nb ++ segment base den density E pg nb

local notation "PP" => program base den density E pg nb
local notation "OLD" => Install.prog base den density E pg nb

theorem extends_initializer : Install.Extends
    (InitializerInstalled.program base den density E pg nb) PP := Install.extends_append _ _

theorem extends_prefix : Install.Extends OLD PP := by
  intro i b hi
  exact extends_initializer base den density E pg nb i b
    (InitializerInstalled.extends_prefix base den density E pg nb i b hi)

theorem program_length : (program base den density E pg nb).length = 302 := by
  simp only [program,List.length_append,InitializerInstalled.program_length]
  rfl

theorem slots : WrappersFL.Slots Install.wL indices Install.queryFn (Install.hashFn E pg nb)
    base den density Install.yR PP := ⟨rfl,rfl,rfl,rfl⟩

/-- The only premise is the original hash implementation's validity, exactly
as in the pinned installer; no new callback validity is assumed. -/
theorem compile_valid (hH : ∀ x, (Install.hashFn E pg nb).ValidAt OLD x) : ∀ x,
    (WrappersFL.compileF Install.wL indices Install.queryFn (Install.hashFn E pg nb)
      base den density).ValidAt PP x := by
  have oldL := Install.wL_ok base den density E pg nb
  have oldQ := Install.query_valid base den density E pg nb
  have he := extends_prefix base den density E pg nb
  have hadd := fun x => Install.ValidAt.extend he (oldL.add x)
  have hsub := fun x => Install.ValidAt.extend he (oldL.sub x)
  have hrep := fun x => Install.ValidAt.extend he (oldL.rep .bool x)
  have hQ := fun x => Install.ValidAt.extend he (oldQ x)
  have hHash : ∀ x, (hashWF Install.wL indices (Install.hashFn E pg nb) base den).ValidAt PP x :=
    fun x => Install.ValidAt.extend he
      (Trans.Wire.hashW_valid oldL oldQ hH Install.wC_ok x)
  have hs := slots base den density E pg nb
  have hc : ∀ x, (WrappersFL.cellQF Install.wL indices Install.queryFn
      (Install.hashFn E pg nb) base den density).ValidAt PP x := fun x =>
    bodySig_valid hs.cellQ (by
      simp [WrappersFL.cellQBody,WrappersFL.Xr,tm_simp,hadd,hsub,hrep,hQ,hHash])
  have hb : ∀ x, (WrappersFL.baseQF Install.wL indices Install.queryFn density).ValidAt PP x :=
    fun x => bodySig_valid hs.baseQ (by simp [WrappersFL.baseQBody,WrappersFL.Xr,tm_simp,hadd,hsub,hQ])
  intro x
  exact bodySig_valid hs.compile (by simp [WrappersFL.compileBody,tm_simp,hc,hb])

theorem endpoint_valid : ∀ x,
    (WrappersFL.endpointWF Install.wL indices Install.yR).ValidAt PP x := by
  have oldL := Install.wL_ok base den density E pg nb
  have he := extends_prefix base den density E pg nb
  have hadd := fun x => Install.ValidAt.extend he (oldL.add x)
  have hsub := fun x => Install.ValidAt.extend he (oldL.sub x)
  have hz := fun x => Install.ValidAt.extend he (Trans.Control.endpoint_valid Install.yR_ok x)
  intro x
  exact bodySig_valid (slots base den density E pg nb).endpointW
    (by simp [WrappersFL.endpointWBody,WrappersFL.Xr,tm_simp,hadd,hsub,hz])

theorem initializer_valid : ∀ w,
    (InitializerFL.initialF Install.wL Install.wH Install.wP ParserInstalled.indices
      Install.wA Install.yI Install.yR Install.paramsFn base den
      InitializerInstalled.ctxIdx InitializerInstalled.terminalIdx InitializerInstalled.topIdx).ValidAt PP w :=
  fun w => Install.ValidAt.extend (extends_initializer base den density E pg nb)
    (InitializerInstalled.initializer_valid base den density E pg nb w)

end QecReliability.LatentMachine.WrappersInstalled
