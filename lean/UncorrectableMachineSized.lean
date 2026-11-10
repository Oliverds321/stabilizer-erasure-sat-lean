import UncorrectableMachine

/-! Explicit size bounds for `uncorrectable_machine_guarantee`.

The instance run by the multiclass machine is the `m`-fold code `rowsPower m rows` (on `n*m`
qubits) with the duplication circuit `dupProgram n m` (no gates, `n*m` outputs). We prove

* `satStructuralSize_dup`: `satStructuralSize = n*m + n + m * rowIncidences rows + 1`, hence
  `≤ 2 * m * (n + rowIncidences rows + 1)`;
* `resourceSize_dup_le`: `resourceSize ≤ sizedLength n m rows a b c d`, where
  `sizedLength = 20 * m * (n + rowIncidences rows + rows.length + 1) * (size(n*m) + 1)
                 + 2 * (size a + size b + size c + size d) + 4`.
  The factor `size(n*m)+1` is the binary width of a qubit address of the `m`-fold code; every
  coordinate of every row and every circuit output is written with such an address.

`uncorrectable_machine_guarantee_sized` restates the theorem with time bound
`Ptime(L') * (B+1) * (runtimeEnvelope rateConstant (K' * m * (n + rowIncidences rows + 1)) + 1)`
and space bound `Pspace(L')`, `L' = sizedLength n m rows a b c d`, `K' = 3κ`, where
`κ = Boundary.variableCoefficient 1 Cfixed` is the fixed constant of the SAT-rate argument of
the original theorem (a constant of the fixed certificate, independent of every input). -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
namespace QecReliability.UncorrectableMachine
open Binary SharedCircuit SharedCircuit.LatentEncoding SharedCircuit.FixedLocalEmitter.AllLength
open UniformAdapter FiniteLocalSelectorCandidate
open OracleCost OracleCost.MultiTape RationalOutput Final QecPhysical QecPhysical.Stabilizer
open ExternalSATBridge TensorBernstein TensorLatent
open QecReliability.TensorMachine QecReliability.TensorMachine.Runtime
open QecReliability.LatentMachine.Runtime.FixedQuantum
open QecReliability.TensorMachine.Runtime.FixedQuantum
open QecReliability.IidErasure QecReliability.ProductCode
open QecPhysical.Stabilizer.Uncorrectable
open OracleCost.WholeWrapperCandidate.InputEncoding OracleCost.QueryCodec

/-! ## Encoding lengths -/

theorem flatMap_length_le {α : Type*} (xs : List α) (f : α → List Bool) (K : ℕ)
    (h : ∀ x ∈ xs, (f x).length ≤ K) : (xs.flatMap f).length ≤ xs.length * K := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have hx := h x (by simp)
      have ht := ih (fun y hy => h y (by simp [hy]))
      simp only [List.flatMap_cons, List.length_append, List.length_cons, Nat.succ_mul]
      omega

theorem size_le_self (x : ℕ) : x.size ≤ x :=
  Nat.size_le.mpr Nat.lt_two_pow_self

theorem coordBits_length_le {N : ℕ} (c : PauliCoord N) :
    (coordBits c).length ≤ 2*N.size+2 := by
  cases c with
  | inl i =>
      have := Nat.size_le_size i.isLt.le
      simp only [coordBits, List.length_cons, natHeader_length]
      omega
  | inr i =>
      have := Nat.size_le_size i.isLt.le
      simp only [coordBits, List.length_cons, natHeader_length]
      omega

theorem rowBits_length_le {N : ℕ} (row : List (PauliCoord N)) :
    (rowBits row).length ≤ (2*N.size+4)*row.length+1 := by
  have hf := flatMap_length_le row coordBits (2*N.size+2) (fun c _ => coordBits_length_le c)
  have hs := size_le_self row.length
  simp only [rowBits, List.length_append, natHeader_length]
  have he : (2*N.size+4)*row.length = row.length*(2*N.size+2)+2*row.length := by ring
  omega

theorem rowsBody_length_le {N : ℕ} (rows : List (List (PauliCoord N))) :
    (rows.flatMap rowBits).length ≤ (2*N.size+4)*rowIncidences rows+rows.length := by
  induction rows with
  | nil => simp
  | cons row rows ih =>
      have hr := rowBits_length_le row
      simp only [List.flatMap_cons, List.length_append, List.length_cons,
        rowIncidences, List.map_cons, List.sum_cons] at *
      have he : (2*N.size+4)*(row.length+(List.map List.length rows).sum) =
        (2*N.size+4)*row.length+(2*N.size+4)*(List.map List.length rows).sum := by ring
      omega

theorem rowsBits_length_le {N : ℕ} (rows : List (List (PauliCoord N))) :
    (rowsBits rows).length ≤ (2*N.size+4)*rowIncidences rows+3*rows.length+1 := by
  have h := rowsBody_length_le rows
  have hs := size_le_self rows.length
  simp only [rowsBits, List.length_append, natHeader_length]
  omega

theorem outputBits_length_le {N r : ℕ} (C : Program r N) :
    (outputBits C).length ≤ N*(2*(r+C.gates).size+1) := by
  have h := flatMap_length_le (List.ofFn (fun i : Fin N => C.output i))
    (fun i => natHeader i.val) (2*(r+C.gates).size+1) (by
      intro i _
      have := Nat.size_le_size i.isLt.le
      simp only [natHeader_length]
      omega)
  simpa only [List.length_ofFn, outputBits] using h

theorem rowsPower_length (m : ℕ) {n : ℕ} (rows : List (List (PauliCoord n))) :
    (rowsPower m rows).length = m * rows.length := by
  simp [rowsPower, List.length_flatMap, List.map_const', List.sum_replicate]

theorem dupProgram_gates (n m : ℕ) : (dupProgram n m).gates = 0 := rfl

theorem programBits_dup_length_le (n m : ℕ) :
    (programBits (dupProgram n m)).length ≤ 1+n*m*(2*n.size+1) := by
  have h := outputBits_length_le (dupProgram n m)
  rw [dupProgram_gates] at h
  have hs : ([n].sum+0) = n := by simp
  rw [hs] at h
  have hc : circuitBits (dupProgram n m).circuit = [] := rfl
  simp only [programBits, List.length_append, natHeader_length, hc, dupProgram_gates,
    List.length_nil]
  simp
  omega

/-! ## The two size measures of the instance -/

theorem satStructuralSize_dup (n m : ℕ) (rows : List (List (PauliCoord n))) :
    Boundary.satStructuralSize (rowsPower m rows) (dupProgram n m) =
      n*m+n+m*rowIncidences rows+1 := by
  unfold Boundary.satStructuralSize
  rw [rowIncidences_rowsPower, dupProgram_gates]
  simp

theorem satStructuralSize_dup_le (n m : ℕ) (rows : List (List (PauliCoord n))) (hm : 1 ≤ m) :
    Boundary.satStructuralSize (rowsPower m rows) (dupProgram n m) ≤
      2*m*(n+rowIncidences rows+1) := by
  rw [satStructuralSize_dup]
  have h1 : n ≤ n*m := Nat.le_mul_of_pos_right n hm
  have he : 2*m*(n+rowIncidences rows+1) = 2*(n*m)+2*(m*rowIncidences rows)+2*m := by ring
  omega

/-- Explicit function of the original input sizes bounding `resourceSize` of the instance. -/
def sizedLength (n m : ℕ) (rows : List (List (PauliCoord n))) (a b c d : ℕ) : ℕ :=
  20*m*(n+rowIncidences rows+rows.length+1)*((n*m).size+1)+2*(a.size+b.size+c.size+d.size)+4

theorem resourceSize_dup_le (n m : ℕ) (rows : List (List (PauliCoord n))) (a b c d : ℕ)
    (hm : 1 ≤ m) :
    Boundary.resourceSize (rowsPower m rows) (dupProgram n m) a b c d ≤
      sizedLength n m rows a b c d := by
  have hR := rowsBits_length_le (rowsPower m rows)
  rw [rowIncidences_rowsPower, rowsPower_length] at hR
  have hP := programBits_dup_length_le n m
  have hpr := precisionBits_length a b c d
  have hslots : slots [n] = n+1 := by
    simp only [slots, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  have hsum : [n].sum = n := by simp
  have hns : n.size ≤ (n*m).size := Nat.size_le_size (Nat.le_mul_of_pos_right n hm)
  have hsz : ([n].sum).size = n.size := by rw [hsum]
  obtain ⟨P, hPdef⟩ : ∃ P, P = m*(n+rowIncidences rows+rows.length+1)*((n*m).size+1) := ⟨_, rfl⟩
  have hX1 : 1 ≤ n+rowIncidences rows+rows.length+1 := by omega
  have hmX : 1 ≤ m*(n+rowIncidences rows+rows.length+1) := Nat.mul_le_mul hm hX1
  have hP0 : (n*m).size+1 ≤ P := by
    rw [hPdef]; exact Nat.le_mul_of_pos_left _ (by omega)
  have hnX : n*m ≤ m*(n+rowIncidences rows+rows.length+1) := by
    rw [Nat.mul_comm n m]; exact Nat.mul_le_mul_left m (by omega)
  have hIX : m*rowIncidences rows ≤ m*(n+rowIncidences rows+rows.length+1) :=
    Nat.mul_le_mul_left m (by omega)
  have hlX : m*rows.length ≤ m*(n+rowIncidences rows+rows.length+1) :=
    Nat.mul_le_mul_left m (by omega)
  have hA : n*m*(2*n.size+1) ≤ 2*P := by
    rw [hPdef]
    calc n*m*(2*n.size+1) ≤ (m*(n+rowIncidences rows+rows.length+1))*(2*((n*m).size+1)) :=
          Nat.mul_le_mul hnX (by omega)
      _ = _ := by ring
  have hB : (2*(n*m).size+4)*(m*rowIncidences rows) ≤ 4*P := by
    rw [hPdef]
    calc (2*(n*m).size+4)*(m*rowIncidences rows) ≤
          (4*((n*m).size+1))*(m*(n+rowIncidences rows+rows.length+1)) :=
          Nat.mul_le_mul (by omega) hIX
      _ = _ := by ring
  have hC : m*rows.length ≤ P := by
    rw [hPdef]; exact le_trans hlX (Nat.le_mul_of_pos_right _ (by omega))
  have hD : n*m ≤ P := by
    rw [hPdef]; exact le_trans hnX (Nat.le_mul_of_pos_right _ (by omega))
  have hE : n ≤ P := le_trans (Nat.le_mul_of_pos_right n hm) hD
  have he : 20*m*(n+rowIncidences rows+rows.length+1)*((n*m).size+1) = 20*P := by
    rw [hPdef]; ring
  unfold Boundary.resourceSize paperLength problemBits sizedLength
  simp only [List.length_append, natHeader_length, hslots, List.length_cons, List.length_nil]
  rw [he]
  omega

theorem rate_argument_le (κ n m I S : ℕ) (hm : 1 ≤ m) (hS : S ≤ 2*m*(n+I+1)) :
    κ*(S+1) ≤ 3*κ*m*(n+I+1) := by
  have h1 : 1 ≤ m*(n+I+1) :=
    le_trans (by norm_num : 1 ≤ 1*1) (Nat.mul_le_mul hm (show 1 ≤ n+I+1 by omega))
  have he : 2*m*(n+I+1) = 2*(m*(n+I+1)) := by ring
  have h2 : S+1 ≤ 3*(m*(n+I+1)) := by omega
  calc κ*(S+1) ≤ κ*(3*(m*(n+I+1))) := Nat.mul_le_mul_left κ h2
    _ = 3*κ*m*(n+I+1) := by ring

/-! ## The sized corollary -/

local notation "HD" => fixedDegree_eq
local notation "HS" => fixedDegree_scale
local notation "CERT" => explicitCertificate

/-- `uncorrectable_machine_guarantee` with explicit sizes. `L' = sizedLength n m rows a b c d`
`= 20 m (n + rowIncidences rows + rows.length + 1)(size(n m) + 1) + 2(size a + size b + size c
+ size d) + 4` is an explicit function of the original input; `K' = 3 κ` with
`κ = Boundary.variableCoefficient 1 Cfixed`, a constant fixed with the machine. The SAT-rate
argument is linear in `m (n + rowIncidences rows + 1)`. -/
theorem uncorrectable_machine_guarantee_sized :
    ∃ (engine : OAI.Algorithms.SubexponentialSAT.Computation.PrimitiveMachine)
      (rateConstant : ℝ) (Ptime Pspace : PolynomialEnvelope),
    0<rateConstant ∧ ∀ {n : ℕ}
    (rows : List (List (PauliCoord n))) (m a b c d : ℕ), 1 ≤ m → 0<a → a≤b → 0<c → 0<d →
    ∀ hS : rowSpace rows ≤ QecReliability.normalizer (symplectic n) (rowSpace rows),
    let R := rowsPower m rows
    let C := dupProgram n m
    let lift := QecPhysical.Stabilizer.isotropicLift (rowSpace R) (rowsPower_isotropic hS)
    let U := uncorrectableProb (rowSpace rows)
    let L' := sizedLength n m rows a b c d
    let K' := 3*Boundary.variableCoefficient 1 (data HD HS CERT).Cfixed
    let B := rationalCellBudget a b
    let r := rationalRepetitionBudget (2*slots [n]) c d
    let N := CodeHash.repeatBits (Factory.length HD HS CERT (n*m) [n])
      (Factory.width HD HS CERT (n*m) [n]) r
    let E := PrimitiveTransport.machine (PrimitiveLink.queryMachine engine)
    let M := Assembly.theMachine E (program HD HS CERT 1) (indices HD HS CERT 1)
    let outputTape := Assembly.outTape (PrimitiveLink.queryMachine engine).tapeCount
    let Uhat := fun (v : Vector (slots [n]-1)) (p : ℝ) => 1 - bernsteinCurve n (coefficients v) p
    -- the two size measures of the instance
    Boundary.satStructuralSize R C = n*m+n+m*rowIncidences rows+1 ∧
    Boundary.satStructuralSize R C ≤ 2*m*(n+rowIncidences rows+1) ∧
    Boundary.resourceSize R C a b c d ≤ L' ∧
    -- (i) the target of the instance is the latent fidelity `F_m` of the `m`-fold code
    (∀ p (hp : p ∈ Set.Icc (0:ℝ) 1),
      entanglementFidelity (lift.erasureFlagDecoder.comp
          (lift.multivariateLatentErasure (TensorEncoding.circuitMap C)
            (p, PUnit.unit) ⟨hp, trivial⟩)).map = powerFidelity m (rowSpace rows) p) ∧
    -- (ii) every coin string
    (∀ coins : Fin N → Bool,
      ∃ (run : Completed M (input [n] R C a b c d (List.ofFn coins)))
        (v : Vector (slots [n]-1)),
        Outputs M run outputTape v ∧
        run.time ≤ Ptime.eval L'*(B+1)*(RateMajorant.runtimeEnvelope rateConstant
          (K'*m*(n+rowIncidences rows+1))+1) ∧
        run.cells ≤ Pspace.eval L' ∧
        MonotoneOn (Uhat v) (Set.Icc 0 1) ∧
        (∀ p ∈ Set.Icc (0:ℝ) 1, 0 ≤ Uhat v p ∧ Uhat v p ≤ 1) ∧
        (∀ j, 1 - coefficients v j = 0 ↔ layerFraction (rowSpace rows) j = 0)) ∧
    -- (iii) one coin event: the two-sided bound for every `p ∈ [0,1]` simultaneously
    1-(c:ℝ)/d ≤ (uniformLaw (CodeHash.BitTape N)).prob
      (fun coins => ∀ (run : Completed M (input [n] R C a b c d (List.ofFn coins)))
        (v : Vector (slots [n]-1)), Outputs M run outputTape v →
          ∀ p ∈ Set.Icc (0:ℝ) 1,
            ((1 - (a:ℝ)/b) * (1 - ((2:ℝ)^m)⁻¹) * U p ≤ Uhat v p ∧
              Uhat v p ≤ (1 + (a:ℝ)/b) * U p) ∧
            (((2:ℝ)^m)⁻¹ ≤ (a:ℝ)/b → |Uhat v p - U p| ≤ 2 * ((a:ℝ)/b) * U p)) := by
  obtain ⟨engine,rateConstant,Ptime,Pspace,hrate,hclosed⟩ := uncorrectable_machine_guarantee
  refine ⟨engine,rateConstant,Ptime,Pspace,hrate,?_⟩
  intro n rows m a b c d hm ha hab hc hd hS
  obtain ⟨htarget,hruns,hprob⟩ := hclosed rows m a b c d hm ha hab hc hd hS
  have hL := resourceSize_dup_le n m rows a b c d hm
  have hSz := satStructuralSize_dup_le n m rows hm
  refine ⟨satStructuralSize_dup n m rows, hSz, hL, htarget, ?_, hprob⟩
  intro coins
  obtain ⟨run,v,hout,htime,hspace,hmono,hrange,hzero⟩ := hruns coins
  refine ⟨run,v,hout,?_,hspace.trans (Pspace.monotone hL),hmono,hrange,hzero⟩
  have hk := rate_argument_le (Boundary.variableCoefficient 1 (data HD HS CERT).Cfixed)
    n m (rowIncidences rows) _ hm hSz
  exact htime.trans (Nat.mul_le_mul (Nat.mul_le_mul_right _ (Ptime.monotone hL))
    (Nat.add_le_add_right (RateMajorant.runtimeEnvelope_monotone rateConstant hk) 1))

end QecReliability.UncorrectableMachine

#print axioms QecReliability.UncorrectableMachine.satStructuralSize_dup
#print axioms QecReliability.UncorrectableMachine.resourceSize_dup_le
#print axioms QecReliability.UncorrectableMachine.uncorrectable_machine_guarantee_sized
