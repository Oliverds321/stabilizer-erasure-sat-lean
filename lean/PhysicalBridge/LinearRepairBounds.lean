import PhysicalBridge.LinearRepairVector

/-! Bounds for the running rational accumulator and comparison operands.
They concern the instrumented source recursion, not native heap residency. -/
namespace QecReliability.RationalOutput.LinearRepair
open Binary SharedCircuit SharedCircuit.LatentEncoding SharedCircuit.ConcreteQuantum

theorem sourceEntry_den_le {r j M : ℕ} (a ell : Ratio) (g b : ℕ × ℕ)
    (ha : a.den≤M) (hell : ell.den≤M) (h1 : 1≤M) (hgb : g.1+b.1≤M) :
    (sourceEntry r a ell j g b).den≤M := by
  unfold sourceEntry
  split_ifs
  · exact ha
  · exact hell
  · exact Ratio.counts_den_le h1 hgb

theorem run_accumulator_bound (shape : Bool) (r : ℕ) (a ell : Ratio)
    (gs bs : List (ℕ × ℕ)) (j : ℕ) (previous : Ratio) {M : ℕ}
    (ha : a.den≤M) (hell : ell.den≤M) (hp : previous.den≤M) (h1 : 1≤M)
    (hgb : ∀ g∈gs, ∀ b∈bs, g.1+b.1≤M) :
    (run shape r a ell j previous gs bs).maxAccumulatorDen≤M := by
  induction gs generalizing bs j previous with
  | nil => exact hp
  | cons g gs ih =>
    cases bs with
    | nil => exact hp
    | cons b bs =>
      have he := sourceEntry_den_le (r:=r) (j:=j) a ell g b ha hell h1
        (hgb g (by simp) b (by simp))
      have hc : (if j=0 then sourceEntry r a ell j g b else
          Ratio.lesser previous (sourceEntry r a ell j g b)).den≤M := by
        split_ifs
        · exact he
        · exact Ratio.lesser_den_le hp he
      have ho : (if shape then Ratio.greater ell
          (if j=0 then sourceEntry r a ell j g b else Ratio.lesser previous (sourceEntry r a ell j g b))
          else sourceEntry r a ell j g b).den≤M := by
        cases shape
        · exact he
        · exact Ratio.greater_den_le hell hc
      have ht := ih bs (j+1) _ hc
        (fun g hg b hb => hgb g (by simp [hg]) b (by simp [hb]))
      exact max_le hp (max_le he (max_le hc (max_le ho ht)))

theorem comparison_products_size {x y : Ratio} {M : ℕ} (hx : x.den≤M) (hy : y.den≤M) :
    (x.num*y.den).size≤2*M.size ∧ (y.num*x.den).size≤2*M.size := by
  have hxn := Nat.size_le_size (x.num_le_den.trans hx)
  have hyn := Nat.size_le_size (y.num_le_den.trans hy)
  have hxd := Nat.size_le_size hx
  have hyd := Nat.size_le_size hy
  have h0 := size_mul_bound x.num y.den
  have h1 := size_mul_bound y.num x.den
  omega

theorem fromCache_accumulator_bound {n r B : ℕ} (shape : Bool)
    (rows : List (List (PauliCoord n))) (C : Program r n) (T : CoefficientTable r)
    (hT : ∀ j, (T.good.get j).1≤trialValueBound (keySize n r) B ∧
      (T.bad.get j).1≤trialValueBound (keySize n r) B) :
    (fromCache shape rows C T).maxAccumulatorDen≤2*trialValueBound (keySize n r) B := by
  apply run_accumulator_bound
  · exact dyadic_den_bound rows _ B
  · exact dyadic_den_bound rows _ B
  · exact dyadic_den_bound rows _ B
  · have : 0<trialValueBound (keySize n r) B := by unfold trialValueBound; positivity
    omega
  · intro g hg b hb
    obtain ⟨i,hi⟩ := List.mem_iff_get.mp hg
    obtain ⟨j,hj⟩ := List.mem_iff_get.mp hb
    have hi' : i.val<r+1 := by simpa only [T.good.length_eq] using i.isLt
    have hj' : j.val<r+1 := by simpa only [T.bad.length_eq] using j.isLt
    have hG := (hT ⟨i.val,hi'⟩).1
    have hB := (hT ⟨j.val,hj'⟩).2
    change (T.good.entries.get i).1≤_ at hG
    change (T.bad.entries.get j).1≤_ at hB
    rw [hi] at hG
    rw [hj] at hB
    omega

theorem prepared_accumulator_bound {Ω : Type*} [Fintype Ω] {n r : ℕ} (shape : Bool)
    (rows : List (List (PauliCoord n))) (C : Program r n)
    (H : HashStages Ω (CoefficientKey n r) (keySize n r))
    (K : SuppliedHashCircuits H (keyBits n r)) (solver : ∀ v, PrefixCNF.ExactSAT v 3)
    (B m : ℕ) (ω : Fin (2*m+1) → Ω) :
    (fromCache shape rows C (prepare rows C H K solver B m ω)).maxAccumulatorDen≤
      2*trialValueBound (keySize n r) B :=
  fromCache_accumulator_bound shape rows C _ (prepare_count_bounds rows C H K solver B m ω)

end QecReliability.RationalOutput.LinearRepair
