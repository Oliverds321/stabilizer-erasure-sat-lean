import PhysicalBridge.RationalOutputEdges

/-! A measured traversal of two cached count lists. Each pair is consumed once;
endpoint replacement and the running minimum occur inside this same recursion.
Counters describe source-level operations, not native instruction costs. -/
namespace QecReliability.RationalOutput.LinearRepair

structure Result where
  values : List Ratio
  pairVisits : ℕ
  ratioBuilds : ℕ
  orderComparisons : ℕ
  endpointTests : ℕ
  maxAccumulatorDen : ℕ

def sourceEntry (r : ℕ) (a ell : Ratio) (j : ℕ) (g b : ℕ × ℕ) : Ratio :=
  if j=0 then a else if j=r then ell else Ratio.counts g.1 b.1

def run (shape : Bool) (r : ℕ) (a ell : Ratio) (j : ℕ) (previous : Ratio) :
    List (ℕ × ℕ) → List (ℕ × ℕ) → Result
  | [],_ => ⟨[],0,0,0,0,previous.den⟩
  | _::_,[] => ⟨[],0,0,0,0,previous.den⟩
  | g::gs,b::bs =>
    let e := sourceEntry r a ell j g b
    let current := if j=0 then e else Ratio.lesser previous e
    let output := if shape then Ratio.greater ell current else e
    let rest := run shape r a ell (j+1) current gs bs
    ⟨output::rest.values,rest.pairVisits+1,
      rest.ratioBuilds+(if j=0 ∨ j=r then 0 else 1),
      rest.orderComparisons+(if j=0 then 0 else 1)+(if shape then 1 else 0),
      rest.endpointTests+(if j=0 then 1 else 2),
      max previous.den (max e.den (max current.den (max output.den rest.maxAccumulatorDen)))⟩

theorem run_length (shape : Bool) (r : ℕ) (a ell : Ratio) (gs bs : List (ℕ × ℕ))
    (j : ℕ) (previous : Ratio) :
    (run shape r a ell j previous gs bs).values.length=min gs.length bs.length := by
  induction gs generalizing bs j previous with
  | nil => simp [run]
  | cons g gs ih =>
    cases bs with
    | nil => simp [run]
    | cons b bs => simp [run,ih,min_add_add_right]

theorem run_visits (shape : Bool) (r : ℕ) (a ell : Ratio) (gs bs : List (ℕ × ℕ))
    (j : ℕ) (previous : Ratio) :
    (run shape r a ell j previous gs bs).pairVisits=min gs.length bs.length := by
  induction gs generalizing bs j previous with
  | nil => simp [run]
  | cons g gs ih =>
    cases bs with
    | nil => simp [run]
    | cons b bs => simp [run,ih,min_add_add_right]

theorem run_bounds (shape : Bool) (r : ℕ) (a ell : Ratio) (gs bs : List (ℕ × ℕ))
    (j : ℕ) (previous : Ratio) :
    (run shape r a ell j previous gs bs).ratioBuilds≤min gs.length bs.length ∧
    (run shape r a ell j previous gs bs).orderComparisons≤2*min gs.length bs.length ∧
    (run shape r a ell j previous gs bs).endpointTests≤2*min gs.length bs.length := by
  induction gs generalizing bs j previous with
  | nil => simp [run]
  | cons g gs ih =>
    cases bs with
    | nil => simp [run]
    | cons b bs =>
      have h := ih bs (j+1) (if j=0 then sourceEntry r a ell j g b else
        Ratio.lesser previous (sourceEntry r a ell j g b))
      simp only [run,List.length_cons,min_add_add_right]
      split_ifs at h ⊢ <;> omega

theorem run_semantics (shape : Bool) (r : ℕ) (a ell : Ratio)
    (e : ℕ → Ratio) (gs bs : List (ℕ × ℕ)) (j : ℕ) (previous : Ratio)
    (hentry : ∀ i (hg : i<gs.length) (hb : i<bs.length),
      sourceEntry r a ell (j+i) gs[i] bs[i]=e (j+i))
    (hprev : j≠0 → previous=Ratio.prefixMinimum e (j-1)) :
    (run shape r a ell j previous gs bs).values=
      List.ofFn (fun i : Fin (min gs.length bs.length) =>
        if shape then Ratio.greater ell (Ratio.prefixMinimum e (j+i.val)) else e (j+i.val)) := by
  induction gs generalizing bs j previous with
  | nil => simp [run]
  | cons g gs ih =>
    cases bs with
    | nil => simp [run]
    | cons b bs =>
      have he : sourceEntry r a ell j g b=e j := by
        simpa using hentry 0 (by simp) (by simp)
      have hc : (if j=0 then sourceEntry r a ell j g b else
          Ratio.lesser previous (sourceEntry r a ell j g b))=Ratio.prefixMinimum e j := by
        rw [he]
        cases j with
        | zero => rfl
        | succ j => simp [hprev (by omega),Ratio.prefixMinimum]
      have ht := ih bs (j+1) (Ratio.prefixMinimum e j)
        (fun i hg hb => by
          have h := hentry (i+1) (by simp; omega) (by simp; omega)
          change sourceEntry r a ell (j+(i+1)) gs[i] bs[i]=e (j+(i+1)) at h
          have hij : j+1+i=j+(i+1) := by omega
          rw [hij]
          exact h)
        (fun _ => by simp)
      rw [run]
      dsimp only
      rw [hc,he,ht]
      simp only [List.length_cons,min_add_add_right]
      rw [List.ofFn_succ]
      simp only [Fin.coe_cast,Fin.val_zero,Fin.val_succ,add_zero]
      congr 2
      funext i
      have hi : j+1+i.val=j+(i.val+1) := by omega
      rw [hi]

theorem run_comparisons_positive (shape : Bool) (r : ℕ) (a ell : Ratio)
    (gs bs : List (ℕ × ℕ)) (j : ℕ) (hj : 0<j) (previous : Ratio) :
    (run shape r a ell j previous gs bs).orderComparisons=
      (if shape then 2 else 1)*min gs.length bs.length := by
  induction gs generalizing bs j previous with
  | nil => simp [run]
  | cons g gs ih =>
    cases bs with
    | nil => simp [run]
    | cons b bs =>
      simp only [run,if_neg (Nat.ne_of_gt hj),List.length_cons,min_add_add_right]
      rw [ih bs (j+1) (by omega)]
      cases shape <;> simp
      omega

theorem run_comparisons_initial (shape : Bool) (r : ℕ) (a ell : Ratio)
    (gs bs : List (ℕ × ℕ)) (previous : Ratio) :
    (run shape r a ell 0 previous gs bs).orderComparisons=
      if shape then 2*min gs.length bs.length-1 else min gs.length bs.length-1 := by
  cases gs with
  | nil => simp [run]
  | cons g gs =>
    cases bs with
    | nil => simp [run]
    | cons b bs =>
      simp only [run,↓reduceIte,List.length_cons,min_add_add_right]
      rw [run_comparisons_positive shape r a ell gs bs 1 (by omega)]
      cases shape <;> simp
      omega

end QecReliability.RationalOutput.LinearRepair
