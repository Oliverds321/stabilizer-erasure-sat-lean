import Trans.Bounds.Size

/-!
# Trans.Bounds.Loop: closed-form bounds of the loop-interface functions

At every argument of the form `(c, encCfg s)` (any context `c`, any configuration `s`):

| function | cost | depth | msize |
|---|---|---|---|
| `isInvokeF` | `≤ 2000` | `≤ 20` | `≤ 200` |
| `isDoneF` | `≤ 4000` | `≤ 20` | `≤ 200` |
| `queryOfF` | `≤ 20` | `≤ 1` | `= 0` |
| `answerSTF` / `resumeTopF` | `≤ 1000` | `≤ 5` | `≤ 2 · size(result)` |
| `outputF` | `≤ 600 (C+1)^3` | `≤ 10 (C+1)^2` | `≤ 40 (C+1)` |

with `C = (Ty.enc TCfg (encCfg s)).size` (`outputF_bounds`). The `resume` result is the
encoded successor state, which is again reachable, so the size bridge bounds it too.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace QecReliability.Trans.Bounds
open QecReliability.FL QecReliability.FL.Lib Tm
open QecReliability.Trans.Control (TR encCfg encCtx TArg TCfg TCtx bodySig bodySig_cost
  bodySig_depth bodySig_msize pcCode toR)
open QecReliability.OracleCost QecReliability.OracleCost.WholeWrapperCandidate

theorem pc_size (s : Config) : (pcCode s.pc).size ≤ 5 :=
  Nat.size_le.mpr (by have := Control.pcCode_lt s.pc; omega)

theorem enc_pc (s : Config) : (Enc.nat (pcCode s.pc)).size ≤ 21 :=
  sz_lt_pow _ 5 (by have := Control.pcCode_lt s.pc; omega)

theorem enc_lit (t k : ℕ) (h : t < 2 ^ k) : (Enc.nat t).size ≤ 4 * k + 1 := sz_lt_pow t k h

theorem size_lit (t k : ℕ) (h : t < 2 ^ k) : t.size ≤ k := Nat.size_le.mpr h

section Simple
variable {TX' : Ty} (x : Control.Ix TX') (c : (TCtx TX').den) (s : Config)

theorem isInvoke_bounds :
    (Control.isInvokeF x).cost (c, encCfg s) ≤ 2000 ∧
      (Control.isInvokeF x).depth (c, encCfg s) ≤ 20 ∧
      (Control.isInvokeF x).msize (c, encCfg s) ≤ 200 := by
  have h1 := pc_size s
  have h2 := enc_pc s
  have h3 := enc_lit 3 2 (by omega)
  have h4 := size_lit 3 2 (by omega)
  refine ⟨?_, ?_, ?_⟩ <;>
  simp [Control.isInvokeF, bodySig_cost, bodySig_depth, bodySig_msize, Control.isInvokeBody,
    tm_simp, encCfg] <;> omega

theorem isDone_bounds :
    (Control.isDoneF x).cost (c, encCfg s) ≤ 4000 ∧
      (Control.isDoneF x).depth (c, encCfg s) ≤ 20 ∧
      (Control.isDoneF x).msize (c, encCfg s) ≤ 200 := by
  have h1 := pc_size s
  have h2 := enc_pc s
  have h3 := enc_lit 18 5 (by omega)
  have h4 := size_lit 18 5 (by omega)
  have h5 := enc_lit 19 5 (by omega)
  have h6 := size_lit 19 5 (by omega)
  refine ⟨?_, ?_, ?_⟩ <;>
  simp [Control.isDoneF, bodySig_cost, bodySig_depth, bodySig_msize, Control.isDoneBody,
    tm_simp, encCfg] <;> split_ifs <;> omega

theorem queryOf_bounds :
    (Control.queryOfF x).cost (c, encCfg s) ≤ 20 ∧
      (Control.queryOfF x).depth (c, encCfg s) ≤ 1 ∧
      (Control.queryOfF x).msize (c, encCfg s) = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;>
  simp [Control.queryOfF, bodySig_cost, bodySig_depth, bodySig_msize, Control.queryOfBody,
    tm_simp]

theorem answer_cost_le (b : Bool) :
    (Control.answerF x).cost ((c, encCfg s), b) ≤ 800 ∧
      (Control.answerF x).depth ((c, encCfg s), b) ≤ 2 := by
  have h3 := enc_lit 4 3 (by omega)
  constructor <;>
  simp [Control.answerF, bodySig_cost, bodySig_depth, Control.answerBody, tm_simp] <;> omega

theorem answer_msize_le (b : Bool) :
    (Control.answerF x).msize ((c, encCfg s), b) ≤
      (Ty.enc TCfg ((Control.answerF x).den ((c, encCfg s), b))).size := by
  have h := Control.bodySig_msize_le x.answer Control.answerBody ((c, encCfg s), b)
  have h0 : Control.Tm'.ex (Control.answerBody (TX := TX')) (Env.one ((c, encCfg s), b)) = 0 := by
    simp only [Control.answerBody, Control.Tm'.ex, Tm.msize, max_self]
  rw [h0, Nat.add_zero] at h
  exact h

theorem answerST_bounds (b : Bool) :
    (Control.answerSTF x).cost ((c, encCfg s), b) ≤ 1000 ∧
      (Control.answerSTF x).depth ((c, encCfg s), b) ≤ 5 ∧
      (Control.answerSTF x).msize ((c, encCfg s), b) ≤
        2 * (Ty.enc (TArg TX') ((Control.answerSTF x).den ((c, encCfg s), b))).size := by
  obtain ⟨h1, h2⟩ := answer_cost_le x c s b
  have h3 := answer_msize_le x c s b
  have h4 := Control.bodySig_msize_le x.answerST (Control.answerSTBody x) ((c, encCfg s), b)
  have e1 : (Control.answerSTF x).den ((c, encCfg s), b) =
      (c, (Control.answerF x).den ((c, encCfg s), b)) := rfl
  refine ⟨?_, ?_, ?_⟩
  · simp only [Control.answerSTF, bodySig_cost, Control.answerSTBody, Tm.cost, Tm.den,
      Env.get] at h1 ⊢
    omega
  · simp only [Control.answerSTF, bodySig_depth, Control.answerSTBody, Tm.depth, Tm.den,
      Env.get] at h2 ⊢
    omega
  · have h5 : Control.Tm'.ex (Control.answerSTBody x) (Env.one ((c, encCfg s), b)) =
        (Control.answerF x).msize ((c, encCfg s), b) := by
      simp [Control.answerSTBody, tm_simp]
    have h6 : (Ty.enc (TArg TX') ((Control.answerSTF x).den ((c, encCfg s), b))).size =
        (Ty.enc (TCtx TX') c).size +
          (Ty.enc TCfg ((Control.answerF x).den ((c, encCfg s), b))).size + 1 := by
      rw [e1, shape2]
    change (Control.answerSTF x).msize _ ≤ _ at h4
    rw [h5] at h4
    rw [h6]
    have : (Ty.enc (TArg TX') ((Control.answerSTF x).den ((c, encCfg s), b))).size =
        (Ty.enc (TCtx TX') c).size +
          (Ty.enc TCfg ((Control.answerF x).den ((c, encCfg s), b))).size + 1 := h6
    have h7 : (Ty.enc (TArg TX') ((bodySig x.answerST (Control.answerSTBody x)).den
        ((c, encCfg s), b))).size = (Ty.enc (TArg TX') ((Control.answerSTF x).den
        ((c, encCfg s), b))).size := rfl
    omega

theorem resumeTop_bounds (o : OIx) (b : Bool) :
    (resumeTopF o x).cost (b, (c, encCfg s)) ≤ 1100 ∧
      (resumeTopF o x).depth (b, (c, encCfg s)) ≤ 6 ∧
      (resumeTopF o x).msize (b, (c, encCfg s)) ≤
        2 * (Ty.enc (TArg TX') ((resumeTopF o x).den (b, (c, encCfg s)))).size +
          (Ty.enc (.prod (TArg TX') .bool) ((c, encCfg s), b)).size := by
  obtain ⟨h1, h2, h3⟩ := answerST_bounds x c s b
  have e : (resumeTopF o x).den (b, (c, encCfg s)) = (Control.answerSTF x).den ((c, encCfg s), b) :=
    rfl
  rw [e]
  refine ⟨?_, ?_, ?_⟩
  · simp only [resumeTopF, bodySig_cost, resumeTopBody, Tm.cost, Tm.den, Env.get] at h1 ⊢
    omega
  · simp only [resumeTopF, bodySig_depth, resumeTopBody, Tm.depth, Tm.den, Env.get] at h2 ⊢
    omega
  · simp only [resumeTopF, bodySig_msize, resumeTopBody, Tm.msize, Tm.den, Env.get] at h3 ⊢
    omega

end Simple

/-! ## The output function -/

theorem wordCost_le (k : ℕ) : Query.wordCost k ≤ 105 * (k + 1) ^ 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Query.wordCost_succ]
    have h := NatSize.size_le_self (k + 1)
    nlinarith

theorem natHeaderCost_le (n : ℕ) : Query.natHeaderCost n ≤ 300 * (n.size + 1) ^ 2 := by
  have h1 := wordCost_le n.size
  have h2 := NatSize.size_le_self n.size
  unfold Query.natHeaderCost
  nlinarith

/-- One ratio's header pair. -/
theorem ratHdr_bounds (o : OIx) (p : ℕ × ℕ) :
    (ratHdrF o).cost p ≤ 700 * (p.1.size + p.2.size + 1) ^ 2 ∧
      (ratHdrF o).depth p ≤ 6 * (p.1.size + p.2.size) + 20 ∧
      (ratHdrF o).msize p ≤ 40 * (p.1.size + p.2.size) + 60 ∧
      ((ratHdrF o).den p).length = 2 * p.1.size + 2 * p.2.size + 2 := by
  have h1 := natHeaderCost_le p.1
  have h2 := natHeaderCost_le p.2
  have s1 := NatSize.size_le_self p.1.size
  have s2 := NatSize.size_le_self p.2.size
  have z1 := sz_boolList (QueryCodec.natHeader p.1)
  have z2 := sz_boolList (QueryCodec.natHeader p.2)
  simp only [QueryCodec.natHeader_length] at z1 z2
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [ratHdrF, bodySig_cost, ratHdrBody, Tm.cost, Tm.den, Env.get, appendF_cost,
      Query.natHeaderF_cost, Query.natHeaderF_den, QueryCodec.natHeader_length]
    nlinarith
  · simp only [ratHdrF, bodySig_depth, ratHdrBody, Tm.depth, Tm.den, Env.get, appendF_depth,
      Query.natHeaderF_depth, Query.natHeaderF_den, QueryCodec.natHeader_length]
    omega
  · simp only [ratHdrF, bodySig_msize, ratHdrBody, Tm.msize, Tm.den, Env.get, appendF_msize,
      Query.natHeaderF_msize, Query.natHeaderF_den, Ty.sz_prod]
    omega
  · simp [ratHdrF_den]
    omega

theorem sum_le_len_mul {α : Type} (xs : List α) (f : α → ℕ) (M : ℕ) (h : ∀ x ∈ xs, f x ≤ M) :
    (xs.map f).sum ≤ xs.length * M := by
  induction xs with
  | nil => simp
  | cons y ys ih =>
    have := h y (by simp)
    have := ih (fun z hz => h z (by simp [hz]))
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
    omega

theorem mem_ratio_le {xs : List (ℕ × ℕ)} {p : ℕ × ℕ} (h : p ∈ xs) :
    p.1.size + p.2.size + 1 ≤ (Ty.enc (.list TR) xs).size := by
  have h1 := Ty.sz_mem_le TR h
  have h2 : p.1.size ≤ (Ty.enc .nat p.1).size := Control.size_le_enc p.1
  have h3 : p.2.size ≤ (Ty.enc .nat p.2).size := Control.size_le_enc p.2
  rw [shape2] at h1
  omega

/-- The encoded output word is small: its length is the header weight of the output. -/
theorem ratioWord_length (xs : List RationalOutput.Ratio) :
    (Assembly.ratioWord xs).length = hw (ratW xs) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have e : ratW (x :: xs) = [x.num, x.den] ++ ratW xs := rfl
    simp only [Assembly.ratioWord, List.flatMap_cons, List.length_append,
      QueryCodec.natHeader_length] at ih ⊢
    rw [e, hw_append, hw_cons, hw_cons, hw_nil, ← ih]

theorem flatMap_len_le (o : OIx) (xs : List (ℕ × ℕ)) :
    (xs.flatMap (ratHdrF o).den).length ≤ 2 * (Ty.enc (.list TR) xs).size := by
  induction xs with
  | nil => simp
  | cons p ps ih =>
    obtain ⟨-, -, -, h4⟩ := ratHdr_bounds o p
    have h2 : p.1.size ≤ (Ty.enc .nat p.1).size := Control.size_le_enc p.1
    have h3 : p.2.size ≤ (Ty.enc .nat p.2).size := Control.size_le_enc p.2
    rw [List.flatMap_cons, List.length_append, Ty.sz_list_cons, shape2]
    omega

theorem outWord_bounds (o : OIx) (xs : List (ℕ × ℕ)) :
    (outWordF o).cost xs ≤ 1000 * ((Ty.enc (.list TR) xs).size + 1) ^ 3 ∧
      (outWordF o).depth xs ≤ 10 * ((Ty.enc (.list TR) xs).size + 1) ^ 2 ∧
      (outWordF o).msize xs ≤ 40 * (Ty.enc (.list TR) xs).size + 60 := by
  generalize hT : (Ty.enc (.list TR) xs).size = T
  have hlen := Ty.length_le_sz TR xs
  rw [hT] at hlen
  have hp : ∀ p ∈ xs, p.1.size + p.2.size + 1 ≤ T := fun p hp => by
    have := mem_ratio_le hp; omega
  have q1 : 1 ≤ (T + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have q2 : T + 1 ≤ (T + 1) ^ 2 := Nat.le_self_pow (by norm_num) _
  have q3 : 1 ≤ (T + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
  refine ⟨?_, ?_, ?_⟩
  · have h9 : xs.length * (900 * (T + 1) ^ 2) ≤ 900 * (T + 1) ^ 3 := by
      calc xs.length * (900 * (T + 1) ^ 2) ≤ (T + 1) * (900 * (T + 1) ^ 2) :=
            Nat.mul_le_mul_right _ (by omega)
        _ = 900 * (T + 1) ^ 3 := by ring
    refine le_trans (Nat.add_le_add_right (sum_le_len_mul xs _ (900 * (T + 1) ^ 2) ?_) 10) ?_
    · intro p hp'
      obtain ⟨h1, -, -, h4⟩ := ratHdr_bounds o p
      have h5 := hp p hp'
      have h6 : (p.1.size + p.2.size + 1) ^ 2 ≤ (T + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      omega
    · omega
  · simp only [outWordF, flatMapF_depth]
    have hm := maxOf_le (fun x => (ratHdrF o).depth x + ((ratHdrF o).den x).length + 1) xs
      (9 * T + 23) (fun p hp' => by
        obtain ⟨-, h2, -, h4⟩ := ratHdr_bounds o p
        have h5 := hp p hp'
        omega)
    nlinarith
  · simp only [outWordF, flatMapF_msize]
    have hm := maxOf_le (ratHdrF o).msize xs (40 * T + 60) (fun p hp' => by
        obtain ⟨-, -, h3, -⟩ := ratHdr_bounds o p
        have h5 := hp p hp'
        omega)
    have hl := flatMap_len_le o xs
    have hb := sz_boolList (xs.flatMap (ratHdrF o).den)
    rw [hT] at hl
    omega

theorem output_le_cfg (s : Config) :
    (Ty.enc (.list TR) (s.output.map toR)).size ≤ (Ty.enc TCfg (encCfg s)).size := by
  have h := sz_cfg_split s
  have h5 : (Ty.enc Control.TG5 (toR s.endpoint0, toR s.endpoint1, toR s.previous, s.repairIndex,
      s.outputRev.map toR, s.output.map toR)).size =
      (Ty.enc TR (toR s.endpoint0)).size + (Ty.enc TR (toR s.endpoint1)).size +
      (Ty.enc TR (toR s.previous)).size + (Ty.enc .nat s.repairIndex).size +
      (Ty.enc (.list TR) (s.outputRev.map toR)).size +
      (Ty.enc (.list TR) (s.output.map toR)).size + 5 := shape6 _ _ _ _ _ _
  omega

/-- **Closed-form bounds of the output function** (`C` = encoded configuration size). -/
theorem outputF_bounds (o : OIx) {TX' : Ty} (c : (TCtx TX').den) (s : Config) :
    (outputF o TX').cost (c, encCfg s) ≤ 1100 * ((Ty.enc TCfg (encCfg s)).size + 1) ^ 3 ∧
      (outputF o TX').depth (c, encCfg s) ≤ 10 * ((Ty.enc TCfg (encCfg s)).size + 1) ^ 2 + 1 ∧
      (outputF o TX').msize (c, encCfg s) ≤ 40 * (Ty.enc TCfg (encCfg s)).size + 60 := by
  obtain ⟨h1, h2, h3⟩ := outWord_bounds o (s.output.map toR)
  have h4 := output_le_cfg s
  generalize (Ty.enc TCfg (encCfg s)).size = C at h4 ⊢
  generalize (Ty.enc (.list TR) (s.output.map toR)).size = T at h1 h2 h3 h4
  have e3 : (T + 1) ^ 3 ≤ (C + 1) ^ 3 := Nat.pow_le_pow_left (by omega) 3
  have e2 : (T + 1) ^ 2 ≤ (C + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have q3 : 1 ≤ (C + 1) ^ 3 := Nat.one_le_pow _ _ (by omega)
  refine ⟨?_, ?_, ?_⟩
  · simp only [outputF, bodySig_cost, outputBody, Tm.cost, Tm.den, Env.get]
    change _ + (outWordF o).cost (s.output.map toR) + _ ≤ _
    omega
  · simp only [outputF, bodySig_depth, outputBody, Tm.depth, Tm.den, Env.get]
    change max _ ((outWordF o).depth (s.output.map toR)) + 1 ≤ _
    omega
  · simp only [outputF, bodySig_msize, outputBody, Tm.msize, Tm.den, Env.get]
    change max _ ((outWordF o).msize (s.output.map toR)) ≤ _
    omega

end QecReliability.Trans.Bounds
