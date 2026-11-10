import Trans.BoundsRest.InitHdr

/-!
# Trans.BoundsRest.InitParse: the parser on the machine input

All bounds in one size parameter `Q` (`P = Q + 2`) with: every input suffix visited has length
`≤ Q`, `n ≤ Q`, row/row-count/incidence numbers `≤ Q`. Header counts are evaluated at the actual
input (`rowBits`, `rowsBits`, `programBits (iidProgram n)` = `n+1` headers), via
`InitMany.many_bounds`:

* `hdr_le`, `coord_le` (`InitHdr` bounds made monotone in `Q`);
* `row_le`: `rowF` at `rowBits row ++ R`: cost `≤ 1000 P³`, depth `≤ 12Q + 50`, msize `≤ 300 P²`;
* `rows_le`: `rowsF` at `rowsBits rows ++ R`: `≤ 2000 P⁴`, `≤ 16Q + 100`, `≤ 1000 P²`;
* `hdrs_le`: `hdrsF` at `(n+1, programBits (iidProgram n) ++ R)`;
* `prec_le`: `precF` on any input; **`parse_le`**: `parseF` at
  `problemBits rows (iidProgram n) a b c d ++ coins`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace QecReliability.Trans.BoundsRest
open QecReliability.FL QecReliability.FL.Lib QecReliability.FL.Tm QecReliability.Trans.Query.Bound
open QecReliability.Trans.Control (bodySig bodySig_den bodySig_cost bodySig_depth bodySig_msize)
open QecReliability.Trans.Wire
open QecReliability.OracleCost QecReliability.OracleCost.WholeWrapperCandidate
open QecReliability.SharedCircuit

/-- Shape of `rowF`/`rowsF`: `bs ↦ F2 (F1 bs)`. -/
theorem comp2_eqs {a b c : Ty} (i : ℕ) (F1 : FnSig a b) (F2 : FnSig b c) (x : a.den) :
    (bodySig i (.app F2 (.app F1 v0))).cost x = 1 + F1.cost x + F2.cost (F1.den x) + 2 ∧
    (bodySig i (.app F2 (.app F1 v0))).depth x =
      max (max 0 (F1.depth x)) (F2.depth (F1.den x)) + 1 ∧
    (bodySig i (.app F2 (.app F1 v0))).msize x =
      max (max 0 (F1.msize x)) (F2.msize (F1.den x)) := ⟨rfl, rfl, rfl⟩

theorem pow_facts (Q : ℕ) :
    Q + 2 ≤ (Q + 2) ^ 2 ∧ (Q + 2) ^ 2 ≤ (Q + 2) ^ 3 ∧ (Q + 2) ^ 3 ≤ (Q + 2) ^ 4 ∧
      Q * (Q + 2) ^ 2 ≤ (Q + 2) ^ 3 ∧ Q * (Q + 2) ^ 3 ≤ (Q + 2) ^ 4 ∧
      (Q + 2) * (Q + 2) = (Q + 2) ^ 2 ∧ 4 * Q + 4 ≤ (Q + 2) ^ 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, by ring, ?_⟩
  · nlinarith
  · exact Nat.pow_le_pow_right (by omega) (by omega)
  · exact Nat.pow_le_pow_right (by omega) (by omega)
  · have : Q * (Q + 2) ^ 2 ≤ (Q + 2) * (Q + 2) ^ 2 := Nat.mul_le_mul_right _ (by omega)
    nlinarith
  · have : Q * (Q + 2) ^ 3 ≤ (Q + 2) * (Q + 2) ^ 3 := Nat.mul_le_mul_right _ (by omega)
    nlinarith
  · have e : (Q + 2) ^ 2 = Q * Q + 4 * Q + 4 := by ring
    rw [e]; omega

section Parse
variable (L : Wire.Lib) (h : HIx) (p : PIx)

/-! ## Readers made monotone in `Q` -/

theorem hdr_le {Q : ℕ} (bs : List Bool) (hQ : bs.length ≤ Q) :
    (hdrF L h).cost bs ≤ 400 * (Q + 2) ^ 2 ∧ (hdrF L h).depth bs ≤ 10 * Q + 20 ∧
      (hdrF L h).msize bs ≤ 100 * Q + 100 := by
  obtain ⟨c1, c2, c3⟩ := hdr_bounds L h bs
  have m : (bs.length + 2) * (bs.length + 2) ≤ (Q + 2) ^ 2 := by
    rw [sq]; exact Nat.mul_le_mul (by omega) (by omega)
  exact ⟨by omega, by omega, by omega⟩

theorem coord_le {Q : ℕ} (bs : List Bool) (hQ : bs.length ≤ Q) :
    (coordF L h).cost bs ≤ 400 * (Q + 2) ^ 2 + 20 ∧ (coordF L h).depth bs ≤ 10 * Q + 22 ∧
      (coordF L h).msize bs ≤ 120 * Q + 200 := by
  obtain ⟨c1, c2, c3⟩ := coord_bounds L h bs
  have m : (bs.length + 2) * (bs.length + 2) ≤ (Q + 2) ^ 2 := by
    rw [sq]; exact Nat.mul_le_mul (by omega) (by omega)
  exact ⟨by omega, by omega, by omega⟩

/-! ## One row -/

theorem hdr_rowBits {n : ℕ} (row : List (PauliCoord n)) (R : List Bool) :
    (hdrF L h).den (InputEncoding.rowBits row ++ R) = (row.length, row.flatMap InputEncoding.coordBits ++ R) := by
  rw [hdrF_den]
  simp only [InputEncoding.rowBits, List.append_assoc, hdr_natHeader]

theorem coordF_read {n : ℕ} (x : PauliCoord n) (r : List Bool) :
    (coordF L h).den (InputEncoding.coordBits x ++ r) = (Query.encCoord x, r) := by
  rw [coordF_den]; exact coordR_coordBits x r

theorem row_arith {Q k mg B c1 c2 c3 m1 m2 m3 : ℕ} (hk : k ≤ Q) (hB : B ≤ 4 * Q + 1)
    (hmg : mg ≤ (Q + 2) ^ 2)
    (hc1 : c1 ≤ 400 * (Q + 2) ^ 2) (hd1 : c2 ≤ 10 * Q + 20) (hm1 : c3 ≤ 100 * Q + 100)
    (hc2 : m1 ≤ (400 * (Q + 2) ^ 2 + 20 + 60) * k + 60 * ((k + 1) * (k + 1)) + 100)
    (hd2 : m2 ≤ 2 * k + (10 * Q + 22) + 20)
    (hm2 : m3 ≤ 3 * (120 * Q + 200) + 20 * ((k + 1) * (k + 1)) + 3 * (5 * mg + 1) + 6 * B + 100) :
    1 + c1 + m1 + 2 ≤ 1000 * (Q + 2) ^ 3 ∧ max (max 0 c2) m2 + 1 ≤ 12 * Q + 50 ∧
      max (max 0 c3) m3 ≤ 300 * (Q + 2) ^ 2 := by
  obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := pow_facts Q
  have k1 : (k + 1) * (k + 1) ≤ (Q + 2) ^ 2 := by rw [← f6]; exact Nat.mul_le_mul (by omega) (by omega)
  have k2 : (400 * (Q + 2) ^ 2 + 20 + 60) * k ≤ 400 * (Q * (Q + 2) ^ 2) + 80 * Q := by
    have := Nat.mul_le_mul_left (400 * (Q + 2) ^ 2 + 20 + 60) hk
    nlinarith
  refine ⟨by omega, by omega, ?_⟩
  exact max_le (max_le (by omega) (by omega)) (by omega)

/-- **One row** at the machine input. -/
theorem row_le {n Q : ℕ} (row : List (PauliCoord n)) (R : List Bool)
    (hQ : (InputEncoding.rowBits row ++ R).length ≤ Q) (hn : n ≤ Q) (hr : row.length ≤ Q) :
    (rowF L h p).cost (InputEncoding.rowBits row ++ R) ≤ 1000 * (Q + 2) ^ 3 ∧
      (rowF L h p).depth (InputEncoding.rowBits row ++ R) ≤ 12 * Q + 50 ∧
      (rowF L h p).msize (InputEncoding.rowBits row ++ R) ≤ 300 * (Q + 2) ^ 2 := by
  obtain ⟨e1, e2, e3⟩ := comp2_eqs p.row (hdrF L h) (manyF L (coordF L h) p.cStep p.cFold p.cMany)
    (InputEncoding.rowBits row ++ R)
  have hsuf : ∀ j, ((row.drop j).flatMap InputEncoding.coordBits ++ R).length ≤ Q := by
    intro j
    have h1 := (suffix_flatMap InputEncoding.coordBits row R j).length_le
    have h2 : (row.flatMap InputEncoding.coordBits ++ R).length ≤ (InputEncoding.rowBits row ++ R).length := by
      simp only [InputEncoding.rowBits, List.append_assoc, List.length_append]; omega
    omega
  obtain ⟨m1, m2, m3⟩ := many_bounds L (coordF L h) p.cStep p.cFold p.cMany
    InputEncoding.coordBits Query.encCoord (coordF_read L h) row R _ _ _
    (fun j _ => coord_le L h _ (hsuf j))
  rw [← hdr_rowBits L h row R] at m1 m2 m3
  obtain ⟨c1, c2, c3⟩ := hdr_le L h _ hQ
  have hB : (Ty.enc (.list .bool) (row.flatMap InputEncoding.coordBits ++ R)).size ≤ 4 * Q + 1 := by
    have h0 := hsuf 0
    rw [List.drop_zero] at h0
    have := sz_bools (row.flatMap InputEncoding.coordBits ++ R)
    omega
  have hmg : mag (.list TCoordW) (row.map Query.encCoord) ≤ (Q + 2) ^ 2 := by
    have := mag_row_le row
    have := Nat.mul_le_mul hr (show n + 2 ≤ Q + 2 by omega)
    obtain ⟨f1, -, -, -, -, f6, -⟩ := pow_facts Q
    nlinarith
  obtain ⟨r1, r2, r3⟩ := row_arith (k := row.length) hr hB hmg c1 c2 c3 m1 m2 m3
  exact ⟨e1.trans_le r1, e2.trans_le r2, e3.trans_le r3⟩


/-! ## All rows -/

theorem hdr_rowsBits {n : ℕ} (rows : List (List (PauliCoord n))) (R : List Bool) :
    (hdrF L h).den (InputEncoding.rowsBits rows ++ R) =
      (rows.length, rows.flatMap InputEncoding.rowBits ++ R) := by
  rw [hdrF_den]
  simp only [InputEncoding.rowsBits, List.append_assoc, hdr_natHeader]

theorem rowF_read {n : ℕ} (row : List (PauliCoord n)) (r : List Bool) :
    (rowF L h p).den (InputEncoding.rowBits row ++ r) = (row.map Query.encCoord, r) := by
  rw [rowF_den]; exact rowR_rowBits row r

theorem rows_arith {Q k mg B c1 c2 c3 m1 m2 m3 : ℕ} (hk : k ≤ Q) (hB : B ≤ 4 * Q + 1)
    (hmg : mg ≤ 2 * (Q + 2) ^ 2)
    (hc1 : c1 ≤ 400 * (Q + 2) ^ 2) (hd1 : c2 ≤ 10 * Q + 20) (hm1 : c3 ≤ 100 * Q + 100)
    (hc2 : m1 ≤ (1000 * (Q + 2) ^ 3 + 60) * k + 60 * ((k + 1) * (k + 1)) + 100)
    (hd2 : m2 ≤ 2 * k + (12 * Q + 50) + 20)
    (hm2 : m3 ≤ 3 * (300 * (Q + 2) ^ 2) + 20 * ((k + 1) * (k + 1)) + 3 * (5 * mg + 1) + 6 * B + 100) :
    1 + c1 + m1 + 2 ≤ 2000 * (Q + 2) ^ 4 ∧ max (max 0 c2) m2 + 1 ≤ 16 * Q + 100 ∧
      max (max 0 c3) m3 ≤ 1000 * (Q + 2) ^ 2 := by
  obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := pow_facts Q
  have k1 : (k + 1) * (k + 1) ≤ (Q + 2) ^ 2 := by rw [← f6]; exact Nat.mul_le_mul (by omega) (by omega)
  have k2 : (1000 * (Q + 2) ^ 3 + 60) * k ≤ 1000 * (Q * (Q + 2) ^ 3) + 60 * Q := by
    have := Nat.mul_le_mul_left (1000 * (Q + 2) ^ 3 + 60) hk
    nlinarith
  refine ⟨by omega, by omega, ?_⟩
  exact max_le (max_le (by omega) (by omega)) (by omega)

/-- **All rows** at the machine input. -/
theorem rows_le {n Q : ℕ} (rows : List (List (PauliCoord n))) (R : List Bool)
    (hQ : (InputEncoding.rowsBits rows ++ R).length ≤ Q) (hn : n ≤ Q)
    (hrows : rows.length + rowIncidences rows ≤ Q) :
    (rowsF L h p).cost (InputEncoding.rowsBits rows ++ R) ≤ 2000 * (Q + 2) ^ 4 ∧
      (rowsF L h p).depth (InputEncoding.rowsBits rows ++ R) ≤ 16 * Q + 100 ∧
      (rowsF L h p).msize (InputEncoding.rowsBits rows ++ R) ≤ 1000 * (Q + 2) ^ 2 := by
  obtain ⟨e1, e2, e3⟩ := comp2_eqs p.rows (hdrF L h) (manyF L (rowF L h p) p.rStep p.rFold p.rMany)
    (InputEncoding.rowsBits rows ++ R)
  have hsuf : ∀ j, ((rows.drop j).flatMap InputEncoding.rowBits ++ R).length ≤ Q := by
    intro j
    have h1 := (suffix_flatMap InputEncoding.rowBits rows R j).length_le
    have h2 : (rows.flatMap InputEncoding.rowBits ++ R).length ≤
        (InputEncoding.rowsBits rows ++ R).length := by
      simp only [InputEncoding.rowsBits, List.append_assoc, List.length_append]; omega
    omega
  have hstep : ∀ j, j < rows.length →
      (rowF L h p).cost ((rows.drop j).flatMap InputEncoding.rowBits ++ R) ≤ 1000 * (Q + 2) ^ 3 ∧
      (rowF L h p).depth ((rows.drop j).flatMap InputEncoding.rowBits ++ R) ≤ 12 * Q + 50 ∧
      (rowF L h p).msize ((rows.drop j).flatMap InputEncoding.rowBits ++ R) ≤ 300 * (Q + 2) ^ 2 := by
    intro j hj
    have hs := hsuf j
    rw [List.drop_eq_getElem_cons hj, List.flatMap_cons, List.append_assoc] at hs ⊢
    have hl : rows[j].length ≤ Q :=
      (Bounds.length_le_rowIncidences (List.getElem_mem hj)).trans (by omega)
    exact row_le L h p rows[j] _ hs hn hl
  obtain ⟨m1, m2, m3⟩ := many_bounds L (rowF L h p) p.rStep p.rFold p.rMany
    InputEncoding.rowBits (fun row => row.map Query.encCoord) (rowF_read L h p) rows R _ _ _ hstep
  rw [← hdr_rowsBits L h rows R] at m1 m2 m3
  obtain ⟨c1, c2, c3⟩ := hdr_le L h _ hQ
  have hB : (Ty.enc (.list .bool) (rows.flatMap InputEncoding.rowBits ++ R)).size ≤ 4 * Q + 1 := by
    have h0 := hsuf 0
    rw [List.drop_zero] at h0
    have := sz_bools (rows.flatMap InputEncoding.rowBits ++ R)
    omega
  have hmg : mag (.list (.list TCoordW)) (rows.map (fun row => row.map Query.encCoord)) ≤
      2 * (Q + 2) ^ 2 := by
    have h1 : mag TRowsW (Query.encRows rows) ≤ rowIncidences rows * (n + 2) + 2 * rows.length + 1 :=
      mag_rows_le rows
    have h2 := Nat.mul_le_mul (show rowIncidences rows ≤ Q by omega) (show n + 2 ≤ Q + 2 by omega)
    obtain ⟨f1, -, -, -, -, f6, f7⟩ := pow_facts Q
    have h3 : Q * (Q + 2) ≤ (Q + 2) ^ 2 := by rw [← f6]; exact Nat.mul_le_mul_right _ (by omega)
    show mag TRowsW (Query.encRows rows) ≤ _
    omega
  obtain ⟨r1, r2, r3⟩ := rows_arith (k := rows.length) (by omega) hB hmg c1 c2 c3 m1 m2 m3
  exact ⟨e1.trans_le r1, e2.trans_le r2, e3.trans_le r3⟩

/-! ## The program headers -/

theorem hdrs_arith {Q n mg B m1 m2 m3 : ℕ} (hn : n ≤ Q) (hB : B ≤ 4 * Q + 1)
    (hmg : mg ≤ (Q + 2) ^ 2)
    (hc2 : m1 ≤ (400 * (Q + 2) ^ 2 + 60) * (n + 1) + 60 * ((n + 1 + 1) * (n + 1 + 1)) + 100)
    (hd2 : m2 ≤ 2 * (n + 1) + (10 * Q + 20) + 20)
    (hm2 : m3 ≤ 3 * (100 * Q + 100) + 20 * ((n + 1 + 1) * (n + 1 + 1)) + 3 * (5 * mg + 1) +
      6 * B + 100) :
    m1 ≤ 1000 * (Q + 2) ^ 3 ∧ m2 ≤ 12 * Q + 50 ∧ m3 ≤ 200 * (Q + 2) ^ 2 := by
  obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := pow_facts Q
  have k1 : (n + 1 + 1) * (n + 1 + 1) ≤ (Q + 2) ^ 2 := by
    rw [← f6]; exact Nat.mul_le_mul (by omega) (by omega)
  have k2 : (400 * (Q + 2) ^ 2 + 60) * (n + 1) ≤
      400 * (Q * (Q + 2) ^ 2) + 400 * (Q + 2) ^ 2 + 60 * Q + 60 := by
    have := Nat.mul_le_mul_left (400 * (Q + 2) ^ 2 + 60) (show n + 1 ≤ Q + 1 by omega)
    nlinarith
  exact ⟨by omega, by omega, by omega⟩

/-- The `n+1` headers of `programBits (iidProgram n)`. -/
abbrev iidHdrs (n : ℕ) : List ℕ := 0 :: List.ofFn (fun i : Fin n => i.val)

theorem hdrs_le {n Q : ℕ} (R : List Bool)
    (hQ : (InputEncoding.programBits (ZeroLengthDispatch.iidProgram n) ++ R).length ≤ Q)
    (hn : n ≤ Q) :
    (hdrsF L h p).cost (n + 1, InputEncoding.programBits (ZeroLengthDispatch.iidProgram n) ++ R) ≤
        1000 * (Q + 2) ^ 3 ∧
      (hdrsF L h p).depth (n + 1, InputEncoding.programBits (ZeroLengthDispatch.iidProgram n) ++ R) ≤
        12 * Q + 50 ∧
      (hdrsF L h p).msize (n + 1, InputEncoding.programBits (ZeroLengthDispatch.iidProgram n) ++ R) ≤
        200 * (Q + 2) ^ 2 := by
  have e : (n + 1, InputEncoding.programBits (ZeroLengthDispatch.iidProgram n) ++ R) =
      ((iidHdrs n).length, (iidHdrs n).flatMap QueryCodec.natHeader ++ R) := by
    rw [programBits_iid, iidHdrs, List.length_cons, List.length_ofFn]
  rw [programBits_iid] at hQ
  rw [e]
  have hQ' : ((iidHdrs n).flatMap QueryCodec.natHeader ++ R).length ≤ Q := hQ
  clear hQ
  have hsuf : ∀ j, (((iidHdrs n).drop j).flatMap QueryCodec.natHeader ++ R).length ≤ Q := fun j =>
    (suffix_flatMap QueryCodec.natHeader (iidHdrs n) R j).length_le.trans hQ'
  have hread : ∀ (x : ℕ) (r : List Bool),
      (hdrF L h).den (QueryCodec.natHeader x ++ r) = ((fun v : ℕ => v) x, r) := fun x r => by
    rw [hdrF_den, hdr_natHeader]
  obtain ⟨m1, m2, m3⟩ := many_bounds L (hdrF L h) p.hStep p.hFold p.hMany QueryCodec.natHeader
    (fun v : ℕ => v) hread (iidHdrs n) R _ _ _ (fun j _ => hdr_le L h _ (hsuf j))
  have hB : (Ty.enc (.list .bool) ((iidHdrs n).flatMap QueryCodec.natHeader ++ R)).size ≤
      4 * Q + 1 := by
    have := sz_bools ((iidHdrs n).flatMap QueryCodec.natHeader ++ R); omega
  have hmem : ∀ v ∈ (iidHdrs n).map (fun v : ℕ => v), mag .nat v ≤ n := by
    intro v hv
    rw [List.map_id'] at hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact Nat.zero_le _
    · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hv
      exact i.isLt.le
  have hmg : mag (.list .nat) ((iidHdrs n).map (fun v : ℕ => v)) ≤ (Q + 2) ^ 2 := by
    have h1 := BoundsQH.mag_list_le .nat ((iidHdrs n).map (fun v : ℕ => v)) n hmem
    have hl : ((iidHdrs n).map (fun v : ℕ => v)).length = n + 1 := by
      rw [List.length_map, iidHdrs, List.length_cons, List.length_ofFn]
    rw [hl] at h1
    obtain ⟨-, -, -, -, -, f6, -⟩ := pow_facts Q
    have h2 : (n + 2) * (n + 2) ≤ (Q + 2) * (Q + 2) := Nat.mul_le_mul (by omega) (by omega)
    have h3 : (n + 1) * (n + 1) + 1 ≤ (n + 2) * (n + 2) := by nlinarith
    omega
  have hl : (iidHdrs n).length = n + 1 := by rw [iidHdrs, List.length_cons, List.length_ofFn]
  rw [hl] at m1 m2 m3 ⊢
  exact hdrs_arith hn hB hmg m1 m2 m3


/-! ## Precision headers -/

theorem hdr_suf_le {Q : ℕ} (bs : List Bool) (hQ : bs.length ≤ Q) : (hdr bs).2.length ≤ Q :=
  (hdr_suffix bs).length_le.trans hQ

/-- **`precF`** on any input of length `≤ Q`. -/
theorem prec_le {Q : ℕ} (bs : List Bool) (hQ : bs.length ≤ Q) :
    (precF L h p).cost bs ≤ 2000 * (Q + 2) ^ 2 ∧ (precF L h p).depth bs ≤ 10 * Q + 30 ∧
      (precF L h p).msize bs ≤ 200 * Q + 200 := by
  have q1 := hdr_suf_le bs hQ
  have q2 := hdr_suf_le _ q1
  have q3 := hdr_suf_le _ q2
  have q4 := hdr_suf_le _ q3
  obtain ⟨a1, b1, c1⟩ := hdr_le L h bs hQ
  obtain ⟨a2, b2, c2⟩ := hdr_le L h _ q1
  obtain ⟨a3, b3, c3⟩ := hdr_le L h _ q2
  obtain ⟨a4, b4, c4⟩ := hdr_le L h _ q3
  have v1 := hdr_val_sz bs
  have v2 := hdr_val_sz (hdr bs).2
  have v3 := hdr_val_sz (hdr (hdr bs).2).2
  have v4 := hdr_val_sz (hdr (hdr (hdr bs).2).2).2
  have z4 := sz_bools (hdr (hdr (hdr (hdr bs).2).2).2).2
  obtain ⟨-, -, -, -, -, -, f7⟩ := pow_facts Q
  refine ⟨?_, ?_, ?_⟩
  · simp only [precF, bodySig_cost, precBody, Tm.cost, Tm.den, Env.get, hdrF_den]
    omega
  · simp only [precF, bodySig_depth, precBody, Tm.depth, Tm.den, Env.get, hdrF_den]
    omega
  · simp only [precF, bodySig_msize, precBody, Tm.msize, Tm.den, Env.get, hdrF_den, Ty.sz_prod]
    simp only [max_le_iff]
    repeat' apply And.intro
    all_goals omega


/-! ## The whole parser -/

theorem parse_den_facts {n : ℕ} (rows : List (List (PauliCoord n))) (a b c d : ℕ) (coins : List Bool) :
    (hdrF L h).den (InputEncoding.problemBits rows (ZeroLengthDispatch.iidProgram n) a b c d ++ coins) =
      (n, QueryCodec.natHeader n ++ (InputEncoding.rowsBits rows ++
        (InputEncoding.programBits (ZeroLengthDispatch.iidProgram n) ++
          (InputEncoding.precisionBits a b c d ++ coins)))) ∧
    (hdrF L h).den (QueryCodec.natHeader n ++ (InputEncoding.rowsBits rows ++
        (InputEncoding.programBits (ZeroLengthDispatch.iidProgram n) ++
          (InputEncoding.precisionBits a b c d ++ coins)))) =
      (n, InputEncoding.rowsBits rows ++
        (InputEncoding.programBits (ZeroLengthDispatch.iidProgram n) ++
          (InputEncoding.precisionBits a b c d ++ coins))) ∧
    (rowsF L h p).den (InputEncoding.rowsBits rows ++
        (InputEncoding.programBits (ZeroLengthDispatch.iidProgram n) ++
          (InputEncoding.precisionBits a b c d ++ coins))) =
      (Query.encRows rows, InputEncoding.programBits (ZeroLengthDispatch.iidProgram n) ++
          (InputEncoding.precisionBits a b c d ++ coins)) ∧
    (hdrsF L h p).den (n + 1, InputEncoding.programBits (ZeroLengthDispatch.iidProgram n) ++
          (InputEncoding.precisionBits a b c d ++ coins)) =
      (iidHdrs n, InputEncoding.precisionBits a b c d ++ coins) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hdrF_den]; simp only [InputEncoding.problemBits, List.append_assoc, hdr_natHeader]
  · rw [hdrF_den, hdr_natHeader]
  · rw [rowsF_den, rowsR_rowsBits]
  · rw [hdrsF_den, programBits_iid]
    have := many_flatMap hdr QueryCodec.natHeader id hdr_natHeader (iidHdrs n)
      (InputEncoding.precisionBits a b c d ++ coins)
    simp only [iidHdrs, List.length_cons, List.length_ofFn, List.map_id] at this
    exact this

theorem sz_iidHdrs_le (n Q : ℕ) (hn : n ≤ Q) :
    (Ty.enc (.list .nat) (iidHdrs n)).size ≤ 5 * (Q + 2) ^ 2 + 6 := by
  have h1 := BoundsQH.sz_le (.list .nat) (iidHdrs n)
  have h2 := BoundsQH.mag_list_le .nat (iidHdrs n) n (fun v hv => by
    rcases List.mem_cons.mp hv with rfl | hv
    · exact Nat.zero_le _
    · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hv
      exact i.isLt.le)
  have hl : (iidHdrs n).length = n + 1 := by rw [iidHdrs, List.length_cons, List.length_ofFn]
  rw [hl] at h2
  obtain ⟨-, -, -, -, -, f6, -⟩ := pow_facts Q
  have h3 : (n + 1) * (n + 1) ≤ (Q + 2) * (Q + 2) := Nat.mul_le_mul (by omega) (by omega)
  omega

/-- **The parser at the machine input.** -/
theorem parse_le {n Q : ℕ} (rows : List (List (PauliCoord n))) (a b c d : ℕ) (coins : List Bool)
    (hQ : (InputEncoding.problemBits rows (ZeroLengthDispatch.iidProgram n) a b c d ++ coins).length ≤ Q)
    (hn : n ≤ Q) (hrows : rows.length + rowIncidences rows ≤ Q) :
    (parseF L h p).cost (InputEncoding.problemBits rows (ZeroLengthDispatch.iidProgram n) a b c d ++ coins)
        ≤ 7000 * (Q + 2) ^ 4 ∧
      (parseF L h p).depth (InputEncoding.problemBits rows (ZeroLengthDispatch.iidProgram n) a b c d ++ coins)
        ≤ 20 * Q + 200 ∧
      (parseF L h p).msize (InputEncoding.problemBits rows (ZeroLengthDispatch.iidProgram n) a b c d ++ coins)
        ≤ 2000 * (Q + 2) ^ 2 := by
  obtain ⟨d1, d2, d3, d4⟩ := parse_den_facts L h p rows a b c d coins
  have e0 : InputEncoding.problemBits rows (ZeroLengthDispatch.iidProgram n) a b c d ++ coins =
      QueryCodec.natHeader n ++ (QueryCodec.natHeader n ++ (InputEncoding.rowsBits rows ++
        (InputEncoding.programBits (ZeroLengthDispatch.iidProgram n) ++
          (InputEncoding.precisionBits a b c d ++ coins)))) := by
    simp only [InputEncoding.problemBits, List.append_assoc]
  have l1 : (QueryCodec.natHeader n ++ (InputEncoding.rowsBits rows ++
        (InputEncoding.programBits (ZeroLengthDispatch.iidProgram n) ++
          (InputEncoding.precisionBits a b c d ++ coins)))).length ≤ Q := by
    rw [e0] at hQ; simp only [List.length_append] at hQ ⊢; omega
  have l2 : (InputEncoding.rowsBits rows ++
        (InputEncoding.programBits (ZeroLengthDispatch.iidProgram n) ++
          (InputEncoding.precisionBits a b c d ++ coins))).length ≤ Q := by
    simp only [List.length_append] at l1 ⊢; omega
  have l3 : (InputEncoding.programBits (ZeroLengthDispatch.iidProgram n) ++
          (InputEncoding.precisionBits a b c d ++ coins)).length ≤ Q := by
    simp only [List.length_append] at l2 ⊢; omega
  have l4 : (InputEncoding.precisionBits a b c d ++ coins).length ≤ Q := by
    simp only [List.length_append] at l3 ⊢; omega
  obtain ⟨a1, b1, c1⟩ := hdr_le L h _ hQ
  obtain ⟨a2, b2, c2⟩ := hdr_le L h _ l1
  obtain ⟨a3, b3, c3⟩ := rows_le L h p rows _ l2 hn hrows
  obtain ⟨a4, b4, c4⟩ := hdrs_le L h p _ l3 hn
  obtain ⟨a5, b5, c5⟩ := prec_le L h p _ l4
  obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := pow_facts Q
  have sn := (NatSize.size_le_self n).trans hn
  have zn := Bounds.sz_nat_le_self n
  have zn1 := Bounds.sz_nat_le_self (n + 1)
  have z1 := sz_bools (QueryCodec.natHeader n ++ (InputEncoding.rowsBits rows ++
        (InputEncoding.programBits (ZeroLengthDispatch.iidProgram n) ++
          (InputEncoding.precisionBits a b c d ++ coins))))
  have z2 := sz_bools (InputEncoding.rowsBits rows ++
        (InputEncoding.programBits (ZeroLengthDispatch.iidProgram n) ++
          (InputEncoding.precisionBits a b c d ++ coins)))
  have z3 := sz_bools (InputEncoding.programBits (ZeroLengthDispatch.iidProgram n) ++
          (InputEncoding.precisionBits a b c d ++ coins))
  have z4 := sz_bools (InputEncoding.precisionBits a b c d ++ coins)
  have zh := sz_iidHdrs_le n Q hn
  have zr : (Ty.enc TRowsW (Query.encRows rows)).size ≤ 10 * (Q + 2) ^ 2 + 1 := by
    have h1 := BoundsQH.sz_le TRowsW (Query.encRows rows)
    have h2 := mag_rows_le rows
    have h3 := Nat.mul_le_mul (show rowIncidences rows ≤ Q by omega) (show n + 2 ≤ Q + 2 by omega)
    have h4 : Q * (Q + 2) ≤ (Q + 2) ^ 2 := by rw [← f6]; exact Nat.mul_le_mul_right _ (by omega)
    omega
  have zp : (Ty.enc (.prod .nat (.prod .nat (.prod .nat (.prod .nat (.list .bool)))))
      ((precF L h p).den (InputEncoding.precisionBits a b c d ++ coins))).size ≤ 30 * Q + 30 := by
    rw [precF_den]
    have v1 := hdr_val_sz (InputEncoding.precisionBits a b c d ++ coins)
    have q1 := hdr_suf_le _ l4
    have v2 := hdr_val_sz (hdr (InputEncoding.precisionBits a b c d ++ coins)).2
    have q2 := hdr_suf_le _ q1
    have v3 := hdr_val_sz (hdr (hdr (InputEncoding.precisionBits a b c d ++ coins)).2).2
    have q3 := hdr_suf_le _ q2
    have v4 := hdr_val_sz (hdr (hdr (hdr (InputEncoding.precisionBits a b c d ++ coins)).2).2).2
    have q4 := hdr_suf_le _ q3
    have z := sz_bools (hdr (hdr (hdr (hdr (InputEncoding.precisionBits a b c d ++ coins)).2).2).2).2
    simp only [precR, Ty.sz_prod]
    omega
  have hsucc : 25 * n.size + 25 ≤ 25 * Q + 25 := by omega
  have zp' := zp
  simp only [Ty.sz_prod] at zp'
  refine ⟨?_, ?_, ?_⟩
  · simp only [parseF, bodySig_cost, parseBody, Tm.cost, Tm.den, Env.get, succF_cost, succF_den]
    rw [d1, d2, d3, d4]
    dsimp only
    omega
  · simp only [parseF, bodySig_depth, parseBody, Tm.depth, Tm.den, Env.get, succF_depth, succF_den]
    rw [d1, d2, d3, d4]
    dsimp only
    omega
  · simp only [parseF, bodySig_msize, parseBody, Tm.msize, Tm.den, Env.get, succF_msize, succF_den]
    rw [d1, d2, d3, d4]
    dsimp only
    simp only [Ty.sz_prod, max_le_iff]
    repeat' apply And.intro
    all_goals omega

end Parse

end QecReliability.Trans.BoundsRest
