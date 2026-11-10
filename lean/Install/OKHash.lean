import Install.Table

/-!
# Install.OKHash: the library and the hash program are valid in the installed program

* `std_ok`: `Trans.Query.stdLib_valid` (proved for `queryProg`) lifted to `prog …`
  (`Install.Mono`), `query_valid` likewise;
* the shared library additions (`divMod`, `reverse`, `odd`, `min`, `subb`);
* `hL_ok` / `wL_ok`: the library records of `Trans.HashCallees` and `Trans.Wire`;
* the encoder index records `rotI baseI ampI pcI encI` (all bodies at their indices, `rfl`);
* `hash_ok`: validity of the hash program `hashFn E pg nb` at every argument, from
  `Trans.Hash.hash_valid`, given the two oracle meanings (`hpg`: the encoder family means `pg`;
  `hnb`: the neighbour map means `nb`) and `4 ≤ E.1`.
-/

set_option autoImplicit false

namespace QecReliability.Install
open QecReliability.FL QecReliability.FL.Lib
open QecReliability.Trans.Query.Plain (ProgP)

section
variable (base den density : ℕ) (E : ℕ × ℕ × ℕ) (pg : ℕ → ProgP) (nb : ℕ → ℕ → ℕ → ℕ)

local notation "PP" => prog base den density E pg nb

theorem ext_query : Extends Trans.Query.queryProg PP := extends_append _ _

/-- Lift a validity fact of `queryProg` to the installed program. -/
theorem lift {a b : Ty} {F : FnSig a b} {x : a.den} (h : F.ValidAt Trans.Query.queryProg x) :
    F.ValidAt PP x :=
  ValidAt.extend (ext_query base den density E pg nb) h

/-- The query library, valid in the installed program. -/
theorem std_ok : Trans.Query.LibOK PP Trans.Query.stdIx := by
  have h := Trans.Query.stdLib_valid
  have e := ext_query base den density E pg nb
  exact
    { succ := fun y => ValidAt.extend e (h.succ y)
      pred := fun y => ValidAt.extend e (h.pred y)
      add := fun y => ValidAt.extend e (h.add y)
      sub := fun y => ValidAt.extend e (h.sub y)
      le := fun y => ValidAt.extend e (h.le y)
      lt := fun y => ValidAt.extend e (h.lt y)
      eq := fun y => ValidAt.extend e (h.eq y)
      max := fun y => ValidAt.extend e (h.max y)
      mul := fun y => ValidAt.extend e (h.mul y)
      bitLen := fun y => ValidAt.extend e (h.bitLen y)
      div2 := fun y => ValidAt.extend e (h.div2 y)
      length := fun t y => ValidAt.extend e (h.length t y)
      append := fun t y => ValidAt.extend e (h.append t y)
      replicate := fun t y => ValidAt.extend e (h.replicate t y)
      getD := fun t y => ValidAt.extend e (h.getD t y)
      take := fun t y => ValidAt.extend e (h.take t y)
      drop := fun t y => ValidAt.extend e (h.drop t y)
      rangeFrom := fun y => ValidAt.extend e (h.rangeFrom y)
      range := fun y => ValidAt.extend e (h.range y) }

/-- **The SAT-query function is valid in the installed program.** -/
theorem query_valid : ∀ p, queryFn.ValidAt PP p := fun p =>
  lift base den density E pg nb (Trans.Query.queryFn_valid p)

/-! ## Shared library additions -/

theorem subb_ok : ∀ x, (subbF 4).ValidAt PP x :=
  subb_valid (std_ok base den density E pg nb).pred rfl

theorem dm_ok : ∀ x : ℕ × ℕ, 0 < x.2 → hL.dmF.ValidAt PP x :=
  Trans.Hash.divMod_valid (std_ok base den density E pg nb).le
    (std_ok base den density E pg nb).sub rfl

theorem revApp_ok (t : Ty) : ∀ x, (revAppF t iRevApp).ValidAt PP x := revApp_valid rfl

theorem rev_ok (t : Ty) : ∀ x, (reverseF t wL.rev).ValidAt PP x :=
  reverse_valid (revApp_ok base den density E pg nb t) rfl

theorem odd_ok : ∀ x, (oddF hL.odd).ValidAt PP x := odd_valid rfl

theorem min_ok : ∀ x, (minF iMin).ValidAt PP x := min_valid (subb_ok base den density E pg nb) rfl

/-! ## Library records -/

theorem hL_ok : hL.OK PP := by
  have S := std_ok base den density E pg nb
  exact
    { succ := S.succ, pred := S.pred, add := S.add, sub := S.sub, le := S.le, lt := S.lt,
      mul := S.mul, dm := dm_ok base den density E pg nb, range := S.range, len := S.length,
      app := S.append, rep := S.replicate, odd := odd_ok base den density E pg nb,
      div2 := S.div2, gd := S.getD .nat }

theorem wL_ok : wL.OK PP := by
  have S := std_ok base den density E pg nb
  exact
    { succ := S.succ, pred := S.pred, add := S.add, sub := S.sub, le := S.le, eq := S.eq,
      mul := S.mul, bitLen := S.bitLen, dm := dm_ok base den density E pg nb, take := S.take,
      drop := S.drop, range := S.range, rev := rev_ok base den density E pg nb, rep := S.replicate }

/-! ## Encoder index records -/

theorem rotI_ok : rotI.OK PP hL := ⟨rfl, rfl, rfl⟩
theorem baseI_ok : baseI.OK PP hL := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
theorem ampI_ok : ampI.OK PP hL :=
  ⟨rotI_ok base den density E pg nb, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
theorem pcI_ok : pcI.OK PP hL := ⟨rfl, rfl, rfl, rfl, rfl⟩
theorem encI_ok : encI.OK PP hL E :=
  ⟨baseI_ok base den density E pg nb, ampI_ok base den density E pg nb,
    pcI_ok base den density E pg nb, rfl, rfl, rfl, rfl, rfl⟩


/-! ## The hash program -/

section Hash
variable {base den density E pg nb}

theorem params_ok : ∀ x, paramsFn.ValidAt PP x := by
  have S := std_ok base den density E pg nb
  exact Trans.Hash.params_valid S.range S.mul (Trans.Hash.dyStep_valid S.le S.succ S.mul rfl)
    (fun _ => rfl) (Trans.Hash.csStep_valid S.le S.succ S.mul rfl) (fun _ => rfl)
    (Trans.Hash.powStep_valid S.mul rfl) (fun _ => rfl) rfl rfl rfl rfl

theorem tg_ok : ∀ x, (pcI.tgF hL).ValidAt PP x := by
  have S := std_ok base den density E pg nb
  have htw := Trans.Hash.tw_valid (P := PP) (i := pcI.tw) S.lt (S.getD .nat) S.add S.sub rfl
  exact Trans.Hash.mapEnv_validAll (Trans.Hash.gmap_valid htw (fun _ => rfl) rfl) rfl

theorem twl_ok : ∀ x, (pcI.twlF hL).ValidAt PP x := by
  have S := std_ok base den density E pg nb
  have htw := Trans.Hash.tw_valid (P := PP) (i := pcI.tw) S.lt (S.getD .nat) S.add S.sub rfl
  exact Trans.Hash.mapEnv_validAll htw rfl

theorem twl_den (x : (Ty.prod Trans.Hash.TTab (.list .nat)).den) :
    (pcI.twlF hL).den x = Trans.Hash.tabWires x.1 x.2 :=
  Trans.Hash.tabWiresF_den _ _ (fun _ => rfl) x.1 x.2

theorem pad_ok : ∀ x, padFn.ValidAt PP x := by
  have S := std_ok base den density E pg nb
  exact Trans.Hash.pad_valid (Trans.Hash.mapEnv_validAll (min_ok base den density E pg nb) rfl)
    (fun _ => rfl) S.range S.succ (S.length .nat) S.sub (S.replicate .nat) (S.append .nat)
    tg_ok twl_ok (fun _ => rfl) twl_den rfl

theorem gd0_ok : ∀ x, gd0F.ValidAt PP x :=
  Trans.Hash.getD0_valid ((std_ok base den density E pg nb).getD .nat) rfl

theorem sel_ok : ∀ x, selFn.ValidAt PP x :=
  Trans.Hash.pselect_valid gd0_ok rfl rfl

theorem abit_ok : ∀ x, abitFn.ValidAt PP x := by
  have S := std_ok base den density E pg nb
  exact Trans.Hash.abit_valid S.succ rfl (S.append _) S.add (S.length _) rfl rfl rfl

theorem aff_ok : ∀ x, affFn.ValidAt PP x := by
  have S := std_ok base den density E pg nb
  have hst : ∀ x, afSF.ValidAt PP x :=
    Trans.Hash.affStep_valid abit_ok (fun _ => rfl) S.mul S.range S.add (S.length _)
      (S.append _) tg_ok twl_ok (fun _ => rfl) twl_den rfl
  exact Trans.Hash.aff_valid S.succ rfl hst (fun _ => rfl) rfl rfl

theorem rows_ok : ∀ x, rowsFn.ValidAt PP x := by
  have S := std_ok base den density E pg nb
  exact Trans.Hash.seedRows_valid S.range
    (Trans.Hash.row_valid S.succ S.mul (S.drop _) (S.take _) (S.getD _) S.add rfl)
    (fun _ => rfl) rfl rfl

theorem set_ok : ∀ x, setFn.ValidAt PP x := by
  have S := std_ok base den density E pg nb
  exact Trans.Hash.set_valid S.succ rfl S.eq rfl rfl rfl

theorem aw_ok : ∀ x, awF.ValidAt PP x := by
  have S := std_ok base den density E pg nb
  exact Trans.Hash.addWire_valid (S.append _) gd0_ok (fun _ => rfl) set_ok (fun _ => rfl) S.add
    (S.length _) rfl

theorem trans_ok : ∀ x, transFn.ValidAt PP x := by
  have S := std_ok base den density E pg nb
  have hsc : ∀ x, scF.ValidAt PP x := Trans.Hash.scatStep_valid aw_ok (fun _ => rfl) rfl
  have hdl : ∀ x, dlF.ValidAt PP x := Trans.Hash.dropLast_valid (S.length _) S.pred (S.take _) rfl
  have hrs : ∀ x, rsF.ValidAt PP x :=
    Trans.Hash.revStep_valid aw_ok (fun _ => rfl) hdl (fun _ => rfl) gd0_ok (fun _ => rfl) S.pred
      (S.length _) rfl
  exact Trans.Hash.trans_valid S.length S.add (S.replicate _) (rev_ok base den density E pg nb _)
    S.succ rfl hsc (fun _ => rfl) hrs (fun _ => rfl) rfl rfl rfl

theorem comp_ok : ∀ x, (pcI.pcF hL).ValidAt PP x :=
  Trans.HashCallees.PcIx.OK.valid (hL_ok base den density E pg nb) (pcI_ok base den density E pg nb)

theorem encOuts_ok (hnb : ∀ x, nbrFn.den x = nb x.1 x.2.1 x.2.2) :
    ∀ x, 0 < x.1.2.1 ∧ 0 < x.1.2.2.1 ∧ 0 < x.1.2.2.2 → (encOutsFn nb).ValidAt PP x := by
  have S := std_ok base den density E pg nb
  have HL := hL_ok base den density E pg nb
  have hnbv : ∀ x, nbrFn.ValidAt PP x :=
    Trans.HashCallees.nbr_valid HL (rotI_ok base den density E pg nb).coord
      (rotI_ok base den density E pg nb).rot rfl
  intro x hx
  refine Trans.Hash.mapEnv_valid rfl x (fun y _ => ?_)
  exact Trans.Hash.encIdx_valid S.le S.sub rfl S.mul S.add S.range hnbv hnb rfl rfl rfl (x.1, y) hx

/-- **Validity of the hash program** at every argument. -/
theorem hash_ok (hE : 4 ≤ E.1) (hpg : ∀ ell, (Trans.HashCallees.progF hL encI E).den ell = pg ell)
    (hnb : ∀ x, nbrFn.den x = nb x.1 x.2.1 x.2.2) :
    ∀ x, (hashFn E pg nb).ValidAt PP x := by
  have S := std_ok base den density E pg nb
  have HL := hL_ok base den density E pg nb
  exact Trans.Hash.hash_valid (hC E nb) pg nb params_ok (fun _ => rfl) pad_ok (fun _ => rfl)
    (Trans.HashCallees.prog_valid HL (encI_ok base den density E pg nb) hE) hpg sel_ok
    (fun _ => rfl) (encOuts_ok hnb) (fun _ => rfl) S.range S.mul S.succ aff_ok (fun _ => rfl)
    rows_ok (fun _ => rfl) trans_ok (fun _ => rfl) comp_ok (fun _ => rfl)
    (fun a => HL.dm' a (by norm_num)) (fun _ => rfl) rfl

end Hash

end

end QecReliability.Install
