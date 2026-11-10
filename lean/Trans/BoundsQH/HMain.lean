import Trans.BoundsQH.Compile
import Trans.BoundsQH.PointE

/-!
# Trans.BoundsQH.HMain: the hash program `hashF` from bounds of its callees

`hash_on`: for fixed constants `base ≥ 1`, `den` (the hash program's literals), if the callees
are polynomially bounded — `params` at `(base, den, q)` (its bounds involve `16^(256 den²)`, a
constant once `den` is fixed), the encoder oracle `prog` polynomially in `2^ell` (its programs
have `≈ 2^ell · const` gates), all other callees `PolyB` — then `hashF` has one polynomial
bound `G K C` on all arguments `(base, den, q, r, bits)`. The oracle bound is used through
the environment-aware term bound (`Tm.boundE`): at the call `prog e1` the environment holds
`N1 = base · 2^e1 ≥ 2^e1` (resp. `L = base · 2^e2` for `prog e2`).

`hash_on` is exactly the hypothesis `hH` of `compileF_P` / `compile_poly`.
-/

set_option autoImplicit false

namespace QecReliability.Trans.BoundsQH
open QecReliability.FL QecReliability.FL.Lib QecReliability.Trans.Query.Bound
open QecReliability.Trans.Hash QecReliability.Trans.Query.Plain

theorem fnBAtE_of_P {a b : Ty} {F : FnSig a b} (h : PolyB F) :
    ∃ k c, ∀ K C, k ≤ K → c ≤ C → ∀ y M, FnBAtE (G K C) F y M := by
  obtain ⟨k, c, hF⟩ := h
  exact ⟨k, c, fun K C hk hc y M => fnBAtE_of hF hk hc y M⟩

theorem mag_tuple_N1 (p : Params) : p.N1 ≤ mag TParams p.tuple := by
  simp only [Params.tuple, mag_prod, mag_nat]; omega

theorem mag_tuple_L (p : Params) : p.L ≤ mag TParams p.tuple := by
  simp only [Params.tuple, mag_prod, mag_nat]; omega

theorem two_pow_le_N1 (base den q : ℕ) (hb : 1 ≤ base) :
    2 ^ (params base den q).e1 ≤ (params base den q).N1 := by
  show 2 ^ (params base den q).e1 ≤ base * 2 ^ (params base den q).e1
  exact Nat.le_mul_of_pos_left _ hb

theorem two_pow_le_L (base den q : ℕ) (hb : 1 ≤ base) :
    2 ^ (params base den q).e2 ≤ (params base den q).L := by
  show 2 ^ (params base den q).e2 ≤ base * 2 ^ (params base den q).e2
  exact Nat.le_mul_of_pos_left _ hb

/-- **The hash program from its callees' bounds** (fixed `base ≥ 1`, `den`). -/
theorem hash_on (C : HashCallees) (prog : ℕ → ProgP) (nb : ℕ → ℕ → ℕ → ℕ) (i : ℕ)
    (base den : ℕ) (hb : 1 ≤ base)
    {kp cp : ℕ} (hparams : ∀ q, FnBAt (G kp cp) C.params (base, den, q))
    (hparamsd : ∀ x, C.params.den x = (params x.1 x.2.1 x.2.2).tuple)
    {kq cq : ℕ} (hprog : ∀ ell, C.prog.cost ell ≤ G kq cq (2 ^ ell) ∧
      C.prog.depth ell ≤ G kq cq (2 ^ ell) ∧ C.prog.msize ell ≤ G kq cq (2 ^ ell) ∧
      mag TProg (C.prog.den ell) ≤ G kq cq (2 ^ ell))
    (hpad : PolyB C.pad) (hsel : PolyB C.sel) (henc : PolyB C.encOuts) (haff : PolyB C.aff)
    (hrows : PolyB C.rows) (htrans : PolyB C.trans) (hcomp : PolyB C.comp) (hdm : PolyB C.dm)
    (hpadd : ∀ x, C.pad.den x = padP x.1 x.2.1 x.2.2.1 x.2.2.2)
    (hprogd : ∀ x, C.prog.den x = prog x) (hseld : ∀ x, C.sel.den x = pselect x.1 x.2)
    (hencd : ∀ x, C.encOuts.den x =
      x.2.map (encIndex (nb x.1.1) 16 x.1.2.1 x.1.2.2.1 x.1.2.2.2))
    (haffd : ∀ x, C.aff.den x = affP x.1 x.2.1 x.2.2.1 x.2.2.2)
    (hrowsd : ∀ x, C.rows.den x = seedRows x.1 x.2.1 x.2.2)
    (htransd : ∀ x, C.trans.den x = transP x.1 x.2)
    (hcompd : ∀ x, C.comp.den x = pcompose x.1 x.2.1 x.2.2)
    (hdmd : ∀ x, C.dm.den x = (x.1 / x.2, x.1 % x.2)) :
    ∃ K C', ∀ q r bits, FnBAt (G K C') (hashF C prog nb i) (base, den, q, r, bits) := by
  obtain ⟨k1, c1, h1⟩ := fnBAtE_of_P hpad
  obtain ⟨k2, c2, h2⟩ := fnBAtE_of_P hsel
  obtain ⟨k3, c3, h3⟩ := fnBAtE_of_P henc
  obtain ⟨k4, c4, h4⟩ := fnBAtE_of_P haff
  obtain ⟨k5, c5, h5⟩ := fnBAtE_of_P hrows
  obtain ⟨k6, c6, h6⟩ := fnBAtE_of_P htrans
  obtain ⟨k7, c7, h7⟩ := fnBAtE_of_P hcomp
  obtain ⟨k8, c8, h8⟩ := fnBAtE_of_P hdm
  set K := k1 + k2 + k3 + k4 + k5 + k6 + k7 + k8 + kp + kq + 2 with hK
  set Cc := c1 + c2 + c3 + c4 + c5 + c6 + c7 + c8 + cp + cq + 300 with hC
  have e1 := h1 (K + 1) Cc (by omega) (by omega)
  have e2 := h2 (K + 1) Cc (by omega) (by omega)
  have e3 := h3 (K + 1) Cc (by omega) (by omega)
  have e4 := h4 (K + 1) Cc (by omega) (by omega)
  have e5 := h5 (K + 1) Cc (by omega) (by omega)
  have e6 := h6 (K + 1) Cc (by omega) (by omega)
  have e7 := h7 (K + 1) Cc (by omega) (by omega)
  have e8 := h8 (K + 1) Cc (by omega) (by omega)
  have es : ∀ y M, FnBAtE (G (K + 1) Cc) (succF C.succ) y M := fun y M =>
    fnBAtE_of (succF_B C.succ) (by omega) (by omega) y M
  have em : ∀ y M, FnBAtE (G (K + 1) Cc) (mulF C.mul) y M := fun y M =>
    fnBAtE_of (mulF_B C.mul) (by omega) (by omega) y M
  have er : ∀ y M, FnBAtE (G (K + 1) Cc) (rangeF C.range) y M := fun y M =>
    fnBAtE_of (rangeF_B C.range) (by omega) (by omega) y M
  have ep : ∀ q M, FnBAtE (G (K + 1) Cc) C.params (base, den, q) M := fun q M => by
    obtain ⟨a1, a2, a3, a4⟩ := hparams q
    have e := G_mono (k := kp) (c := cp) (k' := K + 1) (c' := Cc)
      (m := mag (.prod .nat (.prod .nat .nat)) (base, den, q))
      (m' := max (mag (.prod .nat (.prod .nat .nat)) (base, den, q)) M) (by omega) (by omega)
      (le_max_left _ _)
    exact ⟨a1.trans e, a2.trans e, a3.trans e, a4.trans e⟩
  have eq : ∀ ell M, 2 ^ ell ≤ M → FnBAtE (G (K + 1) Cc) C.prog ell M := fun ell M hM => by
    obtain ⟨a1, a2, a3, a4⟩ := hprog ell
    have e := G_mono (k := kq) (c := cq) (k' := K + 1) (c' := Cc) (m := 2 ^ ell)
      (m' := max (mag .nat ell) M) (by omega) (by omega) (hM.trans (le_max_right _ _))
    exact ⟨a1.trans e, a2.trans e, a3.trans e, a4.trans e⟩
  refine fnBOn_of_bodyE (K := K) (C := Cc) (hashF C prog nb i) (hashBody C) (fun _ => le_rfl)
    (fun _ => le_rfl) (fun _ => le_rfl) (fun x => ?_)
    (fun x => x.1 = base ∧ x.2.1 = den) (fun x hx => ?_) |>.elim
    (fun K' h => h.elim (fun C' h' => ⟨K', C', fun q r bits => h' _ ⟨rfl, rfl⟩⟩))
  · obtain ⟨base', den', q, r, bits⟩ := x
    rw [eq_comm]
    simp only [hashF, exactSig_den, hashBody, tm_simp, hparamsd, Params.tuple, hpadd, hprogd,
      hseld, hencd, haffd, hrowsd, htransd, hcompd, hdmd, succF_den, mulF_den, rangeF_den,
      hashPlain]
  · obtain ⟨base', den', q, r, bits⟩ := x
    obtain ⟨rfl, rfl⟩ := hx
    simp only [Tm.CallsBE, hashBody, e1, e2, e3, e4, e5, e6, e7, e8, es, em, er, true_and,
      and_true]
    refine ⟨ep q _, eq _ _ ?_, eq _ _ ?_⟩
    · simp only [Tm.den, Env.get, hparamsd, Params.tuple, envMag_cons, envMag, mag_prod, mag_nat]
      have := two_pow_le_N1 base' den' q hb
      omega
    · simp only [Tm.den, Env.get, hparamsd, Params.tuple, envMag_cons, envMag, mag_prod, mag_nat]
      have := two_pow_le_L base' den' q hb
      omega

end QecReliability.Trans.BoundsQH
