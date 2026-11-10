import RegMachine.Lang

/-!
# Structured programs

`Stmt P`: primitives, sequencing, `ite t a b` (run test primitive `t`, branch on its
answer) and `loop t pol body` (`while (answer of t) = pol do body`). `BigStep σ Inv st s N C t` is the
big-step semantics (`N` primitives executed, abstract cost `C`, every visited state
satisfies `Inv`).

`SProg P` = a statement followed by a final primitive whose answer is the output.
`SProg.toProg` flattens it into a CFG `Prog P n` (`Stmt.code` lays out nodes with
absolute successor indices) and `SProg.exec` proves: a big-step run of the body
followed by the final primitive is a halting `Exec` of the CFG with the same steps,
cost and answer. Combined with `basic_completed` / `oracle_completed`, structured
programs compile to `MultiTape.Machine`s.
-/

set_option autoImplicit false

namespace QecReliability.RegMachine

/-- Structured statements over primitives `P`. -/
inductive Stmt (P : Type) where
  | prim (p : P)
  | seq (a b : Stmt P)
  | ite (t : P) (a b : Stmt P)
  | loop (t : P) (pol : Bool) (body : Stmt P)

/-- A CFG node: primitive and absolute successor per answer. -/
abbrev Node (P : Type) := P × (Bool → Option ℕ)

namespace Stmt
variable {P S : Type}

/-- Number of CFG nodes. -/
def size : Stmt P → ℕ
  | prim _ => 1
  | seq a b => a.size + b.size
  | ite _ a b => 1 + a.size + b.size
  | loop _ _ body => 1 + body.size

theorem size_pos : ∀ st : Stmt P, 0 < st.size
  | prim _ => by simp only [size]; omega
  | seq a _ => by have := size_pos a; simp only [size]; omega
  | ite _ _ _ => by simp only [size]; omega
  | loop _ _ _ => by simp only [size]; omega

/-- Layout of a statement at node `base`, continuing at node `exit`. -/
def code : Stmt P → ℕ → ℕ → List (Node P)
  | prim p, _, exit => [(p, fun _ => some exit)]
  | seq a b, base, exit => a.code base (base + a.size) ++ b.code (base + a.size) exit
  | ite t a b, base, exit =>
      (t, fun c => if c then some (base + 1) else some (base + 1 + a.size)) ::
        (a.code (base + 1) exit ++ b.code (base + 1 + a.size) exit)
  | loop t pol body, base, exit =>
      (t, fun c => if c = pol then some (base + 1) else some exit) :: body.code (base + 1) base

theorem length_code : ∀ (st : Stmt P) (base exit : ℕ), (st.code base exit).length = st.size
  | prim _, _, _ => rfl
  | seq a b, base, exit => by simp [code, size, length_code a, length_code b]
  | ite _ a b, base, exit => by simp [code, size, length_code a, length_code b]; omega
  | loop _ _ body, base, exit => by simp [code, size, length_code body]; omega

/-- Big-step semantics with step count, abstract cost and invariant. -/
inductive BigStep (σ : PrimSem P S) (Inv : S → Prop) : Stmt P → S → ℕ → ℕ → S → Prop
  | prim {p : P} {s s' : S} {b : Bool} : Inv s → σ.pre p s → σ.eval p s = (s', b) → Inv s' →
      BigStep σ Inv (prim p) s 1 (σ.cost p s) s'
  | seq {a b : Stmt P} {s s1 s2 : S} {n1 n2 c1 c2 : ℕ} :
      BigStep σ Inv a s n1 c1 s1 → BigStep σ Inv b s1 n2 c2 s2 →
      BigStep σ Inv (seq a b) s (n1 + n2) (c1 + c2) s2
  | iteT {t : P} {a b : Stmt P} {s s' s'' : S} {n c : ℕ} : Inv s → σ.pre t s →
      σ.eval t s = (s', true) → BigStep σ Inv a s' n c s'' →
      BigStep σ Inv (ite t a b) s (n + 1) (σ.cost t s + c) s''
  | iteF {t : P} {a b : Stmt P} {s s' s'' : S} {n c : ℕ} : Inv s → σ.pre t s →
      σ.eval t s = (s', false) → BigStep σ Inv b s' n c s'' →
      BigStep σ Inv (ite t a b) s (n + 1) (σ.cost t s + c) s''
  | loopF {t : P} {pol b : Bool} {body : Stmt P} {s s' : S} : Inv s → σ.pre t s →
      σ.eval t s = (s', b) → b ≠ pol → Inv s' →
      BigStep σ Inv (loop t pol body) s 1 (σ.cost t s) s'
  | loopT {t : P} {pol : Bool} {body : Stmt P} {s s' s1 s2 : S} {n1 n2 c1 c2 : ℕ} : Inv s →
      σ.pre t s → σ.eval t s = (s', pol) → BigStep σ Inv body s' n1 c1 s1 →
      BigStep σ Inv (loop t pol body) s1 n2 c2 s2 →
      BigStep σ Inv (loop t pol body) s (n1 + n2 + 1) (σ.cost t s + c1 + c2) s2

theorem BigStep.inv_end {σ : PrimSem P S} {Inv : S → Prop} {st : Stmt P} {s t : S} {N C : ℕ}
    (h : BigStep σ Inv st s N C t) : Inv t := by
  induction h with
  | prim _ _ _ ht => exact ht
  | seq _ _ _ ih => exact ih
  | iteT _ _ _ _ ih => exact ih
  | iteF _ _ _ _ ih => exact ih
  | loopF _ _ _ _ ht => exact ht
  | loopT _ _ _ _ _ _ ih => exact ih

end Stmt

/-! ## Partial CFG runs -/

section Reach
variable {P S : Type} {n : ℕ}

/-- Partial CFG execution from node `i` to node `j` (without halting). -/
inductive Reach (σ : PrimSem P S) (prog : Prog P n) (Inv : S → Prop) :
    Fin n → S → ℕ → ℕ → Fin n → S → Prop
  | refl (i : Fin n) (s : S) : Reach σ prog Inv i s 0 0 i s
  | step {i j l : Fin n} {s s' t : S} {b : Bool} {N C : ℕ} : Inv s → σ.pre (prog.prim i) s →
      σ.eval (prog.prim i) s = (s', b) → prog.next i b = some j → Reach σ prog Inv j s' N C l t →
      Reach σ prog Inv i s (N + 1) (σ.cost (prog.prim i) s + C) l t

variable {σ : PrimSem P S} {prog : Prog P n} {Inv : S → Prop}

theorem Reach.trans {i j l : Fin n} {s t u : S} {N C N' C' : ℕ}
    (h : Reach σ prog Inv i s N C j t) (g : Reach σ prog Inv j t N' C' l u) :
    Reach σ prog Inv i s (N + N') (C + C') l u := by
  induction h with
  | refl => simpa using g
  | @step i j l s s' t b N C hs hp he hn _ ih =>
    have := Reach.step hs hp he hn (ih g)
    have e1 : N + 1 + N' = N + N' + 1 := by omega
    rw [e1, Nat.add_assoc (σ.cost (prog.prim i) s)]
    exact this

theorem Reach.exec {i j : Fin n} {s t u : S} {N C N' C' : ℕ} {b : Bool}
    (h : Reach σ prog Inv i s N C j t) (g : Exec σ prog Inv j t N' C' u b) :
    Exec σ prog Inv i s (N + N') (C + C') u b := by
  induction h with
  | refl => simpa using g
  | @step i j l s s' t b N C hs hp he hn _ ih =>
    have := Exec.step hs hp he hn (ih g)
    have e1 : N + 1 + N' = N + N' + 1 := by omega
    rw [e1, Nat.add_assoc (σ.cost (prog.prim i) s)]
    exact this

end Reach

/-! ## Flattening -/

section Flat
variable {P S : Type}

/-- Partial conversion of an absolute node index. -/
def toFin (n j : ℕ) : Option (Fin n) := if h : j < n then some ⟨j, h⟩ else none

/-- The CFG of a node list (entry node `0`). -/
def ofNodes (nodes : List (Node P)) (h : 0 < nodes.length) : Prog P nodes.length :=
  ⟨⟨0, h⟩, fun i => (nodes.get i).1, fun i b => ((nodes.get i).2 b).bind (toFin nodes.length)⟩

/-- `sub` occurs in `nodes` at offset `base`. -/
def IsAt (nodes : List (Node P)) (base : ℕ) (sub : List (Node P)) : Prop :=
  ∃ pre post, nodes = pre ++ sub ++ post ∧ pre.length = base

theorem IsAt.get {nodes : List (Node P)} {base : ℕ} {sub : List (Node P)}
    (h : IsAt nodes base sub) {m : ℕ} (hm : m < sub.length) :
    ∃ hb : base + m < nodes.length, nodes.get ⟨base + m, hb⟩ = sub.get ⟨m, hm⟩ := by
  obtain ⟨pre, post, rfl, rfl⟩ := h
  refine ⟨by simp; omega, ?_⟩
  simp only [List.get_eq_getElem]
  have h1 : pre.length + m < (pre ++ sub).length := by simp; omega
  rw [List.getElem_append_left h1, List.getElem_append_right (by omega)]
  simp

theorem IsAt.left {nodes : List (Node P)} {base : ℕ} {a b : List (Node P)}
    (h : IsAt nodes base (a ++ b)) : IsAt nodes base a := by
  obtain ⟨pre, post, rfl, hl⟩ := h
  exact ⟨pre, b ++ post, by simp, hl⟩

theorem IsAt.right {nodes : List (Node P)} {base : ℕ} {a b : List (Node P)}
    (h : IsAt nodes base (a ++ b)) : IsAt nodes (base + a.length) b := by
  obtain ⟨pre, post, rfl, hl⟩ := h
  exact ⟨pre ++ a, post, by simp, by simp [hl]⟩

theorem IsAt.tail {nodes : List (Node P)} {base : ℕ} {x : Node P} {a : List (Node P)}
    (h : IsAt nodes base (x :: a)) : IsAt nodes (base + 1) a := by
  obtain ⟨pre, post, rfl, hl⟩ := h
  exact ⟨pre ++ [x], post, by simp, by simp [hl]⟩

theorem ofNodes_prim {nodes : List (Node P)} (h0 : 0 < nodes.length) {i : ℕ}
    (hi : i < nodes.length) : (ofNodes nodes h0).prim ⟨i, hi⟩ = (nodes.get ⟨i, hi⟩).1 := rfl

theorem ofNodes_next {nodes : List (Node P)} (h0 : 0 < nodes.length) {i : ℕ}
    (hi : i < nodes.length) {b : Bool} {j : ℕ} (hj : j < nodes.length)
    (hn : (nodes.get ⟨i, hi⟩).2 b = some j) :
    (ofNodes nodes h0).next ⟨i, hi⟩ b = some ⟨j, hj⟩ := by
  show ((nodes.get ⟨i, hi⟩).2 b).bind (toFin nodes.length) = _
  rw [hn]
  simp [toFin, hj]

theorem IsAt.head {nodes : List (Node P)} {base : ℕ} {x : Node P} {a : List (Node P)}
    (h : IsAt nodes base (x :: a)) :
    ∃ hb : base < nodes.length, nodes.get ⟨base, hb⟩ = x := by
  obtain ⟨hb, hg⟩ := h.get (m := 0) (by simp)
  exact ⟨hb, by simpa using hg⟩

/-- **Flattening is correct.** A big-step run of `st`, laid out at `base` with exit
`exit`, is a partial CFG run from `base` to `exit` with the same steps and cost. -/
theorem Stmt.BigStep.reach {σ : PrimSem P S} {Inv : S → Prop} {nodes : List (Node P)}
    (h0 : 0 < nodes.length) {st : Stmt P} {s t : S} {N C : ℕ}
    (h : Stmt.BigStep σ Inv st s N C t) :
    ∀ {base exit : ℕ} (hb : base < nodes.length) (he : exit < nodes.length),
      IsAt nodes base (st.code base exit) →
      Reach σ (ofNodes nodes h0) Inv ⟨base, hb⟩ s N C ⟨exit, he⟩ t := by
  induction h with
  | @prim p s s' b hs hp hev ht =>
    intro base exit hb he hat
    obtain ⟨hb', hg⟩ := hat.head
    have hpr : (ofNodes nodes h0).prim ⟨base, hb⟩ = p := by rw [ofNodes_prim, hg]
    have hn : (ofNodes nodes h0).next ⟨base, hb⟩ b = some ⟨exit, he⟩ :=
      ofNodes_next h0 hb he (by rw [hg])
    have := Reach.step (σ := σ) (Inv := Inv) hs (hpr ▸ hp) (hpr ▸ hev) hn (Reach.refl _ s')
    simpa [hpr] using this
  | @seq a b s s1 s2 n1 n2 c1 c2 _ _ iha ihb =>
    intro base exit hb he hat
    have hatA := IsAt.left hat
    have hatB := IsAt.right hat
    rw [Stmt.length_code] at hatB
    have hmid : base + a.size < nodes.length := by
      obtain ⟨hh, _⟩ := hatB.get (m := 0) (by rw [Stmt.length_code]; exact Stmt.size_pos b)
      simpa using hh
    exact (iha hb hmid hatA).trans (ihb hmid he hatB)
  | @iteT tp a b s s' s'' n c hs hp hev _ iha =>
    intro base exit hb he hat
    obtain ⟨_, hg⟩ := hat.head
    have hrest := IsAt.tail hat
    have hatA := IsAt.left hrest
    have ha1 : base + 1 < nodes.length := by
      obtain ⟨hh, _⟩ := hatA.get (m := 0) (by rw [Stmt.length_code]; exact Stmt.size_pos a)
      simpa using hh
    have hpr : (ofNodes nodes h0).prim ⟨base, hb⟩ = tp := by rw [ofNodes_prim, hg]
    have hn : (ofNodes nodes h0).next ⟨base, hb⟩ true = some ⟨base + 1, ha1⟩ :=
      ofNodes_next h0 hb ha1 (by rw [hg]; simp)
    have := Reach.step (σ := σ) (Inv := Inv) hs (hpr ▸ hp) (hpr ▸ hev) hn (iha ha1 he hatA)
    rw [hpr] at this
    rwa [Nat.add_comm n 1, Nat.add_comm 1 n] at this ⊢
  | @iteF tp a b s s' s'' n c hs hp hev _ ihb =>
    intro base exit hb he hat
    obtain ⟨_, hg⟩ := hat.head
    have hrest := IsAt.tail hat
    have hatB := IsAt.right hrest
    rw [Stmt.length_code] at hatB
    have hb1 : base + 1 + a.size < nodes.length := by
      obtain ⟨hh, _⟩ := hatB.get (m := 0) (by rw [Stmt.length_code]; exact Stmt.size_pos b)
      simpa using hh
    have hpr : (ofNodes nodes h0).prim ⟨base, hb⟩ = tp := by rw [ofNodes_prim, hg]
    have hn : (ofNodes nodes h0).next ⟨base, hb⟩ false = some ⟨base + 1 + a.size, hb1⟩ :=
      ofNodes_next h0 hb hb1 (by rw [hg]; simp)
    have := Reach.step (σ := σ) (Inv := Inv) hs (hpr ▸ hp) (hpr ▸ hev) hn (ihb hb1 he hatB)
    rw [hpr] at this
    exact this
  | @loopF tp pol bb body s s' hs hp hev hne ht =>
    intro base exit hb he hat
    obtain ⟨_, hg⟩ := hat.head
    have hpr : (ofNodes nodes h0).prim ⟨base, hb⟩ = tp := by rw [ofNodes_prim, hg]
    have hn : (ofNodes nodes h0).next ⟨base, hb⟩ bb = some ⟨exit, he⟩ :=
      ofNodes_next h0 hb he (by rw [hg]; simp [hne])
    have := Reach.step (σ := σ) (Inv := Inv) hs (hpr ▸ hp) (hpr ▸ hev) hn (Reach.refl _ s')
    simpa [hpr] using this
  | @loopT tp pol body s s' s1 s2 n1 n2 c1 c2 hs hp hev _ _ ihb ihl =>
    intro base exit hb he hat
    obtain ⟨_, hg⟩ := hat.head
    have hatB := IsAt.tail hat
    have hb1 : base + 1 < nodes.length := by
      obtain ⟨hh, _⟩ := hatB.get (m := 0) (by rw [Stmt.length_code]; exact Stmt.size_pos body)
      simpa using hh
    have hpr : (ofNodes nodes h0).prim ⟨base, hb⟩ = tp := by rw [ofNodes_prim, hg]
    have hn : (ofNodes nodes h0).next ⟨base, hb⟩ pol = some ⟨base + 1, hb1⟩ :=
      ofNodes_next h0 hb hb1 (by rw [hg]; simp)
    have hbody := ihb hb1 hb hatB
    have hrest := ihl hb he hat
    have := Reach.step (σ := σ) (Inv := Inv) hs (hpr ▸ hp) (hpr ▸ hev) hn (hbody.trans hrest)
    rw [hpr] at this
    rw [show n1 + n2 + 1 = n1 + n2 + 1 from rfl, Nat.add_assoc] at *
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this

/-- A structured program: a body followed by a final primitive giving the output. -/
structure SProg (P : Type) where
  body : Stmt P
  final : P

/-- Node list of a structured program. -/
def SProg.nodes (sp : SProg P) : List (Node P) :=
  sp.body.code 0 sp.body.size ++ [(sp.final, fun _ => none)]

theorem SProg.nodes_length (sp : SProg P) : sp.nodes.length = sp.body.size + 1 := by
  simp [SProg.nodes, Stmt.length_code]

theorem SProg.nodes_pos (sp : SProg P) : 0 < sp.nodes.length := by
  rw [SProg.nodes_length]; omega

/-- The flattened CFG. -/
def SProg.toProg (sp : SProg P) : Prog P sp.nodes.length := ofNodes sp.nodes sp.nodes_pos

/-- **Structured programs are executed by their flattened CFG.** -/
theorem SProg.exec {σ : PrimSem P S} {Inv : S → Prop} (sp : SProg P) {s t u : S} {N C : ℕ}
    {b : Bool} (h : Stmt.BigStep σ Inv sp.body s N C t) (hinv : Inv t)
    (hp : σ.pre sp.final t) (he : σ.eval sp.final t = (u, b)) (hu : Inv u) :
    Exec σ sp.toProg Inv sp.toProg.entry s (N + 1) (C + σ.cost sp.final t) u b := by
  have hlen := sp.nodes_length
  have hfin : sp.body.size < sp.nodes.length := by omega
  have hat : IsAt sp.nodes 0 (sp.body.code 0 sp.body.size) :=
    ⟨[], [(sp.final, fun _ => none)], by simp [SProg.nodes], rfl⟩
  have hr := h.reach sp.nodes_pos sp.nodes_pos hfin hat
  have hlast : sp.nodes.get ⟨sp.body.size, hfin⟩ = (sp.final, fun _ => none) := by
    simp only [SProg.nodes, List.get_eq_getElem]
    rw [List.getElem_append_right (by simp [Stmt.length_code])]
    simp [Stmt.length_code]
  have hpr : sp.toProg.prim ⟨sp.body.size, hfin⟩ = sp.final := by
    show (sp.nodes.get _).1 = _; rw [hlast]
  have hn : sp.toProg.next ⟨sp.body.size, hfin⟩ b = none := by
    show ((sp.nodes.get _).2 b).bind _ = _; rw [hlast]; rfl
  have hx : Exec σ sp.toProg Inv ⟨sp.body.size, hfin⟩ t 1 (σ.cost sp.final t) u b := by
    have := Exec.halt (σ := σ) (prog := sp.toProg) (Inv := Inv) (i := ⟨sp.body.size, hfin⟩)
      hinv (hpr ▸ hp) (hpr ▸ he) hu hn
    rwa [hpr] at this
  exact hr.exec hx

end Flat

end QecReliability.RegMachine
