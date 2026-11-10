import QecReliability.ExplicitBitSampler
import Mathlib.Tactic.DeriveFintype

/-!

All theorem declarations have
proof bodies.

The operational model is a fixed finite-control, first-order stack machine.
A stack is a finite constructor list, never a function Fin n -> Bool. One
transition inspects/pops/pushes at most one cell of each of a fixed number of
stacks. Nat-valued iteration counts and costs below are ghost observations,
not unit-cost unbounded machine registers. No enumeration, rejection,
random-graph walk, set/deduplication, or arbitrary-function evaluator occurs
in either transition table. Actual multitape-TM lowering is not claimed.
-/

namespace QecReliability.CodeHash.FiniteRandomTape

/-- An explicit finite word, as constructors rather than an oracle function. -/
inductive InputWord : Nat → Type where
  | nil : InputWord 0
  | cons {n : Nat} (bit : Bool) (tail : InputWord n) : InputWord (n+1)

namespace InputWord

def cells : {n : Nat} → InputWord n → List Bool
  | 0, .nil => []
  | _+1, .cons b w => b :: cells w

@[simp] theorem cells_length {n : Nat} (w : InputWord n) : w.cells.length = n := by
  induction w with
  | nil => rfl
  | cons b w ih => simpa only [cells, List.length_cons, ih]

/-- Ghost denotation of a finite word; this function is not machine storage. -/
def denote : {n : Nat} → InputWord n → BitTape n
  | 0, .nil => Fin.elim0
  | _+1, .cons b w => Fin.cases b (denote w)

def ofTape : (n : Nat) → BitTape n → InputWord n
  | 0, _ => .nil
  | n+1, f => .cons (f 0) (ofTape n (fun i => f i.succ))

@[simp] theorem denote_ofTape (n : Nat) (f : BitTape n) :
    denote (ofTape n f) = f := by
  induction n with
  | zero => funext i; exact Fin.elim0 i
  | succ n ih =>
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · change denote (ofTape n (fun j => f j.succ)) j = f j.succ
        exact congrFun (ih (fun j => f j.succ)) j

@[simp] theorem ofTape_denote {n : Nat} (w : InputWord n) :
    ofTape n (denote w) = w := by
  induction w with
  | nil => rfl
  | cons b w ih => simpa [ofTape, denote] using congrArg (InputWord.cons b) ih

/-- Used only for semantic/law transport, not as the executable sampler. -/
def tapeEquiv (n : Nat) : InputWord n ≃ BitTape n where
  toFun := denote
  invFun := ofTape n
  left_inv := ofTape_denote
  right_inv := denote_ofTape n

instance (n : Nat) : Nonempty (InputWord n) := ⟨ofTape n (fun _ => false)⟩

end InputWord

/-! A fixed loader with two work stacks. The input stack is consumed linearly;
    scratch reverses it once, then store restores its original row-major order.
    The two phase-boundary transitions read no random bit. -/
inductive LoadPC where
  | load | transfer | halt
  deriving DecidableEq, Fintype

structure LoadCfg where
  pc : LoadPC
  input : List Bool
  scratch : List Bool
  store : List Bool
  deriving DecidableEq

def loadStep : LoadCfg → LoadCfg
  | ⟨.load, [], a, s⟩ => ⟨.transfer, [], a, s⟩
  | ⟨.load, b::bs, a, s⟩ => ⟨.load, bs, b::a, s⟩
  | ⟨.transfer, u, [], s⟩ => ⟨.halt, u, [], s⟩
  | ⟨.transfer, u, b::bs, s⟩ => ⟨.transfer, u, bs, b::s⟩
  | ⟨.halt, u, a, s⟩ => ⟨.halt, u, a, s⟩

def loadRun : Nat → LoadCfg → LoadCfg
  | 0, c => c
  | n+1, c => loadRun n (loadStep c)

def loadInit (u : List Bool) : LoadCfg := ⟨.load, u, [], []⟩

def drawStep : LoadCfg → Nat
  | ⟨.load, _::_, _, _⟩ => 1
  | _ => 0

def draws : Nat → LoadCfg → Nat
  | 0, _ => 0
  | n+1, c => drawStep c + draws n (loadStep c)

/-- Live payload cells, excluding fixed control and stack delimiters. -/
def loadCells (c : LoadCfg) : Nat :=
  c.input.length + c.scratch.length + c.store.length

theorem loadRun_add (a b : Nat) (c : LoadCfg) :
    loadRun (a+b) c = loadRun b (loadRun a c) := by
  induction a generalizing c with
  | zero => simp only [Nat.zero_add, loadRun]
  | succ a ih => simpa only [Nat.succ_add, loadRun] using ih (loadStep c)

theorem load_prefix (u a s : List Bool) :
    loadRun u.length ⟨.load, u, a, s⟩ =
      ⟨.load, [], u.reverse ++ a, s⟩ := by
  induction u generalizing a with
  | nil => rfl
  | cons b u ih =>
      simpa [loadRun, loadStep, List.reverse_cons, List.append_assoc] using ih (b::a)

theorem transfer_prefix (u a s : List Bool) :
    loadRun a.length ⟨.transfer, u, a, s⟩ =
      ⟨.transfer, u, [], a.reverse ++ s⟩ := by
  induction a generalizing s with
  | nil => rfl
  | cons b a ih =>
      simpa [loadRun, loadStep, List.reverse_cons, List.append_assoc] using ih (b::s)

theorem load_complete (u a s : List Bool) :
    loadRun (u.length+1) ⟨.load, u, a, s⟩ =
      ⟨.transfer, [], u.reverse ++ a, s⟩ := by
  rw [loadRun_add, load_prefix]
  rfl

theorem transfer_complete (u a s : List Bool) :
    loadRun (a.length+1) ⟨.transfer, u, a, s⟩ =
      ⟨.halt, u, [], a.reverse ++ s⟩ := by
  rw [loadRun_add, transfer_prefix]
  rfl

/-- Exact finite execution: 2N+2 stack transitions, original order preserved. -/
theorem load_exact (u : List Bool) :
    loadRun (2*u.length+2) (loadInit u) = ⟨.halt, [], [], u⟩ := by
  have h : 2*u.length+2 = (u.length+1) + (u.reverse.length+1) := by
    simp only [List.length_reverse]
    omega
  rw [h, loadRun_add]
  simp only [loadInit, load_complete, List.append_nil]
  rw [transfer_complete]
  simp

/-- A ghost ranking function also proves that 2N+2 is the FIRST halt time. -/
def loadRank (c : LoadCfg) : Nat :=
  match c.pc with
  | .load => 2*c.input.length + c.scratch.length + 2
  | .transfer => c.scratch.length + 1
  | .halt => 0

theorem loadRank_zero_iff (c : LoadCfg) : loadRank c = 0 ↔ c.pc = .halt := by
  rcases c with ⟨pc, u, a, s⟩
  cases pc <;> simp [loadRank]

theorem loadStep_rank (c : LoadCfg) : loadRank (loadStep c) = loadRank c - 1 := by
  rcases c with ⟨pc, u, a, s⟩
  cases pc <;> cases u <;> cases a <;> simp [loadRank, loadStep] <;> omega

theorem loadRun_rank (n : Nat) (c : LoadCfg) :
    loadRank (loadRun n c) = loadRank c - n := by
  induction n generalizing c with
  | zero => simp [loadRun]
  | succ n ih =>
      rw [loadRun, ih, loadStep_rank]
      omega

theorem load_first_halt (u : List Bool) (n : Nat) :
    (loadRun n (loadInit u)).pc = .halt ↔ 2*u.length+2 ≤ n := by
  rw [← loadRank_zero_iff, loadRun_rank]
  simp [loadRank, loadInit, Nat.sub_eq_zero_iff_le]

theorem drawStep_balance (c : LoadCfg) :
    drawStep c + (loadStep c).input.length = c.input.length := by
  rcases c with ⟨pc, u, a, s⟩
  cases pc <;> cases u <;> cases a <;> simp [drawStep, loadStep] <;> omega

theorem draws_balance (n : Nat) (c : LoadCfg) :
    draws n c + (loadRun n c).input.length = c.input.length := by
  induction n generalizing c with
  | zero => simp [draws, loadRun]
  | succ n ih =>
      have h := ih (loadStep c)
      have hs := drawStep_balance c
      simp only [draws, loadRun]
      omega

theorem load_draws_exact (u : List Bool) :
    draws (2*u.length+2) (loadInit u) = u.length := by
  have h := draws_balance (2*u.length+2) (loadInit u)
  rw [load_exact] at h
  simpa [loadInit] using h

theorem loadStep_cells (c : LoadCfg) : loadCells (loadStep c) = loadCells c := by
  rcases c with ⟨pc, u, a, s⟩
  cases pc <;> cases u <;> cases a <;> simp [loadCells, loadStep] <;> omega

theorem loadRun_cells (n : Nat) (c : LoadCfg) :
    loadCells (loadRun n c) = loadCells c := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih => simp only [loadRun, ih, loadStep_cells]

/-- This is an explicit payload-space bound at EVERY time, including after halt. -/
theorem load_space (u : List Bool) (n : Nat) :
    loadCells (loadRun n (loadInit u)) = u.length := by
  rw [loadRun_cells]
  simp [loadInit, loadCells]

/-! Read-only coordinate decoder. The address is a finite unary word, not a
    unit-cost natural register. The driver temporarily moves the addressed
    prefix to trail and then restores every bit. The answer is a finite symbol.
    This gives actual reuse, rather than fresh independent seeds per query. -/
inductive ReadPC where
  | seek | restore | halt
  deriving DecidableEq, Fintype

structure ReadCfg where
  pc : ReadPC
  address : List Unit
  store : List Bool
  trail : List Bool
  answer : Option Bool
  deriving DecidableEq

def unary : Nat → List Unit
  | 0 => []
  | n+1 => () :: unary n

@[simp] theorem unary_length (n : Nat) : (unary n).length = n := by
  induction n <;> simp_all [unary]

def readStep : ReadCfg → ReadCfg
  | ⟨.seek, [], [], a, _⟩ => ⟨.restore, [], [], a, none⟩
  | ⟨.seek, [], b::bs, a, _⟩ => ⟨.restore, [], b::bs, a, some b⟩
  | ⟨.seek, _::qs, [], a, _⟩ => ⟨.restore, qs, [], a, none⟩
  | ⟨.seek, _::qs, b::bs, a, v⟩ => ⟨.seek, qs, bs, b::a, v⟩
  | ⟨.restore, q, s, [], v⟩ => ⟨.halt, q, s, [], v⟩
  | ⟨.restore, q, s, b::bs, v⟩ => ⟨.restore, q, b::s, bs, v⟩
  | ⟨.halt, q, s, a, v⟩ => ⟨.halt, q, s, a, v⟩

def readRun : Nat → ReadCfg → ReadCfg
  | 0, c => c
  | n+1, c => readRun n (readStep c)

def readInit (s : List Bool) (q : List Unit) : ReadCfg := ⟨.seek, q, s, [], none⟩

def readCells (c : ReadCfg) : Nat :=
  c.address.length + c.store.length + c.trail.length

theorem readRun_add (a b : Nat) (c : ReadCfg) :
    readRun (a+b) c = readRun b (readRun a c) := by
  induction a generalizing c with
  | zero => simp only [Nat.zero_add, readRun]
  | succ a ih => simpa only [Nat.succ_add, readRun] using ih (readStep c)

theorem seek_prefix (p s a : List Bool) (v : Option Bool) :
    readRun p.length ⟨.seek, unary p.length, p++s, a, v⟩ =
      ⟨.seek, [], s, p.reverse++a, v⟩ := by
  induction p generalizing a with
  | nil => rfl
  | cons b p ih =>
      simpa [readRun, readStep, unary, List.reverse_cons, List.append_assoc] using
        ih (b::a)

theorem restore_prefix (q : List Unit) (s a : List Bool) (v : Option Bool) :
    readRun a.length ⟨.restore, q, s, a, v⟩ =
      ⟨.restore, q, a.reverse++s, [], v⟩ := by
  induction a generalizing s with
  | nil => rfl
  | cons b a ih =>
      simpa [readRun, readStep, List.reverse_cons, List.append_assoc] using ih (b::s)

theorem read_exact (p s : List Bool) (b : Bool) :
    readRun (2*p.length+2) (readInit (p++b::s) (unary p.length)) =
      ⟨.halt, [], p++b::s, [], some b⟩ := by
  have h : 2*p.length+2 = p.length + 1 + p.reverse.length + 1 := by
    simp only [List.length_reverse]
    omega
  rw [h, readRun_add, readRun_add, readRun_add]
  simp only [readInit, seek_prefix, List.append_nil]
  change readRun 1 (readRun p.reverse.length
    ⟨.restore, [], b::s, p.reverse, some b⟩) = _
  rw [restore_prefix]
  simp [readRun, readStep]

theorem readStep_cells_le (c : ReadCfg) : readCells (readStep c) ≤ readCells c := by
  rcases c with ⟨pc, q, s, a, v⟩
  cases pc <;> cases q <;> cases s <;> cases a <;> simp [readCells, readStep] <;> omega

theorem read_space (n : Nat) (c : ReadCfg) : readCells (readRun n c) ≤ readCells c := by
  induction n generalizing c with
  | zero => exact le_rfl
  | succ n ih =>
      exact (ih (readStep c)).trans (readStep_cells_le c)

/-- An index relation whose proof objects, unlike addresses, are erased. -/
inductive At : List Bool → Nat → Bool → Prop where
  | here (b : Bool) (s : List Bool) : At (b::s) 0 b
  | there (a : Bool) {s : List Bool} {n : Nat} {b : Bool} :
      At s n b → At (a::s) (n+1) b

theorem At.prefix {s : List Bool} {n : Nat} {b : Bool} (h : At s n b) :
    ∃ p q, s = p++b::q ∧ n = p.length := by
  induction h with
  | here b s => exact ⟨[], s, rfl, rfl⟩
  | there a h ih =>
      rcases ih with ⟨p, q, rfl, rfl⟩
      exact ⟨a::p, q, rfl, rfl⟩

theorem InputWord.at_denote {n : Nat} (w : InputWord n) (i : Fin n) :
    At w.cells i.val (w.denote i) := by
  induction w with
  | nil => exact Fin.elim0 i
  | cons b w ih =>
      refine Fin.cases ?_ (fun j => ?_) i
      · exact At.here b w.cells
      · exact At.there b (ih j)

/-- A completed loader's canonical, finite stored representation. -/
def sample {n : Nat} (w : InputWord n) : LoadCfg :=
  loadRun (2*n+2) (loadInit w.cells)

theorem sample_exact {n : Nat} (w : InputWord n) :
    sample w = ⟨.halt, [], [], w.cells⟩ := by
  simpa only [sample, InputWord.cells_length] using load_exact w.cells

theorem sample_draws_exact {n : Nat} (w : InputWord n) :
    draws (2*n+2) (loadInit w.cells) = n := by
  simpa only [InputWord.cells_length] using load_draws_exact w.cells

theorem sample_space {n : Nat} (w : InputWord n) (time : Nat) :
    loadCells (loadRun time (loadInit w.cells)) = n := by
  simpa only [InputWord.cells_length] using load_space w.cells time

/-- Query is genuinely first order. The unary address must already exist.
    Constructing that address is NOT silently included in this execution bound. -/
def query (s : List Bool) (q : List Unit) : ReadCfg :=
  readRun (2*q.length+2) (readInit s q)

theorem query_at {s : List Bool} {n : Nat} {b : Bool} (h : At s n b) :
    query s (unary n) = ⟨.halt, [], s, [], some b⟩ := by
  rcases h.prefix with ⟨p, q, rfl, rfl⟩
  simpa only [query, unary_length] using read_exact p q b

theorem query_sample_exact {n : Nat} (w : InputWord n) (i : Fin n) :
    query (sample w).store (unary i.val) =
      ⟨.halt, [], w.cells, [], some (w.denote i)⟩ := by
  rw [sample_exact]
  exact query_at (w.at_denote i)

/-- At every decoder step there are at most N+k payload/counter cells.
    A valid address k<N therefore uses fewer than 2N such cells. -/
theorem query_space {n : Nat} (w : InputWord n) (i : Fin n) (time : Nat) :
    readCells (readRun time (readInit (sample w).store (unary i.val))) ≤ n+i.val := by
  have h := read_space time (readInit (sample w).store (unary i.val))
  simpa [sample_exact, readCells, readInit, Nat.add_comm] using h

theorem query_time_le {n : Nat} (i : Fin n) : 2*i.val+2 ≤ 2*n := by
  have h := i.isLt
  omega

/-- Both queries use exactly the same tape; the first leaves it unchanged. -/
theorem query_reuse {n : Nat} (w : InputWord n) (i j : Fin n) :
    query (query (sample w).store (unary i.val)).store (unary j.val) =
      ⟨.halt, [], w.cells, [], some (w.denote j)⟩ := by
  rw [query_sample_exact]
  exact query_at (w.at_denote j)

/-- This nested index is EXACTLY the row-major convention. -/
def blockIndex (L t m : Nat) (r : Fin (2*m+1)) (l : Fin L) (h : Fin (t+1)) :
    Fin (repeatBits L t m) :=
  finProdFinEquiv (r, finProdFinEquiv (l, h))

/-- Explicit address arithmetic as a semantic identity, not a unit-cost step. -/
theorem blockIndex_val (L t m : Nat) (r : Fin (2*m+1)) (l : Fin L)
    (h : Fin (t+1)) :
    (blockIndex L t m r l h).val = h.val + (t+1)*l.val + seedBits L t*r.val := by
  rfl

/-- Machine readout of the packed bit for one seed/local-row/coordinate. -/
theorem block_read_exact (L t m : Nat) (w : InputWord (repeatBits L t m))
    (r : Fin (2*m+1)) (l : Fin L) (h : Fin (t+1)) :
    (query (sample w).store (unary (blockIndex L t m r l h).val)).answer =
      some (w.denote (blockIndex L t m r l h)) := by
  rw [query_sample_exact]

/-- The decoded seed tuple is a GHOST interpretation of the stored finite word.
    It is NOT a machine that materializes a higher-order function. -/
def semanticSeeds (L t m : Nat) (w : InputWord (repeatBits L t m)) :
    Fin (2*m+1) → Seed L t := repeatedSeedTapeEquiv L t m w.denote

/-- Exact execution-to-decoder refinement, coordinate by coordinate. -/
theorem block_read_refines (L t m : Nat) (w : InputWord (repeatBits L t m))
    (r : Fin (2*m+1)) (l : Fin L) (h : Fin (t+1)) :
    (query (sample w).store (unary (blockIndex L t m r l h).val)).answer =
      some ((localSeedTapeEquiv t).symm (semanticSeeds L t m w r l) h) := by
  rw [block_read_exact]
  change some (w.denote (blockIndex L t m r l h)) =
    some ((localSeedTapeEquiv t).symm
      (localSeedTapeEquiv t (fun j => w.denote (blockIndex L t m r l j))) h)
  rw [Equiv.symm_apply_apply]

/-- The only symbol conversion is the fixed two-element Bool/field table.
    No arithmetic on a growing field or integer is hidden in this conversion. -/
def fieldAnswer (c : ReadCfg) : Option F := c.answer.map Binary.bitBool.symm

/-- First t local columns are affine coefficients. The cast has no runtime cost:
    it is only the proof-level address corresponding to the unary query input. -/
theorem coefficient_read_refines (L t m : Nat)
    (w : InputWord (repeatBits L t m)) (r : Fin (2*m+1)) (l : Fin L) (j : Fin t) :
    fieldAnswer (query (sample w).store
      (unary (blockIndex L t m r l j.castSucc).val)) =
      some ((semanticSeeds L t m w r l).1 j) := by
  rw [query_sample_exact]
  rfl

/-- The final local column, NOT the first, is the affine intercept. -/
theorem intercept_read_refines (L t m : Nat)
    (w : InputWord (repeatBits L t m)) (r : Fin (2*m+1)) (l : Fin L) :
    fieldAnswer (query (sample w).store
      (unary (blockIndex L t m r l (Fin.last t)).val)) =
      some ((semanticSeeds L t m w r l).2) := by
  rw [query_sample_exact]
  rfl

/-- Total ghost interpretation of a finite stored word. Invalid addresses
    return false; the loader/refinement theorems use only valid addresses. -/
def storedBit : List Bool → Nat → Bool
  | [], _ => false
  | b::_, 0 => b
  | _::bs, n+1 => storedBit bs n

theorem At.storedBit {s : List Bool} {n : Nat} {b : Bool} (h : At s n b) :
    storedBit s n = b := by
  induction h with
  | here b s => rfl
  | there a h ih => exact ih

/-- Only a denotation of actual storage, never a higher-order output object. -/
def outputSeeds (L t m : Nat) (s : List Bool) : Fin (2*m+1) → Seed L t :=
  repeatedSeedTapeEquiv L t m (fun i => storedBit s i.val)

theorem outputSeeds_sample (L t m : Nat) (w : InputWord (repeatBits L t m)) :
    outputSeeds L t m (sample w).store = semanticSeeds L t m w := by
  unfold outputSeeds semanticSeeds
  apply congrArg (repeatedSeedTapeEquiv L t m)
  funext i
  rw [sample_exact]
  exact (w.at_denote i).storedBit

end QecReliability.CodeHash.FiniteRandomTape

/-! Only the probability interpretation uses Fintype/enumeration. There is no
    such operation in the deterministic machine above. -/
noncomputable section
namespace QecReliability.CodeHash.FiniteRandomTape

noncomputable instance inputWordFintype (n : Nat) : Fintype (InputWord n) :=
  Fintype.ofEquiv (BitTape n) (InputWord.tapeEquiv n).symm

theorem inputWord_card (n : Nat) : Fintype.card (InputWord n) = 2^n := by
  rw [Fintype.card_congr (InputWord.tapeEquiv n)]
  simp [BitTape, Fintype.card_fun]

/-- Uniform finite words mean independent fair bits, exactly, not asymptotically. -/
theorem inputWord_independent_bits (n : Nat) (P : BitTape n → Prop) :
    (uniformLaw (InputWord n)).prob (fun w => P w.denote) =
      (FiniteProbability.product (fun _ : Fin n => uniformLaw Bool)).prob P := by
  calc
    _ = (uniformLaw (BitTape n)).prob P :=
      uniformLaw_equiv_prob (InputWord.tapeEquiv n) P
    _ = _ := (uniformLaw_product_prob P).symm

/-- Randomized-machine INTERFACE: first choose one length-N word uniformly;
    run the deterministic loader once; retain that one tape for all queries.
    The semantic outcome is the exact tuple from the equivalence. -/
theorem sampler_exact_law (L t m : Nat)
    (P : (Fin (2*m+1) → Seed L t) → Prop) :
    (uniformLaw (InputWord (repeatBits L t m))).prob
      (fun w => P (semanticSeeds L t m w)) =
      (repeatedLaw (uniformLaw (Seed L t)) m).prob P := by
  calc
    _ = (uniformLaw (BitTape (repeatBits L t m))).prob
        (fun u => P (repeatedSeedTapeEquiv L t m u)) :=
      uniformLaw_equiv_prob (InputWord.tapeEquiv (repeatBits L t m))
        (fun u => P (repeatedSeedTapeEquiv L t m u))
    _ = _ := repeatedSeedTape_law L t m P

/-- Exact law of the ACTUAL final stored output, not only of an input equiv.
    The randomized interface is an external uniform finite input-word law;
    the deterministic machine has no probabilistic primitive or hidden draws. -/
theorem executed_sampler_exact_law (L t m : Nat)
    (P : (Fin (2*m+1) → Seed L t) → Prop) :
    (uniformLaw (InputWord (repeatBits L t m))).prob
      (fun w => P (outputSeeds L t m (sample w).store)) =
      (repeatedLaw (uniformLaw (Seed L t)) m).prob P := by
  simp only [outputSeeds_sample]
  exact sampler_exact_law L t m P

/-- The confidence event is over the WHOLE fixed tuple. No pointwise/per-query
    independent resampling is introduced by this transport. -/
theorem sampler_confidence (L t m : Nat)
    (Good : (Fin (2*m+1) → Seed L t) → Prop) (δ : ℝ)
    (h : 1-δ ≤ (repeatedLaw (uniformLaw (Seed L t)) m).prob Good) :
    1-δ ≤ (uniformLaw (InputWord (repeatBits L t m))).prob
      (fun w => Good (semanticSeeds L t m w)) := by
  rw [sampler_exact_law]
  exact h

end QecReliability.CodeHash.FiniteRandomTape
