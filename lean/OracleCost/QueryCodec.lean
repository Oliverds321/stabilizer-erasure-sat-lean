import OracleCost.ServiceAdapter
import Mathlib.Data.Nat.Size

/-! A concrete self-delimiting SAT serialization. Natural headers use a unary
bit-length followed by binary digits. Each clause has a two-bit arity, including
00 for the empty clause. Literal addresses are zero-based fixed-width binary.
The parser reconstructs all clauses and duplicate literals exactly. -/
namespace QecReliability.OracleCost.QueryCodec

abbrev Bits := List Bool
abbrev PlainFormula := List (List (ℕ × Bool))

def word : ℕ → ℕ → Bits
  | 0,_ => []
  | k+1,n => decide (n%2=1) :: word k (n/2)

def readWord : ℕ → Bits → Option (ℕ × Bits)
  | 0,bits => some (0,bits)
  | _+1,[] => none
  | k+1,b::bits => do
    let (n,rest) ← readWord k bits
    pure (b.toNat+2*n,rest)

@[simp] theorem word_length (k n : ℕ) : (word k n).length=k := by
  induction k generalizing n <;> simp_all [word]

theorem readWord_word (k n : ℕ) (rest : Bits) (hn : n<2^k) :
    readWord k (word k n++rest)=some (n,rest) := by
  induction k generalizing n with
  | zero =>
    have : n=0 := by simpa using hn
    subst n
    rfl
  | succ k ih =>
    have hdiv : n/2<2^k := by rw [pow_succ] at hn; omega
    simp only [word,List.cons_append,readWord,ih (n/2) hdiv]
    have hmod := Nat.mod_lt n (by omega : 0<2)
    by_cases hm : n%2=1 <;> simp [hm] <;> omega

def natHeader (n : ℕ) : Bits := List.replicate n.size true ++ false :: word n.size n

def readHeader (k : ℕ) : Bits → Option (ℕ × Bits)
  | [] => none
  | true::rest => readHeader (k+1) rest
  | false::rest => readWord k rest

theorem readHeader_prefix (j k n : ℕ) (rest : Bits) (hn : n<2^(j+k)) :
    readHeader j (List.replicate k true ++ false :: (word (j+k) n++rest))=some (n,rest) := by
  induction k generalizing j with
  | zero => simpa [readHeader] using readWord_word j n rest hn
  | succ k ih =>
    simp only [List.replicate_succ,List.cons_append,readHeader]
    convert ih (j+1) (by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hn) using 1
    simp [Nat.add_comm,Nat.add_left_comm]

theorem readHeader_natHeader (n : ℕ) (rest : Bits) :
    readHeader 0 (natHeader n++rest)=some (n,rest) := by
  simpa [natHeader,List.append_assoc] using readHeader_prefix 0 n.size n rest (by simpa using Nat.lt_size_self n)

@[simp] theorem natHeader_length (n : ℕ) : (natHeader n).length=2*n.size+1 := by
  simp [natHeader]; omega

def literal (k : ℕ) (lit : ℕ × Bool) : Bits := lit.2 :: word k lit.1

def readLiteral (k : ℕ) : Bits → Option ((ℕ × Bool) × Bits)
  | [] => none
  | b::bits => do
    let (n,rest) ← readWord k bits
    pure ((n,b),rest)

theorem readLiteral_literal (k : ℕ) (lit : ℕ × Bool) (rest : Bits) (hl : lit.1<2^k) :
    readLiteral k (literal k lit++rest)=some (lit,rest) := by
  simp [literal,readLiteral,readWord_word k lit.1 rest hl]

def literals (k : ℕ) (ls : List (ℕ × Bool)) : Bits := ls.flatMap (literal k)

def readLiterals (k : ℕ) : ℕ → Bits → Option (List (ℕ × Bool) × Bits)
  | 0,bits => some ([],bits)
  | m+1,bits => do
    let (lit,tail) ← readLiteral k bits
    let (ls,rest) ← readLiterals k m tail
    pure (lit::ls,rest)

theorem readLiterals_literals (k : ℕ) (ls : List (ℕ × Bool)) (rest : Bits)
    (hl : ∀ lit∈ls, lit.1<2^k) :
    readLiterals k ls.length (literals k ls++rest)=some (ls,rest) := by
  induction ls with
  | nil => rfl
  | cons lit ls ih =>
    have ht := ih (fun x hx => hl x (by simp [hx]))
    simp only [literals,List.flatMap_cons,List.append_assoc,List.length_cons,readLiterals,
      readLiteral_literal k lit _ (hl lit (by simp)),Option.bind_eq_bind,Option.bind_some]
    change (readLiterals k ls.length (literals k ls++rest)).bind _ = _
    rw [ht]
    rfl

@[simp] theorem literals_length (k : ℕ) (ls : List (ℕ × Bool)) :
    (literals k ls).length=ls.length*(k+1) := by
  induction ls <;> simp_all [literals,literal,Nat.add_mul]
  omega

def clause (k : ℕ) (c : List (ℕ × Bool)) : Bits := word 2 c.length ++ literals k c

def readClause (k : ℕ) (bits : Bits) : Option (List (ℕ × Bool) × Bits) := do
  let (m,rest) ← readWord 2 bits
  readLiterals k m rest

theorem readClause_clause (k : ℕ) (c : List (ℕ × Bool)) (rest : Bits)
    (hw : c.length≤3) (hl : ∀ lit∈c, lit.1<2^k) :
    readClause k (clause k c++rest)=some (c,rest) := by
  simp only [clause,List.append_assoc,readClause,
    readWord_word 2 c.length _ (by omega)]
  exact readLiterals_literals k c rest hl

def body (k : ℕ) (F : PlainFormula) : Bits := F.flatMap (clause k)

def readBody (k : ℕ) : ℕ → Bits → Option (PlainFormula × Bits)
  | 0,bits => some ([],bits)
  | m+1,bits => do
    let (c,tail) ← readClause k bits
    let (F,rest) ← readBody k m tail
    pure (c::F,rest)

theorem readBody_body (k : ℕ) (F : PlainFormula) (rest : Bits)
    (hw : ∀ c∈F, c.length≤3) (hl : ∀ c∈F, ∀ lit∈c, lit.1<2^k) :
    readBody k F.length (body k F++rest)=some (F,rest) := by
  induction F with
  | nil => rfl
  | cons c F ih =>
    have ht := ih (fun x hx => hw x (by simp [hx])) (fun x hx => hl x (by simp [hx]))
    simp only [body,List.flatMap_cons,List.append_assoc,List.length_cons,readBody,
      readClause_clause k c _ (hw c (by simp)) (hl c (by simp)),Option.bind_eq_bind,Option.bind_some]
    change (readBody k F.length (body k F++rest)).bind _ = _
    rw [ht]
    rfl

def plain {v : ℕ} (F : PrefixCNF.Formula v) : PlainFormula :=
  F.map (fun c => c.map (fun lit => (lit.1.val,lit.2)))

def encode (request : SATRequest) : Bits :=
  natHeader request.varCount ++ natHeader request.formula.length ++ body request.varCount.size (plain request.formula)

def decode (bits : Bits) : Option (ℕ × PlainFormula) := do
  let (v,tail) ← readHeader 0 bits
  let (m,tail) ← readHeader 0 tail
  let (F,rest) ← readBody v.size m tail
  if rest=[] then pure (v,F) else none

theorem decode_encode (request : SATRequest) :
    decode (encode request)=some (request.varCount,plain request.formula) := by
  have hw : ∀ c∈plain request.formula, c.length≤3 := by
    intro c hc
    unfold plain at hc
    obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hc
    simpa using request.width d hd
  have hl : ∀ c∈plain request.formula, ∀ lit∈c, lit.1<2^request.varCount.size := by
    intro c hc lit hl
    unfold plain at hc
    obtain ⟨d,_hd,rfl⟩ := List.mem_map.mp hc
    obtain ⟨lit,hl,rfl⟩ := List.mem_map.mp hl
    exact lit.1.isLt.trans (Nat.lt_size_self request.varCount)
  have hb := readBody_body request.varCount.size (plain request.formula) [] hw hl
  simp only [plain,List.length_map,List.append_nil] at hb
  simp only [encode,decode,List.append_assoc,readHeader_natHeader,Option.bind_eq_bind,Option.bind_some]
  change (do
    let (F,rest) ← readBody request.varCount.size request.formula.length (body request.varCount.size (plain request.formula))
    if rest=[] then pure (request.varCount,F) else none)=_
  simp only [plain,Option.bind_eq_bind,hb,Option.bind_some]
  rfl

theorem body_length_bound (k : ℕ) (F : PlainFormula) (hw : ∀ c∈F, c.length≤3) :
    (body k F).length≤F.length*(2+3*(k+1)) := by
  induction F with
  | nil => simp [body]
  | cons c F ih =>
    have hc := hw c (by simp)
    have ht := ih (fun x hx => hw x (by simp [hx]))
    simp only [body,List.flatMap_cons,List.length_append,clause,word_length,literals_length,
      List.length_cons] at *
    nlinarith

/-- Header bits are charged as well as each literal and each empty clause. -/
theorem encode_length (request : SATRequest) :
    (encode request).length≤2*request.varCount.size+2*request.formula.length.size+2+
      request.formula.length*(2+3*(request.varCount.size+1)) := by
  have hw : ∀ c∈plain request.formula, c.length≤3 := by
    intro c hc
    unfold plain at hc
    obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hc
    simpa using request.width d hd
  have h := body_length_bound request.varCount.size (plain request.formula) hw
  simp only [plain,List.length_map] at h
  simp only [encode,List.length_append,natHeader_length,plain]
  omega

end QecReliability.OracleCost.QueryCodec
