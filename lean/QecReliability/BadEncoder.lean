import QecReliability.SparseNormalizer
import QecReliability.QuantumDecisionBridge

/-! A complete concrete projected CNF for the unstratified Bad certificate.
Projection inputs are E,z; true existential inputs are x; gate outputs are separate. -/

namespace QecReliability.SharedCircuit
open PrefixCNF

def pairingBlock {n v : ℕ} (x z x' z' : Fin n → Fin v) : Block v :=
  Block.constrained (productParityCircuit (pairingPairs x z x' z'))
    (Fin.last (v + 2 * (pairingPairs x z x' z').length)) true

def badBlock {n v : ℕ} (rows : List (List (PauliCoord n)))
    (e zx zz xx xz : Fin n → Fin v) : Block v :=
  (normalizerBlock rows zx zz).and ((normalizerBlock rows xx xz).and
    ((Block.direct (supportClauses (supportPairs xx xz e))).and (pairingBlock xx xz zx zz)))

theorem badBlock_correct {n v : ℕ} (rows : List (List (PauliCoord n)))
    (e zx zz xx xz : Fin n → Fin v) (a : BitModels v) :
    (badBlock rows e zx zz xx xz).Accepts a ↔
      wiredPauli a zx zz ∈ normalizer (F := Binary.Bit) (Binary.symplectic n) (rowSpace rows) ∧
      wiredPauli a xx xz ∈ normalizer (F := Binary.Bit) (Binary.symplectic n) (rowSpace rows) ∧
      wiredPauli a xx xz ∈ Binary.supported (wiredErasures a e) ∧
      Binary.symplectic n (wiredPauli a xx xz) (wiredPauli a zx zz) = 1 := by
  simp only [badBlock, Block.and_accepts, normalizerBlock_correct, Block.direct_accepts,
    support_cnf_correct]
  have hp := pairing_cnf_exists a xx xz zx zz
  exact and_congr_right (fun _ => and_congr_right (fun _ => and_congr_right (fun _ => hp)))

theorem badBlock_deterministic {n v : ℕ} (rows : List (List (PauliCoord n)))
    (e zx zz xx xz : Fin n → Fin v) : (badBlock rows e zx zz xx xz).Deterministic :=
  Block.and_deterministic _ _ (normalizerBlock_deterministic _ _ _)
    (Block.and_deterministic _ _ (normalizerBlock_deterministic _ _ _)
      (Block.and_deterministic _ _ (Block.direct_deterministic _)
        (Block.constrained_deterministic _ _ _)))

theorem badBlock_width {n v : ℕ} (rows : List (List (PauliCoord n)))
    (e zx zz xx xz : Fin n → Fin v) : Width 3 (badBlock rows e zx zz xx xz).formula := by
  apply Block.and_width _ _ (normalizerBlock_width _ _ _)
  apply Block.and_width _ _ (normalizerBlock_width _ _ _)
  apply Block.and_width
  · apply width_rename
    intro c hc
    have h := supportClauses_width (supportPairs xx xz e) c hc
    omega
  · exact Circuit.constrained_width _ _ _

theorem badBlock_aux {n v : ℕ} (rows : List (List (PauliCoord n)))
    (e zx zz xx xz : Fin n → Fin v) :
    (badBlock rows e zx zz xx xz).aux ≤ 4 * rowIncidences rows + 4 * n + 1 := by
  have hz := normalizerBlock_aux rows zx zz
  have hx := normalizerBlock_aux rows xx xz
  have hp := pairingPairs_length xx xz zx zz
  change (normalizerBlock rows zx zz).aux + ((normalizerBlock rows xx xz).aux +
    (0 + (2 * (pairingPairs xx xz zx zz).length + 1))) ≤ _
  omega

theorem badBlock_length {n v : ℕ} (rows : List (List (PauliCoord n)))
    (e zx zz xx xz : Fin n → Fin v) :
    (badBlock rows e zx zz xx xz).formula.length ≤ 18 * rowIncidences rows + 18 * n + 5 := by
  have hz := normalizerBlock_length rows zx zz
  have hx := normalizerBlock_length rows xx xz
  have hp := pairing_cnf_clause_bound xx xz zx zz
  have hs := support_cnf_length xx xz e
  simp only [badBlock, Block.and_length]
  change (normalizerBlock rows zx zz).formula.length + ((normalizerBlock rows xx xz).formula.length +
    ((rename _ (supportClauses (supportPairs xx xz e))).length + _)) ≤ _
  simp only [rename, List.length_map]
  change _ + (_ + ((supportClauses (supportPairs xx xz e)).length +
    ((productParityCircuit (pairingPairs xx xz zx zz)).asserted _).length)) ≤ _
  omega

namespace BadEncoding

abbrev projectionSize (n : ℕ) := n + (n + n)
abbrev witnessSize (n : ℕ) := n + n
abbrev primarySize (n : ℕ) := projectionSize n + witnessSize n

def eWire {n : ℕ} (i : Fin n) : Fin (primarySize n) :=
  Fin.castAdd (witnessSize n) (Fin.castAdd (n + n) i)
def zxWire {n : ℕ} (i : Fin n) : Fin (primarySize n) :=
  Fin.castAdd (witnessSize n) (Fin.natAdd n (Fin.castAdd n i))
def zzWire {n : ℕ} (i : Fin n) : Fin (primarySize n) :=
  Fin.castAdd (witnessSize n) (Fin.natAdd n (Fin.natAdd n i))
def xxWire {n : ℕ} (i : Fin n) : Fin (primarySize n) :=
  Fin.natAdd (projectionSize n) (Fin.castAdd n i)
def xzWire {n : ℕ} (i : Fin n) : Fin (primarySize n) :=
  Fin.natAdd (projectionSize n) (Fin.natAdd n i)

def erasures {n : ℕ} (a : BitModels (projectionSize n)) : Finset (Fin n) :=
  wiredErasures a (Fin.castAdd (n + n))
def pauli {n : ℕ} (a : BitModels (projectionSize n)) : Binary.Pauli n :=
  wiredPauli a (fun i => Fin.natAdd n (Fin.castAdd n i)) (fun i => Fin.natAdd n (Fin.natAdd n i))
def witness {n : ℕ} (b : BitModels (witnessSize n)) : Binary.Pauli n :=
  wiredPauli b (Fin.castAdd n) (Fin.natAdd n)

theorem decode_primary {n : ℕ} (a : BitModels (projectionSize n)) (b : BitModels (witnessSize n)) :
    wiredErasures (Fin.append a b) eWire = erasures a ∧
    wiredPauli (Fin.append a b) zxWire zzWire = pauli a ∧
    wiredPauli (Fin.append a b) xxWire xzWire = witness b := by
  simp [eWire, zxWire, zzWire, xxWire, xzWire, erasures, pauli, witness, wiredErasures, wiredPauli]

theorem boolBit_bitBool (b : Binary.Bit) : boolBit (Binary.bitBool b) = b := by
  have hi : ∀ a : Bool, Binary.bitBool.symm a = boolBit a := by
    intro a
    cases a <;> rfl
  rw [← hi, Equiv.symm_apply_apply]

def encodeWitness {n : ℕ} (x : Binary.Pauli n) : BitModels (witnessSize n) :=
  Fin.append (fun i => Binary.bitBool (x.1 i)) (fun i => Binary.bitBool (x.2 i))

theorem witness_encode {n : ℕ} (x : Binary.Pauli n) : witness (encodeWitness x) = x := by
  apply Prod.ext <;> funext i
  · exact (congrArg boolBit (Fin.append_left _ _ i)).trans (boolBit_bitBool _)
  · exact (congrArg boolBit (Fin.append_right _ _ i)).trans (boolBit_bitBool _)

def block {n : ℕ} (rows : List (List (PauliCoord n))) : Block (primarySize n) :=
  badBlock rows eWire zxWire zzWire xxWire xzWire

def formula {n : ℕ} (rows : List (List (PauliCoord n))) :
    Formula (projectionSize n + (witnessSize n + (block rows).aux)) :=
  (block rows).projectedFormula

/-- Exact projected semantics. Isotropy is unnecessary for this algebraic encoding;
the interpretation as a stabilizer-code certificate uses the earlier isotropy hypotheses. -/
theorem projected_correct {n : ℕ} (rows : List (List (PauliCoord n)))
    (a : BitModels (projectionSize n)) :
    Projected (formula rows) a ↔
      pauli a ∈ normalizer (F := Binary.Bit) (Binary.symplectic n) (rowSpace rows) ∧
      Bad (F := Binary.Bit) (Binary.symplectic n) (rowSpace rows) (Binary.supported (erasures a)) (pauli a) := by
  rw [formula, Block.projectedFormula_correct]
  have hb : ∀ b : BitModels (witnessSize n), (block rows).Accepts (Fin.append a b) ↔
      pauli a ∈ normalizer (F := Binary.Bit) (Binary.symplectic n) (rowSpace rows) ∧
      witness b ∈ normalizer (F := Binary.Bit) (Binary.symplectic n) (rowSpace rows) ∧
      witness b ∈ Binary.supported (erasures a) ∧
      Binary.symplectic n (witness b) (pauli a) = 1 := by
    intro b
    rw [block, badBlock_correct, (decode_primary a b).1,
      (decode_primary a b).2.1, (decode_primary a b).2.2]
  simp_rw [hb]
  constructor
  · rintro ⟨b, hz, hx, he, hp⟩
    exact ⟨hz, witness b, ⟨hx, he⟩, hp⟩
  · rintro ⟨hz, x, ⟨hx, he⟩, hp⟩
    exact ⟨encodeWitness x, by simpa only [witness_encode] using And.intro hz ⟨hx, he, hp⟩⟩

theorem compiler_contract {n : ℕ} (rows : List (List (PauliCoord n))) :
    Width 3 (formula rows) ∧
    (formula rows).length ≤ 18 * rowIncidences rows + 18 * n + 5 ∧
    projectionSize n + (witnessSize n + (block rows).aux) ≤ 9 * n + 4 * rowIncidences rows + 1 ∧
    (block rows).Deterministic ∧
    ∀ a : BitModels (projectionSize n), Projected (formula rows) a ↔
      pauli a ∈ normalizer (F := Binary.Bit) (Binary.symplectic n) (rowSpace rows) ∧
      Bad (F := Binary.Bit) (Binary.symplectic n) (rowSpace rows) (Binary.supported (erasures a)) (pauli a) := by
  refine ⟨Block.projectedFormula_width _ (badBlock_width _ _ _ _ _ _), ?_, ?_,
    badBlock_deterministic _ _ _ _ _ _, projected_correct rows⟩
  · rw [formula, Block.projectedFormula_length]
    exact badBlock_length _ _ _ _ _ _
  · have h := badBlock_aux rows eWire zxWire zzWire xxWire xzWire
    change n + (n + n) + ((n + n) + _) ≤ _
    change (block rows).aux ≤ _ at h
    omega

def decision {n : ℕ} (rows : List (List (PauliCoord n)))
    (solver : ExactSAT (projectionSize n + (witnessSize n + (block rows).aux)) 3) :
    PrefixEnumeration.ExactDecision (fun a : BitModels (projectionSize n) =>
      pauli a ∈ normalizer (F := Binary.Bit) (Binary.symplectic n) (rowSpace rows) ∧
      Bad (F := Binary.Bit) (Binary.symplectic n) (rowSpace rows) (Binary.supported (erasures a)) (pauli a)) where
  answer pre := solver.solve (PrefixCNF.restrict (formula rows) pre)
  correct pre := by
    rw [solver.correct _ (PrefixCNF.restrict_width (compiler_contract rows).1 (by omega) pre),
      PrefixCNF.restrict_sat]
    simp only [PrefixEnumeration.PrefixSat, projected_correct]

end BadEncoding
end QecReliability.SharedCircuit
