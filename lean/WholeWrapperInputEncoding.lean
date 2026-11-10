import WholeWrapperWordPolynomial

/-! A concrete structural bit representation of
the actual quantum problem data. Paper L is n+r PLUS this representation's
length, exactly the latent theorem's extent convention; it is not a numerical
maximum chosen to satisfy later inequalities. No physical parser is asserted. -/
namespace QecReliability.OracleCost.WholeWrapperCandidate.InputEncoding
open Binary SharedCircuit SharedCircuit.LatentEncoding SharedCircuit.ConcreteQuantum
open QueryCodec

/-- One type bit plus a self-delimiting coordinate address. Multiplicity/order
are preserved, including repeated coordinates in a row. -/
def coordBits {n : ℕ} : PauliCoord n → List Bool
  | .inl i => false::natHeader i.val
  | .inr i => true::natHeader i.val

def rowBits {n : ℕ} (row : List (PauliCoord n)) : List Bool :=
  natHeader row.length++row.flatMap coordBits

/-- Every row receives its OWN length header, including every empty row.
Thus zero incidences never make input row traversal free. -/
def rowsBits {n : ℕ} (rows : List (List (PauliCoord n))) : List Bool :=
  natHeader rows.length++rows.flatMap rowBits

/-- Fixed two-bit gate tags followed by the actual earlier-wire addresses.
Constants carry their value bit. No expression-tree expansion or gate deletion. -/
def gateBits {v : ℕ} : Gate v → List Bool
  | .andGate x y => [false,false]++natHeader x.val++natHeader y.val
  | .xorGate x y => [false,true]++natHeader x.val++natHeader y.val
  | .notGate x => [true,false]++natHeader x.val
  | .constGate b => [true,true,b]

/-- The circuit's existing chronological spine, each actual gate once. -/
def circuitBits {r : ℕ} : {g : ℕ} → Circuit r g → List Bool
  | _,.nil => []
  | _,.snoc C gate => circuitBits C++gateBits gate

/-- Every output occurrence is represented, including repeated wire uses. -/
def outputBits {n r : ℕ} (C : Program r n) : List Bool :=
  (List.ofFn (fun i : Fin n => C.output i)).flatMap (fun i => natHeader i.val)

def programBits {n r : ℕ} (C : Program r n) : List Bool :=
  natHeader C.gates++circuitBits C.circuit++outputBits C

/-- Raw rational numerators and denominators, without reduction. Long
precision descriptions are charged even when their represented value is small. -/
def precisionBits (a b c d : ℕ) : List Bool :=
  natHeader a++natHeader b++natHeader c++natHeader d

/-- Dimensions are also encoded as ordinary binary headers. The separate
n+r extent below is the manuscript convention, not inferred from header size. -/
def problemBits {n r : ℕ} (rows : List (List (PauliCoord n))) (C : Program r n)
    (a b c d : ℕ) : List Bool :=
  natHeader n++natHeader r++rowsBits rows++programBits C++precisionBits a b c d

def paperLength {n r : ℕ} (rows : List (List (PauliCoord n))) (C : Program r n)
    (a b c d : ℕ) : ℕ := n+r+(problemBits rows C a b c d).length

theorem coordBits_nonempty {n : ℕ} (i : PauliCoord n) : 1≤(coordBits i).length := by
  cases i <;> simp [coordBits]

theorem flatMap_length_lower {α : Type*} (xs : List α) (f : α → List Bool)
    (h : ∀ x∈xs,1≤(f x).length) : xs.length≤(xs.flatMap f).length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have hx := h x (by simp)
      have ht := ih (fun y hy => h y (by simp [hy]))
      simp only [List.flatMap_cons,List.length_append,List.length_cons]
      omega

theorem rowBits_length_lower {n : ℕ} (row : List (PauliCoord n)) :
    row.length+1≤(rowBits row).length := by
  have h := flatMap_length_lower row coordBits (fun i _ => coordBits_nonempty i)
  simp only [rowBits,List.length_append,natHeader_length]
  omega

theorem rowsBody_length_lower {n : ℕ} (rows : List (List (PauliCoord n))) :
    rows.length+rowIncidences rows≤(rows.flatMap rowBits).length := by
  induction rows with
  | nil => simp [rowIncidences]
  | cons row rows ih =>
      have hr := rowBits_length_lower row
      simp only [List.flatMap_cons,List.length_append,List.length_cons,
        rowIncidences,List.map_cons,List.sum_cons] at *
      omega

theorem rowsBits_length_lower {n : ℕ} (rows : List (List (PauliCoord n))) :
    rows.length+rowIncidences rows≤(rowsBits rows).length := by
  have h := rowsBody_length_lower rows
  simp only [rowsBits,List.length_append]
  omega

theorem gateBits_length_lower {v : ℕ} (gate : Gate v) :
    1+gate.arity≤(gateBits gate).length := by
  cases gate <;> simp [gateBits,Gate.arity] <;> omega

theorem circuitBits_length_lower {r g : ℕ} (C : Circuit r g) :
    g+C.edges≤(circuitBits C).length := by
  induction C with
  | nil => simp [Circuit.edges,circuitBits]
  | snoc C gate ih =>
      have h := gateBits_length_lower gate
      simp only [circuitBits,List.length_append,Circuit.edges]
      omega

theorem outputBits_length_lower {n r : ℕ} (C : Program r n) :
    n≤(outputBits C).length := by
  have h := flatMap_length_lower (List.ofFn (fun i : Fin n => C.output i))
    (fun i => natHeader i.val) (by intro i _; simp)
  simpa only [List.length_ofFn,outputBits] using h

theorem programBits_length_lower {n r : ℕ} (C : Program r n) :
    C.gates+C.circuit.edges+n≤(programBits C).length := by
  have hg := circuitBits_length_lower C.circuit
  have ho := outputBits_length_lower C
  simp only [programBits,List.length_append]
  omega

/-- All four raw rational widths, not just the denominators, enter L. -/
theorem precisionBits_length (a b c d : ℕ) :
    (precisionBits a b c d).length=2*(a.size+b.size+c.size+d.size)+4 := by
  simp only [precisionBits,List.length_append,natHeader_length]
  omega

/-- Explicit extent/payload accounting. In particular empty row count,
incidences, all circuit gate/edge/output occurrences, and precision widths are
bounded by the represented paper input, with no resource hypothesis. -/
theorem paperLength_components {n r : ℕ} (rows : List (List (PauliCoord n)))
    (C : Program r n) (a b c d : ℕ) :
    let L := paperLength rows C a b c d
    n≤L ∧ r≤L ∧ rows.length+rowIncidences rows≤L ∧
      C.gates+C.circuit.edges+n≤L ∧ a.size+b.size+c.size+d.size≤L := by
  have hr := rowsBits_length_lower rows
  have hg := programBits_length_lower C
  have hp := precisionBits_length a b c d
  simp only [paperLength,problemBits,List.length_append]
  omega

/-- Stronger key bound uses the separately charged n+r dimension extent;
binary dimension headers by themselves would NOT justify this inequality. -/
theorem keySize_le_paperLength {n r : ℕ} (rows : List (List (PauliCoord n)))
    (C : Program r n) (a b c d : ℕ) :
    keySize n r≤2*paperLength rows C a b c d := by
  unfold keySize paperLength
  omega

end QecReliability.OracleCost.WholeWrapperCandidate.InputEncoding
