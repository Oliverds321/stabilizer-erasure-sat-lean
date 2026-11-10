import OracleCost.PrefixTransitions
import OracleCost.QueryCodec

/-! Reachability invariants and an actual finite Boolean representation for the
prefix controller. These bounds concern represented data, not native Lean heap
allocation or a proved tape interpreter. -/
namespace QecReliability.OracleCost.PrefixTransitions

inductive StackOK (Q M : ℕ) : ℕ → ℕ → List Frame → Prop
  | nil {cap} (h : cap≤M) : StackOK Q M Q cap []
  | left {q pre parentCap cap stack} (hlen : pre.length+q+1=Q)
      (hcap : cap≤parentCap) (outer : StackOK Q M (q+1) parentCap stack) :
      StackOK Q M q cap (.left q pre parentCap::stack)
  | right {q left cap stack} (outer : StackOK Q M (q+1) (left+cap) stack) :
      StackOK Q M q cap (.right left::stack)

def ControlOK (Q depth budget : ℕ) : Control → Prop
  | .enter q pre cap => q=depth ∧ cap=budget ∧ pre.length+q=Q
  | .await q pre cap => q=depth ∧ cap=budget ∧ pre.length+q=Q ∧ 0<cap
  | .ret count => count=budget

def Valid (Q M : ℕ) (s : Config) : Prop :=
  ∃ depth budget, ControlOK Q depth budget s.control ∧ StackOK Q M depth budget s.stack

theorem StackOK.mono {Q M d b b' : ℕ} {stack : List Frame}
    (h : StackOK Q M d b stack) (hb : b'≤b) : StackOK Q M d b' stack := by
  induction h generalizing b' with
  | nil h => exact .nil (hb.trans h)
  | left hlen hcap outer _ => exact .left hlen (hb.trans hcap) outer
  | right outer ih => exact .right (ih (Nat.add_le_add_left hb _))

def FrameBound (Q M : ℕ) : Frame → Prop
  | .left q pre cap => q≤Q ∧ pre.length≤Q ∧ cap≤M
  | .right left => left≤M

theorem StackOK.bounds {Q M d b : ℕ} {stack : List Frame}
    (h : StackOK Q M d b stack) :
    d+stack.length=Q ∧ b≤M ∧ ∀ f∈stack, FrameBound Q M f := by
  induction h with
  | nil h => exact ⟨by simp,h,by simp⟩
  | @left q pre parentCap cap stack hlen hcap outer ih =>
    refine ⟨by simp only [List.length_cons]; omega,hcap.trans ih.2.1,?_⟩
    intro f hf
    rcases List.mem_cons.mp hf with rfl|hf
    · exact ⟨by omega,by omega,ih.2.1⟩
    · exact ih.2.2 f hf
  | @right q left cap stack outer ih =>
    refine ⟨by simp only [List.length_cons]; omega,by omega,?_⟩
    intro f hf
    rcases List.mem_cons.mp hf with rfl|hf
    · change left≤M; omega
    · exact ih.2.2 f hf

theorem initial_valid (q cap : ℕ) : Valid q cap ⟨.enter q [] cap,[]⟩ :=
  ⟨q,cap,⟨rfl,rfl,by simp⟩,.nil le_rfl⟩

/-- Preservation is explicitly restricted to well-formed reachable states.
In particular, Await with a zero cap is not a valid configuration. -/
theorem step_valid {Q M : ℕ} {s : Config} {e : Edge}
    (oracle : List Bool → SATReply) (hs : Valid Q M s)
    (he : step oracle s=some e) : Valid Q M e.next := by
  rcases s with ⟨control,stack⟩
  obtain ⟨depth,budget,hc,hstack⟩ := hs
  cases control with
  | enter q pre cap =>
    obtain ⟨rfl,rfl,hlen⟩ := hc
    by_cases hz : cap=0
    · simp only [step,hz,↓reduceIte,Option.some.injEq] at he
      subst e
      exact ⟨q,0,rfl,hstack.mono (Nat.zero_le _)⟩
    · simp only [step,hz,↓reduceIte,Option.some.injEq] at he
      subst e
      exact ⟨q,cap,⟨rfl,rfl,hlen,Nat.pos_of_ne_zero hz⟩,hstack⟩
  | await q pre cap =>
    obtain ⟨rfl,rfl,hlen,hpos⟩ := hc
    cases ho : (oracle pre).value with
    | false =>
      simp only [step,ho,Bool.false_eq_true,↓reduceIte,Option.some.injEq] at he
      subst e
      exact ⟨q,0,rfl,hstack.mono (Nat.zero_le _)⟩
    | true =>
      cases q with
      | zero =>
        simp only [step,ho,↓reduceIte,Option.some.injEq] at he
        subst e
        exact ⟨0,1,rfl,hstack.mono hpos⟩
      | succ q =>
        simp only [step,ho,↓reduceIte,Option.some.injEq] at he
        subst e
        refine ⟨q,cap,⟨rfl,rfl,?_⟩,.left (by omega) le_rfl hstack⟩
        simp only [List.length_append,List.length_singleton]
        omega
  | ret count =>
    change count=budget at hc
    subst budget
    cases hstack with
    | nil h => simp [step] at he
    | @left q pre parentCap count stack hlen hcap outer =>
      simp only [step,Option.some.injEq] at he
      subst e
      refine ⟨depth,parentCap-count,⟨rfl,rfl,?_⟩,.right ?_⟩
      · simp only [List.length_append,List.length_singleton]; omega
      · simpa only [Nat.add_sub_of_le hcap] using outer
    | @right q left count stack outer =>
      simp only [step,Option.some.injEq] at he
      subst e
      exact ⟨depth+1,left+count,rfl,outer⟩

theorem Trace.valid {Q M : ℕ} {oracle : List Bool → SATReply} {s t : Config}
    {n calls time : ℕ} (h : Trace oracle s n calls time t) (hs : Valid Q M s) :
    Valid Q M t := by
  induction h with
  | nil => exact hs
  | cons he _ ih => exact ih (step_valid oracle hs he)

theorem valid_await {Q M q cap : ℕ} {pre : List Bool} {stack : List Frame}
    (h : Valid Q M ⟨.await q pre cap,stack⟩) :
    pre.length≤Q ∧ 0<cap ∧ cap≤M ∧ stack.length≤Q := by
  obtain ⟨depth,budget,⟨rfl,rfl,hlen,hpos⟩,hs⟩ := h
  have hb := hs.bounds
  dsimp at hb
  exact ⟨by omega,hpos,hb.2.1,by omega⟩

/-- An explicit self-delimiting Boolean representation. Tags and natural
headers are included; duplicated saved prefixes are charged in full. -/
def frameBits : Frame → List Bool
  | .left q pre cap => [false] ++ QueryCodec.natHeader q ++
      QueryCodec.natHeader cap ++ QueryCodec.natHeader pre.length ++ pre
  | .right count => [true] ++ QueryCodec.natHeader count

def controlBits : Control → List Bool
  | .enter q pre cap => [false,false] ++ QueryCodec.natHeader q ++
      QueryCodec.natHeader cap ++ QueryCodec.natHeader pre.length ++ pre
  | .await q pre cap => [false,true] ++ QueryCodec.natHeader q ++
      QueryCodec.natHeader cap ++ QueryCodec.natHeader pre.length ++ pre
  | .ret count => [true,false] ++ QueryCodec.natHeader count

def configBits (s : Config) : List Bool := controlBits s.control ++
  QueryCodec.natHeader s.stack.length ++ s.stack.flatMap frameBits

def frameBitBound (Q M : ℕ) : ℕ := Q+4*Q.size+2*M.size+4

def configBitBound (Q M : ℕ) : ℕ :=
  frameBitBound Q M+1+(2*Q.size+1)+Q*frameBitBound Q M

theorem frameBits_length {Q M : ℕ} {f : Frame} (h : FrameBound Q M f) :
    (frameBits f).length≤frameBitBound Q M := by
  cases f with
  | left q pre cap =>
    obtain ⟨hq,hp,hc⟩ := h
    have qs := Nat.size_le_size hq
    have ps := Nat.size_le_size hp
    have cs := Nat.size_le_size hc
    simp only [frameBits,List.length_append,List.length_singleton,
      QueryCodec.natHeader_length,frameBitBound]
    omega
  | right count =>
    have cs := Nat.size_le_size h
    simp only [frameBits,List.length_append,List.length_singleton,
      QueryCodec.natHeader_length,frameBitBound]
    omega

theorem controlBits_length {Q M depth budget : ℕ} {control : Control}
    (h : ControlOK Q depth budget control) (hd : depth≤Q) (hb : budget≤M) :
    (controlBits control).length≤frameBitBound Q M+1 := by
  cases control with
  | enter q pre cap =>
    obtain ⟨rfl,rfl,hlen⟩ := h
    have qs := Nat.size_le_size hd
    have ps := Nat.size_le_size (show pre.length≤Q by omega)
    have cs := Nat.size_le_size hb
    simp only [controlBits,List.length_append,List.length_cons,List.length_nil,
      QueryCodec.natHeader_length,frameBitBound]
    omega
  | await q pre cap =>
    obtain ⟨rfl,rfl,hlen,_⟩ := h
    have qs := Nat.size_le_size hd
    have ps := Nat.size_le_size (show pre.length≤Q by omega)
    have cs := Nat.size_le_size hb
    simp only [controlBits,List.length_append,List.length_cons,List.length_nil,
      QueryCodec.natHeader_length,frameBitBound]
    omega
  | ret count =>
    change count=budget at h
    subst budget
    have cs := Nat.size_le_size hb
    simp only [controlBits,List.length_append,List.length_cons,List.length_nil,
      QueryCodec.natHeader_length,frameBitBound]
    omega

theorem stackBits_length {Q M : ℕ} {stack : List Frame}
    (h : ∀ f∈stack, FrameBound Q M f) :
    (stack.flatMap frameBits).length≤stack.length*frameBitBound Q M := by
  induction stack with
  | nil => simp
  | cons f stack ih =>
    have hf := frameBits_length (h f (by simp))
    have ht := ih (fun g hg => h g (by simp [hg]))
    simp only [List.flatMap_cons,List.length_append,List.length_cons]
    nlinarith

/-- Every reachable configuration has this explicit encoded payload bound.
This excludes the immutable formula, service tapes and interpreter overhead. -/
theorem configBits_length {Q M : ℕ} {s : Config} (h : Valid Q M s) :
    (configBits s).length≤configBitBound Q M := by
  obtain ⟨depth,budget,hc,hs⟩ := h
  obtain ⟨hd,hb,hf⟩ := hs.bounds
  have hdepth : depth≤Q := by omega
  have hstack : s.stack.length≤Q := by omega
  have cs := controlBits_length hc hdepth hb
  have ss := Nat.size_le_size hstack
  have fs := (stackBits_length hf).trans (Nat.mul_le_mul_right (frameBitBound Q M) hstack)
  simp only [configBits,List.length_append,QueryCodec.natHeader_length,configBitBound]
  omega

end QecReliability.OracleCost.PrefixTransitions
