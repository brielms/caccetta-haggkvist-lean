import checkpoints.shen_extension.SeymourTransition
import checkpoints.shen_extension.TightRowCapstone

namespace LeanCH.BR.ShenPuncture
open BRq2 BRq3 Finset

def tight (E : CH.Digraph) (U : Finset ℕ) (s : ℕ) :=
  U.filter (fun v => (outN E U v).card+1=s)

/-- A puncture records the first bank of the removed vertex, its real
two-step exits, and the forbidden rectangle to the tight rows. -/
structure PunctureAt (E : CH.Digraph) (U A : Finset ℕ) (s n : ℕ) : Prop where
  free : QFree E U 3
  size : U.card+1=n
  degrees : ∀ v ∈ U, (outN E U v).card+1=s ∨ (outN E U v).card=s
  few : (tight E U s).card<s
  bank : A ⊆ U
  width : A.card=s
  heavy : Disjoint A (tight E U s)
  rectangle : ∀ a∈A, ∀ t∈tight E U s, E a t ≠ true
  exits : s ≤ (A.biUnion (outN E U) \ A).card

abbrev Puncture (E : CH.Digraph) (U A : Finset ℕ) (s : ℕ) := PunctureAt E U A s (3*s)

theorem extract_at_order {F W s} (hf : QFree F W 3) (wlive : W.Nonempty)
    (size : W.card≤3*s) (mind : ∀ x∈W, s≤(outN F W x).card) :
    ∃ E U A, PunctureAt E U A s W.card := by
  obtain ⟨E,sub,reg⟩ := exists_outEq mind
  have ef := qfree_sub sub hf
  obtain ⟨x,hx,good,small⟩ := ShenSeymour.surviving_row ef (by decide) (Subset.refl W) wlive
  let U := W.erase x
  let A := outN E W x
  have noLoop := loopfree ef (by decide) hx
  have bank : A ⊆ U := fun a ha => mem_erase.mpr
    ⟨fun eq => noLoop (eq ▸ (mem_outN.mp ha).2),outN_subset ha⟩
  have width : A.card=s := reg x hx
  have eraseRow (v) : outN E U v = (outN E W v).erase x := by
    ext z
    simp only [U,mem_outN,mem_erase]
    tauto
  have charRow {v} (hv : v ∈ U) :
      (outN E U v).card+1=s ↔ E v x=true := by
    rw [eraseRow]
    have h := reg v (mem_of_mem_erase hv)
    by_cases e : E v x=true
    · have hit := mem_outN.mpr ⟨hx,e⟩
      rw [card_erase_of_mem hit]
      have pos := card_pos.mpr ⟨x,hit⟩
      exact ⟨fun _ => e, fun _ => by omega⟩
    · rw [erase_eq_of_notMem (fun h => e (mem_outN.mp h).2)]
      exact ⟨fun bad => by omega,fun arc => (e arc).elim⟩
  have eqT : tight E U s = ShenSeymour.parents E W x := by
    ext v
    constructor
    · intro h
      obtain ⟨hv,deg⟩ := mem_filter.mp h
      exact mem_filter.mpr ⟨mem_of_mem_erase hv,(charRow hv).mp deg⟩
    · intro h
      obtain ⟨hv,e⟩ := mem_filter.mp h
      have vu : v∈U := mem_erase.mpr ⟨fun h => noLoop (h ▸ e),hv⟩
      exact mem_filter.mpr ⟨vu,(charRow vu).mpr e⟩
  have arcFree {a t} (ha : a∈A) (ht : t∈tight E U s) : E a t ≠ true := by
    rw [eqT] at ht
    intro e
    exact ef x 3 (by decide) le_rfl (.step (outN_subset ha) (mem_outN.mp ha).2
      (.step (mem_filter.mp ht).1 e (.step hx (mem_filter.mp ht).2 (.refl x))))
  refine ⟨E,U,A,ef.mono_set (erase_subset _ _),?_,?_,?_,bank,width,?_,fun _ ha _ ht => arcFree ha ht,?_⟩
  · change (W.erase x).card+1=_
    rw [card_erase_of_mem hx]
    have := wlive.card_pos
    omega
  · intro v hv
    by_cases e : E v x=true
    · exact Or.inl ((charRow hv).mpr e)
    · right
      rw [eraseRow,erase_eq_of_notMem (fun h => e (mem_outN.mp h).2)]
      exact reg v (mem_of_mem_erase hv)
  · rw [eqT]
    rw [reg x hx] at small
    omega
  · apply disjoint_left.mpr
    intro v hv ht
    rw [eqT] at ht
    exact digonfree ef (by decide) hx (outN_subset hv) (mem_outN.mp hv).2 (mem_filter.mp ht).2
  · have inc : ShenSeymour.second E W x ⊆ A.biUnion (outN E U) \ A := by
      intro z hz
      obtain ⟨zw,ne,nonarc,y,yw,xy,yz⟩ := mem_filter.mp hz
      exact mem_sdiff.mpr ⟨mem_biUnion.mpr ⟨y,mem_outN.mpr ⟨yw,xy⟩,
        mem_outN.mpr ⟨mem_erase.mpr ⟨ne,zw⟩,yz⟩⟩,fun h => nonarc (mem_outN.mp h).2⟩
    rw [← width]
    exact good.trans (card_le_card inc)

theorem extract {D V s} (free : QFree D V 3) (live : V.Nonempty)
    (order : V.card≤3*s) (degree : ∀ x∈V, s≤(outN D V x).card) :
    ∃ E U A, Puncture E U A s := by
  obtain ⟨F,W,hf,hw,mind⟩ := TightRow.pad_to (3*s-V.card) D V free live degree
  have size : W.card=3*s := by omega
  have wlive : W.Nonempty := card_pos.mp (by have := live.card_pos; omega)
  simpa only [size] using extract_at_order hf wlive size.le mind

/-- Rows available to be heads of a restored vertex. -/
def available (E : CH.Digraph) (U : Finset ℕ) (s : ℕ) := U.filter (fun a =>
  a ∉ tight E U s ∧ Disjoint (outN E U a) (tight E U s))

theorem PunctureAt.available_card {E U A s n} (h : PunctureAt E U A s n) : s≤(available E U s).card := by
  have sub : A ⊆ available E U s := by
    intro a ha
    refine mem_filter.mpr ⟨h.bank ha,fun ht => disjoint_left.mp h.heavy ha ht,?_⟩
    exact disjoint_left.mpr (fun z hz ht => h.rectangle a ha z ht (mem_outN.mp hz).2)
  exact h.width.symm.trans_le (card_le_card sub)

theorem Puncture.available_card {E U A s} (h : Puncture E U A s) : s≤(available E U s).card :=
  PunctureAt.available_card h

/-- Reinsert a vertex pointing to A and receiving one arc from each tight row. -/
def restore (E : CH.Digraph) (x : ℕ) (A T : Finset ℕ) : CH.Digraph :=
  fun v w => if v=x then decide (w∈A) else if w=x then decide (v∈T) else E v w

private theorem three_free {F V}
    (loops : ∀ a∈V, F a a ≠ true)
    (digons : ∀ a∈V, ∀ b∈V, F a b = true → F b a ≠ true)
    (triangles : ∀ a∈V, ∀ b∈V, ∀ c∈V, F a b = true → F b c = true → F c a ≠ true) :
    QFree F V 3 := by
  intro a l pos bound walk
  interval_cases l
  · cases walk with
    | step h e p => cases p; exact loops _ h e
  · cases walk with
    | step h e p => cases p with
                    | step k f p => cases p; exact digons _ k _ h e f
  · cases walk with
    | step h e p => cases p with
                    | step k f p => cases p with
                                    | step m g p => cases p; exact triangles _ m _ h _ k e f g

theorem restore_source {E U s A} (free : QFree E U 3) (size : U.card+1=3*s)
    (deg : ∀ v∈U, (outN E U v).card+1=s ∨ (outN E U v).card=s)
    (eligible : A ⊆ available E U s) (width : A.card=s) :
    ∃ F V, QFree F V 3 ∧ V.Nonempty ∧ V.card=3*s ∧ OutEq s F V := by
  let x := U.sup id+1
  have fresh : x ∉ U := by
    intro h
    have := Finset.le_sup (f := id) h
    change U.sup id+1 ≤ U.sup id at this
    omega
  let T := tight E U s
  let F := restore E x A T
  have toU : A ⊆ U := eligible.trans (filter_subset _ _)
  have notA : x ∉ A := fun h => fresh (toU h)
  have old {a b} (ha : a∈U) (hb : b∈U) : F a b=E a b := by
    have da : a ≠ x := fun eq => fresh (eq ▸ ha)
    have db : b ≠ x := fun eq => fresh (eq ▸ hb)
    simp [F,restore,da,db]
  have fromX (a) : F x a=true ↔ a∈A := by simp [F,restore]
  have intoX {a} (ha : a∈U) : F a x=true ↔ a∈T := by
    have da : a ≠ x := fun eq => fresh (eq ▸ ha)
    simp [F,restore,da]
  have noLoop : F x x ≠ true := fun h => notA ((fromX _).mp h)
  have oppose {a} (ha : a∈U) (h : F x a=true) (k : F a x=true) : False :=
    (mem_filter.mp (eligible ((fromX _).mp h))).2.1 ((intoX ha).mp k)
  have cross {a b} (ha : a∈insert x U) (hb : b∈insert x U)
      (xa : F x a=true) (ab : F a b=true) (bx : F b x=true) : False := by
    rcases mem_insert.mp ha with rfl | aa
    · exact noLoop xa
    rcases mem_insert.mp hb with rfl | bb
    · exact noLoop bx
    have paid := (mem_filter.mp (eligible ((fromX _).mp xa))).2.2
    exact disjoint_left.mp paid (mem_outN.mpr ⟨bb,old aa bb ▸ ab⟩) ((intoX bb).mp bx)
  refine ⟨F,insert x U,three_free ?_ ?_ ?_,⟨x,mem_insert_self _ _⟩,?_,?_⟩
  · intro a ha
    rcases mem_insert.mp ha with rfl | aa
    · exact noLoop
    · rw [old aa aa]
      exact loopfree free (by decide) aa
  · intro a ha b hb ab ba
    rcases mem_insert.mp ha with rfl | aa
    · rcases mem_insert.mp hb with rfl | bb
      · exact noLoop ab
      · exact oppose bb ab ba
    rcases mem_insert.mp hb with rfl | bb
    · exact oppose aa ba ab
    · exact digonfree free (by decide) aa bb (old aa bb ▸ ab) (old bb aa ▸ ba)
  · intro a ha b hb c hc ab bc ca
    rcases mem_insert.mp ha with rfl | aa
    · exact cross hb hc ab bc ca
    rcases mem_insert.mp hb with rfl | bb
    · exact cross hc ha bc ca ab
    rcases mem_insert.mp hc with rfl | cc
    · exact cross ha hb ca ab bc
    exact free a 3 (by decide) le_rfl (.step bb (old aa bb ▸ ab) (.step cc (old bb cc ▸ bc)
      (.step aa (old cc aa ▸ ca) (.refl a))))
  · rwa [card_insert_of_notMem fresh]
  · intro a ha
    rcases mem_insert.mp ha with rfl | aa
    · have eq : outN F (insert x U) x = A := by
        ext b
        exact ⟨fun h => (fromX _).mp (mem_outN.mp h).2,
          fun h => mem_outN.mpr ⟨mem_insert_of_mem (toU h),(fromX _).mpr h⟩⟩
      rwa [eq]
    have ne : x ∉ outN E U a := fun h => fresh (outN_subset h)
    have row : outN F (insert x U) a =
        (if a∈T then insert x (outN E U a) else outN E U a) := by
      ext b
      by_cases atight : a∈T <;> by_cases same : b=x
      all_goals first | subst b; simp [atight,mem_outN,intoX aa,fresh] | skip
      all_goals by_cases bu : b∈U
      all_goals simp_all [mem_outN,old aa]
    rw [row]
    split_ifs with ht
    · rw [card_insert_of_notMem ne]
      exact (mem_filter.mp ht).2
    · exact (deg a aa).resolve_left (fun h => ht (mem_filter.mpr ⟨aa,h⟩))

theorem cycle_of_no_puncture {D n s} (hn : 0<n) (order : n≤3*s) (loop : CH.Loopless D n)
    (degree : CH.MinOutdegreeAtLeast D n s) (exclude : ¬∃ E U A, Puncture E U A s) :
    CH.HasDirectedCycleAtMost D n 3 := by
  by_contra no
  exact exclude (extract (qfree_of_noShort loop no) ⟨0,mem_range.mpr hn⟩
    (by simpa using order) (fun v hv => Compose.FloorSix.out_card degree (mem_range.mp hv)))

#print axioms extract
/-- The boundary condition only tests hosts with fewer than s tight rows.
Their tight rows and their parents must cover at least 2s vertices. -/
def BankLaw (s : ℕ) : Prop :=
  ∀ E U, QFree E U 3 → U.card+1=3*s →
    (∀ v∈U, (outN E U v).card+1=s ∨ (outN E U v).card=s) →
    (tight E U s).card<s → (available E U s).card<s

theorem bankLaw_iff (s : ℕ) : BankLaw s ↔
    ∀ D V, QFree D V 3 → V.Nonempty → V.card≤3*s →
      (∀ v∈V, s≤(outN D V v).card) → False := by
  constructor
  · intro law D V free live size degree
    obtain ⟨E,U,A,h⟩ := extract free live size degree
    exact (law E U h.free h.size h.degrees h.few).not_ge h.available_card
  · intro no E U free size deg _few
    by_contra! many
    obtain ⟨A,sub,width⟩ := Finset.exists_subset_card_eq many
    obtain ⟨F,V,hf,live,order,reg⟩ := restore_source free size deg sub width
    exact no F V hf live order.le (fun v hv => (reg v hv).ge)

theorem capstone_of_bankLaw {D n s} (hn : 0<n) (order : n≤3*s) (loop : CH.Loopless D n)
    (degree : CH.MinOutdegreeAtLeast D n s) (law : BankLaw s) : CH.HasDirectedCycleAtMost D n 3 := by
  by_contra h
  exact (bankLaw_iff s).mp law D (range n) (qfree_of_noShort loop h)
    ⟨0,mem_range.mpr hn⟩ (by simpa using order)
    (fun v hv => Compose.FloorSix.out_card degree (mem_range.mp hv))

#print axioms restore_source
#print axioms bankLaw_iff
#print axioms capstone_of_bankLaw
#print axioms cycle_of_no_puncture
end LeanCH.BR.ShenPuncture
