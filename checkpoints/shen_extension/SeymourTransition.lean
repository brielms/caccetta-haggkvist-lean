import OAI.Combinatorics.SecondNeighborhood.Main
import LeanCH.BR.BRq3Base

namespace LeanCH.BR.ShenSeymour
open BRq2 BRq3 Finset

def parents (D : CH.Digraph) (U : Finset ℕ) (x : ℕ) :=
  U.filter (fun z => D z x = true)

/-- Exact two-step destinations inside this carrier, retaining the intermediary. -/
noncomputable def second (D : CH.Digraph) (U : Finset ℕ) (x : ℕ) : Finset ℕ := by
  classical
  exact U.filter (fun z => z ≠ x ∧ D x z ≠ true ∧ ∃ y ∈ U, D x y = true ∧ D y z = true)

theorem witness {D U q} (free : QFree D U q) (two : 2 ≤ q) (live : U.Nonempty) :
    ∃ x ∈ U, (outN D U x).card ≤ (second D U x).card := by
  classical
  let : Nonempty ↥U := ⟨⟨live.choose,live.choose_spec⟩⟩
  let R (x y : ↥U) := D x.val y.val = true
  have oriented : OAI.SeymourSecondNeighborhood.IsOriented R :=
    ⟨fun x => loopfree free (by omega) x.property,
     fun {x y} => digonfree free two x.property y.property⟩
  obtain ⟨x,good⟩ := OAI.SeymourSecondNeighborhood.exists_goodVertex R oriented
  let F := OAI.SeymourSecondNeighborhood.firstNeighbors R x
  let S := OAI.SeymourSecondNeighborhood.secondNeighbors R x
  have fEq : F.image Subtype.val = outN D U x.val := by
    ext z
    constructor
    · intro h
      obtain ⟨a,ha,rfl⟩ := mem_image.mp h
      have edge : R x a := (OAI.SeymourSecondNeighborhood.mem_firstNeighbors (r := R)).mp ha
      exact mem_outN.mpr ⟨a.property,edge⟩
    · intro h
      obtain ⟨hz,edge⟩ := mem_outN.mp h
      exact mem_image.mpr ⟨⟨z,hz⟩,OAI.SeymourSecondNeighborhood.mem_firstNeighbors.mpr edge,rfl⟩
  have sSub : S.image Subtype.val ⊆ second D U x.val := by
    intro z hz
    obtain ⟨a,ha,rfl⟩ := mem_image.mp hz
    obtain ⟨diff,missing,y,xy,ya⟩ := OAI.SeymourSecondNeighborhood.mem_secondNeighbors.mp ha
    exact mem_filter.mpr ⟨a.property,fun h => diff (Subtype.ext h),missing,
      y.val,y.property,xy,ya⟩
  have size := card_le_card sSub
  rw [card_image_of_injective _ Subtype.val_injective] at size
  refine ⟨x.val,x.property,?_⟩
  rw [← fEq,card_image_of_injective _ Subtype.val_injective]
  exact good.trans size

/-- A surviving graph supplies a low incoming row in *every* nonempty induced bank. -/
theorem surviving_row {D V q} (free : QFree D V q) (three : 3 ≤ q)
    {U : Finset ℕ} (sub : U ⊆ V) (live : U.Nonempty) :
    ∃ x ∈ U, (outN D U x).card ≤ (second D U x).card ∧
      2*(outN D U x).card+(parents D U x).card < U.card := by
  have hf := free.mono_set sub
  obtain ⟨x,hx,good⟩ := witness hf (by omega) live
  let O := outN D U x
  let I := parents D U x
  let S := second D U x
  have oi : Disjoint O I := by
    apply disjoint_left.mpr
    intro y h k
    exact digonfree hf (by omega) hx (outN_subset h) (mem_outN.mp h).2 (mem_filter.mp k).2
  have os : Disjoint O S := by
    apply disjoint_left.mpr
    intro y h k
    exact (mem_filter.mp k).2.2.1 (mem_outN.mp h).2
  have is' : Disjoint I S := by
    apply disjoint_left.mpr
    intro z h k
    obtain ⟨hz,_,_,y,hy,xy,yz⟩ := mem_filter.mp k
    exact hf x 3 (by decide) three (.step hy xy (.step hz yz (.step hx (mem_filter.mp h).2 (.refl x))))
  have loop := loopfree hf (by omega) hx
  have empty : x ∉ O ∪ I ∪ S := by
    intro h
    rcases mem_union.mp h with h | h
    · rcases mem_union.mp h with h | h
      · exact loop (mem_outN.mp h).2
      · exact loop (mem_filter.mp h).2
    · exact (mem_filter.mp h).2.1 rfl
  have allIn : insert x (O ∪ I ∪ S) ⊆ U :=
    insert_subset hx (union_subset (union_subset outN_subset (filter_subset _ _)) (filter_subset _ _))
  have total := card_le_card allIn
  rw [card_insert_of_notMem empty,card_union_of_disjoint (disjoint_union_left.mpr ⟨os,is'⟩),
    card_union_of_disjoint oi] at total
  change O.card ≤ S.card at good
  exact ⟨x,hx,good,show 2*O.card+I.card < U.card by omega⟩

/-- A family of concrete graphs, specified without any cycle hypothesis. -/
def DenseBank (D : CH.Digraph) (V : Finset ℕ) : Prop :=
  ∃ U ⊆ V, U.Nonempty ∧ ∀ x ∈ U, U.card ≤ 2*(outN D U x).card+(parents D U x).card

theorem cycle_of_dense_bank {D n q} (three : 3 ≤ q) (loop : CH.Loopless D n)
    (bank : DenseBank D (range n)) : CH.HasDirectedCycleAtMost D n q := by
  by_contra no
  obtain ⟨U,sub,live,rows⟩ := bank
  obtain ⟨x,hx,_,low⟩ := surviving_row (qfree_of_noShort loop no) three sub live
  exact low.not_ge (rows x hx)

/-- Each deletion recomputes both neighbourhoods on the remaining actual vertices. -/
inductive Peels (D : CH.Digraph) : Finset ℕ → Prop where
  | empty : Peels D ∅
  | erase {U x} (hx : x ∈ U) (good : (outN D U x).card ≤ (second D U x).card)
      (low : 2*(outN D U x).card+(parents D U x).card < U.card)
      (tail : Peels D (U.erase x)) : Peels D U

theorem stuck_of_dense_bank {D V} (bank : DenseBank D V) : ∃ U ⊆ V, ¬ Peels D U := by
  obtain ⟨U,sub,live,rows⟩ := bank
  refine ⟨U,sub,?_⟩
  intro p
  cases p with
  | empty => simpa using live
  | erase hx _ low _ => exact low.not_ge (rows _ hx)

theorem peels_of_free {D V q} (free : QFree D V q) (three : 3 ≤ q) :
    ∀ U ⊆ V, Peels D U := by
  intro U
  induction U using Finset.strongInductionOn with
  | _ U ih =>
    intro sub
    by_cases live : U.Nonempty
    · obtain ⟨x,hx,good,low⟩ := surviving_row free three sub live
      exact .erase hx good low (ih _ (erase_ssubset hx) ((erase_subset _ _).trans sub))
    · rw [not_nonempty_iff_eq_empty.mp live]
      exact .empty

theorem cycle_of_no_peel {D n q U} (three : 3 ≤ q) (loop : CH.Loopless D n)
    (sub : U ⊆ range n) (stuck : ¬Peels D U) : CH.HasDirectedCycleAtMost D n q := by
  by_contra no
  exact stuck (peels_of_free (qfree_of_noShort loop no) three U sub)

#print axioms surviving_row
#print axioms cycle_of_dense_bank
#print axioms peels_of_free
#print axioms cycle_of_no_peel
end LeanCH.BR.ShenSeymour
