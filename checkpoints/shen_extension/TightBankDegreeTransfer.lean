import checkpoints.shen_extension.dot_tensor_research.DegreeSevenVerified_20261121
import checkpoints.shen_extension.dot_tensor_research.DotDegreeSixVerified_20261121
import Mathlib.Data.Finset.Powerset

namespace LeanCH.BR.TightBankDegreeTransfer
open Finset BRq2 BRq3 BR45

/-- At the first order beyond unrestricted deletion, every choice of erased
vertices is completely seen by one surviving row of the original tight degree. -/
theorem bank_cover {D : CH.Digraph} {V : Finset ℕ} {q d r k : ℕ}
    (endpoint : DotDegreeSeven.Endpoint q d) (positive : 0<q*d)
    (free : QFree D V q) (minimum : ∀ i∈V, r≤(outN D V i).card)
    (size : V.card=q*d+k) (cost : d+k=r+1)
    {K : Finset ℕ} (sub : K⊆V) (card : K.card=k) :
    ∃ i∈V \ K, (outN D V i).card=r ∧ K⊆outN D V i := by
  classical
  have kept : (V \ K).card=q*d := by rw [card_sdiff_of_subset sub,card,size]; omega
  have someShort : ∃ i∈V \ K, (outN D (V \ K) i).card<d := by
    by_contra! allPaid
    exact endpoint D (V \ K) (free.mono_set sdiff_subset)
      (card_pos.mp (kept ▸ positive)) kept allPaid
  obtain ⟨i,iKept,short⟩ := someShort
  have low := minimum i (mem_sdiff.mp iKept).1
  have removedSub : outN D K i⊆K := fun _ h => (mem_outN.mp h).1
  have removedBound := card_le_card removedSub
  have partition := card_outN_union (D:=D) (show Disjoint K (V \ K) from disjoint_sdiff) i
  rw [union_sdiff_of_subset sub] at partition
  have full : outN D K i=K := eq_of_subset_of_card_le removedSub (by omega)
  refine ⟨i,iKept,by omega,?_⟩
  intro j jK
  have jRemoved : j ∈ outN D K i := by rw [full]; exact jK
  obtain ⟨_,edge⟩ := mem_outN.mp jRemoved
  exact mem_outN.mpr ⟨sub jK,edge⟩

/-- The tight rows must cover every labelled k-set. Their number gives an
explicit numerical obstruction at any solved degree and cutoff. -/
theorem tight_cover_count {D : CH.Digraph} {V : Finset ℕ} {q d r k : ℕ}
    (endpoint : DotDegreeSeven.Endpoint q d) (positive : 0<q*d)
    (free : QFree D V q) (minimum : ∀ i∈V, r≤(outN D V i).card)
    (size : V.card=q*d+k) (cost : d+k=r+1) :
    V.card.choose k ≤ (V.filter (fun i => (outN D V i).card=r)).card * r.choose k := by
  classical
  let T := V.filter (fun i => (outN D V i).card=r)
  let banks := fun i => (outN D V i).powersetCard k
  have covered : V.powersetCard k ⊆ T.biUnion banks := by
    intro K hK
    obtain ⟨sub,card⟩ := mem_powersetCard.mp hK
    obtain ⟨i,im,degree,inc⟩ := bank_cover endpoint positive free minimum size cost sub card
    exact mem_biUnion.mpr ⟨i,mem_filter.mpr ⟨(mem_sdiff.mp im).1,degree⟩,mem_powersetCard.mpr ⟨inc,card⟩⟩
  calc
    V.card.choose k = (V.powersetCard k).card := (card_powersetCard k V).symm
    _ ≤ (T.biUnion banks).card := card_le_card covered
    _ ≤ ∑ i ∈ T, (banks i).card := card_biUnion_le
    _ = T.card*r.choose k := by
      have equal (i) (hi : i∈T) : (banks i).card=r.choose k := by
        rw [show (banks i).card=(outN D V i).card.choose k from card_powersetCard k _,(mem_filter.mp hi).2]
      simp only [sum_congr rfl equal,sum_const,nsmul_eq_mul,Nat.cast_id]

theorem cycle_of_count {n q d r k : ℕ} (D : CH.Digraph)
    (endpoint : DotDegreeSeven.Endpoint q d) (positive : 0<q*d)
    (size : n=q*d+k) (cost : d+k=r+1) (room : n*r.choose k<n.choose k)
    (loopless : CH.Loopless D n) (degree : CH.MinOutdegreeAtLeast D n r) :
    CH.HasDirectedCycleAtMost D n q := by
  by_contra missing
  have cover := tight_cover_count (D:=D) (V:=range n) endpoint positive (qfree_of_noShort loopless missing)
    (fun _ hi => Compose.FloorSix.out_card degree (mem_range.mp hi)) (by simpa only [card_range] using size) cost
  have bound := card_le_card (filter_subset (fun i => (outN D (range n) i).card=r) (range n))
  rw [card_range] at cover bound
  exact (not_lt_of_ge (cover.trans (Nat.mul_le_mul_right _ bound))) room

/-- Fix actual labels in advance. Every completion of S to a k-set still has to
be seen by a single tight parent of the entire S. -/
theorem shared_parent_count {D : CH.Digraph} {V S : Finset ℕ} {q d r k : ℕ}
    (endpoint : DotDegreeSeven.Endpoint q d) (positive : 0<q*d)
    (free : QFree D V q) (minimum : ∀ i∈V, r≤(outN D V i).card)
    (size : V.card=q*d+k) (cost : d+k=r+1) (sub : S⊆V) (fit : S.card≤k) :
    (V.card-S.card).choose (k-S.card) ≤
      (V.filter (fun i => (outN D V i).card=r ∧ S⊆outN D V i)).card *
      (r-S.card).choose (k-S.card) := by
  classical
  let T := V.filter (fun i => (outN D V i).card=r ∧ S⊆outN D V i)
  let banks := fun i => ((outN D V i) \ S).powersetCard (k-S.card)
  have cover : (V \ S).powersetCard (k-S.card) ⊆ T.biUnion banks := by
    intro W hw
    obtain ⟨tails,wsize⟩ := mem_powersetCard.mp hw
    have disj : Disjoint S W := disjoint_left.mpr (fun _ hs hw => (mem_sdiff.mp (tails hw)).2 hs)
    have whole : S∪W ⊆ V := union_subset sub (fun _ hx => (mem_sdiff.mp (tails hx)).1)
    have total : (S∪W).card=k := by rw [card_union_of_disjoint disj,wsize]; omega
    obtain ⟨i,im,deg,both⟩ := bank_cover endpoint positive free minimum size cost whole total
    have sees := union_subset_iff.mp both
    refine mem_biUnion.mpr ⟨i,mem_filter.mpr ⟨(mem_sdiff.mp im).1,deg,sees.1⟩,mem_powersetCard.mpr ⟨?_,wsize⟩⟩
    exact fun _ hx => mem_sdiff.mpr ⟨sees.2 hx,(mem_sdiff.mp (tails hx)).2⟩
  have bound := card_biUnion_le_card_mul T banks ((r-S.card).choose (k-S.card)) (by
    intro i hi
    obtain ⟨deg,sees⟩ := (mem_filter.mp hi).2
    change (((outN D V i) \ S).powersetCard (k-S.card)).card ≤ _
    rw [card_powersetCard,card_sdiff_of_subset sees,deg])
  have lhs := card_le_card cover
  rw [card_powersetCard,card_sdiff_of_subset sub] at lhs
  exact lhs.trans bound

/-- Every set of exactly k−1 prescribed labels requires q+1 original tight
parents in common. There are q*d+1 ways to complete it and each common
parent accommodates only d of them. -/
theorem common_extra_parent {D : CH.Digraph} {V S : Finset ℕ} {q d r k : ℕ}
    (endpoint : DotDegreeSeven.Endpoint q d) (positive : 0<q*d)
    (free : QFree D V q) (minimum : ∀ i∈V, r≤(outN D V i).card)
    (size : V.card=q*d+k) (cost : d+k=r+1) (sub : S⊆V) (oneLeft : S.card+1=k) :
    q+1 ≤ (V.filter (fun i => (outN D V i).card=r ∧ S⊆outN D V i)).card := by
  classical
  have covers := shared_parent_count endpoint positive free minimum size cost sub (by omega)
  have one : k-S.card=1 := by omega
  have available : V.card-S.card=q*d+1 := by omega
  have perRow : r-S.card=d := by omega
  rw [one,available,perRow,Nat.choose_one_right,Nat.choose_one_right] at covers
  by_contra! few
  have cap := Nat.mul_le_mul_right d (show
    (V.filter (fun i => (outN D V i).card=r ∧ S⊆outN D V i)).card≤q by omega)
  omega

/-- When one degree above the solved degree, q*d+1 companions must fit in
banks of size d. The residue forces an extra tight parent at every label. -/
theorem extra_tight_parent {D : CH.Digraph} {V : Finset ℕ} {q d : ℕ}
    (endpoint : DotDegreeSeven.Endpoint q d) (positive : 0<q*d)
    (free : QFree D V q) (minimum : ∀ i∈V, d+1≤(outN D V i).card)
    (size : V.card=q*d+2) {v : ℕ} (member : v∈V) :
    q+1 ≤ (V.filter (fun i => (outN D V i).card=d+1 ∧ D i v=true)).card := by
  classical
  simpa only [singleton_subset_iff,mem_outN,member,true_and] using
    common_extra_parent (S:={v}) (k:=2) endpoint positive free minimum size (by omega)
      (singleton_subset_iff.mpr member) (by simp)

theorem order_38_degree_9 (D : CH.Digraph) (loopless : CH.Loopless D 38)
    (degree : CH.MinOutdegreeAtLeast D 38 9) :
    CH.HasDirectedCycleAtMost D 38 (CH.ceilDiv 38 9) :=
  cycle_of_count (k:=3) D DotDegreeSevenLow.endpoint_five_seven
    (by decide) (by decide) (by decide) (by decide) loopless degree

theorem order_33_degree_8_from_six (D : CH.Digraph) (loopless : CH.Loopless D 33)
    (degree : CH.MinOutdegreeAtLeast D 33 8) :
    CH.HasDirectedCycleAtMost D 33 (CH.ceilDiv 33 8) :=
  cycle_of_count (k:=3) D DotDegreeSix.endpoint_five_six
    (by decide) (by decide) (by decide) (by decide) loopless degree

open CHRuleCatalog in
/-- A recursive child can use its own order, cutoff and degree at any depth. -/
theorem impossible_at_descendant {p c : Input} (bad : Bad p) (path : Relation.ReflTransGen Child p c)
    {d k : ℕ} (endpoint : DotDegreeSeven.Endpoint (cutoff c) d) (positive : 0<cutoff c*d)
    (size : c.n=cutoff c*d+k) (cost : d+k=c.s+1) (room : c.n*c.s.choose k<c.n.choose k) : False := by
  have child := bad_descendant bad path
  exact child.missing (cycle_of_count c.D endpoint positive size cost room child.loopless child.degree)

#print axioms bank_cover
#print axioms tight_cover_count
#print axioms cycle_of_count
#print axioms shared_parent_count
#print axioms common_extra_parent
#print axioms extra_tight_parent
#print axioms order_38_degree_9
#print axioms order_33_degree_8_from_six
#print axioms impossible_at_descendant
end LeanCH.BR.TightBankDegreeTransfer
