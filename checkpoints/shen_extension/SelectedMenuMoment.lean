import checkpoints.shen_extension.SelectedMenuGrowth
import checkpoints.shen_extension.TripleMomentCount
import checkpoints.shen_extension.TripleMomentArithmetic
import checkpoints.shen_extension.TripleColumnTangent

namespace LeanCH.BR.TripleBank
open Finset BRq2 BRq3 BR45

/-- Count the triples of neutral rows sharing a head. The common-head
maximum on the original carrier bounds both column pools together. -/
theorem neutral_pool_moment {D : CH.Digraph} {V U P : Finset ℕ} {t : ℕ}
    (safe : QFree D U 3) (uv : U ⊆ V) (ht : 7 ≤ t) (hm : 2 ≤ P.card)
    (cap : TripleCap D V P.card) (pools : NeutralPools D U P t) :
    t ≤ 3*P.card ∧ 4 ≤ P.card := by
  classical
  let L := pools.L
  let Y := pools.Y
  let N := outN D U
  let f := columnDegree L N
  have size : L.card+1=t := pools.size
  have equal : Y.card=L.card := pools.equal
  have mass : L.card*t+P.card ≤ (∑ w ∈ L, f w)+(∑ w ∈ Y, f w) := by
    change _ ≤ (∑ w ∈ L, columnDegree L N w)+(∑ w ∈ Y, columnDegree L N w)
    rw [columnDegree_sum_split pools.separate pools.support]
    have rows (a) (ha : a ∈ L) : t+(if a ∈ P then 1 else 0) ≤ (N a).card := by
      by_cases ap : a ∈ P
      · simp [ap,N,pools.full _ ap]
      · simpa [ap,N] using pools.floor _ ha
    have h := sum_le_sum rows
    have ones : (∑ a ∈ L, if a ∈ P then (1:ℕ) else 0) = P.card := by
      rw [← sum_filter]
      have same : L.filter (fun a => a ∈ P) = P := by
        ext a; simpa only [mem_filter, and_iff_right_iff_imp] using (show a ∈ P → a ∈ L from fun ha => pools.selected ha)
      simp [same]
    simpa only [sum_add_distrib,sum_const,Nat.nsmul_eq_mul,ones] using h
  have head : (∑ w ∈ L, f w) ≤ L.card*(P.card+1) := by
    change (∑ w ∈ L, columnDegree L N w) ≤ _
    rw [columnDegree_sum]
    simpa only [sum_const,Nat.nsmul_eq_mul] using sum_le_sum (fun a (ha : a ∈ L) => pools.internal a ha)
  have rowCount := columnDegree_sum L L N
  have directed (r) (hr : r ∈ L) : f r + (N r ∩ L).card ≤ L.card-1 := by
    let I := L.filter (fun a => r ∈ N a)
    change I.card + (N r ∩ L).card ≤ _
    have ru := pools.rows hr
    have apart : Disjoint I (N r ∩ L) := by
      apply disjoint_left.mpr
      intro v iv ov
      obtain ⟨vl,vr⟩ := mem_filter.mp iv
      exact digonfree safe (by decide) (pools.rows vl) ru (mem_outN.mp vr).2 (mem_outN.mp (mem_inter.mp ov).1).2
    have inc : I ∪ (N r ∩ L) ⊆ L.erase r := by
      intro v vm
      rcases mem_union.mp vm with iv | ov
      · obtain ⟨vl,vr⟩ := mem_filter.mp iv
        exact mem_erase.mpr ⟨fun e => loopfree safe (by decide) ru (e ▸ (mem_outN.mp vr).2),vl⟩
      · obtain ⟨rv,vl⟩ := mem_inter.mp ov
        exact mem_erase.mpr ⟨fun e => loopfree safe (by decide) ru (e ▸ (mem_outN.mp rv).2),vl⟩
    rw [← card_union_of_disjoint apart,← card_erase_of_mem hr]
    exact card_le_card inc
  have oriented := sum_le_sum directed
  simp only [sum_add_distrib,sum_const,Nat.nsmul_eq_mul] at oriented
  change (∑ w ∈ L, f w) = _ at rowCount
  rw [← rowCount,← two_mul] at oriented
  have bounded (Q : Finset ℕ) (_ : Q ⊆ L ∪ Y) (count : 3 ≤ (L.filter (fun a => Q ⊆ N a)).card) :
      Q.card ≤ P.card := by
    obtain ⟨a,am,b,bm,c,cm,ab,ac,bc⟩ := two_lt_card.mp (by omega : 2 < (L.filter (fun a => Q ⊆ N a)).card)
    have inc {a} (ha : a ∈ L.filter (fun i => Q ⊆ N i)) : Q ⊆ outN D V a :=
      fun _ m => let h := (mem_filter.mp ha).2 m
                 mem_outN.mpr ⟨uv (outN_subset h),(mem_outN.mp h).2⟩
    exact (card_le_card (subset_inter (subset_inter (inc am) (inc bm)) (inc cm))).trans
      (cap a b c (uv (pools.rows (mem_filter.mp am).1)) (uv (pools.rows (mem_filter.mp bm).1))
        (uv (pools.rows (mem_filter.mp cm).1)) ab ac bc)
  have triples := columnChoose_sum_split_le pools.separate bounded
  have lhs := sum_choose_three_tangent L f
  have rhs := sum_choose_three_tangent Y f
  rw [equal] at rhs
  rw [← size] at mass ht ⊢
  exact moment_frontier ht hm mass head oriented triples lhs rhs

/-- Carry the size and inherited-head bounds on the same selected bank. -/
theorem selected_moment_frontier {D : CH.Digraph} {V : Finset ℕ} {s : ℕ}
    (safe : QFree D V 3) (reg : OutEq s D V) (hs : 8 ≤ s) (order : V.card = 3*s)
    (no : BypassRepair.NoHost 3 (s-1)) :
    ∃ P ⊆ V, 2 ≤ P.card ∧ TripleCap D V P.card ∧ ∃ B ⊆ V, B.card=3 ∧
      (∀ b ∈ B, P ⊆ outN D V b) ∧
      let U := V \ B
      let S := U.filter (fun c => 2 ≤ (outN D B c).card)
      (∀ c ∈ S, ∃ z ∈ P, D c z ≠ true) ∧
      (2 ≤ S.card ∨ ∃ c, S={c} ∧ (outN D B c).card=3 ∧ (rowMenu D U P c).card=1 ∧
        (4 ≤ (tightParents D U c (s-1)).card ∨
          (tightParents D U c (s-1)).card=3 ∧ s-1 ≤ 3*P.card ∧ 4 ≤ P.card ∧ 3 ≤ (P ∩ outN D V c).card)) := by
  classical
  obtain ⟨P,pv,many,cap,B,bv,three,common,miss,_,front⟩ :=
    GlobalTripleChoice.top_repair_frontier safe reg (by omega) order no
  refine ⟨P,pv,many,cap,B,bv,three,common,miss,?_⟩
  rcases front with several | ⟨c,one,hits,menu⟩
  · exact Or.inl several
  · refine Or.inr ⟨c,one,hits,menu,?_⟩
    have cs : c ∈ (V \ B).filter (fun a => 2 ≤ (outN D B a).card) := one ▸ mem_singleton_self _
    have lone (v) (vu : v ∈ V \ B) (vc : v ≠ c) : (outN D B v).card ≤ 1 := by
      by_contra! bad
      exact vc (mem_singleton.mp (one ▸ (mem_filter.mpr ⟨vu,by omega⟩)))
    have parents := three_tight_on_lone_frontier safe reg (by omega) order no bv three pv many common
      (mem_filter.mp cs).1 lone menu.le
    by_cases large : 4 ≤ (tightParents D (V \ B) c (s-1)).card
    · exact Or.inl large
    · have eq : (tightParents D (V \ B) c (s-1)).card=3 := by omega
      obtain ⟨_,⟨pools⟩⟩ := bank_menu_pools safe reg hs order no bv three pv many common cap
        (mem_filter.mp cs).1 hits lone menu.le (miss c cs) eq
      obtain ⟨height,heads⟩ := neutral_pool_moment (safe.mono_set sdiff_subset) sdiff_subset
        (by omega) many cap pools
      have small : (P \ outN D V c).card ≤ 1 := by
        refine (card_le_card (show P \ outN D V c ⊆ rowMenu D (V \ B) P c from ?_)).trans menu.le
        intro p pm
        obtain ⟨mp,off⟩ := mem_sdiff.mp pm
        exact mem_union_left _ (mem_sdiff.mpr ⟨mp,fun hit => off
          (mem_outN.mpr ⟨(mem_sdiff.mp (outN_subset hit)).1,(mem_outN.mp hit).2⟩)⟩)
      have split := card_sdiff_add_card_inter P (outN D V c)
      exact Or.inr ⟨eq,height,heads,by omega⟩

#print axioms neutral_pool_moment
#print axioms selected_moment_frontier
end LeanCH.BR.TripleBank
