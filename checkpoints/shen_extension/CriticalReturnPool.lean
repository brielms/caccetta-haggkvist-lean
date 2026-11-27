import checkpoints.shen_extension.OneArcReturnBudget

namespace LeanCH.BR.TripleBank
open Finset BRq2 BRq3 BR45

/-- Repeated out-neighbour incidences on the return p→w→x. -/
def returnOverlap (D : CH.Digraph) (U : Finset ℕ) (p w x : ℕ) : ℕ :=
  let A := outN D U p
  let B := outN D U w
  let C := outN D U x
  (A∩C).card+((A∪C)∩B).card

/-- The repeated incidences pay exactly for the labels outside all three
outgoing rows plus two. For a pair of bare arcs only A∩C contributes. -/
theorem return_pool_count {D : CH.Digraph} {U : Finset ℕ} {p w x t : ℕ}
    (safe : QFree D U 3) (pu : p∈U) (wu : w∈U) (xu : x∈U)
    (pw : D p w=true) (wx : D w x=true) (size : U.card=3*t)
    (np : (outN D U p).card=t+1) (nw : (outN D U w).card=t+1)
    (nx : (outN D U x).card+1=t)
    :
    let A := outN D U p
    let B := outN D U w
    let C := outN D U x
    let pool := U \ insert p ((A∪C)∪B)
    returnOverlap D U p w x=pool.card+2 ∧
    ∀ y∈A∩C, ∀ z∈outN D U y ∩ inN D U w, z∉A → z∈pool := by
  classical
  intro A B C pool
  have guard : D x p≠true := fun xp => safe p 3 (by decide) (by decide)
    (.step wu pw (.step xu wx (.step pu xp (.refl _))))
  have pm : p∉(A∪C)∪B := by
    intro h
    rcases mem_union.mp h with h | bp
    · rcases mem_union.mp h with ap | cp
      · exact loopfree safe (by decide) pu (mem_outN.mp ap).2
      · exact guard (mem_outN.mp cp).2
    · exact digonfree safe (by decide) pu wu pw (mem_outN.mp bp).2
  have sub : insert p ((A∪C)∪B) ⊆ U :=
    insert_subset pu (union_subset (union_subset outN_subset outN_subset) outN_subset)
  have count := card_sdiff_add_card_eq_card sub
  change pool.card + (insert p ((A∪C)∪B)).card = U.card at count
  rw [card_insert_of_notMem pm] at count
  change pool.card+(((A∪C)∪B).card+1)=U.card at count
  have sum := card_union_add_card_inter A C
  have sum' := card_union_add_card_inter (A∪C) B
  change A.card=t+1 at np
  change B.card=t+1 at nw
  change C.card+1=t at nx
  refine ⟨?_,?_⟩
  · change (A∩C).card+((A∪C)∩B).card=pool.card+2
    omega
  intro y ym z zm off
  obtain ⟨ay,cy⟩ := mem_inter.mp ym
  obtain ⟨yz,zw⟩ := mem_inter.mp zm
  obtain ⟨zu,yz'⟩ := mem_outN.mp yz
  have yu := outN_subset ay
  have zp : z≠p := fun eq => digonfree safe (by decide) pu yu
    (mem_outN.mp ay).2 (eq ▸ yz')
  have zc : z∉C := fun m => safe w 3 (by decide) (by decide)
    (.step xu wx (.step zu (mem_outN.mp m).2 (.step wu (mem_inN.mp zw).2 (.refl _))))
  have zb : z∉B := fun m => digonfree safe (by decide) wu zu (mem_outN.mp m).2 (mem_inN.mp zw).2
  exact mem_sdiff.mpr ⟨zu,by simp [zp,off,zc,zb]⟩

/-- D is the retained original graph. H is the partial repair after
dropping the unpaid w→x leg. The two protected rows ensure all remaining
returns of y→w use old arcs. Only the exterior positions in the pool can house tight tails outside A. -/
theorem return_spent_budget {D H : CH.Digraph} {U : Finset ℕ} {p w x y t : ℕ}
    (safe : QFree D U 3) (pu : p∈U) (wu : w∈U) (xu : x∈U)
    (pw : D p w=true) (wx : D w x=true) (size : U.card=3*t)
    (np : (outN D U p).card=t+1) (nw : (outN D U w).card=t+1)
    (nx : (outN D U x).card+1=t)
    (ym : y∈outN D U p ∩ outN D U x)
    (clean : QFree H U 3) (no : BypassRepair.NoHost 3 t)
    (near : t≤(outN H U w).card+1)
    (floor : ∀ i∈U, i≠w → t≤(outN H U i).card)
    (yOld : outN H U y ⊆ outN D U y) (wOld : inN H U w ⊆ inN D U w)
    (wy : H w y≠true) :
    (outN H U y).card+2 <
      t+(((outN H U y ∩ inN H U w) ∩ outN D U p).filter
        (fun z => (outN H U z).card=t)).card + returnOverlap D U p w x := by
  classical
  obtain ⟨n,region⟩ := return_pool_count safe pu wu xu pw wx size np nw nx
  have yu := outN_subset (mem_inter.mp ym).1
  have back : H y w≠true := fun h => safe w 3 (by decide) (by decide) (.step xu wx
    (.step yu (mem_outN.mp (mem_inter.mp ym).2).2 (.step wu (mem_outN.mp (yOld (mem_outN.mpr ⟨wu,h⟩))).2 (.refl _))))
  have neq : w≠y := fun eq => digonfree safe (by decide) wu xu wx (eq ▸ (mem_outN.mp (mem_inter.mp ym).2).2)
  let T := (outN H U y ∩ inN H U w).filter (fun z => (outN H U z).card≤t)
  let A := outN D U p
  have outer := card_le_card (show T \ A ⊆ U \ insert p ((A∪outN D U x)∪outN D U w) by
    intro z zm
    obtain ⟨tight,off⟩ := mem_sdiff.mp zm
    have zm' := (mem_filter.mp tight).1
    exact region y ym z (mem_inter.mpr ⟨yOld (mem_inter.mp zm').1,wOld (mem_inter.mp zm').2⟩) off)
  have sets : T ∩ A =
      (((outN H U y ∩ inN H U w) ∩ outN D U p).filter (fun z => (outN H U z).card=t)) := by
    ext z
    constructor
    · intro h
      obtain ⟨tight,ap⟩ := mem_inter.mp h
      obtain ⟨zm,low⟩ := mem_filter.mp tight
      have off : z≠w := fun eq => back (eq ▸ (mem_outN.mp (mem_inter.mp zm).1).2)
      exact mem_filter.mpr ⟨mem_inter.mpr ⟨zm,ap⟩,
        le_antisymm low (floor z (outN_subset (mem_inter.mp zm).1) off)⟩
    · intro h
      obtain ⟨zm,eq⟩ := mem_filter.mp h
      exact mem_inter.mpr ⟨mem_filter.mpr ⟨(mem_inter.mp zm).1,eq.le⟩,(mem_inter.mp zm).2⟩
  have cost : (outN H U y).card < t+T.card := by
    by_contra! budget
    obtain ⟨E,ok,_,minDegree⟩ := one_arc_return_budget clean wu yu neq wy back near floor budget
    exact no E U ⟨w,wu⟩ size.le ok minDegree
  have split := card_sdiff_add_card_inter T A
  rw [←sets]
  change returnOverlap D U p w x = (U \ insert p ((A∪outN D U x)∪outN D U w)).card+2 at n
  omega

/-- Specialization on a common-target bank, identifying the original
degree of every forced payer as exactly one above quota. -/
theorem bank_return_spent_budget {D H : CH.Digraph} {V B : Finset ℕ} {p w x y t : ℕ}
    (safe : QFree D V 3) (reg : OutEq (t+1) D V) (bv : B⊆V)
    (pu : p∈V\B) (wu : w∈V\B) (xu : x∈V\B) (common : ∀ b∈B, D b p=true)
    (pw : D p w=true) (wx : D w x=true) (size : (V\B).card=3*t) (hits : (outN D B x).card=2)
    (ym : y∈outN D (V\B) p ∩ outN D (V\B) x)
    (clean : QFree H (V\B) 3) (no : BypassRepair.NoHost 3 t)
    (near : t≤(outN H (V\B) w).card+1)
    (floor : ∀ i∈V\B, i≠w → t≤(outN H (V\B) i).card)
    (yOld : outN H (V\B) y ⊆ outN D (V\B) y) (wOld : inN H (V\B) w ⊆ inN D (V\B) w)
    (wy : H w y≠true) :
    let U := V\B
    (outN H U y).card+2 < t+(((outN H U y ∩ inN H U w) ∩ outN D U p).filter
        (fun z => (outN H U z).card=t ∧ (outN D U z).card=t+1)).card + returnOverlap D U p w x := by
  classical
  intro U
  have uv : U⊆V := sdiff_subset
  have split (i) (iu : i∈U) : (outN D B i).card + (outN D U i).card=t+1 := by
    have h := card_outN_union (D:=D) (show Disjoint B U from disjoint_sdiff) i
    rw [union_sdiff_of_subset bv,reg _ (uv iu)] at h
    omega
  have none {i} (abs : ∀ b∈B, D i b≠true) : outN D B i=∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro b h
    exact abs b (outN_subset h) (mem_outN.mp h).2
  have np := split p pu
  rw [none (fun b bb => digonfree safe (by decide) (bv bb) (uv pu) (common b bb)),card_empty,zero_add] at np
  have full (z) (zm : z∈outN D U p) : (outN D U z).card=t+1 := by
    obtain ⟨zu,pz⟩ := mem_outN.mp zm
    have h := split z zu
    rw [none (fun b bb zb => safe b 3 (by decide) (by decide)
      (.step (uv pu) (common b bb) (.step (uv zu) pz (.step (bv bb) zb (.refl _))))),card_empty,zero_add] at h
    exact h
  have nx := split x xu
  have budget := return_spent_budget (safe.mono_set uv) pu wu xu pw wx size np
    (full w (mem_outN.mpr ⟨wu,pw⟩)) (by omega) ym clean no near floor yOld wOld wy
  apply lt_of_lt_of_le budget
  apply Nat.add_le_add_right
  apply Nat.add_le_add_left
  apply card_le_card
  intro z zm
  obtain ⟨mem,tight⟩ := mem_filter.mp zm
  exact mem_filter.mpr ⟨mem,tight,full z (mem_inter.mp mem).2⟩

/-- Every other predecessor of w missed by p consumes one of the exterior
positions, regardless of any choices of cuts. -/
theorem return_predecessor_budget {D : CH.Digraph} {U : Finset ℕ} {p w x t : ℕ}
    (safe : QFree D U 3) (pu : p∈U) (wu : w∈U) (xu : x∈U)
    (pw : D p w=true) (wx : D w x=true) (size : U.card=3*t)
    (np : (outN D U p).card=t+1) (nw : (outN D U w).card=t+1)
    (nx : (outN D U x).card+1=t)
    :
    (((inN D U w).erase p) \ outN D U p).card+2 ≤ returnOverlap D U p w x := by
  classical
  obtain ⟨n,_⟩ := return_pool_count safe pu wu xu pw wx size np nw nx
  rw [n]
  apply Nat.add_le_add_right
  apply card_le_card
  intro q qm
  obtain ⟨er,off⟩ := mem_sdiff.mp qm
  obtain ⟨qp,inc⟩ := mem_erase.mp er
  obtain ⟨qu,qw⟩ := mem_inN.mp inc
  have b : q∉outN D U w := fun h => digonfree safe (by decide) qu wu qw (mem_outN.mp h).2
  have c : q∉outN D U x := fun h => safe q 3 (by decide) (by decide)
    (.step wu qw (.step xu wx (.step qu (mem_outN.mp h).2 (.refl _))))
  exact mem_sdiff.mpr ⟨qu,by simp [qp,off,b,c]⟩

/-- On one middle w, minimum overlap two can belong to at most one
starting vertex, even when the short endpoints differ. -/
theorem exact_two_owner_unique {D : CH.Digraph} {U : Finset ℕ} {p q w : ℕ}
    (safe : QFree D U 3) (pu : p∈U) (qu : q∈U) (pw : D p w=true) (qw : D q w=true)
    (atP : (((inN D U w).erase p) \ outN D U p).card=0)
    (atQ : (((inN D U w).erase q) \ outN D U q).card=0) : p=q := by
  classical
  by_contra ne
  have hit {a b : ℕ} (ab : a≠b) (bu : b∈U) (bw : D b w=true)
      (empty : (((inN D U w).erase a) \ outN D U a).card=0) : D a b=true := by
    by_contra off
    have m : b ∈ ((inN D U w).erase a) \ outN D U a :=
      mem_sdiff.mpr ⟨mem_erase.mpr ⟨ab.symm,mem_inN.mpr ⟨bu,bw⟩⟩,fun h => off (mem_outN.mp h).2⟩
    exact (notMem_empty b) (card_eq_zero.mp empty ▸ m)
  exact digonfree safe (by decide) pu qu (hit ne qu qw atP) (hit (Ne.symm ne) pu pw atQ)

#print axioms return_predecessor_budget
#print axioms exact_two_owner_unique

#print axioms bank_return_spent_budget

#print axioms return_pool_count
#print axioms return_spent_budget
end LeanCH.BR.TripleBank
