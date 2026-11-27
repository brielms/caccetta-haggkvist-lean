import checkpoints.shen_extension.ThreeTightParents

/-! Replacing the lone deficient row by a vertex with fixed incoming rows.
On a saturated carrier the same bound survives a promotion. -/
namespace LeanCH.BR.TripleBank
open Finset BRq2 BRq3 BR45

def neutral (D : CH.Digraph) (U H : Finset ℕ) (c : ℕ) : Finset ℕ :=
  ((U.erase c) \ H).filter (fun v => Disjoint (outN D U v) H)

/-- All old heads and all additionally affordable heads together have fewer
than t labels. This also bounds the heads of a fresh replacement for c. -/
theorem affordable_bound {D : CH.Digraph} {U : Finset ℕ} {c t : ℕ}
    (safe : QFree D U 3) (cu : c ∈ U) (small : U.card ≤ 3*t)
    (no : BypassRepair.NoHost 3 t)
    (others : ∀ v ∈ U, v ≠ c → t ≤ (outN D U v).card) :
    let H := tightParents D U c t
    ((U.erase c).filter (fun v => t ≤ (outN D U v \ insert c H).card)).card < t := by
  classical
  intro H
  have inc : (U.erase c).filter (fun v => t ≤ (outN D U v \ insert c H).card) ⊆
      outN D U c ∪ fullMenu D U c t := by
    intro v vm
    obtain ⟨ve,room⟩ := mem_filter.mp vm
    by_cases old : v ∈ outN D U c
    · exact mem_union_left _ old
    · exact mem_union_right _ (mem_filter.mpr ⟨mem_sdiff.mpr ⟨ve,old⟩,room⟩)
  exact lt_of_le_of_lt ((card_le_card inc).trans (card_union_le _ _))
    (full_menu_obstruction safe cu small no others)

/-- Law R on a survivor set on which every row other than c meets the floor. -/
theorem neutral_bound {D : CH.Digraph} {U : Finset ℕ} {c t : ℕ}
    (safe : QFree D U 3) (cu : c ∈ U) (small : U.card ≤ 3*t)
    (no : BypassRepair.NoHost 3 t)
    (others : ∀ v ∈ U, v ≠ c → t ≤ (outN D U v).card) :
    (neutral D U (tightParents D U c t) c).card < t := by
  classical
  let H := tightParents D U c t
  apply lt_of_le_of_lt (card_le_card ?_) (affordable_bound safe cu small no others)
  intro v vm
  obtain ⟨base,off⟩ := mem_filter.mp vm
  obtain ⟨ve,vh⟩ := mem_sdiff.mp base
  obtain ⟨vc,vu⟩ := mem_erase.mp ve
  have row : outN D U v \ insert c H = (outN D U v).erase c := by
    ext w
    simp only [mem_sdiff,mem_insert,mem_erase]
    have absent (wm : w ∈ outN D U v) : w ∉ H := disjoint_left.mp off wm
    tauto
  refine mem_filter.mpr ⟨ve,?_⟩
  rw [row]
  by_cases cm : c ∈ outN D U v
  · have more : t < (outN D U v).card := by
      by_contra! low
      exact vh (mem_filter.mpr ⟨mem_inN.mpr ⟨vu,(mem_outN.mp cm).2⟩,low⟩)
    rw [card_erase_of_mem cm]; omega
  · rw [erase_eq_of_notMem cm]; exact others v vu vc

/-- If L already occupies t-1 neutral positions, dropping one payable
parent creates no additional neutral position, even in the original graph. -/
theorem neutral_after_promotion {D : CH.Digraph} {U L : Finset ℕ} {a c k t : ℕ}
    (safe : QFree D U 3) (cu : c ∈ U) (ku : k ∈ U) (ck : D c k = true)
    (small : U.card ≤ 3*t) (no : BypassRepair.NoHost 3 t)
    (others : ∀ v ∈ U, v ≠ c → t ≤ (outN D U v).card)
    (parent : a ∈ tightParents D U c t) (miss : D a k ≠ true)
    (spare : ∀ w ∈ outN D U k, t < (outN D U w).card)
    (sat : L.card+1 = t) (clear : L ⊆ neutral D U (tightParents D U c t) c) :
    neutral D U ((tightParents D U c t).erase a) c = L := by
  classical
  let H := tightParents D U c t
  obtain ⟨E,ok,floor,new,_,edges⟩ := promote_parent_with_edges safe cu ku ck parent miss spare others
  have kh : k ∉ H := fun h => digonfree safe (by decide) cu ku ck
    (mem_inN.mp (mem_filter.mp h).1).2
  have inc : neutral D U (H.erase a) c ⊆ neutral E U (tightParents E U c t) c := by
    rw [new]
    intro v vm
    obtain ⟨base,old⟩ := mem_filter.mp vm
    refine mem_filter.mpr ⟨base,disjoint_left.mpr ?_⟩
    intro w wm wh
    obtain ⟨wu,vw⟩ := mem_outN.mp wm
    rcases edges v w vw with ed | ⟨_,eq⟩
    · exact disjoint_left.mp old (mem_outN.mpr ⟨wu,ed⟩) wh
    · exact kh (eq ▸ (mem_erase.mp wh).2)
  have orig : L ⊆ neutral D U (H.erase a) c := by
    intro v vm
    obtain ⟨base,old⟩ := mem_filter.mp (clear vm)
    obtain ⟨ve,off⟩ := mem_sdiff.mp base
    exact mem_filter.mpr ⟨mem_sdiff.mpr ⟨ve,fun m => off (mem_erase.mp m).2⟩,
      old.mono_right (erase_subset _ _)⟩
  have lim := lt_of_le_of_lt (card_le_card inc) (neutral_bound ok cu small no floor)
  exact (eq_of_subset_of_card_le orig (by omega)).symm

/-- Every individually promotable tight parent has an outgoing arc to
another tight parent whenever the neutral positions are saturated. -/
theorem parent_has_successor {D : CH.Digraph} {U L : Finset ℕ} {a c k t : ℕ}
    (safe : QFree D U 3) (cu : c ∈ U) (ku : k ∈ U) (ck : D c k = true)
    (small : U.card ≤ 3*t) (no : BypassRepair.NoHost 3 t)
    (others : ∀ v ∈ U, v ≠ c → t ≤ (outN D U v).card)
    (parent : a ∈ tightParents D U c t) (miss : D a k ≠ true)
    (spare : ∀ w ∈ outN D U k, t < (outN D U w).card)
    (sat : L.card+1 = t) (clear : L ⊆ neutral D U (tightParents D U c t) c) :
    ∃ h ∈ (tightParents D U c t).erase a, D a h = true := by
  classical
  have eq := neutral_after_promotion safe cu ku ck small no others parent miss spare sat clear
  obtain ⟨au,ac⟩ := mem_inN.mp (mem_filter.mp parent).1
  have nc : a ≠ c := fun e => loopfree safe (by decide) cu (e ▸ ac)
  by_contra! noEdges
  have am : a ∈ neutral D U ((tightParents D U c t).erase a) c := mem_filter.mpr
    ⟨mem_sdiff.mpr ⟨mem_erase.mpr ⟨nc,au⟩,notMem_erase _ _⟩,
     disjoint_left.mpr (fun v vm vh => noEdges v vh (mem_outN.mp vm).2)⟩
  exact (mem_sdiff.mp (mem_filter.mp (clear (eq ▸ am))).1).2 parent

/-- The missed common target fills the last neutral position on the actual
three-hit frontier. The inherited common head has full surviving successors. -/
theorem bank_saturation {D : CH.Digraph} {V B P : Finset ℕ} {s c : ℕ}
    (safe : QFree D V 3) (reg : OutEq s D V) (hs : 3 ≤ s) (order : V.card = 3*s)
    (no : BypassRepair.NoHost 3 (s-1)) (sub : B ⊆ V) (three : B.card = 3)
    (pv : P ⊆ V) (many : 2 ≤ P.card) (common : ∀ b ∈ B, P ⊆ outN D V b)
    (cu : c ∈ V \ B) (hits : (outN D B c).card = 3)
    (lone : ∀ a ∈ V \ B, a ≠ c → (outN D B a).card ≤ 1)
    (menu : (rowMenu D (V \ B) P c).card ≤ 1) (miss : ∃ z ∈ P, D c z ≠ true) :
    let U := V \ B
    let H := tightParents D U c (s-1)
    ∃ z ∈ P, D c z ≠ true ∧
      let L := insert z (outN D U c)
      L.card + 1 = s-1 ∧ neutral D U H c = L ∧ (∀ v ∈ L, D v c ≠ true) ∧
      (∀ v ∈ U, v ≠ c → s-1 ≤ (outN D U v).card) ∧
      ∃ k ∈ P, k ∈ L ∧ k ∈ U ∧ D c k = true ∧
        ∀ w ∈ outN D U k, (outN D U w).card = s := by
  classical
  intro U H
  obtain ⟨z,zp,cz⟩ := miss
  have cv := (mem_sdiff.mp cu).1
  have split (a) (au : a ∈ U) : (outN D U a).card + (outN D B a).card = s := by
    have h := card_outN_union (D := D) (show Disjoint B U from disjoint_sdiff) a
    rw [union_sdiff_of_subset sub,reg a (mem_sdiff.mp au).1] at h
    omega
  have others (a) (au : a ∈ U) (ac : a ≠ c) : s-1 ≤ (outN D U a).card := by
    have h := split a au
    have l := lone a au ac
    omega
  have size : U.card = 3*(s-1) := by
    change (V \ B).card = _; rw [card_sdiff_of_subset sub,order,three]; omega
  have inside {k} (kp : k ∈ P) : k ∈ U := mem_sdiff.mpr ⟨pv kp,fun kb =>
    loopfree safe (by decide) (pv kp) (mem_outN.mp (common k kb kp)).2⟩
  have via {a} (av : a ∈ V) (hit : (outN D B a).Nonempty) {k} (kp : k ∈ P) :
      a ≠ k ∧ D k a ≠ true := by
    obtain ⟨b,bm⟩ := hit
    obtain ⟨bb,ab⟩ := mem_outN.mp bm
    have bk := (mem_outN.mp (common b bb kp)).2
    exact ⟨fun e => digonfree safe (by decide) av (sub bb) ab (e ▸ bk),
      fun ka => safe a 3 (by decide) (by decide)
        (.step (sub bb) ab (.step (pv kp) bk (.step av ka (.refl _))))⟩
  have cHit := card_pos.mp (show 0 < (outN D B c).card by omega)
  obtain ⟨nc,zc⟩ := via cv cHit zp
  have nz : z ∉ outN D U c := fun m => cz (mem_outN.mp m).2
  have count : (insert z (outN D U c)).card + 1 = s-1 := by
    rw [card_insert_of_notMem nz]
    have h := split c cu
    omega
  have clear : insert z (outN D U c) ⊆ neutral D U H c := by
    intro v vm
    rcases mem_insert.mp vm with eq | head
    · subst v
      refine mem_filter.mpr ⟨mem_sdiff.mpr ⟨mem_erase.mpr ⟨nc.symm,inside zp⟩,
        fun zh => zc (mem_inN.mp (mem_filter.mp zh).1).2⟩,disjoint_left.mpr ?_⟩
      intro h hm hh
      obtain ⟨par,cap⟩ := mem_filter.mp hh
      obtain ⟨hu,_⟩ := mem_inN.mp par
      have eq := split h hu
      have hit := card_pos.mp (show 0 < (outN D B h).card by omega)
      exact (via (mem_sdiff.mp hu).1 hit zp).2 (mem_outN.mp hm).2
    · obtain ⟨vu,ed⟩ := mem_outN.mp head
      have vv := (mem_sdiff.mp vu).1
      refine mem_filter.mpr ⟨mem_sdiff.mpr ⟨mem_erase.mpr
        ⟨fun e => loopfree safe (by decide) cv (e ▸ ed),vu⟩,
        fun vh => digonfree safe (by decide) cv vv ed (mem_inN.mp (mem_filter.mp vh).1).2⟩,
        disjoint_left.mpr ?_⟩
      intro h hm hh
      obtain ⟨hu,hc⟩ := mem_inN.mp (mem_filter.mp hh).1
      exact safe c 3 (by decide) (by decide) (.step vv ed (.step (mem_sdiff.mp hu).1
        (mem_outN.mp hm).2 (.step cv hc (.refl _))))
  have lim := neutral_bound (safe.mono_set (sdiff_subset : U ⊆ V)) cu size.le no others
  change (neutral D U H c).card < s-1 at lim
  have noBack (v) (vm : v ∈ insert z (outN D U c)) : D v c ≠ true := by
    rcases mem_insert.mp vm with rfl | ed
    · exact zc
    · exact digonfree safe (by decide) cv (mem_sdiff.mp (outN_subset ed)).1 (mem_outN.mp ed).2
  refine ⟨z,zp,cz,count,(eq_of_subset_of_card_le clear (by omega)).symm,noBack,others,?_⟩
  have existsK : ∃ k ∈ P, D c k = true := by
    by_contra! absent
    have inc : P ⊆ rowMenu D U P c := fun k kp => mem_union_left _ (mem_sdiff.mpr
      ⟨kp,fun e => absent k kp (mem_outN.mp e).2⟩)
    have bound := (card_le_card inc).trans menu
    omega
  obtain ⟨k,kp,ck⟩ := existsK
  refine ⟨k,kp,mem_insert_of_mem (mem_outN.mpr ⟨inside kp,ck⟩),inside kp,ck,?_⟩
  intro w wm
  obtain ⟨wu,kw⟩ := mem_outN.mp wm
  have empty : outN D B w = ∅ := eq_empty_iff_forall_notMem.mpr (fun b bm =>
    (via (mem_sdiff.mp wu).1 ⟨b,bm⟩ kp).2 kw)
  have eq := split w wu
  simpa [empty] using eq

#print axioms bank_saturation
#print axioms neutral_bound
#print axioms neutral_after_promotion
#print axioms parent_has_successor
end LeanCH.BR.TripleBank
