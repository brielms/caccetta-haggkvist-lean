import checkpoints.shen_extension.MixedContactBill

namespace LeanCH.BR.LowShellCycleSelection
open Finset BRq2 BRq3 BR45 BRsGen ExteriorPacking PhysicalCycleStock
open scoped Classical

/-- Inclusion on one layer propagates to every later layer. Across a
native arc the parent itself makes the inclusion strict up to the cutoff. -/
theorem strict_ball_after_contact {D V q a b s k} (free : QFree D V q) (av : a∈V)
    (bv : b∈V) (arc : D a b=true) (included : ball D V b s⊆ball D V a s)
    (later : s≤k) (short : k+1≤q) : (ball D V b k).card<(ball D V a k).card := by
  have expand j (atJ : ball D V b j⊆ball D V a j) : ball D V b (j+1)⊆ball D V a (j+1) := by
    intro z zm
    by_cases old : z∈ball D V b j
    · exact ball_mono_radius (Nat.le_succ j) (atJ old)
    obtain ⟨y,ym,edge⟩ := ball_succ_pred bv zm old
    exact ball_step (atJ ym) (ball_subset zm) edge
  have sub : ball D V b k⊆ball D V a k := by
    clear short
    induction k, later using Nat.le_induction with
    | base => exact included
    | succ j _ ih => exact expand j ih
  apply card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨sub,?_⟩)
  intro eq
  have seen : a∈ball D V b k := eq.symm ▸ self_mem_ball av
  obtain ⟨_,d,cap,road⟩ := mem_ball.mp seen
  exact free a _ (by omega) (by omega) (.step bv arc road)

/-- One exceptional bank label can be recognized from any contacting pair
of primary origins. If the others cannot target the cycle or that exception,
the pair has strictly decreasing ball sizes at every admissible horizon. -/
theorem contact_through_exception {D V q r C d a b k} (free : QFree D V q) (hq : 4≤q)
    (reg : OutEq r D V) (av : a∈V) (bv : b∈V) (first : C⊆outN D V a)
    (also : C⊆outN D V b) (contact : privateHeads D V C a={b})
    (bank : N2 D V a=exterior D V C) (slots : (outN D V a\C).card≤1)
    (other : (outN D V b\C).card≤1) (second : (N2 D V b).card≤r)
    (dm : d∈exterior D V C) (sealed : outN D V d⊆C∪exterior D V C)
    (guard : ∀z∈exterior D V C,z≠d → (∀v∈C,D z v≠true) ∧ D z d≠true)
    (lo : 2≤k) (hi : k+1≤q) : (ball D V b k).card<(ball D V a k).card := by
  classical
  let E := exterior D V C
  let Xa := outN D V a
  let Xb := outN D V b
  have privateB : b∈privateHeads D V C a := contact.symm ▸ mem_singleton_self b
  have bx := (mem_sdiff.mp (mem_sdiff.mp privateB).1).1
  have bc := (mem_sdiff.mp (mem_sdiff.mp privateB).1).2
  have xy : Xa\C={b} := eq_of_subset_of_card_le (by
    intro z zm
    have m := card_le_one.mp slots z zm b (mem_sdiff.mp privateB).1
    exact mem_singleton.mpr m) (by rw [card_singleton]; exact card_pos.mpr ⟨b,(mem_sdiff.mp privateB).1⟩)
  have xe : Xb⊆insert d C := by
    intro w wm
    by_cases wc : w∈C
    · exact mem_insert_of_mem wc
    by_cases wd : w=d
    · exact mem_insert.mpr (.inl wd)
    have late := headX (free.mono_bound hq) av bx (outN_subset wm) (mem_outN.mp wm).2
    have we : w∈E := by
      rcases mem_union.mp late with old|y
      · have ex : w∈Xa\C := mem_sdiff.mpr ⟨old,wc⟩
        rw [xy,mem_singleton] at ex
        subst w
        exact (loopfree free (by omega) bv (mem_outN.mp wm).2).elim
      · exact (show w∈exterior D V C from bank ▸ y)
    have gx := guard w we wd
    have dw : d∉Xb\C := fun m=>wd (card_le_one.mp other w (mem_sdiff.mpr ⟨wm,wc⟩) d m)
    have dy := (mem_union.mp (exterior_subset_menu free hq bv also dm)).resolve_left dw
    have row : outN D V w⊆N2 D V b := by
      intro v vm
      rcases mem_union.mp (headX (free.mono_bound hq) bv wm (outN_subset vm) (mem_outN.mp vm).2) with head|next
      · by_cases vc : v∈C
        · exact (gx.1 v vc (mem_outN.mp vm).2).elim
        have same := card_le_one.mp other v (mem_sdiff.mpr ⟨head,vc⟩) w (mem_sdiff.mpr ⟨wm,wc⟩)
        subst v
        exact (loopfree free (by omega) (outN_subset wm) (mem_outN.mp vm).2).elim
      · exact next
    have equality := eq_of_subset_of_card_le row (by rw [reg _ (outN_subset wm)]; exact second)
    exact (gx.2 (mem_outN.mp (equality.symm ▸ dy)).2).elim
  have near : C∪E⊆ball D V a 2 := by
    intro x xm
    rcases mem_union.mp xm with xc|ex
    · exact ball_mono_radius (by decide : 1≤2) (X_B1 (first xc))
    · exact (mem_N2.mp (bank.symm ▸ ex)).1
  apply strict_ball_after_contact free av bv (mem_outN.mp bx).2 (s:=2) _ lo hi
  intro v vm
  by_cases old : v∈ball D V b 1
  · rcases (mem_ball_one bv).mp old with eq|head
    · exact eq ▸ ball_mono_radius (by decide : 1≤2) (X_B1 bx)
    rcases mem_insert.mp (xe head) with eq|vc
    · exact eq ▸ near (mem_union_right _ dm)
    · exact near (mem_union_left _ vc)
  obtain ⟨x,step,arc⟩ := ball_succ_pred bv vm old
  rcases (mem_ball_one bv).mp step with eq|head
  · subst x
    exact (old ((mem_ball_one bv).mpr (.inr (mem_outN.mpr ⟨ball_subset vm,arc⟩)))).elim
  rcases mem_insert.mp (xe head) with eq|xc
  · exact near (sealed (mem_outN.mpr ⟨ball_subset vm,eq ▸ arc⟩))
  by_cases vc : v∈C
  · exact near (mem_union_left _ vc)
  exact near (mem_union_right _ (mem_sdiff.mpr ⟨mem_biUnion.mpr ⟨x,xc,mem_outN.mpr ⟨ball_subset vm,arc⟩⟩,vc⟩))

#print axioms strict_ball_after_contact
#print axioms contact_through_exception
end LeanCH.BR.LowShellCycleSelection
