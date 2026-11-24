
import LeanCH.BR.BRAcyclicPair
import checkpoints.shen_extension.dot_tensor_research.DotDegreeSixQ4EscortTransfer_20261121

namespace LeanCH.BR.DotDegreeSix
open Finset BRq2 BRq3 BR45 BRsGen
set_option maxHeartbeats 1000000

/-- On six labels a 5-free graph is acyclic or an induced spanning 6-cycle. -/
theorem six_acyclic_or_cycle {D : CH.Digraph} {X : Finset ℕ}
    (hf : QFree D X 5) (hc : X.card=6) : QFree D X 6 ∨ OutEq 1 D X := by
  by_cases a : QFree D X 6
  · exact Or.inl a
  right
  unfold QFree at a
  push Not at a
  obtain ⟨u,k,kp,kl,w⟩ := a
  have k6 : k=6 := by by_contra n; exact hf u k kp (by omega) w
  subst k
  obtain ⟨M,hMX,hM,hm⟩ := boundary_closed_walk_support hf w
  have eq : M=X := eq_of_subset_of_card_le hMX (by omega)
  subst M
  exact (dt_reg (by decide : 1≤5) (ball_q_one 5 (by decide)) hf hm (by omega)).1

theorem cyclic_return_unique {D : CH.Digraph} {X Y : Finset ℕ}
    (hf : QFree D (X∪Y) 5) (hx : X.card=6) (hy : Y.card=6)
    (dis : Disjoint X Y) (cy : OutEq 1 D X)
    (keep : ∀ x∈X, 6≤(outN D (X∪Y) x).card)
    {b c : ℕ} (byy : b∈Y) (cyy : c∈Y)
    (rb : (outN D X b).Nonempty) (rc : (outN D X c).Nonempty) : b=c := by
  have cap (y) (hy : y∈Y) (ry : (outN D X y).Nonempty) :
      (inN D X y).card≤2 := by
    by_cases pr : (inN D X y).Nonempty
    · have r := BRsub.cycle_two_sided_contact_cap (by decide : 2≤5) hf subset_union_left
        hx cy (mem_union_right _ hy) pr ry
      have := card_pos.mpr ry
      omega
    · rw [not_nonempty_iff_eq_empty.mp pr]
      decide
  by_contra ne
  let P := inN D X b ∪ inN D X c
  have pb := cap b byy rb
  have pc := cap c cyy rc
  have p4 : P.card≤4 := (card_union_le _ _).trans (by omega)
  have xx : (X\P).Nonempty := by
    by_contra h
    have cnt := card_le_card (sdiff_eq_empty_iff_subset.mp (not_nonempty_iff_eq_empty.mp h) : X⊆P)
    omega
  obtain ⟨x,xp⟩ := xx
  obtain ⟨xx,n⟩ := mem_sdiff.mp xp
  have ny : outN D Y x ⊆ (Y.erase b).erase c := by
    intro y yx
    obtain ⟨yy,xy⟩ := mem_outN.mp yx
    refine mem_erase.mpr ⟨?_,mem_erase.mpr ⟨?_,yy⟩⟩
    · rintro rfl
      exact n (mem_union_right _ (mem_inN.mpr ⟨xx,xy⟩))
    · rintro rfl
      exact n (mem_union_left _ (mem_inN.mpr ⟨xx,xy⟩))
  have cardb := card_le_card ny
  rw [card_erase_of_mem (mem_erase.mpr ⟨Ne.symm ne,cyy⟩),card_erase_of_mem byy,hy] at cardb
  have hc := card_outN_union (D:=D) dis x
  rw [cy x xx] at hc
  have := keep x xx
  omega

/-- Middle rows with two surviving heads cannot fit in a six-by-six prefix. -/
theorem six_by_six_not_min_two {D : CH.Digraph} {X Y : Finset ℕ}
    (hf : QFree D (X∪Y) 5) (hx : X.card=6) (hy : Y.card=6)
    (dis : Disjoint X Y)
    (keep : ∀ x∈X, 6≤(outN D (X∪Y) x).card)
    (mid : ∀ y∈Y, 2≤(outN D (X∪Y) y).card) : False := by
  classical
  by_cases ret : ∃ b∈Y, (outN D X b).Nonempty
  · obtain ⟨b,byy,rb⟩ := ret
    have no (c) (hc : c∈Y.erase b) : outN D X c = ∅ := by
      by_contra! hz
      have rc := hz
      rcases six_acyclic_or_cycle (hf.mono_set subset_union_left) hx with ac | cy
      · obtain ⟨a,ha⟩ := rb
        obtain ⟨ax,ba⟩ := mem_outN.mp ha
        obtain ⟨v,hv⟩ := rc
        obtain ⟨vx,cv⟩ := mem_outN.mp hv
        have f := acyclic_back_arc_others (s:=6) (by decide) hf ac dis hx hy keep ax byy ba
        exact f.2.1 c hc v vx cv
      · exact (mem_erase.mp hc).1 (cyclic_return_unique hf hx hy dis cy keep (mem_of_mem_erase hc) byy rc rb)
    have hmin (c) (hc : c∈Y.erase b) : 1≤(outN D (Y.erase b) c).card := by
      have hsum := card_outN_union (D:=D) dis c
      have hd := mid c (mem_of_mem_erase hc)
      rw [no c hc,card_empty,zero_add] at hsum
      have sub : outN D Y c⊆insert b (outN D (Y.erase b) c) := by
        intro z hz
        obtain ⟨zy,cz⟩ := mem_outN.mp hz
        by_cases e : z=b
        · simp [e]
        · exact mem_insert_of_mem (mem_outN.mpr ⟨mem_erase.mpr ⟨e,zy⟩,cz⟩)
      have k := (card_le_card sub).trans (card_insert_le _ _)
      omega
    have hY' : (Y.erase b).card=5 := by rw [card_erase_of_mem byy,hy]
    obtain ⟨c,hc,sc⟩ := exists_sink (T:=Y.erase b) (hf.mono_set ((erase_subset _ _).trans subset_union_right))
      (card_pos.mp (by omega)) (by omega)
    obtain ⟨z,hz⟩ := card_pos.mp (hmin c hc)
    exact sc z (mem_outN.mp hz).1 (mem_outN.mp hz).2
  · push Not at ret
    have m (y) (yy : y∈Y) : 2≤(outN D Y y).card := by
      have hsum := card_outN_union (D:=D) dis y
      have hd := mid y yy
      rw [ret y yy,card_empty,zero_add] at hsum
      omega
    have k := corB (D:=D) (U:=Y) (q:=5) (by decide) (hf.mono_set subset_union_right) m
      (card_pos.mp (by omega))
    omega

#print axioms six_by_six_not_min_two
end LeanCH.BR.DotDegreeSix


