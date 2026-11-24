import checkpoints.shen_extension.dot_tensor_research.DotDegreeSevenQ5BankPropagation_20261121
import checkpoints.shen_extension.dot_tensor_research.DotDegreeSevenQ5EndpointSeam_20261121

namespace LeanCH.BR.DotDegreeSevenLow
open Finset BRq2 BRq3 BR45 BRsGen

theorem exact_endpoint_cards {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V 5) (ho : OutEq 7 D V) (n : V.card=35)
    (noLow : ∀ v∈V, 15≤(ball D V v 2).card) :
    ∀ v∈V, (ball D V v 2).card=15 ∧ (ball D V v 3).card=21 := by
  have hm : ∀ v∈V, 7≤(outN D V v).card := fun v hv => (ho v hv).ge
  have lo (v) (hv : v∈V) : 21≤(ball D V v 3).card := by
    have b := floor_three20 hf hm hv
    by_contra! h
    have e : (ball D V v 3).card=20 := by omega
    have wrong := tight_three_only_tight_two hf ho hv e
    have a := noLow v hv
    omega
  intro v hv
  exact ⟨(two_balls_boundary_cards hf (by decide : 2+3≤5) noLow lo (by omega) v hv).1,
    (two_balls_boundary_cards hf (by decide : 3+2≤5) lo noLow (by omega) v hv).1⟩

/-- At the exact endpoint, a nonempty sufficiently small retained bank
whose entire external head set fits in six spill labels is impossible. -/
theorem exact_endpoint_no_supported_bank {D : CH.Digraph} {V B T : Finset ℕ}
    (hf : QFree D V 5) (ho : OutEq 7 D V) (n : V.card≤35)
    (cap : ∀ v∈V, (ball D V v 2).card≤15)
    (bV : B⊆V) (tV : T⊆V) (disj : Disjoint B T)
    (bne : B.Nonempty) (b6 : B.card≤6) (t6 : T.card≤6)
    (keep : ∀ b∈B, outN D V b⊆B∪T) : False := by
  classical
  have sum (b) (hb : b∈B) : 7=(outN D B b).card+(outN D T b).card := by
    have e : outN D V b=outN D (B∪T) b := by
      ext x
      simp only [mem_outN]
      exact ⟨fun h => ⟨keep b hb (mem_outN.mpr h),h.2⟩,
        fun h => ⟨union_subset bV tV h.1,h.2⟩⟩
    rw [← card_outN_union disj,←e,ho b (bV hb)]
  have md (b) (hb : b∈B) : 1≤(outN D B b).card := by
    have e := sum b hb
    have k := card_le_card (outN_subset (D:=D) (W:=T) (y:=b))
    omega
  obtain ⟨b,hb⟩ := bne
  have cb : B.card=6 := by
    by_contra h
    obtain ⟨z,hz,hs⟩ := exists_sink (hf.mono_set bV) ⟨b,hb⟩ (show B.card≤5 by omega)
    obtain ⟨x,hx⟩ := card_pos.mp (md z hz)
    exact hs x (mem_outN.mp hx).1 (mem_outN.mp hx).2
  have one : OutEq 1 D B := (dt_reg (by decide : 1≤5) (ball_q_one 5 (by decide))
    (hf.mono_set bV) md (by simpa only [Nat.mul_one,Nat.reduceAdd] using cb)).1
  have full (x) (hx : x∈B) : (outN D T x).card=6 := by
    have e := sum x hx
    rw [one x hx] at e
    omega
  have ct : T.card=6 := by
    have e := card_le_card (outN_subset (D:=D) (W:=T) (y:=b))
    rw [full b hb] at e
    omega
  apply no_spill_bank_at35 hf ho n cap ⟨bV,tV,cb,ct,disj,one,keep,?_⟩
  intro x hx y hy
  have e : outN D T x=T := eq_of_subset_of_card_le outN_subset (by rw [ct,full x hx])
  exact (mem_outN.mp (e.symm ▸ hy)).2

#print axioms exact_endpoint_cards
#print axioms exact_endpoint_no_supported_bank

end LeanCH.BR.DotDegreeSevenLow

