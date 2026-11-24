import checkpoints.shen_extension.dot_tensor_research.DotDegreeSevenQ6EndpointConstructors_20261121
import checkpoints.shen_extension.dot_tensor_research.DotDegreeSevenQ6EndpointCyclic_20261121
import checkpoints.shen_extension.dot_tensor_research.DotDegreeSevenQ6EndpointAcyclic_20261121

namespace LeanCH.BR.DotDegreeSevenQ6
open Finset BRq2 BRq3 BR45 BRsGen

theorem no_return_of_ball_two15 {D : CH.Digraph} {V : Finset ℕ} {u : ℕ}
    (hf : QFree D V 6) (he : OutEq 7 D V) (hu : u∈V)
    (c2 : (ball D V u 2).card=15) (c3 : (ball D V u 3).card=21) :
    ∀ b ∈ ball D V u 2 \ ball D V u 1,
          ∀ a ∈ (ball D V u 1).erase u, D b a ≠ true := by
  let A := (ball D V u 1).erase u
  let B := ball D V u 2 \ ball D V u 1
  let T := ball D V u 3 \ ball D V u 2
  change ∀ b∈B,∀ a∈A,D b a ≠ true
  have c1 : (ball D V u 1).card=8 := by
    rw [card_B1 (hf.mono_bound (by decide : 4≤6)) hu,he u hu]
  have cA : A.card=7 := by
    simp only [A,card_erase_of_mem (self_mem_ball hu),c1]
  have h2 := card_sdiff_add_card_eq_card
    (ball_mono_radius (D:=D) (W:=V) (u:=u) (by decide : 1≤2))
  have h3 := card_sdiff_add_card_eq_card
    (ball_mono_radius (D:=D) (W:=V) (u:=u) (by decide : 2≤3))
  change B.card + _ = _ at h2
  change T.card + _ = _ at h3
  have cB : B.card=7 := by omega
  have cT : T.card=6 := by omega
  have hA : A⊆V := (erase_subset u _).trans ball_subset
  have hB : B⊆V := sdiff_subset.trans ball_subset
  have keepA a (ha : a∈A) : outN D V a ⊆ A∪B := by
    intro x hx
    change x∈(ball D V u 1).erase u ∪ (ball D V u 2 \ ball D V u 1)
    rw [←erase_ball_succ_eq_union (k:=1) hu]
    exact (mem_outN.mp (outN_prefix_erase_root hf hu (by decide : 1+1≤6) (mem_of_mem_erase ha) hx)).1
  have keepB b (hb : b∈B) : outN D V b ⊆ (A∪B)∪T := by
    intro x hx
    change x∈((ball D V u 1).erase u ∪ (ball D V u 2 \ ball D V u 1)) ∪ (ball D V u 3 \ ball D V u 2)
    rw [←erase_ball_succ_eq_union (k:=1) hu,←erase_ball_succ_eq_union (k:=2) hu]
    exact (mem_outN.mp (outN_prefix_erase_root hf hu (by decide : 2+1≤6) (mem_sdiff.mp hb).1 hx)).1
  by_cases ac : QFree D A 7
  · exact no_return_of_acyclic_first_bank hf he hA hB cA cB cT ac keepA keepB
  · unfold QFree at ac
    push Not at ac
    obtain ⟨a,k,hm,hk,w⟩ := ac
    have eq : k=7 := by
      by_contra hn
      exact (hf.mono_set hA) a k hm (by omega) w
    subst k
    have fa := hf.mono_set hA
    have mn : ∀ v∈A,1≤(outN D A v).card := fun v hv =>
      minOut_of_boundary_closed_walk fa (by omega : A.card=6+1) w v hv
    have reg := (dt_reg (q:=6) (by decide) (ball_q_one 6 (by decide)) fa mn (by omega)).1
    exact no_return_of_degree_one_first_bank hf he hA hB cA cB cT reg keepA keepB

#print axioms no_return_of_ball_two15
end LeanCH.BR.DotDegreeSevenQ6

