import checkpoints.shen_extension.dot_tensor_research.DotDegreeSevenQ7RecipientPacking_20261121
import checkpoints.shen_extension.dot_tensor_research.DotDegreeSevenTwoEndpoints_20261121

namespace LeanCH.BR.DotDegreeSevenQ7
open Finset BRq2 BRq3 BR45

/-- The actual order-49 endpoint, on arbitrary finite labels with original
minimum outdegree at least seven. -/
theorem packed_endpoint_seven_seven : DotDegreeSeven.Endpoint 7 7 := by
  classical
  intro D V free ne hn degree
  obtain ⟨G,sub,ho⟩ := exists_outEq (G:=D) (V:=V) (s:=7) degree
  have hf := qfree_sub sub free
  have hm (v) (hv : v∈V) := (ho v hv).ge
  have profile (v) (hv : v∈V) := order49_exact_balls hf hm hn v hv
  have b2 (v) (hv : v∈V) := paired_profile_two hf ho hv (profile v hv).1 (profile v hv).2.1
  have b3 (v) (hv : v∈V) := (profile v hv).1
  obtain ⟨u,hu⟩ := ne
  let A := outN G V u
  let B := ball G V u 2 \ ball G V u 1
  let T := ball G V u 3 \ ball G V u 2
  have av : A⊆V := outN_subset
  have bv : B⊆V := fun _ mx=>ball_subset (mem_sdiff.mp mx).1
  have na : A.card=7 := ho _ hu
  have nb : B.card=8 := by
    have e := card_sdiff_add_card_eq_card (ball_mono_radius (D:=G) (W:=V) (u:=u) (by decide : 1≤2))
    change B.card+_= _ at e
    rw [card_B1 (hf.mono_bound (by decide : 4≤7)) hu,ho u hu,b2 u hu] at e
    omega
  have nt : T.card=6 := by
    have e := card_sdiff_add_card_eq_card (ball_mono_radius (D:=G) (W:=V) (u:=u) (by decide : 2≤3))
    change T.card+_= _ at e
    rw [b2 u hu,b3 u hu] at e
    omega
  have one (s) (sa : s∈A) (ss : Packing.Sink G A s) : ∃b∈B,outN G V s=B.erase b := by
    have s1 := (mem_ball_one hu).2 (Or.inr sa)
    have inc : outN G V s⊆B := by
      intro z zm
      obtain ⟨zv,sz⟩ := mem_outN.mp zm
      refine mem_sdiff.mpr ⟨ball_step s1 zv sz,?_⟩
      intro z1
      rcases (mem_ball_one hu).1 z1 with rfl|za
      · exact no_back_arc hf hu s1 (by decide : 1+1≤7) sz
      · exact ss z za sz
    have size := ho s (av sa)
    have c := card_sdiff_add_card_eq_card inc
    obtain ⟨b,bm⟩ := card_pos.mp (show 0<(B\outN G V s).card by omega)
    obtain ⟨bb,bn⟩ := mem_sdiff.mp bm
    refine ⟨b,bb,eq_of_subset_of_card_le (fun z hz=>mem_erase.mpr ⟨fun e=>bn (e ▸ hz),inc hz⟩) ?_⟩
    rw [card_erase_of_mem bb,nb,size]
  have row (b) (bm : b∈B) : outN G V b⊆(A∪B)∪T := by
    intro z zm
    obtain ⟨zv,bz⟩ := mem_outN.mp zm
    have b2u := (mem_sdiff.mp bm).1
    have z3 := ball_step b2u zv bz
    by_cases z2 : z∈ball G V u 2
    · apply mem_union_left
      by_cases z1 : z∈ball G V u 1
      · rcases (mem_ball_one hu).1 z1 with rfl|za
        · exact (no_back_arc hf hu b2u (by decide : 2+1≤7) bz).elim
        · exact mem_union_left _ za
      · exact mem_union_right _ (mem_sdiff.mpr ⟨z2,z1⟩)
    · exact mem_union_right _ (mem_sdiff.mpr ⟨z3,z2⟩)
  obtain ⟨s,sa,ss⟩ := exists_sink (T:=A) (hf.mono_set av) (card_pos.mp (by omega)) na.le
  by_cases unique : ∀t∈A, Packing.Sink G A t → t=s
  · exact paired_profile_no_unique_sink hf ho hu b2 b3 (profile u hu).2.1 sa ss unique
  · push Not at unique
    obtain ⟨t,ta,ts,ts'⟩ := unique
    exact Packing.two_sinks_false hf av bv na nb nt sa ta ts'.symm ss ts one row
      (fun v vm=>(b2 v (av vm)).ge)

#print axioms packed_endpoint_seven_seven
end LeanCH.BR.DotDegreeSevenQ7

namespace LeanCH.BR.DotDegreeSeven
theorem ch_seven_of_order35 (five : Endpoint 5 7) (n : ℕ) (D : CH.Digraph)
    (hn : 0<n) (loop : CH.Loopless D n) (degree : CH.MinOutdegreeAtLeast D n 7) :
    CH.HasDirectedCycleAtMost D n (CH.ceilDiv n 7) :=
  ch_seven_of_two_endpoints five DotDegreeSevenQ7.packed_endpoint_seven_seven n D hn loop degree
#print axioms ch_seven_of_order35
end LeanCH.BR.DotDegreeSeven
