import checkpoints.shen_extension.dot_tensor_research.DotDegreeSevenQ5ExactSeven_20261121
import checkpoints.shen_extension.dot_tensor_research.DotDegreeSevenQ5ExactSixShape_20261121
import checkpoints.shen_extension.dot_tensor_research.DotDegreeSevenQ5EndpointAssemblyNoSink_20261121
import LeanCH.BR.BRShortestCycle

namespace LeanCH.BR.DotDegreeSevenLow
open Finset BRq2 BRq3 BR45 BRsGen

theorem exact_endpoint_all_large_impossible {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V 5) (ho : OutEq 7 D V) (n : V.card=35)
    (noLow : ∀ v∈V, 15≤(ball D V v 2).card) : False := by
  classical
  apply exact_endpoint_of_six_shapes hf ho n noLow
  intro u hu
  let A := EndpointLayer1 D V u
  have av : A⊆V := outN_subset
  have a7 : A.card=7 := ho u hu
  have aNe : A.Nonempty := card_pos.mp (by omega)
  have minA (z) (hz : z∈A) : 1≤(outN D A z).card := by
    by_contra h
    apply endpoint_first_layer_no_sink hf ho n noLow hu hz
    intro y hy e
    have yes : y∈outN D A z := mem_outN.mpr ⟨hy,e⟩
    have pos := card_pos.mpr (show (outN D A z).Nonempty from ⟨y,yes⟩)
    omega
  obtain ⟨p,C,hp,hfA,ca,cp,one⟩ :=
    exists_minimal_cycle_support (by decide : 1≤5) (hf.mono_set av) minA aNe
  have bound := card_le_card ca
  have p5 : p=5 := by
    by_contra h
    have p6 : p=6 := by omega
    have e : C=A := eq_of_subset_of_card_le ca (by omega)
    subst p
    subst C
    exact exact_endpoint_no_seven_layer hf ho n noLow hu hfA one
  have c6 : C.card=6 := by omega
  have diff : (A \ C).card=1 := by rw [card_sdiff_of_subset ca,a7,c6]
  obtain ⟨z,hz⟩ := card_eq_one.mp diff
  have zm : z∈A \ C := hz.symm ▸ mem_singleton_self _
  obtain ⟨za,zn⟩ := mem_sdiff.mp zm
  have az : A=insert z C := by
    ext x
    rw [mem_insert]
    constructor
    · intro hx
      by_cases hc : x∈C
      · exact Or.inr hc
      · have h : x∈A \ C := mem_sdiff.mpr ⟨hx,hc⟩
        rw [hz] at h
        exact Or.inl (mem_singleton.mp h)
    · rintro (rfl|h)
      · exact za
      · exact ca h
  refine ⟨C,z,az,zn,c6,one,?_⟩
  obtain ⟨y,hy⟩ := card_pos.mp (minA z za)
  obtain ⟨yA,ey⟩ := mem_outN.mp hy
  rw [az,mem_insert] at yA
  rcases yA with rfl|h
  · exact (loopfree hf (by decide) (av za) ey).elim
  · exact ⟨y,h,ey⟩

#print axioms exact_endpoint_all_large_impossible

end LeanCH.BR.DotDegreeSevenLow
