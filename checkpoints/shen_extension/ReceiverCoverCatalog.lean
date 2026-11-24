import checkpoints.shen_extension.ReceiverCoveredColumns

namespace LeanCH.BR.LabelledCompromiseRecipe
open Finset BRq2 BRq3

theorem parents_of_sole {D : CH.Digraph} {V H Y : Finset ℕ} {g}
    (gm : g∈H)
    (sole : (H.filter fun a=>Y⊆outN D V a)={g})
    (bill : ∀x∈H, 2+(if x∈(H.filter fun a=>Y⊆outN D V a) then 1 else 0)≤
      (H.filter fun a=>Y⊆outN D V a).card+
      ((H.erase x).filter fun u=>D u x=true ∧ (Y\outN D V u).card≤1).card) :
    ∃a∈H,∃a'∈H,a≠a' ∧ D a g=true ∧ D a' g=true ∧
      (Y\outN D V a).card=1 ∧ (Y\outN D V a').card=1 := by
  let P:=(H.erase g).filter fun u=>D u g=true ∧ (Y\outN D V u).card≤1
  have cost := bill g gm
  rw [sole] at cost
  simp only [mem_singleton_self,ite_true,card_singleton] at cost
  obtain ⟨a,am,b,bm,ne⟩ := one_lt_card.mp (show 1<P.card by dsimp [P]; omega)
  have pay (u) (um : u∈P) : u∈H ∧ D u g=true ∧ (Y\outN D V u).card=1 := by
    obtain ⟨mem,arc,one⟩ := mem_filter.mp um
    obtain ⟨other,inside⟩ := mem_erase.mp mem
    have off : ¬Y⊆outN D V u := by
      intro all
      have yes : u∈H.filter (fun a=>Y⊆outN D V a) := mem_filter.mpr ⟨inside,all⟩
      rw [sole] at yes
      exact other (mem_singleton.mp yes)
    have pos : 0<(Y\outN D V u).card := card_pos.mpr
      (nonempty_iff_ne_empty.mpr (fun eq=>off (sdiff_eq_empty_iff_subset.mp eq)))
    exact ⟨inside,arc,by omega⟩
  obtain ⟨ah,ag,one⟩ := pay a am
  obtain ⟨bh,bg,two⟩ := pay b bm
  exact ⟨a,ah,b,bh,ne,ag,bg,one,two⟩
attribute [aesop safe forward (immediate := [gm,sole,bill]) (rule_sets := [CHGraphFamilies])] parents_of_sole
ch_family_split_result parents_of_sole
#print axioms parents_of_sole
end LeanCH.BR.LabelledCompromiseRecipe
