module

public import LeanCH.CompromiseTenPositive

set_option linter.style.header false

/-! Every second-set predecessor of a returning vertex is an additional
missed column for each return target. Retain that cost in the local bound. -/

open Finset CH.CompromiseSeven
public section

namespace CH.CompromiseTenFrame.Frame

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {adj : V → V → Prop} [DecidableRel adj]
variable (H : Ambient adj) (f : Frame adj)
include H

theorem return_predecessor_bound (z : V) (hz : z ∈ f.Z) (positive : 1 ≤ f.aOut z) :
    (inN adj z ∩ f.Z).card + 3 + f.aOut z ≤
      f.omission z + (f.aOut z - 1) / 3 := by
  let P := inN adj z ∩ f.Z
  let Q := outN adj z ∩ f.A
  let S := f.A \ inN adj z
  have qA : Q ⊆ f.A := inter_subset_right
  have qS : Q ⊆ S := by
    intro a ha
    exact mem_sdiff.mpr ⟨qA ha, fun incoming =>
      H.noDigon z a ((mem_outN adj z a).mp (mem_inter.mp ha).1)
        ((mem_inN adj z a).mp incoming)⟩
  obtain ⟨a, ha, low⟩ := H.small Q (card_pos.mp positive)
    ((card_le_card qA).trans (by rw [f.cardA]))
  have edge := (mem_outN adj z a).mp (mem_inter.mp ha).1
  have missed : insert z P ⊆ f.missing a := by
    intro g hg
    rcases mem_insert.mp hg with equal | hg
    · subst g
      exact mem_sdiff.mpr ⟨hz, fun incoming =>
        H.noDigon z a edge ((mem_outN adj a z).mp incoming)⟩
    · exact mem_sdiff.mpr ⟨(mem_inter.mp hg).2, fun incoming =>
        H.noTri z a g edge ((mem_outN adj a g).mp incoming)
          ((mem_inN adj z g).mp (mem_inter.mp hg).1)⟩
  have extra := card_le_card missed
  have self : z ∉ P := by simp [P, H.loopless]
  rw [card_insert_of_notMem self] at extra
  change P.card + 1 ≤ f.extra a at extra
  have row := f.row_counts H a (qA ha)
  have subset : outN adj a ∩ f.A ⊆ Q ∪ (S \ Q) := by
    intro b hb
    have inS : b ∈ S := mem_sdiff.mpr ⟨(mem_inter.mp hb).2, fun incoming =>
      H.noTri z a b edge ((mem_outN adj a b).mp (mem_inter.mp hb).1)
        ((mem_inN adj z b).mp incoming)⟩
    by_cases inQ : b ∈ Q
    · exact mem_union_left _ inQ
    · exact mem_union_right _ (mem_sdiff.mpr ⟨inS, inQ⟩)
  have bound := degree_bound (outN adj a ∩ f.A) Q (S \ Q) subset
  have equal : (outN adj a ∩ f.A) ∩ Q = outN adj a ∩ Q := by
    ext b
    simp only [mem_inter]
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, qA h.2⟩, h.2⟩⟩
  rw [equal, card_sdiff_of_subset qS] at bound
  have cardinal := card_le_card qS
  change Q.card ≤ f.omission z at cardinal
  change (outN adj a ∩ f.A).card ≤ (outN adj a ∩ Q).card + (f.omission z - Q.card) at bound
  change (outN adj a ∩ f.A).card = 2 + f.extra a at row
  change P.card + 3 + Q.card ≤ f.omission z + (Q.card - 1) / 3
  omega

end CH.CompromiseTenFrame.Frame

#print axioms CH.CompromiseTenFrame.Frame.return_predecessor_bound
