import checkpoints.shen_extension.FlatSeymourVertex
import checkpoints.shen_extension.TwoSeymourVertices

/-!
The flat one-short carrier does not exist.

On a balanced carrier of order at most `3t` with no directed triangle, every vertex whose
second out-neighbourhood is at least its first has degree at most `t - 1`, so it is the
marked vertex (`seymour_iff_marked`). A sinkless oriented graph has two such vertices
(`TwoSeymour.exists_two_goodVertices`), and a marked sink is excluded by the one-vertex
theorem on the remaining labels.
-/

namespace LeanCH.BR.ShenSeymour
open BRq2 BRq3 BR45 Finset

/-- Two distinct Seymour witnesses on a sinkless carrier. -/
theorem two_witnesses {D U q} (free : QFree D U q) (two : 2 ≤ q) (live : U.Nonempty)
    (sinkless : ∀ x ∈ U, (outN D U x).Nonempty) :
    ∃ x ∈ U, ∃ y ∈ U, x ≠ y ∧ (outN D U x).card ≤ (second D U x).card ∧
      (outN D U y).card ≤ (second D U y).card := by
  classical
  have : Nonempty ↥U := ⟨⟨live.choose,live.choose_spec⟩⟩
  let R (x y : ↥U) := D x.val y.val = true
  have oriented : OAI.SeymourSecondNeighborhood.IsOriented R :=
    ⟨fun x => loopfree free (by omega) x.property,
     fun {x y} => digonfree free two x.property y.property⟩
  have noSink : ∀ x : ↥U, ∃ y : ↥U, R x y := by
    intro x
    obtain ⟨z,hz⟩ := sinkless x.val x.property
    obtain ⟨zU,edge⟩ := mem_outN.mp hz
    exact ⟨⟨z,zU⟩,edge⟩
  have conv : ∀ x : ↥U, OAI.SeymourSecondNeighborhood.GoodVertex R x →
      (outN D U x.val).card ≤ (second D U x.val).card := by
    intro x good
    let F := OAI.SeymourSecondNeighborhood.firstNeighbors R x
    let S := OAI.SeymourSecondNeighborhood.secondNeighbors R x
    have fEq : F.image Subtype.val = outN D U x.val := by
      ext z
      constructor
      · intro h
        obtain ⟨a,ha,rfl⟩ := mem_image.mp h
        have edge : R x a := (OAI.SeymourSecondNeighborhood.mem_firstNeighbors (r := R)).mp ha
        exact mem_outN.mpr ⟨a.property,edge⟩
      · intro h
        obtain ⟨hz,edge⟩ := mem_outN.mp h
        exact mem_image.mpr ⟨⟨z,hz⟩,OAI.SeymourSecondNeighborhood.mem_firstNeighbors.mpr edge,rfl⟩
    have sSub : S.image Subtype.val ⊆ second D U x.val := by
      intro z hz
      obtain ⟨a,ha,rfl⟩ := mem_image.mp hz
      obtain ⟨diff,missing,y,xy,ya⟩ := OAI.SeymourSecondNeighborhood.mem_secondNeighbors.mp ha
      exact mem_filter.mpr ⟨a.property,fun h => diff (Subtype.ext h),missing,
        y.val,y.property,xy,ya⟩
    have size := card_le_card sSub
    rw [card_image_of_injective _ Subtype.val_injective] at size
    rw [← fEq,card_image_of_injective _ Subtype.val_injective]
    exact good.trans size
  obtain ⟨x,y,ne,gx,gy⟩ :=
    LeanCH.BR.TwoSeymour.exists_two_goodVertices R oriented noSink
  exact ⟨x.val,x.property,y.val,y.property,fun h => ne (Subtype.ext h),conv x gx,conv y gy⟩

end LeanCH.BR.ShenSeymour

namespace LeanCH.BR.FragmentScoreEquality
open Finset BRq2 BRq3 BR45 BRsGen

/-- A balanced one-short carrier of order at most three times the target degree
does not exist. -/
theorem flat_impossible {D U q t x} (carrier : OneShortCarrier D U q t x)
    (flat : FlatErasure D U q t x) (room : U.card ≤ 3*t) (pos : 0 < t) : False := by
  classical
  have cut := flat.cutoff_eq
  by_cases sink : (outN D U x).Nonempty
  · have sl : ∀ v ∈ U, (outN D U v).Nonempty := by
      intro v hv
      by_cases hvx : v = x
      · rw [hvx]
        exact sink
      · exact card_pos.mp (lt_of_lt_of_le pos (carrier.other v hv hvx))
    obtain ⟨a,ha,b,hb,hab,ga,gb⟩ :=
      ShenSeymour.two_witnesses carrier.free (by omega) ⟨x,carrier.marked⟩ sl
    have ea := (seymour_iff_marked carrier flat room ha).mp ga
    have eb := (seymour_iff_marked carrier flat room hb).mp gb
    exact hab (ea.trans eb.symm)
  · have out0 : outN D U x = ∅ := not_nonempty_iff_eq_empty.mp sink
    have in0 : inN D U x = ∅ := by
      have bal := flat.balanced x carrier.marked
      rw [out0,card_empty] at bal
      exact card_eq_zero.mp bal
    obtain ⟨z,hz⟩ := carrier.remaining
    have zU : z ∈ U.erase x := by
      obtain ⟨zu,zx⟩ := mem_sdiff.mp hz
      exact mem_erase.mpr ⟨by simpa only [mem_singleton] using zx,zu⟩
    obtain ⟨w,hw,good⟩ := ShenSeymour.witness
      (carrier.free.mono_set (erase_subset x U)) (by omega) ⟨z,zU⟩
    obtain ⟨wx,wU⟩ := mem_erase.mp hw
    have outEq : outN D (U.erase x) w = outN D U w := by
      ext y
      constructor
      · intro hy
        obtain ⟨ym,edge⟩ := mem_outN.mp hy
        exact mem_outN.mpr ⟨(mem_erase.mp ym).2,edge⟩
      · intro hy
        obtain ⟨ym,edge⟩ := mem_outN.mp hy
        refine mem_outN.mpr ⟨mem_erase.mpr ⟨?_,ym⟩,edge⟩
        intro yx
        rw [yx] at edge
        have : w ∈ inN D U x := mem_inN.mpr ⟨wU,edge⟩
        rw [in0] at this
        exact notMem_empty w this
    have secondSub : ShenSeymour.second D (U.erase x) w ⊆ ShenSeymour.second D U w := by
      intro y hy
      obtain ⟨ym,ne,miss,j,jm,wj,jy⟩ := mem_filter.mp hy
      exact mem_filter.mpr ⟨(mem_erase.mp ym).2,ne,miss,j,(mem_erase.mp jm).2,wj,jy⟩
    have size := card_le_card secondSub
    rw [outEq] at good
    exact wx ((seymour_iff_marked carrier flat room wU).mp (good.trans size))

#print axioms flat_impossible

/-- The flat branch of the bank deletion is contradictory. -/
theorem flat_bank_impossible {q r} {X : ShenMinimumOrder.Source q r}
    {m : BypassBankReplay.Cell} (cell : BypassBankReplay.Marked X m)
    (flat : FlatErasure X.D (X.V \ m.bank) q (r-1) m.x)
    (carrier : OneShortCarrier X.D (X.V \ m.bank) q (r-1) m.x) (rank : 2 ≤ r) : False :=
  flat_impossible carrier flat (room_of_bank cell flat.cutoff_eq) (by omega)

#print axioms flat_bank_impossible

/-- The same contradiction as a rule of the graph-family catalog: it fires on the three
facts that every flat context of the capstone carries. -/
@[aesop safe forward (immediate := [cell, flat, carrier]) (rule_sets := [CHGraphFamilies])]
theorem flat_bank_false {q r} {X : ShenMinimumOrder.Source q r}
    {m : BypassBankReplay.Cell} (cell : BypassBankReplay.Marked X m)
    (flat : FlatErasure X.D (X.V \ m.bank) q (r-1) m.x)
    (carrier : OneShortCarrier X.D (X.V \ m.bank) q (r-1) m.x) : False := by
  have room := room_of_bank cell flat.cutoff_eq
  have live := Finset.card_pos.mpr ⟨m.x, carrier.marked⟩
  exact flat_impossible carrier flat room (by omega)

#print axioms flat_bank_false

end LeanCH.BR.FragmentScoreEquality
