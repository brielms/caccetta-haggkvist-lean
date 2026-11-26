import checkpoints.shen_extension.FlatDeletionBank
import checkpoints.shen_extension.SeymourTransition

namespace LeanCH.BR.FragmentScoreEquality
open Finset BRq2 BRq3 BR45 BRsGen

/-- On a balanced one-short carrier of order at most three times the target
degree, every Seymour witness is the marked vertex. -/
theorem seymour_iff_marked {D U q t x} (carrier : OneShortCarrier D U q t x)
    (flat : FlatErasure D U q t x) (room : U.card ≤ 3*t) {v : ℕ} (hv : v ∈ U) :
    (outN D U v).card ≤ (ShenSeymour.second D U v).card ↔ v = x := by
  have cut := flat.cutoff_eq
  have only (z : ℕ) (hz : z ∈ U)
      (good : (outN D U z).card ≤ (ShenSeymour.second D U z).card) : z = x := by
    by_contra ne
    have disj : Disjoint (ball D U z 1) (ShenSeymour.second D U z) := by
      apply disjoint_left.mpr
      intro y hy hs
      obtain ⟨_, diff, miss, _⟩ := mem_filter.mp hs
      exact ((mem_ball_one hz).mp hy).elim diff (fun h => miss (mem_outN.mp h).2)
    have sub : ball D U z 1 ∪ ShenSeymour.second D U z ⊆ ball D U z 2 := by
      apply union_subset (ball_mono_radius (by decide : 1 ≤ 2))
      intro y hy
      obtain ⟨ym, _, _, j, jm, zj, jy⟩ := mem_filter.mp hy
      exact mem_ball.mpr ⟨ym, 2, le_rfl, .step jm zj (.step ym jy (.refl y))⟩
    have total := card_le_card sub
    rw [card_union_of_disjoint disj, ReachLedger.ball_one carrier.free (by omega) hz] at total
    have cap := ReachLedger.parent_cap (i := 2) carrier.free (by omega) hz
    rw [flat.balanced z hz] at cap
    have degree := carrier.other z hz ne
    omega
  refine ⟨only v hv, ?_⟩
  rintro rfl
  obtain ⟨z, hz, good⟩ := ShenSeymour.witness carrier.free (by omega) ⟨v, hv⟩
  exact only z hz good ▸ good

#print axioms seymour_iff_marked

@[aesop safe forward (immediate := [cell, flat, carrier]) (rule_sets := [CHGraphFamilies])]
theorem seymour_on_bank {q r} {X : ShenMinimumOrder.Source q r} {m : BypassBankReplay.Cell}
    (cell : BypassBankReplay.Marked X m)
    (flat : FlatErasure X.D (X.V \ m.bank) q (r-1) m.x)
    (carrier : OneShortCarrier X.D (X.V \ m.bank) q (r-1) m.x) :
    ∀ v ∈ X.V \ m.bank, (outN X.D (X.V \ m.bank) v).card ≤
      (ShenSeymour.second X.D (X.V \ m.bank) v).card ↔ v = m.x :=
  fun _ hv => seymour_iff_marked carrier flat (room_of_bank cell flat.cutoff_eq) hv

#print axioms seymour_on_bank
end LeanCH.BR.FragmentScoreEquality
