import LeanCH.BR.BRTwoBalls
import LeanCH.BR.BR45Prof
import LeanCH.BR.BRsGenRigid

/-! The cutoff-five cycle theorem at minimum out-degree five. -/

namespace LeanCH.BR.BRsGen

open BRq2 BRq3 BR45

variable {D : CH.Digraph} {W : Finset ℕ}

/-- Acyclicity of the first layer supplies the radius-two bound. -/
theorem card_ball_two_ge_twice {s u : ℕ} (hs : 2 ≤ s) (hf : QFree D W s)
    (hmin : ∀ v ∈ W, s ≤ (outN D W v).card) (hu : u ∈ W) :
    2 * s + 1 ≤ (ball D W u 2).card := by
  obtain ⟨F, hsub, ho⟩ := exists_outEq hmin
  have hF := qfree_sub hsub hf
  have h2 := n2_ge_s hs hF ho hu
  have h1 : (ball F W u 1).card = s + 1 := by
    have heq : ball F W u 1 = insert u (outN F W u) := by
      ext v
      rw [mem_ball_one hu, Finset.mem_insert]
    have hnot : u ∉ outN F W u := fun h => loopfree hF (by omega) hu (mem_outN.mp h).2
    rw [heq, Finset.card_insert_of_notMem hnot, ho u hu]
  have hc := Finset.card_sdiff_add_card_eq_card
    (ball_mono_radius (D := F) (W := W) (u := u) (by decide : 1 ≤ 2))
  have hle := Finset.card_le_card (ball_sub (W := W) (u := u) (k := 2) hsub)
  change s ≤ (ball F W u 2 \ ball F W u 1).card at h2
  omega

/-- A 5-free host of minimum out-degree five has at least 26 vertices. -/
theorem card_ge_twenty_six (hf : QFree D W 5)
    (hmin : ∀ v ∈ W, 5 ≤ (outN D W v).card) (hne : W.Nonempty) :
    26 ≤ W.card := by
  have h := card_ge_of_two_balls (i := 3) (j := 2) (a := 16) (b := 11) hf (by decide)
    (fun _ hv => card_ball_three_ge_sixteen hf hmin hv)
    (fun _ hv => card_ball_two_ge_twice (by decide) hf hmin hv) hne
  omega

/-- Minimum out-degree five forces a cycle of length at most five through order 25. -/
theorem ch_five_of_le_twenty_five {n : ℕ} (hn : 0 < n) (hn25 : n ≤ 25)
    (hloop : CH.Loopless D n) (hout : CH.MinOutdegreeAtLeast D n 5) :
    CH.HasDirectedCycleAtMost D n 5 := by
  by_contra hshort
  have hf := qfree_of_noShort hloop hshort
  have hmin : ∀ v ∈ Finset.range n, 5 ≤ (outN D (Finset.range n) v).card :=
    fun _ hv => Compose.FloorSix.out_card hout (Finset.mem_range.mp hv)
  have h := card_ge_twenty_six hf hmin ⟨0, Finset.mem_range.mpr hn⟩
  rw [Finset.card_range] at h
  omega

/-- The same count at radii three and three gives the cutoff-six order bound. -/
theorem card_ge_thirty_one (hf : QFree D W 6)
    (hmin : ∀ v ∈ W, 5 ≤ (outN D W v).card) (hne : W.Nonempty) :
    31 ≤ W.card := by
  have hb := fun v hv => card_ball_three_ge_sixteen (hf.mono_bound (by decide)) hmin (u := v) hv
  have h := card_ge_of_two_balls (i := 3) (j := 3) (a := 16) (b := 16) hf (by decide) hb hb hne
  omega

/-- Minimum out-degree five forces a cycle of length at most six through order 30. -/
theorem ch_six_of_le_thirty {n : ℕ} (hn : 0 < n) (hn30 : n ≤ 30)
    (hloop : CH.Loopless D n) (hout : CH.MinOutdegreeAtLeast D n 5) :
    CH.HasDirectedCycleAtMost D n 6 := by
  by_contra hshort
  have hf := qfree_of_noShort hloop hshort
  have hmin : ∀ v ∈ Finset.range n, 5 ≤ (outN D (Finset.range n) v).card :=
    fun _ hv => Compose.FloorSix.out_card hout (Finset.mem_range.mp hv)
  have h := card_ge_thirty_one hf hmin ⟨0, Finset.mem_range.mpr hn⟩
  rw [Finset.card_range] at h
  omega

end LeanCH.BR.BRsGen
