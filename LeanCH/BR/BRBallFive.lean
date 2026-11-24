import LeanCH.BR.BR45Prof
import LeanCH.BR.BRsGen2Tri
import LeanCH.BR.BRsGen35
import LeanCH.BR.BRsGenRigid

/-! A radius-four bound at girth at least six and minimum out-degree five. -/

namespace LeanCH.BR.BRsGen

open BRq2 BRq3 BRq4 BR45

/-- Every radius-four ball in a 5-free digraph of minimum out-degree
five has at least 19 vertices. -/
theorem card_ball_four_ge_nineteen {D : CH.Digraph} {W : Finset ℕ} {u : ℕ}
    (hf : QFree D W 5) (hmin : ∀ v ∈ W, 5 ≤ (outN D W v).card) (hu : u ∈ W) :
    19 ≤ (ball D W u 4).card := by
  obtain ⟨F, hsub, hout⟩ := exists_outEq hmin
  have hF := qfree_sub hsub hf
  have hFmin : ∀ v ∈ W, 5 ≤ (outN F W v).card := fun v hv => (hout v hv).ge
  have h2 := n2_ge_s (by decide : 2 ≤ 5) hF hout hu
  have h1 := card_B1 (hF.mono_bound (by decide : 4 ≤ 5)) hu
  have h12 := card_B2 (E := F) (V := W) (u := u)
  change 5 ≤ (N2 F W u).card at h2
  have hF2 : 11 ≤ (ball F W u 2).card := by rw [hout u hu] at h1; omega
  have hF4 : 19 ≤ (ball F W u 4).card :=
    thm6_of_local_ball_s (j := 0) (s := 5) (by decide) BRsGen35.bball35
      (fun G U hG hOut _ z hz => card_ball_three_ge_sixteen hG
        (fun v hv => (hOut v hv).ge) hz)
      hF hout hu hF2 (card_ball_three_ge_sixteen hF hFmin hu)
  exact hF4.trans (Finset.card_le_card (ball_sub hsub))

/-- The radius-four estimate proves the five-cycle bound at degree five
through order 23. -/
theorem ch_five_of_le_twenty_three {D : CH.Digraph} {n : ℕ}
    (hn : 0 < n) (hn23 : n ≤ 23) (hloop : CH.Loopless D n)
    (hout : CH.MinOutdegreeAtLeast D n 5) : CH.HasDirectedCycleAtMost D n 5 := by
  by_contra hshort
  have hf := qfree_of_noShort hloop hshort
  have hmin : ∀ v ∈ Finset.range n, 5 ≤ (outN D (Finset.range n) v).card :=
    fun _ hv => Compose.FloorSix.out_card hout (Finset.mem_range.mp hv)
  have hsize := card_ge_of_ball (q := 5) (s := 5) (b := 19) (by decide) hf hmin
    (fun _ hu => card_ball_four_ge_nineteen hf hmin hu) ⟨0, Finset.mem_range.mpr hn⟩
  rw [Finset.card_range] at hsize
  omega

end LeanCH.BR.BRsGen
