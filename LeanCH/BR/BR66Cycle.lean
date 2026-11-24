import LeanCH.BR.BRDiagonalThird
import LeanCH.BR.BRq6Seeds

/-! The degree-six cutoff-six cycle case from complementary third balls. -/

namespace LeanCH.BR.BRq6
open BRq2 BRq3 BR45 BRsGen

theorem card_ball_three_six_free {D : CH.Digraph} {V : Finset ℕ} {u : ℕ}
    (hf : QFree D V 6) (hm : ∀ v ∈ V, 6 ≤ (outN D V v).card) (hu : u ∈ V) :
    19 ≤ (ball D V u 3).card :=
  third_ball_ge_on_diagonal (by decide : 4 ≤ 6) (by decide : 6 ≤ 6)
    (fun _ hd hd6 _ _ hF hmF hn => lower_order (by decide) hd hd6 hF hmF hn) hf hm hu

theorem card_ge_thirty_seven {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V 6) (hm : ∀ v ∈ V, 6 ≤ (outN D V v).card) (hn : V.Nonempty) :
    37 ≤ V.card := by
  have hh := card_ge_of_two_balls hf (by decide : 3 + 3 ≤ 6)
    (fun _ hv => card_ball_three_six_free hf hm hv)
    (fun _ hv => card_ball_three_six_free hf hm hv) hn
  omega

theorem ch_six_of_le_thirty_six {n : ℕ} {D : CH.Digraph} (hn : 0 < n) (hsmall : n ≤ 36)
    (hloop : CH.Loopless D n) (hdeg : CH.MinOutdegreeAtLeast D n 6) :
    CH.HasDirectedCycleAtMost D n 6 := by
  by_contra hnot
  have hf := qfree_of_noShort hloop hnot
  have hm : ∀ v ∈ Finset.range n, 6 ≤ (outN D (Finset.range n) v).card :=
    fun _ hv => Compose.FloorSix.out_card hdeg (Finset.mem_range.mp hv)
  have hh := card_ge_thirty_seven hf hm ⟨0, Finset.mem_range.mpr hn⟩
  rw [Finset.card_range] at hh
  omega

/-- A small five-free minimum-six host has a six-cycle support, without any module claim. -/
theorem exists_six_cycle_support {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V 5) (hm : ∀ v ∈ V, 6 ≤ (outN D V v).card)
    (hn : V.Nonempty) (hcard : V.card ≤ 36) :
    ∃ M : Finset ℕ, M ⊆ V ∧ M.card = 6 ∧ OutEq 1 D M := by
  obtain ⟨p, M, hp, hF, hMV, hM, hOut⟩ := exists_minimal_cycle_support
    (by decide : 1 ≤ 5) hf (fun v hv => by have hh := hm v hv; omega) hn
  have hp5 : p = 5 := by
    by_contra hnot
    have hh := card_ge_thirty_seven (hF.mono_bound (by omega : 6 ≤ p)) hm hn
    omega
  exact ⟨M, hMV, by omega, hOut⟩

end LeanCH.BR.BRq6
