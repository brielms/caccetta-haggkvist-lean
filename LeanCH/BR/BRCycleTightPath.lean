import LeanCH.BR.BRCycleWindowEquality

/-! Tight reentry along a path of arbitrary length. The contact sets are not
restricted to pairs, and the ambient graph has no order bound. -/
namespace LeanCH.BR.BRsub
open Finset BRq2 BRq3 BR45 BRsGen

theorem cycle_successor_union_card {D : CH.Digraph} {M A : Finset ℕ}
    (hout : OutEq 1 D M) (hin : ∀ v ∈ M, (inN D M v).card = 1)
    (hAM : A ⊆ M) : (A.biUnion (outN D M)).card = A.card := by
  classical
  rw [Finset.card_biUnion]
  · simp only [Finset.sum_congr rfl (fun v hv => hout v (hAM hv))]
    simp
  · intro x hx y hy hxy
    apply Finset.disjoint_left.mpr
    intro z hxz hyz
    exact hxy (Finset.card_le_one.mp (hin z (outN_subset hxz)).le x
      (mem_inN.mpr ⟨hAM hx, (mem_outN.mp hxz).2⟩) y
      (mem_inN.mpr ⟨hAM hy, (mem_outN.mp hyz).2⟩))

/-- Any set of at least two cycle vertices with one-step growth at most one
contains an actual internal edge. -/
theorem cycle_set_internal_arc_of_small_expansion {D : CH.Digraph} {M A : Finset ℕ}
    (hout : OutEq 1 D M) (hin : ∀ v ∈ M, (inN D M v).card = 1)
    (hAM : A ⊆ M) (hA : 2 ≤ A.card)
    (hb : (ballSet D M A 1).card ≤ A.card + 1) :
    ∃ u ∈ A, ∃ v ∈ A, D u v = true := by
  classical
  by_contra hn
  let H := A.biUnion (outN D M)
  have hd : Disjoint A H := by
    apply Finset.disjoint_left.mpr
    intro z hz hzH
    obtain ⟨x, hx, hxz⟩ := Finset.mem_biUnion.mp hzH
    exact hn ⟨x, hx, z, hz, (mem_outN.mp hxz).2⟩
  have hsub : A ∪ H ⊆ ballSet D M A 1 := by
    apply Finset.union_subset (subset_ballSet hAM)
    intro z hz
    obtain ⟨x, hx, hxz⟩ := Finset.mem_biUnion.mp hz
    exact mem_ballSet.mpr ⟨x, hx, ball_of_adj (outN_subset hxz) (mem_outN.mp hxz).2⟩
  have hc := Finset.card_le_card hsub
  have hH : H.card = A.card := cycle_successor_union_card hout hin hAM
  rw [Finset.card_union_of_disjoint hd, hH] at hc
  omega

theorem tight_path_cycle_heads_internal_arc {q l : ℕ} (hl : l + 3 ≤ q)
    {D : CH.Digraph} {V M : Finset ℕ} (hf : QFree D V q)
    (hMV : M ⊆ V) (hM : M.card = q + 1) (hout : OutEq 1 D M)
    (hin : ∀ v ∈ M, (inN D M v).card = 1)
    {a b : ℕ} (ha : a ∈ V) (hab : Walk D V a b l)
    (hIa : (inN D M a).Nonempty) (hOb : 2 ≤ (outN D M b).card)
    (htight : (inN D M a).card + (outN D M b).card = l + 3) :
    ∃ u ∈ outN D M b, ∃ v ∈ outN D M b, D u v = true := by
  have hreach : outN D M b ⊆ ball D V a (l + 1) := by
    intro z hz
    exact mem_ball.mpr ⟨hMV (outN_subset hz), l + 1, le_rfl,
      hab.snoc (hMV (outN_subset hz)) (mem_outN.mp hz).2⟩
  have hg := cycle_reentry_equality_expansion (t := l + 1) (by omega) hf hMV hM hout ha
    hIa outN_subset (Finset.card_pos.mp (by omega)) hreach (by omega)
  exact cycle_set_internal_arc_of_small_expansion hout hin outN_subset hOb hg

end LeanCH.BR.BRsub
