import LeanCH.BR.BRCycleReturn

/-! Return capacity forces a sink in the six-vertex second layer of a small profile. -/

namespace LeanCH.BR.BRsub
open BRq2 BRq3 BR45 BRsGen

/-- If the second layer is a six-cycle and the first layer has at most seven
vertices, the second layer cannot send any arc back to the first. -/
theorem six_second_cycle_no_back_first {D : CH.Digraph} {V : Finset ℕ} {u : ℕ}
    (hf : QFree D V 5) (hu : u ∈ V)
    (hm : ∀ v ∈ V, 6 ≤ (outN D V v).card) (hX : (outN D V u).card ≤ 7)
    (hY : (ball D V u 2 \ ball D V u 1).card = 6)
    (hcyc : OutEq 1 D (ball D V u 2 \ ball D V u 1)) :
    ∀ y ∈ ball D V u 2 \ ball D V u 1, ∀ x ∈ outN D V u, ¬ D y x = true := by
  let X := outN D V u
  let Y := ball D V u 2 \ ball D V u 1
  have hYV : Y ⊆ V := Finset.sdiff_subset.trans ball_subset
  have hdisj : Disjoint X Y := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact (Finset.mem_sdiff.mp hy).2 ((mem_ball_one hu).mpr (Or.inr hx))
  have hretain : ∀ x ∈ X, outN D V x ⊆ outN D (X ∪ Y) x := by
    intro x hx z hz
    have hz2 := outN_prefix_erase_root hf hu (by decide : 1 + 1 ≤ 5)
      ((mem_ball_one hu).mpr (Or.inr hx)) hz
    obtain ⟨hzu, hzball⟩ := Finset.mem_erase.mp (mem_outN.mp hz2).1
    refine mem_outN.mpr ⟨?_, (mem_outN.mp hz).2⟩
    by_cases hz1 : z ∈ ball D V u 1
    · exact Finset.mem_union_left _ ((mem_ball_one hu).mp hz1 |>.resolve_left hzu)
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hzball, hz1⟩)
  exact cycle_no_feed_small_high_set (by decide : 5 ≤ 5) hf hYV outN_subset hdisj hY hcyc hX
    (fun x hx => (hm x (outN_subset hx)).trans (Finset.card_le_card (hretain x hx)))

/-- In the small profile, a six-cycle filling layer two would have only the
five third-layer vertices as exterior heads, and would be a forbidden module. -/
theorem no_second_six_cycle_small_ball {D : CH.Digraph} {V : Finset ℕ} {u : ℕ}
    (hf : QFree D V 5) (hsat : Sat 5 D V) (hu : u ∈ V) (hV : V.card = 31)
    (hm : ∀ v ∈ V, 6 ≤ (outN D V v).card) (hp : RemainingSixProfile D V u)
    (hsmall : (ball D V u 4).card ≤ 23)
    (hY : (ball D V u 2 \ ball D V u 1).card = 6) :
    ¬ OutEq 1 D (ball D V u 2 \ ball D V u 1) := by
  classical
  intro hcyc
  let M := ball D V u 2 \ ball D V u 1
  let Z := ball D V u 3 \ ball D V u 2
  have hMV : M ⊆ V := Finset.sdiff_subset.trans ball_subset
  obtain ⟨_, hZ, _, _, hX⟩ := remaining_six_small_ball_cards hf hu hp hsmall
  have hback := six_second_cycle_no_back_first hf hu hm hX hY hcyc
  have hext : exteriorHeads D V M ⊆ Z := by
    intro z hz
    obtain ⟨m, hmM, hmz⟩ := Finset.mem_biUnion.mp hz
    obtain ⟨hzVM, hmez⟩ := mem_outN.mp hmz
    obtain ⟨hzV, hzM⟩ := Finset.mem_sdiff.mp hzVM
    have hz3 := outN_prefix_erase_root hf hu (by decide : 2 + 1 ≤ 5)
      (Finset.mem_sdiff.mp hmM).1 (mem_outN.mpr ⟨hzV, hmez⟩)
    obtain ⟨hzu, hzb3⟩ := Finset.mem_erase.mp (mem_outN.mp hz3).1
    refine Finset.mem_sdiff.mpr ⟨hzb3, ?_⟩
    intro hzb2
    by_cases hzb1 : z ∈ ball D V u 1
    · have hzX := ((mem_ball_one hu).mp hzb1).resolve_left hzu
      exact hback m hmM z hzX hmez
    · exact hzM (Finset.mem_sdiff.mpr ⟨hzb2, hzb1⟩)
  have hmodule := tight_cycle_module_of_small_exterior hMV hY hcyc
    (fun m hmM => hm m (hMV hmM)) (by
      have hc := Finset.card_le_card hext
      change Z.card = 5 at hZ
      omega)
  have hlocal : M ⊆ (ball D V u 3).erase u := by
    intro m hmM
    obtain ⟨hm2, hm1⟩ := Finset.mem_sdiff.mp hmM
    exact Finset.mem_erase.mpr ⟨fun heq => hm1 (heq.symm ▸ self_mem_ball hu),
      ball_mono_radius (by decide) hm2⟩
  exact no_local_tight_six_small_ball hf hsat hu hV hm hp hsmall hlocal hmodule

/-- The six-vertex second layer in a small surviving profile has a sink. -/
theorem small_profile_six_second_has_sink {D : CH.Digraph} {V : Finset ℕ} {u : ℕ}
    (hf : QFree D V 5) (hsat : Sat 5 D V) (hu : u ∈ V) (hV : V.card = 31)
    (hm : ∀ v ∈ V, 6 ≤ (outN D V v).card) (hp : RemainingSixProfile D V u)
    (hsmall : (ball D V u 4).card ≤ 23)
    (hY : (ball D V u 2 \ ball D V u 1).card = 6) :
    ∃ y ∈ ball D V u 2 \ ball D V u 1,
      outN D (ball D V u 2 \ ball D V u 1) y = ∅ := by
  classical
  by_contra hn
  let Y := ball D V u 2 \ ball D V u 1
  have hYV : Y ⊆ V := Finset.sdiff_subset.trans ball_subset
  have hmin : ∀ y ∈ Y, 1 ≤ (outN D Y y).card := by
    intro y hy
    by_contra he
    have hz : (outN D Y y).card = 0 := by omega
    exact hn ⟨y, hy, Finset.card_eq_zero.mp hz⟩
  have hreg := dt_reg (by decide : 1 ≤ 5) (ball_q_one 5 (by decide))
    (hf.mono_set hYV) hmin hY
  exact no_second_six_cycle_small_ball hf hsat hu hV hm hp hsmall hY hreg.1

/-- The second-layer sink has to return to the first layer: the five vertices
in layer three cannot supply its six required heads. -/
theorem small_profile_six_second_sink_returns {D : CH.Digraph} {V : Finset ℕ} {u : ℕ}
    (hf : QFree D V 5) (hsat : Sat 5 D V) (hu : u ∈ V) (hV : V.card = 31)
    (hm : ∀ v ∈ V, 6 ≤ (outN D V v).card) (hp : RemainingSixProfile D V u)
    (hsmall : (ball D V u 4).card ≤ 23)
    (hY : (ball D V u 2 \ ball D V u 1).card = 6) :
    ∃ y ∈ ball D V u 2 \ ball D V u 1,
      outN D (ball D V u 2 \ ball D V u 1) y = ∅ ∧
      ∃ x ∈ outN D V u, D y x = true := by
  classical
  obtain ⟨y, hy, hsink⟩ := small_profile_six_second_has_sink hf hsat hu hV hm hp hsmall hY
  refine ⟨y, hy, hsink, ?_⟩
  by_contra hn
  have hsub : outN D V y ⊆ ball D V u 3 \ ball D V u 2 := by
    intro z hz
    have hz3 := outN_prefix_erase_root hf hu (by decide : 2 + 1 ≤ 5)
      (Finset.mem_sdiff.mp hy).1 hz
    obtain ⟨hzu, hzb3⟩ := Finset.mem_erase.mp (mem_outN.mp hz3).1
    refine Finset.mem_sdiff.mpr ⟨hzb3, ?_⟩
    intro hzb2
    by_cases hzb1 : z ∈ ball D V u 1
    · exact hn ⟨z, ((mem_ball_one hu).mp hzb1).resolve_left hzu, (mem_outN.mp hz).2⟩
    · have hzy : z ∈ outN D (ball D V u 2 \ ball D V u 1) y :=
        mem_outN.mpr ⟨Finset.mem_sdiff.mpr ⟨hzb2, hzb1⟩, (mem_outN.mp hz).2⟩
      rw [hsink] at hzy
      exact Finset.notMem_empty _ hzy
  have hc := Finset.card_le_card hsub
  have hh := hm y (ball_subset (Finset.mem_sdiff.mp hy).1)
  have hZ := (remaining_six_small_ball_cards hf hu hp hsmall).2.1
  omega

end LeanCH.BR.BRsub
