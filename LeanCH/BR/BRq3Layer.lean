import LeanCH.BR.BRq3Base

/-!
# Layer lemmas for out-degree three, Lean 4.35.0

Paper: `checkpoints/boundary_20261111/BRq2_attempt_subagent.md`, §6.2–§6.4. Throughout, `D` has out-degree exactly
three on `W` (`OutEq 3 D W`), `u ∈ W`, `B_k = ball D W u k`, `N_1 = outN D W u`, `N_k = B_k ∖ B_{k-1}`.

* `six_two` (§6.2): if `D` is 3-free, a sink of `D[N_1]` sends its three arcs into `N_2`, so `|N_2| ≥ 3`.
* `corB_layer` (§6.3 case `n_2 ∈ {4,5}`, §6.4 cases `n_4 = 1`, `(5,1)`): if `|N_{k+1}| ≤ 1` then `D[B_k ∖ {u}]` has
  min out `≥ 2`, so Corollary B gives `|B_k| ≥ 2q+2`.
* `prop3`: if `|A|, |C| ≤ 3` and every out-neighbour of `A` lies in `A ∪ C`, every `a ∈ A` reaches, within two steps,
  a sink of `D[A]` that heads all of `C` (the "within 3" argument of §6.3, with the auditor's sub-case `v = c`).
* `three_layer`, `n3_of_three` (§6.3 case `n_2 = 3`): `N_1` reaches all of `N_2` within three steps, `N_2` has no
  back arcs, and `|N_3| ≥ 3`.
-/

set_option linter.style.longLine false

namespace LeanCH.BR.BRq3

open LeanCH.BR.BRq2

variable {D : CH.Digraph} {W : Finset ℕ} {u : ℕ}

theorem mem_ball_one_of_out {v : ℕ} (hv : v ∈ outN D W u) : v ∈ ball D W u 1 :=
  ball_of_adj (mem_outN.mp hv).1 (mem_outN.mp hv).2

/-- §6.2: `|N_2| ≥ 3` in a 3-free digraph with out-degree three. -/
theorem six_two (hfree : QFree D W 3) (hout : OutEq 3 D W) (hu : u ∈ W) :
    3 ≤ (ball D W u 2 \ ball D W u 1).card := by
  have hN1 := hout u hu
  obtain ⟨c, hc, hsink⟩ := exists_sink (hfree.mono_set (outN_subset (y := u)))
    (by rw [← Finset.card_pos, hN1]; omega) (by omega)
  have hsub : outN D W c ⊆ ball D W u 2 \ ball D W u 1 := by
    intro z hz
    obtain ⟨hzW, hcz⟩ := mem_outN.mp hz
    refine Finset.mem_sdiff.mpr ⟨ball_step (mem_ball_one_of_out hc) hzW hcz, ?_⟩
    intro hz1
    rcases (mem_ball_one hu).mp hz1 with rfl | hz1
    · exact no_back_arc hfree hzW (mem_ball_one_of_out hc) (by omega) hcz
    · exact hsink z hz1 hcz
  have := Finset.card_le_card hsub
  rw [hout c (outN_subset hc)] at this
  exact this

/-- If at most one vertex is first reached at radius `k+1`, then `B_k ∖ {u}` has min out `≥ 2`, and Corollary B
gives `|B_k| ≥ 2q+2`. -/
theorem corB_layer {q k : ℕ} (hk : 1 ≤ k) (hkq : k + 1 ≤ q) (hfree : QFree D W q) (hout : OutEq 3 D W)
    (hu : u ∈ W) (hN : (ball D W u (k + 1)).card ≤ (ball D W u k).card + 1) :
    2 * q + 2 ≤ (ball D W u k).card := by
  classical
  have hsub : ball D W u k ⊆ ball D W u (k + 1) := ball_mono_radius (by omega)
  have hF : (ball D W u (k + 1) \ ball D W u k).card ≤ 1 := by
    rw [Finset.card_sdiff_of_subset hsub]; omega
  have hUW : (ball D W u k).erase u ⊆ W := (Finset.erase_subset _ _).trans ball_subset
  have hmin : MinOut2 D ((ball D W u k).erase u) := by
    intro y hy
    have hyB : y ∈ ball D W u k := Finset.mem_of_mem_erase hy
    have hs : outN D W y \ (ball D W u (k + 1) \ ball D W u k) ⊆
        ((ball D W u k).erase u).filter (fun w => D y w = true) := by
      intro z hz
      obtain ⟨hz1, hz2⟩ := Finset.mem_sdiff.mp hz
      obtain ⟨hzW, hyz⟩ := mem_outN.mp hz1
      have hzB : z ∈ ball D W u (k + 1) := ball_step hyB hzW hyz
      have hzk : z ∈ ball D W u k := by
        by_contra h; exact hz2 (Finset.mem_sdiff.mpr ⟨hzB, h⟩)
      refine Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨?_, hzk⟩, hyz⟩
      rintro rfl
      exact no_back_arc hfree hu hyB (by omega) hyz
    have h1 := Finset.le_card_sdiff (ball D W u (k + 1) \ ball D W u k) (outN D W y)
    have h2 := Finset.card_le_card hs
    have h3 := hout y (hUW hy)
    omega
  have hne : ((ball D W u k).erase u).Nonempty := by
    obtain ⟨z, hz⟩ : (outN D W u).Nonempty := by rw [← Finset.card_pos, hout u hu]; omega
    refine ⟨z, Finset.mem_erase.mpr ⟨?_, ball_mono_radius hk (mem_ball_one_of_out hz)⟩⟩
    rintro rfl; exact loopfree hfree (by omega) hu (mem_outN.mp hz).2
  have hc := corB (by omega) (hfree.mono_set hUW) hmin hne
  have := Finset.card_erase_of_mem (self_mem_ball (D := D) (k := k) hu)
  omega

/-- Propagation: a sink of `D[A]` within two steps of `a` heads all of `C`. -/
theorem prop3 {A C : Finset ℕ} (hfree : QFree D W 3) (hout : OutEq 3 D W) (hAW : A ⊆ W) (hA : A.card ≤ 3)
    (hC : C.card ≤ 3) (hsub : ∀ a ∈ A, outN D W a ⊆ A ∪ C) {a : ℕ} (ha : a ∈ A) :
    ∃ s ∈ A, s ∈ ball D W a 2 ∧ ∀ c ∈ C, D s c = true := by
  obtain ⟨s, hs, hsink, hpath⟩ := reach_sink3 hfree hAW hA ha
  have hsC : outN D W s ⊆ C := by
    intro z hz
    rcases Finset.mem_union.mp (hsub s hs hz) with h | h
    · exact absurd (mem_outN.mp hz).2 (hsink z h)
    · exact h
  have heq : outN D W s = C :=
    Finset.eq_of_subset_of_card_le hsC (by rw [hout s (hAW hs)]; exact hC)
  refine ⟨s, hs, ?_, fun c hc => (mem_outN.mp (heq ▸ hc)).2⟩
  rcases hpath with rfl | has | ⟨x, hx, hax, hxs⟩
  · exact self_mem_ball (hAW hs)
  · exact ball_mono_radius (by omega) (ball_of_adj (hAW hs) has)
  · exact ball_step (ball_of_adj (hAW hx) hax) (hAW hs) hxs

/-- §6.3, case `n_2 = 3`: `N_1` reaches all of `N_2` within three steps, so `N_2` sends no arc back into `B_1`. -/
theorem three_layer (hfree : QFree D W 4) (hout : OutEq 3 D W) (hu : u ∈ W)
    (h2 : (ball D W u 2 \ ball D W u 1).card = 3) :
    (∀ v ∈ outN D W u, ∀ w ∈ ball D W u 2 \ ball D W u 1, w ∈ ball D W v 3) ∧
      ∀ w ∈ ball D W u 2 \ ball D W u 1,
        outN D W w ⊆ (ball D W u 2 \ ball D W u 1) ∪ (ball D W u 3 \ ball D W u 2) := by
  have hf3 : QFree D W 3 := hfree.mono_bound (by omega)
  have P1 : ∀ v ∈ outN D W u, ∀ w ∈ ball D W u 2 \ ball D W u 1, w ∈ ball D W v 3 := by
    intro v hv w hw
    have hs : ∀ a ∈ outN D W u, outN D W a ⊆ outN D W u ∪ (ball D W u 2 \ ball D W u 1) := by
      intro a ha z hz
      obtain ⟨hzW, haz⟩ := mem_outN.mp hz
      have hz2 : z ∈ ball D W u 2 := ball_step (mem_ball_one_of_out ha) hzW haz
      by_cases hz1 : z ∈ ball D W u 1
      · rcases (mem_ball_one hu).mp hz1 with rfl | hz1
        · exact absurd haz (no_back_arc hfree hzW (mem_ball_one_of_out ha) (by omega))
        · exact Finset.mem_union_left _ hz1
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hz2, hz1⟩)
    obtain ⟨s, _, hs2, hsC⟩ := prop3 hf3 hout outN_subset (hout u hu).le h2.le hs hv
    exact ball_step hs2 (ball_subset (Finset.mem_sdiff.mp hw).1) (hsC w hw)
  refine ⟨P1, ?_⟩
  intro w hw z hz
  obtain ⟨hzW, hwz⟩ := mem_outN.mp hz
  have hw2 := (Finset.mem_sdiff.mp hw).1
  have hz3 : z ∈ ball D W u 3 := ball_step hw2 hzW hwz
  have hz1 : z ∉ ball D W u 1 := by
    intro hz1
    rcases (mem_ball_one hu).mp hz1 with rfl | hz1
    · exact no_back_arc hfree hzW hw2 (by omega) hwz
    · exact no_back_arc hfree hzW (P1 z hz1 w hw) (by omega) hwz
  by_cases hz2 : z ∈ ball D W u 2
  · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hz2, hz1⟩)
  · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hz3, hz2⟩)

/-- §6.3, case `n_2 = 3`: then `n_3 ≥ 3` (a sink of `D[N_2]` sends its three arcs into `N_3`). -/
theorem n3_of_three (hfree : QFree D W 4) (hout : OutEq 3 D W) (hu : u ∈ W)
    (h2 : (ball D W u 2 \ ball D W u 1).card = 3) : 3 ≤ (ball D W u 3 \ ball D W u 2).card := by
  have P2 := (three_layer hfree hout hu h2).2
  have hN2W : ball D W u 2 \ ball D W u 1 ⊆ W := fun z hz => ball_subset (Finset.mem_sdiff.mp hz).1
  obtain ⟨t, ht, hsink⟩ := exists_sink (hfree.mono_set hN2W)
    (by rw [← Finset.card_pos, h2]; omega) (by omega)
  have hsub : outN D W t ⊆ ball D W u 3 \ ball D W u 2 := by
    intro z hz
    rcases Finset.mem_union.mp (P2 t ht hz) with h | h
    · exact absurd (mem_outN.mp hz).2 (hsink z h)
    · exact h
  have := Finset.card_le_card hsub
  rw [hout t (hN2W ht)] at this
  exact this

end LeanCH.BR.BRq3
