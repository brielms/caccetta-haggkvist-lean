import LeanCH.BR.BRq3Util

/-!
# `TOP(3)`, Lean 4.35.0

Paper: `checkpoints/boundary_20261111/BRq3_attempt_subagent.md`, §5.1 (Lemma 7).

`top3`: a 3-free digraph with out-degree exactly three on `W` has `|B_3(u)| ≥ 10`. Suppose `|B_3| ≤ 9`;
`|B_2| ≥ 7` by `ball_three_three`.
* `n_3 = 0`: Lemma 1 (`closed_outEq`) and `Ball(3,3)` with the degree sum give `|B_2 ∖ {u}| ≥ 10`.
* `n_3 = 1`: Lemma 2 (`corB_layer_strict`, `q = 3`, `k = 2`) gives `|B_2| ≥ 9`.
* `n_3 = 2`, `n_2 = 3` (`top3_thin`): the explicit argument of the paper. `c` a sink of `D[N_1]` (`O(c) = N_2`),
  `t` a sink of `D[N_2]` heading `v ∈ N_1`, `N_1 = {v, v', c}`, `N_2 = {t, g, g'}`, `O(v) = {v', g, g'}`,
  `v' → g, g'`, and `h ∈ {g, g'}` with no arc to the other has all three arcs in `N_3`.

`top3_TOP : TOP 3`.
-/

set_option linter.style.longLine false

namespace LeanCH.BR.BRq3

open LeanCH.BR.BRq2

variable {D : CH.Digraph} {W : Finset ℕ} {u : ℕ}

/-- Lemma 7, case `n_3 ≤ 2`, `n_2 = 3`: impossible in a 3-free digraph with out-degree three. -/
theorem top3_thin (hfree : QFree D W 3) (hout : OutEq 3 D W) (hu : u ∈ W)
    (h2 : (ball D W u 2 \ ball D W u 1).card = 3) (h3 : (ball D W u 3 \ ball D W u 2).card ≤ 2) : False := by
  classical
  have hN1 := hout u hu
  have hN1W : outN D W u ⊆ W := outN_subset
  have hN2W : ball D W u 2 \ ball D W u 1 ⊆ W := fun z hz => ball_subset (Finset.mem_sdiff.mp hz).1
  -- `c`: a sink of `D[N_1]`, with `O(c) = N_2`
  obtain ⟨c, hc, hcsink⟩ := exists_sink (hfree.mono_set hN1W)
    (by rw [← Finset.card_pos, hN1]; omega) (by omega)
  have hcW := hN1W hc
  have hcN2 : ∀ g ∈ ball D W u 2 \ ball D W u 1, D c g = true := by
    have hsub : outN D W c ⊆ ball D W u 2 \ ball D W u 1 := by
      intro z hz
      obtain ⟨hzW, hcz⟩ := mem_outN.mp hz
      refine Finset.mem_sdiff.mpr ⟨ball_step (mem_ball_one_of_out hc) hzW hcz, ?_⟩
      intro hz1
      rcases (mem_ball_one hu).mp hz1 with rfl | hz1
      · exact no_back_arc hfree hzW (mem_ball_one_of_out hc) (by omega) hcz
      · exact hcsink z hz1 hcz
    have heq := Finset.eq_of_subset_of_card_le hsub (by rw [h2, hout c hcW])
    intro g hg
    rw [← heq] at hg
    exact (mem_outN.mp hg).2
  -- `t`: a sink of `D[N_2]`; it heads some `v ∈ N_1`
  obtain ⟨t, ht, htsink⟩ := exists_sink (hfree.mono_set hN2W)
    (by rw [← Finset.card_pos, h2]; omega) (by omega)
  have ht2 := (Finset.mem_sdiff.mp ht).1
  have htW := hN2W ht
  obtain ⟨v, hv, htv⟩ : ∃ v ∈ outN D W u, D t v = true := by
    by_contra hno
    push Not at hno
    have hsub : outN D W t ⊆ ball D W u 3 \ ball D W u 2 := by
      intro z hz
      obtain ⟨hzW, htz⟩ := mem_outN.mp hz
      refine Finset.mem_sdiff.mpr ⟨ball_step ht2 hzW htz, ?_⟩
      intro hz2
      by_cases hz1 : z ∈ ball D W u 1
      · rcases (mem_ball_one hu).mp hz1 with rfl | hz1
        · exact no_back_arc hfree hzW ht2 (by omega) htz
        · exact hno z hz1 htz
      · exact htsink z (Finset.mem_sdiff.mpr ⟨hz2, hz1⟩) htz
    have := Finset.card_le_card hsub
    rw [hout t htW] at this
    omega
  have hvW := hN1W hv
  have far : t ∉ ball D W v 2 := fun h => no_back_arc hfree hvW h (by omega) htv
  have hvc : v ≠ c := by
    intro h
    rw [h] at far
    exact far (ball_mono_radius (by omega) (ball_of_adj htW (hcN2 t ht)))
  have hv_c : ¬ D v c = true := fun h => far (ball_step (ball_of_adj hcW h) htW (hcN2 t ht))
  have hv_t : ¬ D v t = true := fun h => far (ball_mono_radius (by omega) (ball_of_adj htW h))
  -- `N_1 = {v, v', c}`
  obtain ⟨v', hv'eq⟩ := Finset.card_eq_one.mp (show (((outN D W u).erase v).erase c).card = 1 by
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨Ne.symm hvc, hc⟩), Finset.card_erase_of_mem hv, hN1])
  have hv'mem : v' ∈ ((outN D W u).erase v).erase c := by rw [hv'eq]; simp
  obtain ⟨hv'c, hv'mem'⟩ := Finset.mem_erase.mp hv'mem
  obtain ⟨hv'v, hv'⟩ := Finset.mem_erase.mp hv'mem'
  have hv'W := hN1W hv'
  have hN1mem : ∀ x ∈ outN D W u, x = v ∨ x = c ∨ x = v' := by
    intro x hx
    by_cases hxv : x = v
    · exact Or.inl hxv
    by_cases hxc : x = c
    · exact Or.inr (Or.inl hxc)
    have : x ∈ ((outN D W u).erase v).erase c :=
      Finset.mem_erase.mpr ⟨hxc, Finset.mem_erase.mpr ⟨hxv, hx⟩⟩
    rw [hv'eq] at this
    exact Or.inr (Or.inr (Finset.mem_singleton.mp this))
  -- `N_2 = {t, g, g'}`
  obtain ⟨g, g', hgg', hgeq⟩ := Finset.card_eq_two.mp (show ((ball D W u 2 \ ball D W u 1).erase t).card = 2 by
    rw [Finset.card_erase_of_mem ht, h2])
  have hgmem : g ∈ (ball D W u 2 \ ball D W u 1).erase t := by rw [hgeq]; simp
  have hg'mem : g' ∈ (ball D W u 2 \ ball D W u 1).erase t := by rw [hgeq]; simp
  obtain ⟨hgt, hg⟩ := Finset.mem_erase.mp hgmem
  obtain ⟨hg't, hg'⟩ := Finset.mem_erase.mp hg'mem
  have hN2mem : ∀ x ∈ ball D W u 2 \ ball D W u 1, x = t ∨ x = g ∨ x = g' := by
    intro x hx
    by_cases hxt : x = t
    · exact Or.inl hxt
    have : x ∈ (ball D W u 2 \ ball D W u 1).erase t := Finset.mem_erase.mpr ⟨hxt, hx⟩
    rw [hgeq] at this
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    exact Or.inr this
  -- out-neighbours of a vertex of `N_1` lie in `N_1 ∪ N_2`
  have outN1 : ∀ y ∈ outN D W u, ∀ z ∈ outN D W y,
      (z ∈ outN D W u) ∨ z ∈ ball D W u 2 \ ball D W u 1 := by
    intro y hy z hz
    obtain ⟨hzW, hyz⟩ := mem_outN.mp hz
    have hz2 : z ∈ ball D W u 2 := ball_step (mem_ball_one_of_out hy) hzW hyz
    by_cases hz1 : z ∈ ball D W u 1
    · rcases (mem_ball_one hu).mp hz1 with rfl | hz1
      · exact absurd hyz (no_back_arc hfree hzW (mem_ball_one_of_out hy) (by omega))
      · exact Or.inl hz1
    · exact Or.inr (Finset.mem_sdiff.mpr ⟨hz2, hz1⟩)
  have memO : ∀ y z (S : Finset ℕ), outN D W y = S → z ∈ S → D y z = true := by
    intro y z S h hz
    rw [← h] at hz
    exact (mem_outN.mp hz).2
  -- `O(v) = {v', g, g'}`
  have hOv : outN D W v = {v', g, g'} := by
    refine Finset.eq_of_subset_of_card_le ?_ (by rw [hout v hvW]; exact Finset.card_le_three)
    intro z hz
    have hvz := (mem_outN.mp hz).2
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases outN1 v hv z hz with hz1 | hz2
    · rcases hN1mem z hz1 with rfl | rfl | rfl
      · exact absurd hvz (loopfree hfree (by omega) hvW)
      · exact absurd hvz hv_c
      · exact Or.inl rfl
    · rcases hN2mem z hz2 with rfl | rfl | rfl
      · exact absurd hvz hv_t
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
  have hvv' : D v v' = true := memO _ _ _ hOv (by simp)
  have hvg : D v g = true := memO _ _ _ hOv (by simp)
  have hvg' : D v g' = true := memO _ _ _ hOv (by simp)
  -- `O(v') = {c, g, g'}`
  have hOv' : outN D W v' = {c, g, g'} := by
    refine Finset.eq_of_subset_of_card_le ?_ (by rw [hout v' hv'W]; exact Finset.card_le_three)
    intro z hz
    have hv'z := (mem_outN.mp hz).2
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases outN1 v' hv' z hz with hz1 | hz2
    · rcases hN1mem z hz1 with rfl | rfl | rfl
      · exact absurd hv'z (fun h => digonfree hfree (by omega) hvW hv'W hvv' h)
      · exact Or.inl rfl
      · exact absurd hv'z (loopfree hfree (by omega) hv'W)
    · rcases hN2mem z hz2 with rfl | rfl | rfl
      · exact absurd (ball_step (ball_of_adj hv'W hvv') htW hv'z) far
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
  have hv'g : D v' g = true := memO _ _ _ hOv' (by simp)
  have hv'g' : D v' g' = true := memO _ _ _ hOv' (by simp)
  -- a vertex `h ∈ {g, g'}` with no arc to the other one has all three arcs in `N_3`
  have kill : ∀ h h', h ∈ ball D W u 2 \ ball D W u 1 → D v h = true → D v' h = true →
      (∀ x ∈ ball D W u 2 \ ball D W u 1, x = t ∨ x = h ∨ x = h') → ¬ D h h' = true → False := by
    intro h h' hh hvh hv'h hcov hhh'
    have hhW := hN2W hh
    have hh2 := (Finset.mem_sdiff.mp hh).1
    have hsub : outN D W h ⊆ ball D W u 3 \ ball D W u 2 := by
      intro z hz
      obtain ⟨hzW, hhz⟩ := mem_outN.mp hz
      refine Finset.mem_sdiff.mpr ⟨ball_step hh2 hzW hhz, ?_⟩
      intro hz2
      by_cases hz1 : z ∈ ball D W u 1
      · rcases (mem_ball_one hu).mp hz1 with rfl | hz1
        · exact no_back_arc hfree hzW hh2 (by omega) hhz
        · rcases hN1mem z hz1 with rfl | rfl | rfl
          · exact digonfree hfree (by omega) hvW hhW hvh hhz
          · exact digonfree hfree (by omega) hcW hhW (hcN2 h hh) hhz
          · exact digonfree hfree (by omega) hv'W hhW hv'h hhz
      · rcases hcov z (Finset.mem_sdiff.mpr ⟨hz2, hz1⟩) with rfl | rfl | rfl
        · exact far (ball_step (ball_of_adj hhW hvh) htW hhz)
        · exact loopfree hfree (by omega) hhW hhz
        · exact hhh' hhz
    have := Finset.card_le_card hsub
    rw [hout h hhW] at this
    omega
  by_cases hgg : D g g' = true
  · have hg'g : ¬ D g' g = true := fun h => digonfree hfree (by omega) (hN2W hg) (hN2W hg') hgg h
    refine kill g' g hg' hvg' hv'g' ?_ hg'g
    intro x hx
    rcases hN2mem x hx with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)
  · exact kill g g' hg hvg hv'g hN2mem hgg

/-- **Lemma 7 (`TOP(3)`).** A 3-free digraph with out-degree exactly three has `|B_3(u)| ≥ 10`. -/
theorem top3 (hfree : QFree D W 3) (hout : OutEq 3 D W) (hu : u ∈ W) : 10 ≤ (ball D W u 3).card := by
  classical
  have h1 := card_ball_one (hfree.mono_bound (by omega)) hout hu
  have h12 : ball D W u 1 ⊆ ball D W u 2 := ball_mono_radius (by omega)
  have h23 : ball D W u 2 ⊆ ball D W u 3 := ball_mono_radius (by omega)
  have e2 := Finset.card_sdiff_add_card_eq_card h12
  have e3 := Finset.card_sdiff_add_card_eq_card h23
  have h62 := six_two hfree hout hu
  by_contra hlt
  -- `n_3 = 0`: Lemma 1 and `Ball(3,3)`
  by_cases c0 : (ball D W u 3).card ≤ (ball D W u 2).card
  · obtain ⟨hout', hne⟩ := closed_outEq (q := 3) (k := 2) (by omega) (by omega) hfree hout hu c0
    have hUW : (ball D W u 2).erase u ⊆ W := (Finset.erase_subset _ _).trans ball_subset
    have hfE : QFree D ((ball D W u 2).erase u) 3 := hfree.mono_set hUW
    have hc := card_ge_of_ball (q := 3) (s := 3) (b := 7) (by omega) hfE
      (fun y hy => (hout' y hy).ge) (fun z hz => ball_three_three hfE hout' hz) hne
    have := Finset.card_erase_of_mem (self_mem_ball (D := D) (k := 2) hu)
    omega
  -- `n_3 = 1`: Lemma 2
  by_cases c1 : (ball D W u 3).card ≤ (ball D W u 2).card + 1
  · have := corB_layer_strict (q := 3) (k := 2) (by omega) (by omega) hfree hout hu
      (fun y _ => by
        change (outN D W y ∩ (ball D W u 3 \ ball D W u 2)).card ≤ 1
        exact (Finset.card_le_card Finset.inter_subset_right).trans (by omega))
    omega
  -- `n_3 = 2`, `n_2 = 3`
  exact top3_thin hfree hout hu (by omega) (by omega)

/-- `TOP(3)` as a statement about all digraphs. -/
theorem top3_TOP : TOP 3 := fun _ _ hfree hout _ hu => top3 hfree hout hu

end LeanCH.BR.BRq3
