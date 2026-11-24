import LeanCH.BR.BRq4Rigid
import LeanCH.BR.BRq3Ball4

/-!
# `Ball(4,4)`, `BR(4,4)` and CH at `r = 4` for `n ≤ 16` (Lean 4.35.0)

Paper: `checkpoints/boundary_20261111/BallQ4_attempt_subagent.md`, §2, Proposition 5.

* `ball44` (**Proposition 5**): every `4`-free digraph with out-degree exactly four has `|B_3(u)| ≥ 13`.
  With `U = B_2 ∖ {u}` (so `|U| = 4 + n_2`), every vertex of `U` keeps `≥ 4 - n_3` arcs in `U` and `N_1` keeps all
  four. Cases on `n_3`:
  - `n_3 ≥ 4`: `n_2 ≥ 4` (`n2_ge_four`);
  - `n_3 = 3`: `n_2 ≠ 4` by `rigid` (Lemma 4);
  - `n_3 = 2` ((P3′) with `δ = 2`): min out `≥ 2` on `U` and one vertex of out `≥ 3` give `|U| ≥ 10`
    (`card_ge_of_ball_strict` with the radius-3 bound `7` of `ball_growth`); this is the degree sum behind BR(4,2);
  - `n_3 ≤ 1` (`δ ≥ 3`): min out `≥ 3` on `U` gives `|U| ≥ 13` (`card_ge_of_ball` with `Ball(4,3)` = `ball43`);
    this is CH(3) at `q = 4` on a vertex set.
* `br_four_four`: `BoundaryRegular 4 4` (`br_of_ball`).
* `ch_four_le_sixteen`, `ch_four_ceil`: CH at `r = 4` for `n ≤ 16` in the `q = 4` form, and in the `⌈n/4⌉` form for
  `13 ≤ n ≤ 16`.
-/

set_option linter.style.longLine false

namespace LeanCH.BR.BRq4

open LeanCH.BR.BRq2 LeanCH.BR.BRq3 Compose.Boundary

variable {D : CH.Digraph} {W : Finset ℕ} {u : ℕ}

theorem card_ball_one_four (hfree : QFree D W 4) (hout : OutEq 4 D W) (hu : u ∈ W) :
    (ball D W u 1).card = 5 := by
  classical
  have e : ball D W u 1 = insert u (outN D W u) := by
    ext v; rw [mem_ball_one hu, Finset.mem_insert]
  have hnot : u ∉ outN D W u := fun h => loopfree hfree (by omega) hu (mem_outN.mp h).2
  rw [e, Finset.card_insert_of_notMem hnot, hout u hu]

/-- **Proposition 5 (`Ball(4,4)`), pointwise.** -/
theorem ball44_aux (hfree : QFree D W 4) (hout : OutEq 4 D W) (hu : u ∈ W) : 13 ≤ (ball D W u 3).card := by
  classical
  have hb1 := card_ball_one_four hfree hout hu
  have h12 : ball D W u 1 ⊆ ball D W u 2 := ball_mono_radius (by omega)
  have h23 : ball D W u 2 ⊆ ball D W u 3 := ball_mono_radius (by omega)
  have e2 : (lay2 D W u).card + (ball D W u 1).card = (ball D W u 2).card :=
    Finset.card_sdiff_add_card_eq_card h12
  have e3 : (lay3 D W u).card + (ball D W u 2).card = (ball D W u 3).card :=
    Finset.card_sdiff_add_card_eq_card h23
  have hn2 := n2_ge_four hfree hout hu
  -- `U = B_2 ∖ {u}`
  have hUc : ((ball D W u 2).erase u).card + 1 = (ball D W u 2).card :=
    Finset.card_erase_add_one (self_mem_ball hu)
  have hUW : (ball D W u 2).erase u ⊆ W := (Finset.erase_subset _ _).trans ball_subset
  have hfU : QFree D ((ball D W u 2).erase u) 4 := hfree.mono_set hUW
  -- every vertex of `U` keeps `≥ 4 - n_3` arcs in `U`
  have hmin : ∀ y ∈ (ball D W u 2).erase u, 4 ≤ (outN D ((ball D W u 2).erase u) y).card + (lay3 D W u).card := by
    intro y hy
    have hy2 : y ∈ ball D W u 2 := Finset.mem_of_mem_erase hy
    have hsub : outN D W y \ lay3 D W u ⊆ outN D ((ball D W u 2).erase u) y := by
      intro c hc
      obtain ⟨hc1, hc3⟩ := Finset.mem_sdiff.mp hc
      obtain ⟨hcW, hyc⟩ := mem_outN.mp hc1
      have hc3' : c ∈ ball D W u 3 := ball_step hy2 hcW hyc
      have hc2 : c ∈ ball D W u 2 := by
        by_contra h
        exact hc3 (Finset.mem_sdiff.mpr ⟨hc3', h⟩)
      refine mem_outN.mpr ⟨Finset.mem_erase.mpr ⟨?_, hc2⟩, hyc⟩
      intro e
      rw [e] at hyc
      exact no_back_arc hfree hu hy2 (by omega) hyc
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_sdiff_add_card_inter (outN D W y) (lay3 D W u)
    have h3 := Finset.card_le_card (Finset.inter_subset_right (s₁ := outN D W y) (s₂ := lay3 D W u))
    rw [hout y (hUW hy)] at h2
    omega
  -- `N_1` keeps all four arcs
  obtain ⟨y0, hy0⟩ : (outN D W u).Nonempty := by rw [← Finset.card_pos, hout u hu]; omega
  have hy01 : y0 ∈ ball D W u 1 := mem_ball_one_of_out hy0
  have hy0U : y0 ∈ (ball D W u 2).erase u := by
    refine Finset.mem_erase.mpr ⟨?_, h12 hy01⟩
    intro e
    have h' := (mem_outN.mp hy0).2
    rw [e] at h'
    exact loopfree hfree (by omega) hu h'
  have hy04 : 4 ≤ (outN D ((ball D W u 2).erase u) y0).card := by
    have hsub : outN D W y0 ⊆ outN D ((ball D W u 2).erase u) y0 := by
      intro c hc
      obtain ⟨hcW, hyc⟩ := mem_outN.mp hc
      refine mem_outN.mpr ⟨Finset.mem_erase.mpr ⟨?_, ball_step hy01 hcW hyc⟩, hyc⟩
      intro e
      rw [e] at hyc
      exact no_back_arc hfree hu hy01 (by omega) hyc
    have := Finset.card_le_card hsub
    rwa [hout y0 (outN_subset hy0)] at this
  -- cases on `n_3`
  by_cases c4 : 4 ≤ (lay3 D W u).card
  · omega
  by_cases c3 : (lay3 D W u).card = 3
  · have : (lay2 D W u).card ≠ 4 := fun h => c4 (rigid hfree hout hu h)
    omega
  by_cases c2 : (lay3 D W u).card = 2
  · -- `(P3′)`, `δ = 2`: `|U| ≥ 10`
    have hm2 : ∀ y ∈ (ball D W u 2).erase u, 2 ≤ (outN D ((ball D W u 2).erase u) y).card := by
      intro y hy; have := hmin y hy; omega
    have hc := card_ge_of_ball_strict (q := 4) (b := 7) (by omega) hfU hm2 hy0U (by omega)
      (fun z hz => ball_growth 4 (by omega) D _ hfU hm2 z hz 3 (by omega))
    omega
  · -- `δ ≥ 3`: `|U| ≥ 13` from `Ball(4,3)`
    have hm3 : ∀ y ∈ (ball D W u 2).erase u, 3 ≤ (outN D ((ball D W u 2).erase u) y).card := by
      intro y hy; have := hmin y hy; omega
    obtain ⟨G', hsub', hout'⟩ := exists_outEq hm3
    have hfG' : QFree G' ((ball D W u 2).erase u) 4 := qfree_sub hsub' hfU
    have hc := card_ge_of_ball (q := 4) (s := 3) (b := 10) (by omega) hfU hm3
      (fun z hz => (ball43 hfG' hout' hz).trans (Finset.card_le_card (ball_sub hsub')))
      ⟨y0, hy0U⟩
    omega

/-- **Proposition 5: `Ball(4,4)`.** -/
theorem ball44 : Ball 4 4 :=
  fun _ _ hfree hout _ hu => ball44_aux hfree hout hu

/-- **`BR(4,4)`.** Every loopless digraph on `17` labels with minimum out-degree `4` and no directed cycle of length
at most `4` has every in-degree exactly `4`. -/
theorem br_four_four : BoundaryRegular 4 4 :=
  br_of_ball (by omega) ball44

/-- CH at degree four below the `q = 4` boundary: on `n ≤ 16` labels, min out `≥ 4` forces a cycle of length `≤ 4`. -/
theorem ch_four_le_sixteen {n : ℕ} (hn : 0 < n) (hn16 : n ≤ 16) {G : CH.Digraph}
    (loopless : CH.Loopless G n) (deg : CH.MinOutdegreeAtLeast G n 4) : CH.HasDirectedCycleAtMost G n 4 :=
  ch_of_boundaryRegular (by omega) br_four_four hn (by omega) loopless deg

/-- **CH at `r = 4` for `13 ≤ n ≤ 16`**: a cycle of length at most `⌈n/4⌉ = 4`. -/
theorem ch_four_ceil {n : ℕ} (hn13 : 13 ≤ n) (hn16 : n ≤ 16) {G : CH.Digraph}
    (loopless : CH.Loopless G n) (deg : CH.MinOutdegreeAtLeast G n 4) :
    CH.HasDirectedCycleAtMost G n (CH.ceilDiv n 4) := by
  have hc : CH.ceilDiv n 4 = 4 := by unfold CH.ceilDiv; omega
  rw [hc]
  exact ch_four_le_sixteen (by omega) hn16 loopless deg

end LeanCH.BR.BRq4
