import LeanCH.BR.BRq3Pad

/-!
# Route 1: `Ball(q,3)` and `BR(q,3)` for every `q`, and CH at `r = 3` (Lean 4.35.0)

Paper: `checkpoints/boundary_20261111/Route1_PiIteration_subagent.md`, §3 (Lemma 5), §4 (Theorem 6, Corollary 7).

Indexing: the paper's level `k ≥ 2` is `j + 2` here. `D` is `(j+4)`-free with out-degree three on `W`, `u ∈ W`,
`K = N_{j+3}(u)`, `V = B_{j+3}(u) ∖ {u}` and `F = rewire D u K`.

* `pi_target_mem_P` (**Lemma 5**): if `|V| ≤ 3(j+2)+2`, `p ∈ N_{j+2}`, `p → z` and `z ∉ K`, then `z → K`.
  Case A (`|B^F_{j+2}(z)| ≥ 3(j+2)+1`) is the a-step 1 of `prop8`; Case B (`= 3(j+2)`) uses `exit_lemma` on `F`.
  `|B^F_{j+2}(z)| ≥ 3(j+2)` is `top_ge_ball` on `F`.
* `prop8_ball_aux` / `prop8_ball` (**Theorem 6**): `Ball(k-1), Ball(k), Ball(k+1) ⇒ Ball(k+2)` for `k ≥ 2`, with the
  sink of `D[P]` (`exists_sink`).
* `ball_all` (**Corollary 7**): `Ball(q,3)` for every `q ≥ 1`. `br_q_three`: `BR(q,3)` for every `q ≥ 1`.
* `ch_three_all`: a loopless digraph on `n > 0` vertices with min out-degree `3` has a directed cycle of length
  `≤ ⌈n/3⌉` (Hamidoune's theorem, CH at `r = 3`).
-/

set_option linter.style.longLine false

namespace LeanCH.BR.BRq3

open LeanCH.BR.BRq2

variable {D : CH.Digraph} {W : Finset ℕ} {u : ℕ}

/-- **Lemma 5 (the π-target lies in `P`).** Level `k = j + 2`. -/
theorem pi_target_mem_P {j p z : ℕ} (hb1 : Ball (j + 1) 3) (hb2 : Ball (j + 2) 3) (hfree : QFree D W (j + 4))
    (hout : OutEq 3 D W) (hu : u ∈ W) (hV : ((ball D W u (j + 3)).erase u).card ≤ 3 * (j + 2) + 2)
    (hp : p ∈ ball D W u (j + 2)) (hp1 : p ∉ ball D W u (j + 1)) (hpz : D p z = true) (hzW : z ∈ W)
    (hzK : z ∉ ball D W u (j + 3) \ ball D W u (j + 2)) :
    ∃ c ∈ ball D W u (j + 3) \ ball D W u (j + 2), D z c = true := by
  classical
  have hVW : (ball D W u (j + 3)).erase u ⊆ W := (Finset.erase_subset _ _).trans ball_subset
  have hpW : p ∈ W := ball_subset hp
  have hzV : z ∈ (ball D W u (j + 3)).erase u := by
    refine Finset.mem_erase.mpr ⟨?_, ball_step hp hzW hpz⟩
    intro hzu
    rw [hzu] at hpz
    exact no_back_arc hfree hu hp (by omega) hpz
  have hpV : p ∈ (ball D W u (j + 3)).erase u := by
    refine Finset.mem_erase.mpr ⟨?_, ball_mono_radius (by omega) hp⟩
    intro hpu; rw [hpu] at hp1; exact hp1 (self_mem_ball hu)
  have hDout : OutEq 3 (rewire D u (ball D W u (j + 3) \ ball D W u (j + 2))) ((ball D W u (j + 3)).erase u) :=
    rewire_outEq (q := j + 4) (k := j + 2) (by omega) hfree hout hu
  have hDfree : QFree (rewire D u (ball D W u (j + 3) \ ball D W u (j + 2))) ((ball D W u (j + 3)).erase u) (j + 2) :=
    rewire_qfree (k := j + 2) (by omega) hfree
  -- the π-step: `p ∉ B^F_k(z)`
  have hnot : p ∉ ball (rewire D u (ball D W u (j + 3) \ ball D W u (j + 2))) ((ball D W u (j + 3)).erase u) z (j + 2) := by
    intro hpb
    obtain ⟨_, m, hm, w⟩ := mem_ball.mp hpb
    rcases rewire_walk hVW w with ⟨h, _⟩ | ⟨c, hc, m1, m2, hsum, _, w1, w2⟩
    · exact hfree z (m + 1) (by omega) (by omega) (h.snoc hzW hpz)
    · exact hp1 (rewire_far hzK hc hsum (by omega) w1 w2 hpW)
  -- Lemma 2 on `F` (with `Ball(k-1)`, `Ball(k)`): `|B^F_k(z)| ≥ 3k`
  have hge : 3 * (j + 2) ≤
      (ball (rewire D u (ball D W u (j + 3) \ ball D W u (j + 2))) ((ball D W u (j + 3)).erase u) z (j + 2)).card :=
    top_ge_ball (k := j + 1) (by omega) hb1 hb2 hDfree hDout hzV
  by_cases hA : 3 * (j + 2) + 1 ≤
      (ball (rewire D u (ball D W u (j + 3) \ ball D W u (j + 2))) ((ball D W u (j + 3)).erase u) z (j + 2)).card
  · -- Case A: `B^F_k(z) = V ∖ {p}`; the parent `a ∈ N_{k-1}` of `p` forces `z → K`
    have hsub' : ball (rewire D u (ball D W u (j + 3) \ ball D W u (j + 2))) ((ball D W u (j + 3)).erase u) z (j + 2) ⊆
        ((ball D W u (j + 3)).erase u).erase p := by
      intro x hx
      refine Finset.mem_erase.mpr ⟨?_, ball_subset hx⟩
      intro hxp; rw [hxp] at hx; exact hnot hx
    have heq := Finset.eq_of_subset_of_card_le hsub' (by
      rw [Finset.card_erase_of_mem hpV]
      omega)
    obtain ⟨a, ha, hap⟩ := ball_succ_pred hu hp hp1
    have haj : a ∉ ball D W u j := fun h => hp1 (ball_step h hpW hap)
    have haW : a ∈ W := ball_subset ha
    have haV : a ∈ (ball D W u (j + 3)).erase u := by
      refine Finset.mem_erase.mpr ⟨?_, ball_mono_radius (by omega) ha⟩
      intro hau; rw [hau] at haj; exact haj (self_mem_ball hu)
    have hap' : a ≠ p := by intro h; rw [h] at ha; exact hp1 ha
    have haB : a ∈ ball (rewire D u (ball D W u (j + 3) \ ball D W u (j + 2))) ((ball D W u (j + 3)).erase u) z (j + 2) := by
      rw [heq]; exact Finset.mem_erase.mpr ⟨hap', haV⟩
    obtain ⟨_, m, hm, w⟩ := mem_ball.mp haB
    rcases rewire_walk hVW w with ⟨h, _⟩ | ⟨c, hc, m1, m2, hsum, _, w1, w2⟩
    · -- `z ⇝ a → p → z` is a closed walk of length `≤ k + 2`
      exact absurd ((h.snoc hpW hap).snoc hzW hpz) (hfree z (m + 1 + 1) (by omega) (by omega))
    · have hm2 : j + 1 ≤ m2 := by
        by_contra hlt2
        exact haj (mem_ball_of_walk w2 (by omega) haW)
      have hm1 : m1 = 1 := by
        have : m1 ≠ 0 := by
          rintro rfl
          rw [walk_zero w1] at hzK
          exact hzK hc
        omega
      subst hm1
      obtain ⟨_, hzc⟩ := walk_one w1
      rw [rewire_of_not_mem hzK] at hzc
      exact ⟨c, hc, hzc⟩
  · -- Case B: `|B^F_k(z)| = 3k`; the exit vertex `y` has `O_F(y) = {z, p, w}`
    have hBle : (ball (rewire D u (ball D W u (j + 3) \ ball D W u (j + 2))) ((ball D W u (j + 3)).erase u) z (j + 2)).card ≤
        3 * (j + 2) := by omega
    obtain ⟨y, hy, hyout⟩ := exit_lemma (k := j + 2) (by omega) hb2 hDfree hDout hzV hBle
    have hyV : y ∈ (ball D W u (j + 3)).erase u := ball_subset hy
    have hsubO : outN (rewire D u (ball D W u (j + 3) \ ball D W u (j + 2))) ((ball D W u (j + 3)).erase u) y ⊆
        insert z (((ball D W u (j + 3)).erase u) \
          ball (rewire D u (ball D W u (j + 3) \ ball D W u (j + 2))) ((ball D W u (j + 3)).erase u) z (j + 2)) := by
      intro b hb
      rcases hyout b hb with e | h
      · rw [e]; exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_sdiff.mpr ⟨(mem_outN.mp hb).1, h⟩)
    have hcard1 := Finset.card_insert_le z (((ball D W u (j + 3)).erase u) \
          ball (rewire D u (ball D W u (j + 3) \ ball D W u (j + 2))) ((ball D W u (j + 3)).erase u) z (j + 2))
    rw [Finset.card_sdiff_of_subset ball_subset] at hcard1
    have heqO := Finset.eq_of_subset_of_card_le hsubO (by rw [hDout y hyV]; omega)
    have hpO : p ∈ outN (rewire D u (ball D W u (j + 3) \ ball D W u (j + 2))) ((ball D W u (j + 3)).erase u) y := by
      rw [heqO]; exact Finset.mem_insert_of_mem (Finset.mem_sdiff.mpr ⟨hpV, hnot⟩)
    have hzO : z ∈ outN (rewire D u (ball D W u (j + 3) \ ball D W u (j + 2))) ((ball D W u (j + 3)).erase u) y := by
      rw [heqO]; exact Finset.mem_insert_self _ _
    have hyp := (mem_outN.mp hpO).2
    have hyz := (mem_outN.mp hzO).2
    -- `y ∉ K`: otherwise `y → p` would be the arc `u → p`, but `p ∈ N_k`, `k ≥ 2`
    have hyK : y ∉ ball D W u (j + 3) \ ball D W u (j + 2) := by
      intro hyK
      rw [rewire_of_mem hyK] at hyp
      exact hp1 (ball_mono_radius (by omega) (ball_of_adj hpW hyp))
    rw [rewire_of_not_mem hyK] at hyp hyz
    have hyW : y ∈ W := hVW hyV
    obtain ⟨_, m, hm, w⟩ := mem_ball.mp hy
    rcases rewire_walk hVW w with ⟨h, _⟩ | ⟨c, hc, m1, m2, hsum, _, w1, w2⟩
    · -- a `K`-free geodesic closes `z ⇝ y → z` of length `≤ k + 1`
      exact absurd (h.snoc hzW hyz) (hfree z (m + 1) (by omega) (by omega))
    · -- last-`K` decomposition: `depth(y) ≤ k - i` and `depth(y) ≥ k - 1` force `i = 1`
      have hm2 : j + 1 ≤ m2 := by
        by_contra hlt2
        exact hp1 (ball_step (mem_ball_of_walk w2 (by omega) hyW) hpW hyp)
      have hm1 : m1 = 1 := by
        have : m1 ≠ 0 := by
          rintro rfl
          rw [walk_zero w1] at hzK
          exact hzK hc
        omega
      subst hm1
      obtain ⟨_, hzc⟩ := walk_one w1
      rw [rewire_of_not_mem hzK] at hzc
      exact ⟨c, hc, hzc⟩

/-- **Theorem 6 (π-step without `TOP`)**, level `k = j + 2`: `Ball(k-1)`, `Ball(k)`, `Ball(k+1)` give
`|B_{k+1}(u)| ≥ 3(k+1)+1` in a `(k+2)`-free out-3 digraph. -/
theorem prop8_ball_aux {j : ℕ} (hb1 : Ball (j + 1) 3) (hb2 : Ball (j + 2) 3) (hb3 : Ball (j + 3) 3)
    (hfree : QFree D W (j + 4)) (hout : OutEq 3 D W) (hu : u ∈ W) :
    3 * (j + 3) + 1 ≤ (ball D W u (j + 3)).card := by
  have hbk : 3 * (j + 2) + 1 ≤ (ball D W u (j + 2)).card := by
    have := hb3 D W (hfree.mono_bound (by omega)) hout u hu
    rwa [show j + 3 - 1 = j + 2 by omega] at this
  have hbk1 : 3 * (j + 1) + 1 ≤ (ball D W u (j + 1)).card := by
    have := hb2 D W (hfree.mono_bound (by omega)) hout u hu
    rwa [show j + 2 - 1 = j + 1 by omega] at this
  by_contra hlt
  have hsub : ball D W u (j + 2) ⊆ ball D W u (j + 3) := ball_mono_radius (by omega)
  have eK := Finset.card_sdiff_add_card_eq_card hsub
  -- `n_{k+1} = 0`: the closed layer is `(k+1)`-free; in-degree count with `Ball(k+1)` (`card_ge_of_ball` at `k+1`)
  by_cases c0 : (ball D W u (j + 3)).card ≤ (ball D W u (j + 2)).card
  · obtain ⟨hout', hne⟩ := closed_outEq (q := j + 4) (k := j + 2) (by omega) (by omega) hfree hout hu c0
    have hUW : (ball D W u (j + 2)).erase u ⊆ W := (Finset.erase_subset _ _).trans ball_subset
    have hfE : QFree D ((ball D W u (j + 2)).erase u) (j + 3) := (hfree.mono_bound (by omega)).mono_set hUW
    have hc := card_ge_of_ball (q := j + 3) (s := 3) (b := 3 * (j + 2) + 1) (by omega) hfE
      (fun y hy => (hout' y hy).ge)
      (fun z hz => by
        have := hb3 D _ hfE hout' z hz
        rwa [show j + 3 - 1 = j + 2 by omega] at this) hne
    have := Finset.card_erase_of_mem (self_mem_ball (D := D) (k := j + 2) hu)
    omega
  -- `n_{k+1} ∈ {1, 2}` and `|V| ≤ 3k + 2`
  have hVcard : ((ball D W u (j + 3)).erase u).card ≤ 3 * (j + 2) + 2 := by
    rw [Finset.card_erase_of_mem (self_mem_ball hu)]; omega
  have hKcard : (ball D W u (j + 3) \ ball D W u (j + 2)).card ≤ 2 := by omega
  -- `P ⊆ N_k`, the vertices heading `K`; `|N_k| ≤ 4` by `Ball(k)`
  have hNk : (ball D W u (j + 2) \ ball D W u (j + 1)).card ≤ 4 := by
    rw [Finset.card_sdiff_of_subset (ball_mono_radius (by omega))]; omega
  have hPcard : ((ball D W u (j + 2) \ ball D W u (j + 1)).filter
      (fun p => (outN D (ball D W u (j + 3) \ ball D W u (j + 2)) p).Nonempty)).card ≤ 4 :=
    (Finset.card_filter_le _ _).trans hNk
  have hPW : (ball D W u (j + 2) \ ball D W u (j + 1)).filter
      (fun p => (outN D (ball D W u (j + 3) \ ball D W u (j + 2)) p).Nonempty) ⊆ W :=
    fun p hp => ball_subset (Finset.mem_sdiff.mp (Finset.mem_filter.mp hp).1).1
  have hPne : ((ball D W u (j + 2) \ ball D W u (j + 1)).filter
      (fun p => (outN D (ball D W u (j + 3) \ ball D W u (j + 2)) p).Nonempty)).Nonempty := by
    obtain ⟨c0, hc0⟩ : (ball D W u (j + 3) \ ball D W u (j + 2)).Nonempty := by
      rw [← Finset.card_pos]; omega
    obtain ⟨hc03, hc02⟩ := Finset.mem_sdiff.mp hc0
    obtain ⟨p, hp, hpc0⟩ := ball_succ_pred hu hc03 hc02
    have hp1 : p ∉ ball D W u (j + 1) := fun h => hc02 (ball_step h (ball_subset hc03) hpc0)
    exact ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hp, hp1⟩, c0, mem_outN.mpr ⟨hc0, hpc0⟩⟩⟩
  -- a sink `p` of `D[P]`
  obtain ⟨p, hpP, hsink⟩ := exists_sink ((hfree.mono_bound (by omega : 4 ≤ j + 4)).mono_set hPW) hPne hPcard
  obtain ⟨hpN, -⟩ := Finset.mem_filter.mp hpP
  obtain ⟨hp, hp1⟩ := Finset.mem_sdiff.mp hpN
  have hpW : p ∈ W := ball_subset hp
  -- an out-neighbour `z ∉ K` of `p`
  obtain ⟨z, hz⟩ : (outN D W p \ (ball D W u (j + 3) \ ball D W u (j + 2))).Nonempty := by
    rw [← Finset.card_pos]
    have h1 := Finset.le_card_sdiff (ball D W u (j + 3) \ ball D W u (j + 2)) (outN D W p)
    rw [hout p hpW] at h1
    omega
  obtain ⟨hz1, hzK⟩ := Finset.mem_sdiff.mp hz
  obtain ⟨hzW, hpz⟩ := mem_outN.mp hz1
  -- Lemma 5: `z → K`, so `z ∈ P`, against the choice of `p`
  obtain ⟨c, hc, hzc⟩ := pi_target_mem_P hb1 hb2 hfree hout hu hVcard hp hp1 hpz hzW hzK
  have hz3 : z ∈ ball D W u (j + 3) := ball_step hp hzW hpz
  have hz2 : z ∈ ball D W u (j + 2) := by
    by_contra h; exact hzK (Finset.mem_sdiff.mpr ⟨hz3, h⟩)
  have hz1' : z ∉ ball D W u (j + 1) :=
    fun h => (Finset.mem_sdiff.mp hc).2 (ball_step h (ball_subset (Finset.mem_sdiff.mp hc).1) hzc)
  exact hsink z (Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hz2, hz1'⟩, c, mem_outN.mpr ⟨hc, hzc⟩⟩) hpz

/-- **Theorem 6.** For `k ≥ 2`: `Ball(k-1,3)`, `Ball(k,3)`, `Ball(k+1,3)` give `Ball(k+2,3)`. -/
theorem prop8_ball {k : ℕ} (hk : 2 ≤ k) (hb1 : Ball (k - 1) 3) (hb2 : Ball k 3) (hb3 : Ball (k + 1) 3) :
    Ball (k + 2) 3 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
  intro D W hfree hout u hu
  rw [show j + 2 + 2 - 1 = j + 3 by omega]
  have := prop8_ball_aux (j := j) (by simpa using hb1) hb2 hb3 hfree hout hu
  omega

/-- **Corollary 7.** `Ball(q,3)` for every `q ≥ 1`. -/
theorem ball_all : ∀ q, 1 ≤ q → Ball q 3 := by
  intro q
  induction q using Nat.strong_induction_on with
  | _ q ih =>
  intro hq
  rcases (by omega : q = 1 ∨ q = 2 ∨ q = 3 ∨ 4 ≤ q) with rfl | rfl | rfl | h4
  · intro D W _ _ u hu
    change 1 ≤ (ball D W u 0).card
    exact Finset.card_pos.mpr ⟨u, self_mem_ball hu⟩
  · intro D W hfree hout u hu
    change 4 ≤ (ball D W u 1).card
    exact (card_ball_one (hfree.mono_bound (by omega)) hout hu).ge
  · intro D W hfree hout u hu
    change 7 ≤ (ball D W u 2).card
    exact ball_three_three hfree hout hu
  · obtain ⟨k, rfl⟩ : ∃ k, q = k + 2 := ⟨q - 2, by omega⟩
    exact prop8_ball (by omega) (ih (k - 1) (by omega) (by omega)) (ih k (by omega) (by omega))
      (ih (k + 1) (by omega) (by omega))

/-- Smoke test: `Ball(4,3)` through Theorem 6 at `k = 2`, from `Ball(1)`, `Ball(2)`, `Ball(3)` only. -/
theorem ball43_route1 : Ball 4 3 :=
  prop8_ball (k := 2) le_rfl (ball_all 1 le_rfl) (ball_all 2 (by omega)) (ball_all 3 (by omega))

/-- **`BR(q,3)` for every `q ≥ 1`.** -/
theorem br_q_three : ∀ q, 1 ≤ q → Compose.Boundary.BoundaryRegular q 3 :=
  fun q hq => br_of_ball hq (ball_all q hq)

/-- CH at degree three below the boundary: on `n ≤ 3q` labels, min out `≥ 3` forces a cycle of length `≤ q`. -/
theorem ch_three_of_le {q n : ℕ} (hq : 1 ≤ q) (hn : 0 < n) (hnq : n ≤ q * 3) {G : CH.Digraph}
    (loopless : CH.Loopless G n) (deg : CH.MinOutdegreeAtLeast G n 3) : CH.HasDirectedCycleAtMost G n q :=
  Compose.Boundary.ch_of_boundaryRegular (by omega) (br_q_three q hq) hn hnq loopless deg

/-- **The Caccetta–Häggkvist conjecture at `r = 3`** (Hamidoune's theorem): a cycle of length at most `⌈n/3⌉`. -/
theorem ch_three_all {n : ℕ} {G : CH.Digraph} (hn : 0 < n) (loopless : CH.Loopless G n)
    (deg : CH.MinOutdegreeAtLeast G n 3) : CH.HasDirectedCycleAtMost G n (CH.ceilDiv n 3) := by
  have hc : CH.ceilDiv n 3 = (n + 2) / 3 := by unfold CH.ceilDiv; omega
  exact ch_three_of_le (q := CH.ceilDiv n 3) (by omega) hn (by omega) loopless deg

end LeanCH.BR.BRq3
