import LeanCH.BR.BRq3Rewire

/-!
# Route 1, Lemmas 1 and 2: the diameter lemma and the weak top (Lean 4.35.0)

Paper: `checkpoints/boundary_20261111/Route1_PiIteration_subagent.md`, §3 (Lemma 1, Lemma 2).

* `in_sub`: in-neighbours of `y` lie in `W ∖ B_{j-1}(y)` in a `j`-free digraph.
* `in_eq_three`: with `Ball(j,3)`, a `j`-free out-3 digraph on `≤ 3j+1` vertices has every in-degree exactly three
  (degree sum).
* `diam_small` (**Lemma 1**, excess 0): such a digraph has `B_j(v) = W` for every `v`.
* `top_ge_ball` (**Lemma 2**, weak top): `Ball(k,3)` and `Ball(k+1,3)` give `|B_{k+1}(u)| ≥ 3(k+1)` in a `(k+1)`-free
  out-3 digraph. This is `top_ge` with `TOP(k)` replaced by `Ball(k,3)` through `diam_small` on the rewired digraph.
-/

set_option linter.style.longLine false

namespace LeanCH.BR.BRq3

open LeanCH.BR.BRq2

variable {D : CH.Digraph} {W : Finset ℕ} {u : ℕ}

/-- In-neighbours of `y` avoid `B_{j-1}(y)` in a `j`-free digraph. -/
theorem in_sub {j y : ℕ} (hj : 1 ≤ j) (hfree : QFree D W j) (hy : y ∈ W) :
    W.filter (fun a => D a y = true) ⊆ W \ ball D W y (j - 1) := by
  intro a ha
  obtain ⟨haW, hay⟩ := Finset.mem_filter.mp ha
  exact Finset.mem_sdiff.mpr ⟨haW, fun hab => no_back_arc hfree hy hab (by omega) hay⟩

/-- With `Ball(j,3)`, a `j`-free out-3 digraph on at most `3j+1` vertices has every in-degree exactly three. -/
theorem in_eq_three {j : ℕ} (hj : 1 ≤ j) (hball : Ball j 3) (hfree : QFree D W j) (hout : OutEq 3 D W)
    (hcard : W.card ≤ 3 * j + 1) : ∀ y ∈ W, (W.filter (fun a => D a y = true)).card = 3 := by
  have hle : ∀ y ∈ W, (W.filter (fun a => D a y = true)).card ≤ 3 := by
    intro y hy
    have h1 := Finset.card_le_card (in_sub hj hfree hy)
    rw [Finset.card_sdiff_of_subset ball_subset] at h1
    have h2 := hball D W hfree hout y hy
    omega
  have hsum : ∑ y ∈ W, (W.filter (fun a => D a y = true)).card = ∑ _y ∈ W, 3 :=
    calc ∑ y ∈ W, (W.filter (fun a => D a y = true)).card
        = ∑ x ∈ W, (W.filter (fun w => D x w = true)).card := (Compose.ThinRigid.sum_out_eq_sum_in D W).symm
      _ = ∑ _y ∈ W, 3 := Finset.sum_congr rfl (fun y hy => hout y hy)
  exact (Finset.sum_eq_sum_iff_of_le hle).mp hsum

/-- **Lemma 1 (diameter lemma, excess 0).** With `Ball(j,3)`, `j ≥ 1`, a `j`-free out-3 digraph on at most `3j+1`
vertices has `B_j(v) = W` for every `v ∈ W`. -/
theorem diam_small {j : ℕ} (hj : 1 ≤ j) (hball : Ball j 3) (hfree : QFree D W j) (hout : OutEq 3 D W)
    (hcard : W.card ≤ 3 * j + 1) : ∀ v ∈ W, ball D W v j = W := by
  intro v hv
  refine Finset.Subset.antisymm ball_subset (fun x hx => ?_)
  by_contra hxb
  have hsub : W.filter (fun a => D a x = true) ⊆ (W \ ball D W v (j - 1)).erase x := by
    intro a ha
    obtain ⟨haW, hax⟩ := Finset.mem_filter.mp ha
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_sdiff.mpr ⟨haW, fun hab => hxb ?_⟩⟩
    · rintro rfl; exact loopfree hfree hj hx hax
    · have := ball_step hab hx hax
      rwa [show j - 1 + 1 = j by omega] at this
  have hxin : x ∈ W \ ball D W v (j - 1) :=
    Finset.mem_sdiff.mpr ⟨hx, fun h => hxb (ball_mono_radius (by omega) h)⟩
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem hxin, Finset.card_sdiff_of_subset ball_subset] at h1
  have h2 := hball D W hfree hout v hv
  have h3 := in_eq_three hj hball hfree hout hcard x hx
  omega

/-- **Lemma 2 (weak top).** `Ball(k,3)` and `Ball(k+1,3)` give `|B_{k+1}(u)| ≥ 3(k+1)` in a `(k+1)`-free digraph
with out-degree three. -/
theorem top_ge_ball {k : ℕ} (hk : 1 ≤ k) (hbk : Ball k 3) (hball : Ball (k + 1) 3) (hfree : QFree D W (k + 1))
    (hout : OutEq 3 D W) (hu : u ∈ W) : 3 * (k + 1) ≤ (ball D W u (k + 1)).card := by
  classical
  by_contra hlt
  have hbk1 : 3 * k + 1 ≤ (ball D W u k).card := by
    have := hball D W hfree hout u hu
    rwa [show k + 1 - 1 = k by omega] at this
  have hsub : ball D W u k ⊆ ball D W u (k + 1) := ball_mono_radius (by omega)
  have eK := Finset.card_sdiff_add_card_eq_card hsub
  -- `n_{k+1} = 0`: the closed layer and `Ball(k+1,3)` with the degree sum
  by_cases c0 : (ball D W u (k + 1)).card ≤ (ball D W u k).card
  · obtain ⟨hout', hne⟩ := closed_outEq (q := k + 1) (k := k) hk le_rfl hfree hout hu c0
    have hUW : (ball D W u k).erase u ⊆ W := (Finset.erase_subset _ _).trans ball_subset
    have hfE : QFree D ((ball D W u k).erase u) (k + 1) := hfree.mono_set hUW
    have hc := card_ge_of_ball (q := k + 1) (s := 3) (b := 3 * k + 1) (by omega) hfE
      (fun y hy => (hout' y hy).ge)
      (fun z hz => by
        have := hball D _ hfE hout' z hz
        rwa [show k + 1 - 1 = k by omega] at this) hne
    have := Finset.card_erase_of_mem (self_mem_ball (D := D) (k := k) hu)
    omega
  -- `n_{k+1} = 1` and `|V| ≤ 3k+1`
  obtain ⟨x, hx⟩ : (ball D W u (k + 1) \ ball D W u k).Nonempty := by
    rw [← Finset.card_pos]; omega
  have hK1 : (ball D W u (k + 1) \ ball D W u k).card = 1 := by omega
  have hVW : (ball D W u (k + 1)).erase u ⊆ W := (Finset.erase_subset _ _).trans ball_subset
  have hV : ((ball D W u (k + 1)).erase u).card ≤ 3 * k + 1 := by
    rw [Finset.card_erase_of_mem (self_mem_ball hu)]; omega
  obtain ⟨hx1, hxk⟩ := Finset.mem_sdiff.mp hx
  obtain ⟨p, hp, hpx⟩ := ball_succ_pred hu hx1 hxk
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hpj : p ∉ ball D W u j := fun h => hxk (ball_step h (ball_subset hx1) hpx)
  have hpW : p ∈ W := ball_subset hp
  -- an out-neighbour `z ≠ x` of `p`
  obtain ⟨z, hz⟩ : ((outN D W p).erase x).Nonempty := by
    rw [← Finset.card_pos]
    have := Finset.pred_card_le_card_erase (s := outN D W p) (a := x)
    rw [hout p hpW] at this
    omega
  obtain ⟨hzx, hz'⟩ := Finset.mem_erase.mp hz
  obtain ⟨hzW, hpz⟩ := mem_outN.mp hz'
  have hzV : z ∈ (ball D W u (j + 1 + 1)).erase u := by
    refine Finset.mem_erase.mpr ⟨?_, ball_step hp hzW hpz⟩
    intro hzu
    rw [hzu] at hpz
    exact no_back_arc hfree hu hp le_rfl hpz
  have hpV : p ∈ (ball D W u (j + 1 + 1)).erase u := by
    refine Finset.mem_erase.mpr ⟨?_, hsub hp⟩
    intro hpu
    rw [hpu] at hpj
    exact hpj (self_mem_ball hu)
  have hzK : z ∉ ball D W u (j + 1 + 1) \ ball D W u (j + 1) :=
    fun h => hzx (Finset.card_le_one.mp hK1.le z h x hx)
  -- Lemma 1 on the rewired digraph: `B♮_k(z) = V`
  have hDout := rewire_outEq (q := j + 1 + 1) (k := j + 1) le_rfl hfree hout hu
  have hDfree := rewire_qfree (u := u) (q := j + 1 + 1) (k := j + 1) (by omega) hfree
  have hdiam := diam_small (j := j + 1) (by omega) hbk hDfree hDout hV z hzV
  have hpb : p ∈ ball (rewire D u (ball D W u (j + 1 + 1) \ ball D W u (j + 1)))
      ((ball D W u (j + 1 + 1)).erase u) z (j + 1) := by
    rw [hdiam]; exact hpV
  -- the π-step: `p ∉ B♮_k(z)`
  obtain ⟨_, m, hm, w⟩ := mem_ball.mp hpb
  rcases rewire_walk hVW w with ⟨h, _⟩ | ⟨c, hc, m1, m2, hsum, _, w1, w2⟩
  · exact hfree z (m + 1) (by omega) (by omega) (h.snoc hzW hpz)
  · exact hpj (rewire_far hzK hc hsum (by omega) w1 w2 hpW)

end LeanCH.BR.BRq3
