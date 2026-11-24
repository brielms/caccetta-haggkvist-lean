import LeanCH.BR.BRq3Util

/-!
# Route 1 for general out-degree `s`: the diameter lemma (Lean 4.35.0)

Paper: `checkpoints/boundary_20261111/Route1_GeneralS_subagent.md`, §1 (Lemma 1_s), the `s = 3` case being
`BRq3Diam.lean` (`in_eq_three`, `diam_small`). Copied with `3` replaced by `s`; no existing file is changed.

* `in_sub_s`: in-neighbours of `y` lie in `W ∖ B_{j-1}(y)` in a `j`-free digraph.
* `in_eq_s`: with `Ball(j,s)`, a `j`-free out-`s` digraph on `≤ sj+1` vertices has every in-degree exactly `s`.
* `diam_small_s` (**Lemma 1_s**, excess 0): such a digraph has `B_j(v) = W` for every `v`.
* `card_eq_of_ball_s`: such a digraph has exactly `sj+1` vertices (when `W` is nonempty).
-/

set_option linter.style.longLine false

namespace LeanCH.BR.BRsGen

open LeanCH.BR.BRq2 LeanCH.BR.BRq3

variable {D : CH.Digraph} {W : Finset ℕ}

/-- In-neighbours of `y` avoid `B_{j-1}(y)` in a `j`-free digraph. -/
theorem in_sub_s {j y : ℕ} (hj : 1 ≤ j) (hfree : QFree D W j) (hy : y ∈ W) :
    W.filter (fun a => D a y = true) ⊆ W \ ball D W y (j - 1) := by
  intro a ha
  obtain ⟨haW, hay⟩ := Finset.mem_filter.mp ha
  exact Finset.mem_sdiff.mpr ⟨haW, fun hab => no_back_arc hfree hy hab (by omega) hay⟩

/-- With `Ball(j,s)`, a `j`-free out-`s` digraph on at most `sj+1` vertices has every in-degree exactly `s`. -/
theorem in_eq_s {j s : ℕ} (hj : 1 ≤ j) (hball : Ball j s) (hfree : QFree D W j) (hout : OutEq s D W)
    (hcard : W.card ≤ s * j + 1) : ∀ y ∈ W, (W.filter (fun a => D a y = true)).card = s := by
  have hsj : s * (j - 1) + s = s * j := by
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    rw [Nat.add_sub_cancel, Nat.mul_add_one]
  have hle : ∀ y ∈ W, (W.filter (fun a => D a y = true)).card ≤ s := by
    intro y hy
    have h1 := Finset.card_le_card (in_sub_s hj hfree hy)
    rw [Finset.card_sdiff_of_subset ball_subset] at h1
    have h2 := hball D W hfree hout y hy
    omega
  have hsum : ∑ y ∈ W, (W.filter (fun a => D a y = true)).card = ∑ _y ∈ W, s :=
    calc ∑ y ∈ W, (W.filter (fun a => D a y = true)).card
        = ∑ x ∈ W, (W.filter (fun w => D x w = true)).card := (Compose.ThinRigid.sum_out_eq_sum_in D W).symm
      _ = ∑ _y ∈ W, s := Finset.sum_congr rfl (fun y hy => hout y hy)
  exact (Finset.sum_eq_sum_iff_of_le hle).mp hsum

/-- **Lemma 1_s (diameter lemma, excess 0).** With `Ball(j,s)`, `j ≥ 1`, a `j`-free out-`s` digraph on at most
`sj+1` vertices has `B_j(v) = W` for every `v ∈ W`. -/
theorem diam_small_s {j s : ℕ} (hj : 1 ≤ j) (hball : Ball j s) (hfree : QFree D W j) (hout : OutEq s D W)
    (hcard : W.card ≤ s * j + 1) : ∀ v ∈ W, ball D W v j = W := by
  have hsj : s * (j - 1) + s = s * j := by
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    rw [Nat.add_sub_cancel, Nat.mul_add_one]
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
  have h3 := in_eq_s hj hball hfree hout hcard x hx
  have h5 : 0 < (W \ ball D W v (j - 1)).card := Finset.card_pos.mpr ⟨x, hxin⟩
  rw [Finset.card_sdiff_of_subset ball_subset] at h5
  have h4 := Finset.card_le_card (ball_subset (D := D) (W := W) (u := v) (k := j - 1))
  omega

/-- Lemma 1_s, first item: a nonempty such digraph has exactly `sj+1` vertices. -/
theorem card_eq_of_ball_s {j s : ℕ} (hj : 1 ≤ j) (hball : Ball j s) (hfree : QFree D W j) (hout : OutEq s D W)
    (hcard : W.card ≤ s * j + 1) (hne : W.Nonempty) : W.card = s * j + 1 := by
  obtain ⟨v, hv⟩ := hne
  have hsj : s * (j - 1) + s = s * j := by
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    rw [Nat.add_sub_cancel, Nat.mul_add_one]
  have h1 := Finset.card_le_card (in_sub_s hj hfree hv)
  rw [Finset.card_sdiff_of_subset ball_subset] at h1
  have h2 := hball D W hfree hout v hv
  have h3 := in_eq_s hj hball hfree hout hcard v hv
  have h4 := Finset.card_le_card (ball_subset (D := D) (W := W) (u := v) (k := j - 1))
  omega

end LeanCH.BR.BRsGen
