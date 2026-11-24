import LeanCH.BR.BRsubSetBall21
import LeanCH.BR.BRsubSC
import LeanCH.BR.BRFiveCutoff

/-! A tight-first-layer profile exclusion at boundary order 31. -/

namespace LeanCH.BR.BRsub

open BRq2 BRq3 BR45

variable {E : CH.Digraph} {V : Finset ℕ} {u : ℕ}

/-- When every first-layer vertex heads every second-layer vertex,
the first three set balls of the second layer are the corresponding
root balls with the root and its first layer removed. -/
theorem second_layer_set_ball (hf : QFree E V 5) (hu : u ∈ V)
    (hhead : ∀ x ∈ outN E V u, ∀ y ∈ ball E V u 2 \ ball E V u 1, E x y = true)
    {k : ℕ} (hk : k ≤ 2) :
    ballSet E V (ball E V u 2 \ ball E V u 1) k = ball E V u (k + 2) \ ball E V u 1 := by
  let Y := ball E V u 2 \ ball E V u 1
  have hYV : Y ⊆ V := fun _ hy => ball_subset (Finset.mem_sdiff.mp hy).1
  have hd := (lemmaM_a (q := 5) (by decide) hf outN_subset hYV hhead).1
  have hnotu : u ∉ ballSet E V Y 2 := by
    intro h
    obtain ⟨y, hy, hyu⟩ := mem_ballSet.mp h
    obtain ⟨_, m, hm, wm⟩ := mem_ball.mp (Finset.mem_sdiff.mp hy).1
    obtain ⟨_, n, hn, wn⟩ := mem_ball.mp hyu
    have hmpos : 0 < m := by
      cases m with
      | zero => cases wm; exact ((Finset.mem_sdiff.mp hy).2 (self_mem_ball hu)).elim
      | succ m => omega
    exact hf u (m + n) (by omega) (by omega) (wm.append wn)
  have hforward {j : ℕ} (hj : j ≤ 2) : ballSet E V Y j ⊆ ball E V u (j + 2) \ ball E V u 1 := by
    intro z hz
    obtain ⟨y, hy, hyz⟩ := mem_ballSet.mp hz
    obtain ⟨_, m, hm, wm⟩ := mem_ball.mp (Finset.mem_sdiff.mp hy).1
    obtain ⟨hzV, n, hn, wn⟩ := mem_ball.mp hyz
    refine Finset.mem_sdiff.mpr ⟨mem_ball.mpr ⟨hzV, m + n, by omega, wm.append wn⟩, ?_⟩
    intro hz1
    rcases (mem_ball_one hu).mp hz1 with hzu | hzO
    · exact hnotu (hzu ▸ ballSet_mono hj hz)
    · exact Finset.disjoint_left.mp hd hzO (ballSet_mono (by omega : j ≤ 3) hz)
  have hreverse : ∀ j, j ≤ 2 → ball E V u (j + 2) \ ball E V u 1 ⊆ ballSet E V Y j := by
    intro j
    induction j with
    | zero =>
      intro _ z hz
      exact subset_ballSet hYV hz
    | succ j ih =>
      intro hj z hz
      obtain ⟨hzNext, hz1⟩ := Finset.mem_sdiff.mp hz
      by_cases hzOld : z ∈ ball E V u (j + 2)
      · exact ballSet_mono (by omega : j ≤ j + 1) (ih (by omega) (Finset.mem_sdiff.mpr ⟨hzOld, hz1⟩))
      · have hzNext' : z ∈ ball E V u ((j + 2) + 1) := by simpa [Nat.add_assoc] using hzNext
        obtain ⟨y, hy, hyz⟩ := ball_succ_pred hu hzNext' hzOld
        have hy1 : y ∉ ball E V u 1 := by
          intro h
          exact hzOld (ball_mono_radius (by omega : 2 ≤ j + 2) (ball_step h (ball_subset hzNext) hyz))
        have hySet := ih (by omega) (Finset.mem_sdiff.mpr ⟨hy, hy1⟩)
        exact outN_subset_ballSet_succ hySet (mem_outN.mpr ⟨ball_subset hzNext, hyz⟩)
  exact Finset.Subset.antisymm (hforward hk) (hreverse k hk)

/-- The tight-first-layer profile `(6,5,6,5)` is impossible in a
saturated `(5,6)` boundary graph. -/
theorem no_tight_6565 (hf : QFree E V 5) (hsat : Sat 5 E V)
    (hV : V.card = 31) (hmin : ∀ x ∈ V, 6 ≤ (outN E V x).card)
    (hu : u ∈ V) (ht : TightRoot E V 6 u)
    (h3 : (ball E V u 3 \ ball E V u 2).card = 6)
    (h4 : (ball E V u 4 \ ball E V u 3).card = 5) : False := by
  let Y := ball E V u 2 \ ball E V u 1
  have hYV : Y ⊆ V := fun _ hy => ball_subset (Finset.mem_sdiff.mp hy).1
  have hhead : ∀ x ∈ outN E V u, ∀ y ∈ Y, E x y = true := by
    intro x hx y hy
    exact (ht.2.2 x hx).2.2.2 y (Finset.mem_sdiff.mp hy).1 (Finset.mem_sdiff.mp hy).2
  have h1 := second_layer_set_ball hf hu hhead (by decide : 1 ≤ 2)
  have h2 := second_layer_set_ball hf hu hhead (by decide : 2 ≤ 2)
  have hB : ballSet E V Y 1 \ Y = ball E V u 3 \ ball E V u 2 := by
    rw [h1]
    ext z
    simp only [Finset.mem_sdiff, Y]
    have h12 : z ∈ ball E V u 1 → z ∈ ball E V u 2 := fun hz => ball_mono_radius (by decide : 1 ≤ 2) hz
    tauto
  have hC : ballSet E V Y 2 \ ballSet E V Y 1 = ball E V u 4 \ ball E V u 3 := by
    rw [h2, h1]
    ext z
    simp only [Finset.mem_sdiff]
    have h13 : z ∈ ball E V u 1 → z ∈ ball E V u 3 := fun hz => ball_mono_radius (by decide : 1 ≤ 3) hz
    tauto
  exact no_five_six_five_set_layers hf hsat hV hmin hYV ht.2.1
    (by rw [hB]; exact h3) (by rw [hC]; exact h4)

/-- The cutoff-five degree-five result excludes every deficient profile
whose fourth layer has at most one vertex. No saturation is needed. -/
theorem fourth_layer_ge_two (hf : QFree E V 5) (hu : u ∈ V)
    (hmin : ∀ x ∈ V, 6 ≤ (outN E V x).card)
    (hb4 : (ball E V u 4).card ≤ 24) :
    2 ≤ (ball E V u 4 \ ball E V u 3).card := by
  by_contra hsmall
  let U := ball E V u 3
  let K := ball E V u 4 \ U
  have hK : K.card ≤ 1 := by change (ball E V u 4 \ ball E V u 3).card ≤ 1; omega
  have hUK : U ∪ K = ball E V u 4 := Finset.union_sdiff_of_subset (ball_mono_radius (by decide))
  have hminU : ∀ v ∈ U, 5 ≤ (outN E U v).card := by
    intro v hv
    have hsub : outN E V v ⊆ outN E (U ∪ K) v := by
      intro z hz
      refine mem_outN.mpr ⟨?_, (mem_outN.mp hz).2⟩
      rw [hUK]
      exact ball_step hv (mem_outN.mp hz).1 (mem_outN.mp hz).2
    have hle := Finset.card_le_card hsub
    rw [card_outN_union Finset.disjoint_sdiff] at hle
    change (outN E V v).card ≤ (outN E U v).card + (outN E K v).card at hle
    have hcap := Finset.card_le_card (outN_subset (D := E) (W := K) (y := v))
    have h6 := hmin v (ball_subset hv)
    omega
  have hsize := BRsGen.card_ge_twenty_six (hf.mono_set ball_subset) hminU ⟨u, self_mem_ball hu⟩
  have hle := Finset.card_le_card (ball_mono_radius (D := E) (W := V) (u := u) (by decide : 3 ≤ 4))
  change 26 ≤ (ball E V u 3).card at hsize
  omega

/-- The entire tight-first-layer branch of the strict cap at `(5,6)`:
a tight root has a radius-four ball of at least 24 vertices. -/
theorem tight_six_ball_four_ge_twenty_four (hf : QFree E V 5) (hsat : Sat 5 E V)
    (hV : V.card = 31) (hmin : ∀ x ∈ V, 6 ≤ (outN E V x).card)
    (hu : u ∈ V) (ht : TightRoot E V 6 u) : 24 ≤ (ball E V u 4).card := by
  let Y := ball E V u 2 \ ball E V u 1
  have hYV : Y ⊆ V := fun _ hy => ball_subset (Finset.mem_sdiff.mp hy).1
  have hhead : ∀ x ∈ outN E V u, ∀ y ∈ Y, E x y = true := by
    intro x hx y hy
    exact (ht.2.2 x hx).2.2.2 y (Finset.mem_sdiff.mp hy).1 (Finset.mem_sdiff.mp hy).2
  have h17 := card_ballSet_two_ge_seventeen hf hsat hV hmin hYV ht.2.1
  rw [second_layer_set_ball hf hu hhead (by decide : 2 ≤ 2)] at h17
  change 17 ≤ (ball E V u 4 \ ball E V u 1).card at h17
  have hsum := Finset.card_sdiff_add_card_eq_card
    (ball_mono_radius (D := E) (W := V) (u := u) (by decide : 1 ≤ 4))
  have h1 := card_B1 (hf.mono_bound (by decide)) hu
  have ho := ht.1
  omega

end LeanCH.BR.BRsub
