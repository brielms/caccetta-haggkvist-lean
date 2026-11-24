import LeanCH.BR.BRThreeTightStages

/-! An arbitrary tight BFS prefix forbids back arcs and forces the next layer to expand. -/

namespace LeanCH.BR.BRsGen
open BRq2 BRq3 BR45

theorem ball_mem_positive_layer {D : CH.Digraph} {V : Finset ℕ} {u x m : ℕ}
    (hx : x ∈ ball D V u m) (hne : x ≠ u) :
    ∃ i, 1 ≤ i ∧ i ≤ m ∧ x ∈ ball D V u i \ ball D V u (i - 1) := by
  induction m with
  | zero => exact (hne (eq_of_mem_ball_zero hx)).elim
  | succ m ih =>
    by_cases hold : x ∈ ball D V u m
    · obtain ⟨i, hi, him, hxi⟩ := ih hold
      exact ⟨i, hi, by omega, hxi⟩
    · exact ⟨m + 1, by omega, le_rfl, Finset.mem_sdiff.mpr ⟨hx, by simpa using hold⟩⟩

theorem layer_geodesic_ancestor {D : CH.Digraph} {V : Finset ℕ} {u y i j : ℕ}
    (hu : u ∈ V) (hi : 1 ≤ i) (hij : i ≤ j)
    (hy : y ∈ ball D V u j \ ball D V u (j - 1)) :
    ∃ z ∈ ball D V u i \ ball D V u (i - 1), Walk D V z y (j - i) := by
  induction j using Nat.strong_induction_on generalizing y with
  | h j ih =>
    by_cases heq : i = j
    · subst j
      exact ⟨y, hy, by simpa using (Walk.refl (D := D) (W := V) y)⟩
    have hj : 2 ≤ j := by omega
    have hyu : y ≠ u := by
      intro hh; subst y
      exact (Finset.mem_sdiff.mp hy).2 (self_mem_ball hu)
    obtain ⟨p, hp, hpy⟩ := exists_pred (D := D) (j := j - 1) hu
      (by simpa only [show j - 1 + 1 = j by omega] using (Finset.mem_sdiff.mp hy).1) hyu
    have hpold : p ∉ ball D V u (j - 1 - 1) := by
      intro hpold
      have hh := ball_step hpold (ball_subset (Finset.mem_sdiff.mp hy).1) hpy
      have hr : j - 1 - 1 + 1 = j - 1 := by omega
      exact (Finset.mem_sdiff.mp hy).2 (by simpa only [hr] using hh)
    obtain ⟨z, hz, wz⟩ := ih (j - 1) (by omega) (by omega) (Finset.mem_sdiff.mpr ⟨hp, hpold⟩)
    refine ⟨z, hz, ?_⟩
    have hr : j - 1 - i + 1 = j - i := by omega
    simpa only [hr] using wz.snoc (ball_subset (Finset.mem_sdiff.mp hy).1) hpy

theorem layer_rows_of_no_back {D : CH.Digraph} {V : Finset ℕ} {u i : ℕ}
    (hno : ∀ v ∈ ball D V u i \ ball D V u (i - 1),
      ∀ w ∈ ball D V u (i - 1), ¬ D v w = true)
    {v : ℕ} (hv : v ∈ ball D V u i \ ball D V u (i - 1)) :
    outN D V v ⊆ outN D ((ball D V u i \ ball D V u (i - 1)) ∪
      (ball D V u (i + 1) \ ball D V u i)) v := by
  intro w hw
  obtain ⟨hwV, hvw⟩ := mem_outN.mp hw
  refine mem_outN.mpr ⟨?_, hvw⟩
  by_cases hwi : w ∈ ball D V u i
  · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hwi, fun h => hno v hv w h hvw⟩)
  · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr
      ⟨ball_step (Finset.mem_sdiff.mp hv).1 hwV hvw, hwi⟩)

theorem tight_prefix_no_back {s k : ℕ} (hs : 2 ≤ s) (hk : 1 ≤ k)
    {D : CH.Digraph} {V : Finset ℕ} {u : ℕ}
    (hf : QFree D V (s + k - 1)) (hm : ∀ v ∈ V, s ≤ (outN D V v).card) (hu : u ∈ V)
    (htight : ∀ i, 1 ≤ i → i ≤ k → (ball D V u i \ ball D V u (i - 1)).card = s) :
    ∀ j, 1 ≤ j → j ≤ k → ∀ y ∈ ball D V u j \ ball D V u (j - 1),
      ∀ x ∈ ball D V u (j - 1), ¬ D y x = true := by
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
    intro hj hjk y hy x hx hyx
    by_cases hxu : x = u
    · subst x
      exact no_back_arc hf hu (Finset.mem_sdiff.mp hy).1 (by omega) hyx
    obtain ⟨i, hi, hij, hxi⟩ := ball_mem_positive_layer hx hxu
    have hib : i < j := by omega
    have hnoback := ih i hib hi (by omega)
    let X := ball D V u i \ ball D V u (i - 1)
    let Y := ball D V u (i + 1) \ ball D V u i
    have hXV : X ⊆ V := fun _ hv => ball_subset (Finset.mem_sdiff.mp hv).1
    have hYV : Y ⊆ V := fun _ hv => ball_subset (Finset.mem_sdiff.mp hv).1
    have hXY : Disjoint X Y := Finset.disjoint_left.mpr (fun v hv hw =>
      (Finset.mem_sdiff.mp hw).2 (Finset.mem_sdiff.mp hv).1)
    have hXc : X.card = s := htight i hi (by omega)
    have hYc : Y.card = s := by simpa only [Nat.add_sub_cancel] using htight (i + 1) (by omega) (by omega)
    have hhigh : ∀ v ∈ X, s ≤ (outN D (X ∪ Y) v).card := by
      intro v hv
      exact (hm v (hXV hv)).trans (Finset.card_le_card (layer_rows_of_no_back hnoback hv))
    obtain ⟨z, hz, wz⟩ := layer_geodesic_ancestor hu (by omega : 1 ≤ i + 1) (by omega) hy
    have hzY : z ∈ Y := by simpa only [Nat.add_sub_cancel] using hz
    obtain ⟨m, hmpos, hms, w⟩ := small_first_funnel_of_ball (by omega : 2 ≤ s + 1)
      (ball_q_one (s + 1) (by omega)) (hf.mono_bound (by omega))
      (fun v hv => by have hh := hm v hv; omega) hXV hYV hXY
      (by simp [hXc]) (by omega) hhigh x hxi z hzY
    exact hf x (m + (j - (i + 1)) + 1) (by omega) (by omega)
      ((w.append wz).snoc (ball_subset hx) hyx)

/-- Every tight prefix expands, with one extra return exclusion per extra tight layer. -/
theorem tight_layers_expand {s k : ℕ} (hs : 2 ≤ s) (hk : 1 ≤ k)
    {D : CH.Digraph} {V : Finset ℕ} {u : ℕ}
    (hf : QFree D V (s + k - 1)) (hm : ∀ v ∈ V, s ≤ (outN D V v).card) (hu : u ∈ V)
    (htight : ∀ i, 1 ≤ i → i ≤ k → (ball D V u i \ ball D V u (i - 1)).card = s) :
    s ≤ (ball D V u (k + 1) \ ball D V u k).card := by
  let X := ball D V u k \ ball D V u (k - 1)
  let Y := ball D V u (k + 1) \ ball D V u k
  have hXV : X ⊆ V := fun _ hx => ball_subset (Finset.mem_sdiff.mp hx).1
  have hXc : X.card = s := htight k hk le_rfl
  obtain ⟨x, hx, hsink⟩ := exists_sink (hf.mono_set hXV)
    (Finset.card_pos.mp (by omega : 0 < X.card)) (by omega)
  have hkeep := layer_rows_of_no_back (tight_prefix_no_back hs hk hf hm hu htight k hk le_rfl) hx
  have hsub : outN D V x ⊆ Y := by
    intro y hy
    obtain ⟨hyU, hxy⟩ := mem_outN.mp (hkeep hy)
    rcases Finset.mem_union.mp hyU with hyX | hyY
    · exact (hsink y hyX hxy).elim
    · exact hyY
  exact (hm x (hXV hx)).trans (Finset.card_le_card hsub)

end LeanCH.BR.BRsGen
