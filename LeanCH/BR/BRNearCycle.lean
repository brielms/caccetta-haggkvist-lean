import LeanCH.BR.BR45Base
import LeanCH.BR.BRFiniteWalk

/-! A three-step funnel from a first set one vertex larger than a shortest cycle. -/

namespace LeanCH.BR.BRsGen

open BRq2 BRq3 BR45

variable {D : CH.Digraph} {X Y : Finset ℕ} {s : ℕ}

/-- A set of size `s+1`, with rows of degree s into itself and an `(s-1)`-set,
reaches every exterior vertex in at most three steps when it is `(s-1)`-free. -/
theorem near_cycle_funnel (hs : 4 ≤ s) (hf : QFree D (X ∪ Y) (s - 1))
    (hdisj : Disjoint X Y) (hX : X.card = s + 1) (hY : Y.card = s - 1)
    (hhigh : ∀ x ∈ X, s ≤ (outN D (X ∪ Y) x).card) :
    ∀ x ∈ X, ∀ y ∈ Y, ∃ m, 1 ≤ m ∧ m ≤ 3 ∧ Walk D (X ∪ Y) x y m := by
  classical
  have hXU : X ⊆ X ∪ Y := Finset.subset_union_left
  have hYU : Y ⊆ X ∪ Y := Finset.subset_union_right
  have hfX := hf.mono_set hXU
  have hminX : ∀ x ∈ X, 1 ≤ (outN D X x).card := by
    intro x hx
    have hh := hhigh x hx
    rw [card_outN_union hdisj] at hh
    have hy := Finset.card_le_card (outN_subset (D := D) (W := Y) (y := x))
    omega
  have full : ∀ x ∈ X, (outN D X x).card ≤ 1 → ∀ y ∈ Y, D x y = true := by
    intro x hx hi
    have heq : outN D Y x = Y := Finset.eq_of_subset_of_card_le outN_subset (by
      have hh := hhigh x hx
      rw [card_outN_union hdisj] at hh
      omega)
    intro y hy
    exact (mem_outN.mp (heq.symm ▸ hy)).2
  by_cases hmore : QFree D X s
  · have hreg := (dt_reg (by omega : 1 ≤ s) (ball_q_one _ (by omega)) hmore hminX
      (by rw [hX]; omega)).1
    intro x hx y hy
    exact ⟨1, le_rfl, by decide, .step (hYU hy) (full x hx (hreg x hx).le y hy) (.refl y)⟩
  · unfold QFree at hmore
    push Not at hmore
    obtain ⟨a, l, hl, hls, w⟩ := hmore
    have hleq : l = s := by
      by_contra hn
      exact hfX a l hl (by omega) w
    subst l
    have w' : Walk D X a a (s - 1 + 1) := by simpa only [Nat.sub_add_cancel (by omega : 1 ≤ s)] using w
    obtain ⟨M, hMX, hMc, hminM⟩ := boundary_closed_walk_support hfX w'
    have hM : M.card = s := by omega
    have hMU := hMX.trans hXU
    have hfM := hf.mono_set hMU
    have hreg := (dt_reg (by omega : 1 ≤ s - 1) (ball_q_one _ (by omega)) hfM hminM
      (by rw [hM]; omega)).1
    have hEc : (X \ M).card = 1 := by rw [Finset.card_sdiff_of_subset hMX, hX, hM]; omega
    obtain ⟨e, he⟩ := Finset.card_pos.mp (by omega : 0 < (X \ M).card)
    obtain ⟨heX, heM⟩ := Finset.mem_sdiff.mp he
    have hsplit : ∀ x ∈ X, x ∈ M ∨ x = e := by
      intro x hx
      by_cases hxM : x ∈ M
      · exact Or.inl hxM
      · exact Or.inr (Finset.card_le_one.mp hEc.le x (Finset.mem_sdiff.mpr ⟨hx, hxM⟩) e he)
    obtain ⟨z, hz⟩ := Finset.card_pos.mp (hminX e heX)
    obtain ⟨hzX, hez⟩ := mem_outN.mp hz
    have hzM : z ∈ M := by
      rcases hsplit z hzX with hzM | rfl
      · exact hzM
      · exact (loopfree hfX (by omega) heX hez).elim
    let P := inN D M e
    have hPc : P.card ≤ 2 := by
      have hsub : P ⊆ M \ ball D M z (s - 3) := by
        intro v hv
        obtain ⟨hvM, hve⟩ := mem_inN.mp hv
        refine Finset.mem_sdiff.mpr ⟨hvM, ?_⟩
        intro hvb
        obtain ⟨_, k, hk, wk⟩ := mem_ball.mp hvb
        exact hf z (k + 1 + 1) (by omega) (by omega)
          (((wk.mono hMU).snoc (hXU heX) hve).snoc (hMU hzM) hez)
      have hc := Finset.card_le_card hsub
      rw [Finset.card_sdiff_of_subset ball_subset, hM] at hc
      have hg := ball_one_growth hfM hminM hzM (s - 3) (by omega)
      omega
    have hfull : ∀ v ∈ M, v ∉ P → ∀ y ∈ Y, D v y = true := by
      intro v hv hvP
      apply full v (hMX hv)
      have hsub : outN D X v ⊆ outN D M v := by
        intro t ht
        obtain ⟨htX, hvt⟩ := mem_outN.mp ht
        rcases hsplit t htX with htM | rfl
        · exact mem_outN.mpr ⟨htM, hvt⟩
        · exact (hvP (mem_inN.mpr ⟨hv, hvt⟩)).elim
      exact (Finset.card_le_card hsub).trans (hreg v hv).le
    have hreachM : ∀ x ∈ M, ∀ y ∈ Y, ∃ m, 1 ≤ m ∧ m ≤ 3 ∧ Walk D (X ∪ Y) x y m := by
      intro x hx y hy
      have hc := ball_one_growth hfM hminM hx 2 (by omega)
      have hex : ∃ v ∈ ball D M x 2, v ∉ P := by
        by_contra hn
        push Not at hn
        have hsub : ball D M x 2 ⊆ P := hn
        have := Finset.card_le_card hsub
        omega
      obtain ⟨v, hv, hvP⟩ := hex
      obtain ⟨hvM, k, hk, wk⟩ := mem_ball.mp hv
      exact ⟨k + 1, by omega, by omega, (wk.mono hMU).snoc (hYU hy) (hfull v hvM hvP y hy)⟩
    have hzP : z ∉ P := fun hzP => digonfree hfX (by omega) heX (hMX hzM) hez (mem_inN.mp hzP).2
    intro x hx y hy
    rcases hsplit x hx with hxM | rfl
    · exact hreachM x hxM y hy
    · exact ⟨2, by decide, by decide,
        .step (hMU hzM) hez (.step (hYU hy) (hfull z hzM hzP y hy) (.refl y))⟩

end LeanCH.BR.BRsGen
