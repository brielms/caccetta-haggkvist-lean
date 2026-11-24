import LeanCH.BR.BRDeficiencyRigidity
import LeanCH.BR.BRLocalDegreeDrop

/-! Strict degree-two deficiency limits non-feeding rows and gives shorter funnels. -/

namespace LeanCH.BR.BRsGen

open BRq2 BRq3 BR45

/-- Below the degree-two boundary, few rows can already have two internal heads. -/
theorem small_one_core_high_count {D : CH.Digraph} {X H : Finset ℕ} {q : ℕ}
    (hq : 1 ≤ q) (hf : QFree D X q)
    (hmin : ∀ v ∈ X, 1 ≤ (outN D X v).card) (hne : X.Nonempty)
    (hcard : X.card ≤ 2 * q) (hHX : H ⊆ X)
    (hhigh : ∀ v ∈ H, 2 ≤ (outN D X v).card) :
    2 * q + 2 + H.card ≤ 2 * X.card := by
  classical
  have hb : Ball q 2 := by
    intro F U hf hout u hu
    exact ball_growth q hq F U hf (fun v hv => (hout v hv).ge) u hu (q - 1) (by omega)
  have hnot : ¬ OutEq 2 D X := by
    intro hout
    have hh := corB hq hf (fun v hv => (hout v hv).ge) hne
    omega
  have hd := deficiency_strict_of_not_regular hq hb hf hmin hne hnot
  have hz : (∑ v ∈ H, (2 - (outN D X v).card)) = 0 :=
    Finset.sum_eq_zero (fun v hv => by have := hhigh v hv; omega)
  have hlo : ∀ v ∈ X \ H, 2 - (outN D X v).card ≤ 1 := by
    intro v hv
    have := hmin v (Finset.mem_sdiff.mp hv).1
    omega
  have hsum := Finset.sum_le_sum hlo
  rw [Finset.sum_const_nat (fun _ _ => rfl)] at hsum
  have he := Finset.sum_sdiff hHX (f := fun v => 2 - (outN D X v).card)
  have hc := Finset.card_sdiff_add_card_eq_card hHX
  omega

/-- A first set of size at most q+L reaches every q-set exterior label within L steps.
The ambient minimum-two hypothesis supplies the local degree-drop argument. -/
theorem wide_first_funnel {D : CH.Digraph} {V X Y : Finset ℕ} {q L : ℕ}
    (hL : 2 ≤ L) (hLq : L + 1 ≤ q) (hf : QFree D V q)
    (hmin : ∀ v ∈ V, 2 ≤ (outN D V v).card)
    (hXV : X ⊆ V) (hYV : Y ⊆ V) (hXY : Disjoint X Y)
    (hX : X.card ≤ q + L) (hY : Y.card = q)
    (hhigh : ∀ x ∈ X, q + 1 ≤ (outN D (X ∪ Y) x).card) :
    ∀ x ∈ X, ∀ y ∈ Y, ∃ m, 1 ≤ m ∧ m ≤ L ∧ Walk D V x y m := by
  classical
  have hminX : ∀ x ∈ X, 1 ≤ (outN D X x).card := by
    intro x hx
    have hh := hhigh x hx
    rw [card_outN_union hXY] at hh
    have hc := Finset.card_le_card (outN_subset (D := D) (W := Y) (y := x))
    omega
  intro x hx y hy
  let R := X.filter (fun r => ¬ D r y = true)
  have hRX : R ⊆ X := Finset.filter_subset _ _
  have hRhigh : ∀ r ∈ R, 2 ≤ (outN D X r).card := by
    intro r hr
    have hh := hhigh r (hRX hr)
    rw [card_outN_union hXY] at hh
    have hsub : outN D Y r ⊆ Y.erase y := by
      intro z hz
      exact Finset.mem_erase.mpr
        ⟨fun heq => (Finset.mem_filter.mp hr).2 (heq ▸ (mem_outN.mp hz).2),
          (mem_outN.mp hz).1⟩
    have hc := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem hy, hY] at hc
    omega
  have hcount := small_one_core_high_count (by omega : 1 ≤ q) (hf.mono_set hXV)
    hminX ⟨x, hx⟩ (by omega) hRX hRhigh
  have hRc : R.card ≤ 2 * (L - 1) := by omega
  have hball : Ball L 2 := by
    intro F U hf hout v hv
    exact ball_growth L (by omega) F U hf (fun z hz => (hout z hz).ge) v hv (L - 1) (by omega)
  by_cases hxR : x ∈ R
  · obtain ⟨b, hbR, hlow, m, hm, w⟩ := local_degree_drop_reachable hL hball
      (hf.mono_bound (by omega : L ≤ q)) hmin (hRX.trans hXV) hRc hxR
    obtain ⟨c, hcX, hbc, hcR⟩ : ∃ c ∈ X, D b c = true ∧ c ∉ R := by
      by_contra hn
      have hsub : outN D X b ⊆ outN D R b := by
        intro c hc
        obtain ⟨hcX, hbc⟩ := mem_outN.mp hc
        have hcR : c ∈ R := by
          by_contra hnot
          exact hn ⟨c, hcX, hbc, hnot⟩
        exact mem_outN.mpr ⟨hcR, hbc⟩
      have hh := (hRhigh b hbR).trans (Finset.card_le_card hsub)
      omega
    have hcy : D c y = true := by
      by_contra hn
      exact hcR (Finset.mem_filter.mpr ⟨hcX, hn⟩)
    exact ⟨m + 1 + 1, by omega, by omega,
      ((w.mono (hRX.trans hXV)).snoc (hXV hcX) hbc).snoc (hYV hy) hcy⟩
  · have hxy : D x y = true := by
      by_contra hn
      exact hxR (Finset.mem_filter.mpr ⟨hx, hn⟩)
    exact ⟨1, by decide, by omega, .step (hYV hy) hxy (.refl y)⟩

end LeanCH.BR.BRsGen
