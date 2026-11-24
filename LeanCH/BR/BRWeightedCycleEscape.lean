import LeanCH.BR.BRWeightedArcGap
import LeanCH.BR.BRCycleTightPath

/-! Actual escape sets, quantitative charges, and separation along tight paths.
Both equalizer weightings are retained; strictness and induction are unnecessary
for these local consequences. -/
namespace LeanCH.BR.WeightedSD
open Finset BRq2 BRq3 BR45 BRsub BRsGen

theorem tight_path_forward_gap {q l : ℕ} (hl : l + 3 ≤ q)
    {D : CH.Digraph} {V M : Finset ℕ} (hf : QFree D V q)
    (hMV : M ⊆ V) (hM : M.card = q + 1) (hout : OutEq 1 D M)
    (hin : ∀ v ∈ M, (inN D M v).card = 1)
    {a b : ℕ} (ha : a ∈ V) (hb : b ∈ V) (hab : Walk D V a b l)
    (hIa : (inN D M a).Nonempty) (hOb : 2 ≤ (outN D M b).card)
    (htight : (inN D M a).card + (outN D M b).card = l + 3)
    (w : ℕ → ℚ) (hw : ∀ z ∈ V, 0 ≤ w z) (hwb : 0 < w b)
    (c : ℚ) (hr : ∀ z ∈ V, row q D V w z = c) :
    ∃ u ∈ outN D M b,
      outGap D V u b ⊆ V \ M ∧ (outGap D V u b).Nonempty ∧
      (q : ℚ) * mass (outGap D V u b) w = (q - 1 : ℚ) * w u + w b +
        q * mass ((outGap D V b u).erase u) w ∧
      ∀ z ∈ outGap D V u b, b ∉ ball D V z (q - 2) := by
  obtain ⟨u, hu, v, hv, huv⟩ :=
    tight_path_cycle_heads_internal_arc hl hf hMV hM hout hin ha hab hIa hOb htight
  have huM := outN_subset hu
  have huV := hMV huM
  have hbu := (mem_outN.mp hu).2
  have he : row q D V w u = row q D V w b := (hr u huV).trans (hr b hb).symm
  have hloop := loopfree hf (by omega : 1 ≤ q) huV
  refine ⟨u, hu, ?_, equal_rows_arc_gap_nonempty (by omega) w hw huV hwb hbu hloop he,
    equal_rows_arc_gap_exact w huV hbu hloop he, ?_⟩
  · intro z hz
    obtain ⟨hzV, huz, hnbz⟩ := mem_outGap.mp hz
    refine Finset.mem_sdiff.mpr ⟨hzV, ?_⟩
    intro hzM
    have hez := Finset.card_le_one.mp (hout u huM).le z
      (mem_outN.mpr ⟨hzM, huz⟩) v (mem_outN.mpr ⟨outN_subset hv, huv⟩)
    exact hnbz (hez ▸ (mem_outN.mp hv).2)
  · intro z hz
    exact outGap_no_short_return (by omega) hf huV hb hbu hz

theorem tight_path_reverse_gap {q l : ℕ} (hl : l + 3 ≤ q)
    {D : CH.Digraph} {V M : Finset ℕ} (hf : QFree D V q)
    (hMV : M ⊆ V) (hM : M.card = q + 1) (hout : OutEq 1 D M)
    (hin : ∀ v ∈ M, (inN D M v).card = 1)
    {a b : ℕ} (ha : a ∈ V) (hb : b ∈ V) (hab : Walk D V a b l)
    (hIa : 2 ≤ (inN D M a).card) (hOb : (outN D M b).Nonempty)
    (htight : (inN D M a).card + (outN D M b).card = l + 3)
    (p : ℕ → ℚ) (hp : ∀ z ∈ V, 0 ≤ p z) (hpa : 0 < p a)
    (c : ℚ) (hc : ∀ z ∈ V, col q D V p z = c) :
    ∃ v ∈ inN D M a,
      outGap (fun x y => D y x) V v a ⊆ V \ M ∧
      (outGap (fun x y => D y x) V v a).Nonempty ∧
      (q : ℚ) * mass (outGap (fun x y => D y x) V v a) p =
        (q - 1 : ℚ) * p v + p a +
          q * mass ((outGap (fun x y => D y x) V a v).erase v) p ∧
      ∀ z ∈ outGap (fun x y => D y x) V v a,
        a ∉ ball (fun x y => D y x) V z (q - 2) := by
  exact tight_path_forward_gap (D := fun x y => D y x) hl hf.reverse hMV hM hin hout
    hb ha (hab.reverse_of_mem ha) hOb hIa
    (by change (outN D M b).card + (inN D M a).card = l + 3; omega) p hp hpa c hc

/-- Separation concerns the complete sets, not just selected representatives. -/
theorem path_forward_reverse_gaps_disjoint {q l : ℕ} (hl : l + 4 ≤ q)
    {D : CH.Digraph} {V M : Finset ℕ} (hf : QFree D V q) (hMV : M ⊆ V)
    {a b u v : ℕ} (ha : a ∈ V) (hab : Walk D V a b l)
    (hu : u ∈ outN D M b) (hv : v ∈ inN D M a) :
    Disjoint (outGap D V u b) (outGap (fun x y => D y x) V v a) := by
  apply Finset.disjoint_left.mpr
  intro z hz hzr
  obtain ⟨hzV, huz, _⟩ := mem_outGap.mp hz
  have hzv := (mem_outGap.mp hzr).2.1
  have w4 : Walk D V b a 4 :=
    .step (hMV (outN_subset hu)) (mem_outN.mp hu).2
      (.step hzV huz (.step (hMV (mem_inN.mp hv).1) hzv
        (.step ha (mem_inN.mp hv).2 (.refl a))))
  exact hf a (l + 4) (by omega) hl (hab.append w4)

theorem tight_path_weighted_escapes {q l : ℕ} (hl : l + 4 ≤ q)
    {D : CH.Digraph} {V M : Finset ℕ} (hf : QFree D V q)
    (hMV : M ⊆ V) (hM : M.card = q + 1) (hout : OutEq 1 D M)
    (hin : ∀ v ∈ M, (inN D M v).card = 1)
    {a b : ℕ} (ha : a ∈ V) (hb : b ∈ V) (hab : Walk D V a b l)
    (hIa : 2 ≤ (inN D M a).card) (hOb : 2 ≤ (outN D M b).card)
    (htight : (inN D M a).card + (outN D M b).card = l + 3)
    (w p : ℕ → ℚ) (hw : ∀ z ∈ V, 0 < w z) (hp : ∀ z ∈ V, 0 < p z)
    (c : ℚ) (hr : ∀ z ∈ V, row q D V w z = c)
    (hc : ∀ z ∈ V, col q D V p z = c) :
    ∃ u ∈ outN D M b, ∃ v ∈ inN D M a,
      outGap D V u b ⊆ V \ M ∧ outGap (fun x y => D y x) V v a ⊆ V \ M ∧
      (outGap D V u b).Nonempty ∧ (outGap (fun x y => D y x) V v a).Nonempty ∧
      Disjoint (outGap D V u b) (outGap (fun x y => D y x) V v a) ∧
      (q - 1 : ℚ) * w u + w b ≤ q * mass (outGap D V u b) w ∧
      (q - 1 : ℚ) * p v + p a ≤ q * mass (outGap (fun x y => D y x) V v a) p := by
  obtain ⟨u, hu, hX, hXn, _, _⟩ := tight_path_forward_gap (by omega : l + 3 ≤ q)
    hf hMV hM hout hin ha hb hab (Finset.card_pos.mp (by omega)) hOb htight
    w (fun z hz => (hw z hz).le) (hw b hb) c hr
  obtain ⟨v, hv, hY, hYn, _, _⟩ := tight_path_reverse_gap (by omega : l + 3 ≤ q)
    hf hMV hM hout hin ha hb hab hIa (Finset.card_pos.mp (by omega)) htight
    p (fun z hz => (hp z hz).le) (hp a ha) c hc
  have huV := hMV (outN_subset hu)
  have hvV := hMV (mem_inN.mp hv).1
  refine ⟨u, hu, v, hv, hX, hY, hXn, hYn,
    path_forward_reverse_gaps_disjoint hl hf hMV ha hab hu hv, ?_, ?_⟩
  · exact equal_rows_arc_gap_lower w (fun z hz => (hw z hz).le) huV
      (mem_outN.mp hu).2 (loopfree hf (by omega) huV) ((hr u huV).trans (hr b hb).symm)
  · exact equal_rows_arc_gap_lower (D := fun x y => D y x) p
      (fun z hz => (hp z hz).le) hvV (mem_inN.mp hv).2
      (loopfree hf (by omega) hvV) ((hc v hvV).trans (hc a ha).symm)

theorem rich_connection_weighted_escapes {q : ℕ} (hq : 5 ≤ q)
    {D : CH.Digraph} {V M : Finset ℕ} (hf : QFree D V q)
    (hMV : M ⊆ V) (hM : M.card = q + 1) (hout : OutEq 1 D M)
    (hin : ∀ v ∈ M, (inN D M v).card = 1)
    (w p : ℕ → ℚ) (hw : ∀ z ∈ V, 0 < w z) (hp : ∀ z ∈ V, 0 < p z)
    (c : ℚ) (hr : ∀ z ∈ V, row q D V w z = c)
    (hc : ∀ z ∈ V, col q D V p z = c)
    {a b : ℕ} (ha : a ∈ cycleRichReceivers D V M)
    (hb : b ∈ cycleRichSenders D V M) (hab : D a b = true) :
    ∃ u ∈ outN D M b, ∃ v ∈ inN D M a,
      outGap D V u b ⊆ V \ M ∧ outGap (fun x y => D y x) V v a ⊆ V \ M ∧
      (outGap D V u b).Nonempty ∧ (outGap (fun x y => D y x) V v a).Nonempty ∧
      Disjoint (outGap D V u b) (outGap (fun x y => D y x) V v a) ∧
      (q - 1 : ℚ) * w u + w b ≤ q * mass (outGap D V u b) w ∧
      (q - 1 : ℚ) * p v + p a ≤ q * mass (outGap (fun x y => D y x) V v a) p := by
  have haV := (Finset.mem_sdiff.mp (Finset.mem_filter.mp ha).1).1
  have hbV := (Finset.mem_sdiff.mp (Finset.mem_filter.mp hb).1).1
  have counts := rich_connection_contact_counts (by omega : 3 ≤ q) hf hMV hM hout ha hb hab
  exact tight_path_weighted_escapes (l := 1) hq hf hMV hM hout hin haV hbV
    (.step hbV hab (.refl b)) (by omega) (by omega) (by omega) w p hw hp c hr hc

end LeanCH.BR.WeightedSD
