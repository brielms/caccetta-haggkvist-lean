import LeanCH.BR.BRWeightedCycleStructure
import LeanCH.BR.BRCycleWindowEquality

/-! Connections between the two rich interfaces of an actual shortest cycle.
Strictness is used through genuine smaller-order induction, not an assumed
combinatorial exclusion. -/
namespace LeanCH.BR.WeightedSD
open Finset BRq2 BRq3 BR45 BRsub BRsGen

theorem rich_connection_contact_counts {q : ℕ} (hq : 3 ≤ q)
    {D : CH.Digraph} {V M : Finset ℕ} (hf : QFree D V q)
    (hMV : M ⊆ V) (hM : M.card = q + 1) (hout : OutEq 1 D M)
    {a b : ℕ} (ha : a ∈ cycleRichReceivers D V M)
    (hb : b ∈ cycleRichSenders D V M) (hab : D a b = true) :
    (inN D M a).card = 2 ∧ (outN D M b).card = 2 := by
  obtain ⟨haVM, ha2⟩ := Finset.mem_filter.mp ha
  obtain ⟨hbVM, hb2⟩ := Finset.mem_filter.mp hb
  have haV := (Finset.mem_sdiff.mp haVM).1
  have hbV := (Finset.mem_sdiff.mp hbVM).1
  have hreach : outN D M b ⊆ ball D V a 2 := by
    intro z hz
    exact ball_step (ball_of_adj hbV hab) (hMV (outN_subset hz)) (mem_outN.mp hz).2
  have hc := cycle_reentry_window (t := 2) hq hf hMV hM hout haV
    (Finset.card_pos.mp (by omega)) outN_subset (Finset.card_pos.mp (by omega)) hreach
  omega

theorem rich_connection_adjacent_heads {q : ℕ} (hq : 4 ≤ q)
    {D : CH.Digraph} {V M : Finset ℕ} (hf : QFree D V q)
    (hMV : M ⊆ V) (hM : M.card = q + 1) (hout : OutEq 1 D M)
    (hin : ∀ v ∈ M, (inN D M v).card = 1)
    {a b : ℕ} (ha : a ∈ cycleRichReceivers D V M)
    (hb : b ∈ cycleRichSenders D V M) (hab : D a b = true) :
    ∃ u ∈ outN D M b, ∃ v ∈ outN D M b, u ≠ v ∧ D u v = true := by
  have counts := rich_connection_contact_counts (by omega : 3 ≤ q) hf hMV hM hout ha hb hab
  have haV := (Finset.mem_sdiff.mp (Finset.mem_filter.mp ha).1).1
  have hbV := (Finset.mem_sdiff.mp (Finset.mem_filter.mp hb).1).1
  have hreach : outN D M b ⊆ ball D V a 2 := by
    intro z hz
    exact ball_step (ball_of_adj hbV hab) (hMV (outN_subset hz)) (mem_outN.mp hz).2
  have hg := cycle_reentry_equality_expansion (t := 2) hq hf hMV hM hout haV
    (Finset.card_pos.mp (by omega)) outN_subset (Finset.card_pos.mp (by omega)) hreach
    (by omega)
  exact cycle_pair_adjacent_of_small_expansion (by omega) (hf.mono_set hMV) hout hin
    outN_subset counts.2 (by omega)

/-- An actual rich-to-rich arc forces an exterior vertex beyond its two endpoints.
The witness is distinguished by a real outgoing arc missing at the sender. -/
theorem rich_connection_escape {q : ℕ} (hq : 4 ≤ q)
    {D : CH.Digraph} {V M : Finset ℕ} (hf : QFree D V q)
    (hsmall : SmallerSmallRow q V.card)
    (hMV : M ⊆ V) (hM : M.card = q + 1) (hout : OutEq 1 D M)
    (hin : ∀ v ∈ M, (inN D M v).card = 1)
    (p : ℕ → ℚ) (hp : ∀ v ∈ V, 0 ≤ p v)
    (hc : ∀ v ∈ V, mass V p < col q D V p v)
    {a b : ℕ} (ha : a ∈ cycleRichReceivers D V M)
    (hb : b ∈ cycleRichSenders D V M) (hab : D a b = true) :
    ∃ u ∈ outN D M b, ∃ z ∈ V \ M, z ≠ a ∧ z ≠ b ∧ D u z = true ∧ ¬ D b z = true := by
  classical
  obtain ⟨u, hu, v, hv, huv, huvD⟩ :=
    rich_connection_adjacent_heads hq hf hMV hM hout hin ha hb hab
  have huM := outN_subset hu
  have hvM := outN_subset hv
  have hbu := (mem_outN.mp hu).2
  have hbv := (mem_outN.mp hv).2
  have haV := (Finset.mem_sdiff.mp (Finset.mem_filter.mp ha).1).1
  obtain ⟨hbV, hbM⟩ := Finset.mem_sdiff.mp (Finset.mem_filter.mp hb).1
  have hub : u ≠ b := fun he => hbM (he ▸ huM)
  have hnub : ¬ D u b = true :=
    digonfree hf (by omega : 2 ≤ q) hbV (hMV huM) hbu
  have hnua : ¬ D u a = true := by
    intro hua
    apply hf a 3 (by omega) (by omega)
    exact .step hbV hab (.step (hMV huM) hbu (.step haV hua (.refl a)))
  by_contra hn
  apply strict_no_outgoing_domination hsmall hf p hp hc (hMV huM) hbV hub
  intro z hz huz
  have hzV := (Finset.mem_erase.mp hz).2
  by_cases hzM : z ∈ M
  · have hzv := Finset.card_le_one.mp (hout u huM).le z
      (mem_outN.mpr ⟨hzM, huz⟩) v (mem_outN.mpr ⟨hvM, huvD⟩)
    simpa only [hzv] using hbv
  · by_cases hza : z = a
    · exact (hnua (hza ▸ huz)).elim
    · by_cases hzb : z = b
      · exact (hnub (hzb ▸ huz)).elim
      · by_contra hnbz
        exact hn ⟨u, hu, z, Finset.mem_sdiff.mpr ⟨hzV, hzM⟩, hza, hzb, huz, hnbz⟩

theorem rich_connection_reverse_escape {q : ℕ} (hq : 4 ≤ q)
    {D : CH.Digraph} {V M : Finset ℕ} (hf : QFree D V q)
    (hsmall : SmallerSmallRow q V.card)
    (hMV : M ⊆ V) (hM : M.card = q + 1) (hout : OutEq 1 D M)
    (hin : ∀ v ∈ M, (inN D M v).card = 1)
    (w : ℕ → ℚ) (hw : ∀ v ∈ V, 0 ≤ w v)
    (hr : ∀ v ∈ V, mass V w < row q D V w v)
    {a b : ℕ} (ha : a ∈ cycleRichReceivers D V M)
    (hb : b ∈ cycleRichSenders D V M) (hab : D a b = true) :
    ∃ v ∈ inN D M a, ∃ z ∈ V \ M, z ≠ a ∧ z ≠ b ∧ D z v = true ∧ ¬ D z a = true := by
  obtain ⟨v, hv, z, hz, hzb, hza, hzv, hzaD⟩ :=
    rich_connection_escape (D := fun x y => D y x) hq hf.reverse hsmall
      hMV hM hin hout w hw hr hb ha hab
  exact ⟨v, hv, z, hz, hza, hzb, hzv, hzaD⟩

/-- Two distinct exterior escapes at every cutoff at least five. The witnesses
may not be merged: doing so would create an actual closed walk of length five. -/
theorem rich_connection_two_escapes {q : ℕ} (hq : 5 ≤ q)
    {D : CH.Digraph} {V M : Finset ℕ} (hf : QFree D V q)
    (hsmall : SmallerSmallRow q V.card)
    (hMV : M ⊆ V) (hM : M.card = q + 1) (hout : OutEq 1 D M)
    (hin : ∀ v ∈ M, (inN D M v).card = 1)
    (w p : ℕ → ℚ) (hw : ∀ v ∈ V, 0 ≤ w v) (hp : ∀ v ∈ V, 0 ≤ p v)
    (hr : ∀ v ∈ V, mass V w < row q D V w v)
    (hc : ∀ v ∈ V, mass V p < col q D V p v)
    {a b : ℕ} (ha : a ∈ cycleRichReceivers D V M)
    (hb : b ∈ cycleRichSenders D V M) (hab : D a b = true) :
    ∃ u ∈ outN D M b, ∃ v ∈ inN D M a,
      ∃ x ∈ V \ M, ∃ y ∈ V \ M,
        x ≠ a ∧ x ≠ b ∧ y ≠ a ∧ y ≠ b ∧ x ≠ y ∧
        D u x = true ∧ ¬ D b x = true ∧ D y v = true ∧ ¬ D y a = true := by
  obtain ⟨u, hu, x, hx, hxa, hxb, hux, hnbx⟩ :=
    rich_connection_escape (by omega : 4 ≤ q) hf hsmall hMV hM hout hin p hp hc ha hb hab
  obtain ⟨v, hv, y, hy, hya, hyb, hyv, hnya⟩ :=
    rich_connection_reverse_escape (by omega : 4 ≤ q) hf hsmall hMV hM hout hin w hw hr
      ha hb hab
  have haV := (Finset.mem_sdiff.mp (Finset.mem_filter.mp ha).1).1
  have hbV := (Finset.mem_sdiff.mp (Finset.mem_filter.mp hb).1).1
  have hxy : x ≠ y := by
    intro he
    subst y
    exact hf a 5 (by omega) hq
      (.step hbV hab (.step (hMV (outN_subset hu)) (mem_outN.mp hu).2
        (.step (Finset.mem_sdiff.mp hx).1 hux
          (.step (hMV (mem_inN.mp hv).1) hyv (.step haV (mem_inN.mp hv).2 (.refl a))))))
  exact ⟨u, hu, v, hv, x, hx, y, hy, hxa, hxb, hya, hyb, hxy, hux, hnbx, hyv, hnya⟩

end LeanCH.BR.WeightedSD
