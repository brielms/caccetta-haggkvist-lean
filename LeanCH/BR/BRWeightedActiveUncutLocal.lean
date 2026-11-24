import LeanCH.BR.BRWeightedNoCutDistribution

/-! A local discrete cut-floor argument. No q-freeness, root, source row
bound, or positive-cutoff hypothesis is needed for the witness lemmas. -/
namespace LeanCH.BR.WeightedSD
open Finset BRq2 BRq3 BR45 BRsub

noncomputable def transferGain (q : ℕ) (D : CH.Digraph) (V T : Finset ℕ)
    (α : ℕ → ℚ) (r : ℕ) : ℚ := α r + q * mass (outN D V r ∩ T) α

theorem empty_of_paid_below_head_floor {q : ℕ} {L : Finset ℕ}
    (a : ℕ → ℚ) (ha : ∀ z ∈ L, 0 ≤ a z) (m B : ℚ)
    (hfloor : ∀ z ∈ L, m ≤ a z) (hbound : B < q * m)
    (hpaid : q * mass L a ≤ B) : L = ∅ := by
  apply not_nonempty_iff_eq_empty.mp
  intro hn
  have hmass := nonempty_mass_ge_minimum (Subset.refl L) hn a ha m hfloor
  have hcost := mul_le_mul_of_nonneg_left hmass (Nat.cast_nonneg q : (0 : ℚ) ≤ q)
  linarith

theorem transfer_support_small_row {q : ℕ} {D : CH.Digraph} {V T : Finset ℕ}
    (hTV : T ⊆ V) (α : ℕ → ℚ) (hα : ∀ z ∈ T, 0 ≤ α z)
    (hpos : 0 < mass T α) (hsmall : SmallRow q D (T.filter (fun z => 0 < α z))) :
    ∃ r ∈ T, 0 < α r ∧ transferGain q D V T α r ≤ mass T α := by
  let F := T.filter (fun z => 0 < α z)
  have hFT : F ⊆ T := filter_subset _ _
  have hz : ∀ z ∈ T, z ∉ F → α z = 0 := by
    intro z hz hn
    have hnp : ¬ 0 < α z := fun hp => hn (mem_filter.mpr ⟨hz, hp⟩)
    exact le_antisymm (le_of_not_gt hnp) (hα z hz)
  have hm : mass F α = mass T α := mass_subset_zero hFT hz
  have hne : F.Nonempty := by
    obtain ⟨r, hr, hp⟩ := (sum_pos_iff_of_nonneg hα).mp hpos
    exact ⟨r, mem_filter.mpr ⟨hr, hp⟩⟩
  obtain ⟨r, hr, hrow⟩ := hsmall α (fun z hz => (mem_filter.mp hz).2.le) hne
  have hheads : outN D F r ⊆ outN D V r ∩ T := by
    intro z hz
    obtain ⟨hzF, he⟩ := mem_outN.mp hz
    exact mem_inter.mpr ⟨mem_outN.mpr ⟨hTV (hFT hzF), he⟩, hFT hzF⟩
  have hmass : mass (outN D F r) α = mass (outN D V r ∩ T) α := by
    apply mass_subset_zero hheads
    intro z hzH hn
    apply hz z (mem_inter.mp hzH).2
    intro hzF
    exact hn (mem_outN.mpr ⟨hzF, (mem_outN.mp (mem_inter.mp hzH).1).2⟩)
  rw [row, outW_eq_mass, hmass, hm] at hrow
  exact ⟨r, hFT hr, (mem_filter.mp hr).2, hrow⟩

/-- The analytic master requires only a current-weight low-gain witness. -/
theorem active_uncut_of_gain_witness {q : ℕ} {D : CH.Digraph} {V T : Finset ℕ}
    {C : Finset (ℕ × ℕ)} (a α : ℕ → ℚ)
    (ha : ∀ r ∈ T, 0 < α r → ∀ z ∈ cutHeads V C r, 0 ≤ a z)
    (β P m : ℚ) (hbound : β + P < q * m)
    (hwitness : ∃ r ∈ T, 0 < α r ∧ transferGain q D V T α r ≤ P)
    (hfloor : ∀ r ∈ T, 0 < α r → ∀ z ∈ cutHeads V C r, m ≤ a z)
    (hpaid : ∀ r ∈ T, 0 < α r → q * mass (cutHeads V C r) a ≤ β + transferGain q D V T α r) :
    ∃ r ∈ T, 0 < α r ∧ cutHeads V C r = ∅ ∧ transferGain q D V T α r ≤ P := by
  obtain ⟨r, hr, hp, hgain⟩ := hwitness
  refine ⟨r, hr, hp, ?_, hgain⟩
  apply empty_of_paid_below_head_floor a (ha r hr hp)
    m (β + P) (hfloor r hr hp) hbound
  exact (hpaid r hr hp).trans (by linarith)

theorem active_uncut_of_support_smallRow {q : ℕ} {D : CH.Digraph} {V T : Finset ℕ}
    {C : Finset (ℕ × ℕ)} (hTV : T ⊆ V) (a α : ℕ → ℚ)
    (ha : ∀ r ∈ T, 0 < α r → ∀ z ∈ cutHeads V C r, 0 ≤ a z) (hα : ∀ z ∈ T, 0 ≤ α z)
    (hpos : 0 < mass T α) (hsmall : SmallRow q D (T.filter (fun z => 0 < α z)))
    (β m : ℚ) (hbound : β + mass T α < q * m)
    (hfloor : ∀ r ∈ T, 0 < α r → ∀ z ∈ cutHeads V C r, m ≤ a z)
    (hpaid : ∀ r ∈ T, 0 < α r → q * mass (cutHeads V C r) a ≤ β + transferGain q D V T α r) :
    ∃ r ∈ T, 0 < α r ∧ cutHeads V C r = ∅ ∧ transferGain q D V T α r ≤ mass T α :=
  active_uncut_of_gain_witness a α ha β (mass T α) m hbound
    (transfer_support_small_row hTV α hα hpos hsmall) hfloor hpaid

end LeanCH.BR.WeightedSD
