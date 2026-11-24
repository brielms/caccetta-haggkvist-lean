import LeanCH.BR.BRWeightedAmplifiedReceiver
import LeanCH.BR.BRWeightedRetainedHeadTransfer

/-! Actual no-cut split obstructions for arbitrary amplified distributions.
The root is augmented only for invoking the checked conserving identity. -/
namespace LeanCH.BR.WeightedSD
open Finset BRq2 BRq3 BR45 BRsub

theorem row_congr_weights {q : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (a b : ℕ → ℚ) (hab : ∀ z ∈ V, a z = b z) {x : ℕ} (hx : x ∈ V) :
    row q D V a x = row q D V b x :=
  le_antisymm (row_mono_weights a b (fun z hz => (hab z hz).le) hx)
    (row_mono_weights b a (fun z hz => (hab z hz).ge) hx)

theorem split_surplus_mass {q : ℕ} (hq : 1 ≤ q) {D : CH.Digraph}
    {V : Finset ℕ} {v : ℕ} (hf : QFree D V q) (hv : v ∈ V)
    (a α : ℕ → ℚ) (δ : ℚ) (hs : ∀ z ∈ V, z ∉ outN D V v → α z = 0)
    (hm : mass (outN D V v) α = a v + δ) :
    mass (V.erase v) (fun z => a z + α z) = mass V a + δ := by
  have hα : mass (V.erase v) α = a v + δ := by
    rw [← hm]
    apply (mass_subset_zero (root_interfaces_retained hq hf hv).2 ?_).symm
    exact fun z hz hn => hs z (mem_erase.mp hz).2 hn
  rw [mass_add_weights, hα]
  have he : mass (V.erase v) a + a v = mass V a := sum_erase_add _ _ hv
  linarith

/-- Signed exact identity for any RootCuts and arbitrary surplus. The extra
q*delta comes from augmenting the original root, not from dropping a loss. -/
theorem split_parent_row_surplus {q : ℕ} (hq : 2 ≤ q) {D : CH.Digraph}
    {V : Finset ℕ} {v x : ℕ} {C : Finset (ℕ × ℕ)}
    (hf : QFree D V q) (hv : v ∈ V) (hC : RootCuts D V v C) (hx : x ∈ inN D V v)
    (a α : ℕ → ℚ) (δ : ℚ) (hs : ∀ z ∈ V, z ∉ outN D V v → α z = 0)
    (hm : mass (outN D V v) α = a v + δ) :
    row q (splitTransferGraph q D V v C) (V.erase v) (fun z => a z + α z) x =
      row q D V a x + q * δ + q * mass (splitNew q D V v C x) a -
        q * mass (splitBlocked q D V v C x) α := by
  have hq1 : 1 ≤ q := by omega
  have hxK := (root_interfaces_retained hq1 hf hv).1 hx
  have hsame : ∀ z ∈ V.erase v, addWeightAt a v δ z = a z := by
    intro z hz
    simp [addWeightAt, (mem_erase.mp hz).1]
  have he := splitTransfer_parent_row hq hf hv hC hx (addWeightAt a v δ) α hs
    (by simpa [addWeightAt] using hm)
  have hchild := row_congr_weights (q := q) (D := splitTransferGraph q D V v C)
    (fun z => addWeightAt a v δ z + α z) (fun z => a z + α z)
    (fun z hz => by rw [hsame z hz]) hxK
  have hnew : mass (splitNew q D V v C x) (addWeightAt a v δ) = mass (splitNew q D V v C x) a := by
    apply sum_congr rfl
    intro z hz
    exact hsame z ((root_interfaces_retained hq1 hf hv).2 (mem_filter.mp (mem_sdiff.mp hz).1).1)
  rw [hchild, hnew, row_addWeightAt hv, if_neg (mem_erase.mp hxK).1,
    if_pos (mem_inN.mp hx).2, add_zero] at he
  exact he

theorem no_cut_other_row {q : ℕ} {D : CH.Digraph} {V : Finset ℕ} {v x : ℕ}
    (hx : x ∈ V.erase v) (hn : x ∉ inN D V v) (a α : ℕ → ℚ)
    (hs : ∀ z ∈ V, z ∉ outN D V v → α z = 0) :
    row q (splitTransferGraph q D V v ∅) (V.erase v) (fun z => a z + α z) x =
      row q D V a x + α x + q * mass (outN D V x ∩ outN D V v) α := by
  have hC : RootCuts D V v ∅ := by intro r s h; simp at h
  simpa [cutHeads, mass] using splitTransfer_other_row hC hx hn a α hs

theorem no_cut_transfer_obstruction {q : ℕ} (hq : 2 ≤ q) {D : CH.Digraph}
    {V : Finset ℕ} {v : ℕ} (hf : QFree D V q) (hv : v ∈ V)
    (hsmall : SmallerSmallRow q V.card) (a α : ℕ → ℚ)
    (ha : ∀ z ∈ V, 0 ≤ a z) (hα : ∀ z ∈ V, 0 ≤ α z)
    (δ : ℚ) (hpos : 0 < a v + δ)
    (hs : ∀ z ∈ V, z ∉ outN D V v → α z = 0)
    (hm : mass (outN D V v) α = a v + δ)
    (hr : ∀ x ∈ V, mass V a + δ ≤ row q D V a x) :
    ∃ x ∈ inN D V v, δ + mass (splitNew q D V v ∅ x) a <
      mass (splitBlocked q D V v ∅ x) α := by
  by_contra hn
  push_neg at hn
  have hq1 : 1 ≤ q := by omega
  have hC : RootCuts D V v ∅ := by intro r s h; simp at h
  let E := splitTransferGraph q D V v ∅
  let b := fun z => a z + α z
  have hnn : ∀ x ∈ V.erase v, 0 ≤ b x :=
    fun x hx => add_nonneg (ha x (mem_erase.mp hx).2) (hα x (mem_erase.mp hx).2)
  have hfree : QFree E (V.erase v) q := splitTransferGraph_qfree hq1 hf hv ∅
  have hsup : SmallRow q E ((V.erase v).filter (fun x => 0 < b x)) :=
    hsmall _ _ ((card_le_card (filter_subset _ _)).trans_lt (card_erase_lt_of_mem hv))
      (hfree.mono_set (filter_subset _ _))
  have hmass : mass (V.erase v) b = mass V a + δ := split_surplus_mass hq1 hf hv a α δ hs hm
  have hfeas : ∀ x ∈ V.erase v, mass (V.erase v) b ≤ row q E (V.erase v) b x := by
    intro x hx
    rw [hmass]
    have hrx := hr x (mem_erase.mp hx).2
    change mass V a + δ ≤ row q (splitTransferGraph q D V v ∅) (V.erase v) (fun z => a z + α z) x
    by_cases hp : x ∈ inN D V v
    · rw [split_parent_row_surplus hq hf hv hC hp a α δ hs hm]
      have hle := mul_le_mul_of_nonneg_left (hn x hp) (Nat.cast_nonneg q : (0 : ℚ) ≤ q)
      nlinarith
    · rw [no_cut_other_row hx hp a α hs]
      have ht : 0 ≤ mass (outN D V x ∩ outN D V v) α :=
        mass_nonneg (fun z hz => hα z (outN_subset (mem_inter.mp hz).1))
      nlinarith [hα x (mem_erase.mp hx).2, (Nat.cast_nonneg q : (0 : ℚ) ≤ q)]
  have hsum : 0 < mass (outN D V v) α := by rwa [hm]
  obtain ⟨t, ht, htpos⟩ := (sum_pos_iff_of_nonneg (fun z hz => hα z (outN_subset hz))).mp hsum
  have htK := (root_interfaces_retained hq1 hf hv).2 ht
  have htP : t ∉ inN D V v := fun hp => disjoint_left.mp (root_interfaces_disjoint hq hf hv) hp ht
  have hbt : 0 < b t := by dsimp [b]; linarith [ha t (outN_subset ht)]
  have he := positive_coordinate_tight_of_support_smallRow hq b hnn hsup hfeas htK hbt
  change row q (splitTransferGraph q D V v ∅) (V.erase v) (fun z => a z + α z) t = _ at he
  rw [no_cut_other_row htK htP a α hs, hmass] at he
  have hheads : 0 ≤ mass (outN D V t ∩ outN D V v) α :=
    mass_nonneg (fun z hz => hα z (outN_subset (mem_inter.mp hz).1))
  nlinarith [hr t (outN_subset ht), (Nat.cast_nonneg q : (0 : ℚ) ≤ q)]

theorem no_cut_probability_obstruction {q : ℕ} (hq : 2 ≤ q) {D : CH.Digraph}
    {V : Finset ℕ} {v : ℕ} (hf : QFree D V q) (hv : v ∈ V)
    (hsmall : SmallerSmallRow q V.card) (a μ : ℕ → ℚ)
    (ha : ∀ z ∈ V, 0 ≤ a z) (hμ : ∀ z ∈ V, 0 ≤ μ z)
    (δ : ℚ) (hpos : 0 < a v + δ)
    (hs : ∀ z ∈ V, z ∉ outN D V v → μ z = 0)
    (hm : mass (outN D V v) μ = 1)
    (hr : ∀ x ∈ V, mass V a + δ ≤ row q D V a x) :
    ∃ x ∈ inN D V v, δ + mass (splitNew q D V v ∅ x) a <
      (a v + δ) * mass (splitBlocked q D V v ∅ x) μ := by
  obtain ⟨x, hx, h⟩ := no_cut_transfer_obstruction hq hf hv hsmall a
    (fun z => (a v + δ) * μ z) ha (fun z hz => mul_nonneg hpos.le (hμ z hz)) δ hpos
    (fun z hz hn => by rw [hs z hz hn, mul_zero])
    (by simp only [mass, ← mul_sum]; rw [show ∑ z ∈ outN D V v, μ z = 1 from hm]; ring) hr
  refine ⟨x, hx, ?_⟩
  simpa only [mass, mul_sum] using h

end LeanCH.BR.WeightedSD
