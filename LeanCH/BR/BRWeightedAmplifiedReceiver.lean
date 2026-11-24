import LeanCH.BR.BRWeightedMinimumRootTransfer

/-! A single-receiver transfer may use the entire available row margin.
The child mass changes by the extra transfer and is recorded exactly. -/
namespace LeanCH.BR.WeightedSD
open Finset BRq2 BRq3 BR45 BRsub

theorem row_mono_weights {q : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (a b : ℕ → ℚ) (hab : ∀ z ∈ V, a z ≤ b z) {x : ℕ} (hx : x ∈ V) :
    row q D V a x ≤ row q D V b x := by
  have hs : mass (outN D V x) a ≤ mass (outN D V x) b :=
    sum_le_sum (fun z hz => hab z (outN_subset hz))
  have hm := mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg q : (0 : ℚ) ≤ q)
  simp only [row, outW_eq_mass]
  linarith [hab x hx]

theorem receiver_mass_after_delete {V : Finset ℕ} {v y : ℕ}
    (hv : v ∈ V) (hy : y ∈ V.erase v) (a : ℕ → ℚ) (L : ℚ) :
    mass (V.erase v) (fun z => a z + receiverMass y L z) = mass V a + L - a v := by
  rw [mass_add_weights, mass_receiverMass, if_pos hy]
  have he : mass (V.erase v) a + a v = mass V a := sum_erase_add _ _ hv
  linarith

theorem amplified_receiver_rows_nondecreasing {q : ℕ} (hq : 2 ≤ q)
    {D : CH.Digraph} {V : Finset ℕ} {v y : ℕ} {C : Finset (ℕ × ℕ)}
    (hf : QFree D V q) (hv : v ∈ V) (hy : y ∈ outN D V v) (hC : RootCuts D V v C)
    (a : ℕ → ℚ) (ha : ∀ z ∈ V, 0 ≤ a z) (L : ℚ) (hL : a v ≤ L)
    (hfunded : ∀ r s, (r, s) ∈ C → D r y = true)
    (hpaid : ∀ r ∈ V, (cutHeads V C r).Nonempty → mass (cutHeads V C r) a ≤ L)
    (hcover : ∀ x ∈ inN D V v,
      y ∈ splitSafe q D V v C x ∨ a v ≤ mass (splitNew q D V v C x) a) :
    ∀ x ∈ V.erase v, row q D V a x ≤ row q (splitTransferGraph q D V v C) (V.erase v)
      (fun z => a z + receiverMass y L z) x := by
  have hL0 : 0 ≤ L := (ha v hv).trans hL
  have hs : ∀ z ∈ V, z ∉ outN D V v → receiverMass y L z = 0 :=
    fun z _ hz => receiverMass_supported hy L hz
  intro x hx
  by_cases hp : x ∈ inN D V v
  · have hbase : row q D V a x ≤ row q (splitTransferGraph q D V v C) (V.erase v)
        (fun z => a z + receiverMass y (a v) z) x := by
      rw [splitTransfer_row hq hf hv hC a (receiverMass y (a v))
        (fun z _ hz => receiverMass_supported hy (a v) hz)
        (by simp [mass_receiverMass, hy]) hx, splitGain, if_pos hp]
      have hc := single_receiver_parent_credit_of_mass a ha (ha v hv) (hcover x hp)
      linarith
    apply hbase.trans (row_mono_weights _ _ ?_ hx)
    intro z hz
    unfold receiverMass
    split_ifs <;> linarith
  · rw [splitTransfer_other_row hC hx hp a (receiverMass y L) hs]
    by_cases hne : (cutHeads V C x).Nonempty
    · obtain ⟨s, hsC⟩ := hne
      have hxy := hfunded x s (mem_filter.mp hsC).2
      have hyH : y ∈ outN D V x ∩ outN D V v :=
        mem_inter.mpr ⟨mem_outN.mpr ⟨outN_subset hy, hxy⟩, hy⟩
      rw [mass_receiverMass, if_pos hyH]
      have hcut := mul_le_mul_of_nonneg_left
        (hpaid x (mem_erase.mp hx).2 ⟨s, hsC⟩) (Nat.cast_nonneg q : (0 : ℚ) ≤ q)
      linarith [receiverMass_nonneg hL0 y x]
    · rw [not_nonempty_iff_eq_empty.mp hne]
      simp only [mass, sum_empty, mul_zero, sub_zero]
      have hheads : 0 ≤ mass (outN D V x ∩ outN D V v) (receiverMass y L) :=
        mass_nonneg (fun z _ => receiverMass_nonneg hL0 y z)
      change row q D V a x ≤ row q D V a x + receiverMass y L x +
        q * mass (outN D V x ∩ outN D V v) (receiverMass y L)
      nlinarith [receiverMass_nonneg hL0 y x, (Nat.cast_nonneg q : (0 : ℚ) ≤ q)]

theorem amplified_receiver_exact_gain {q : ℕ} (hq : 2 ≤ q)
    {D : CH.Digraph} {V : Finset ℕ} {v y : ℕ} {C : Finset (ℕ × ℕ)}
    (hf : QFree D V q) (hv : v ∈ V) (hy : y ∈ outN D V v) (hC : RootCuts D V v C)
    (hfunded : ∀ r s, (r, s) ∈ C → D r y = true) (a : ℕ → ℚ) (L : ℚ) :
    row q (splitTransferGraph q D V v C) (V.erase v) (fun z => a z + receiverMass y L z) y =
      row q D V a y + L := by
  have hyV := outN_subset hy
  have hyK := (root_interfaces_retained (by omega : 1 ≤ q) hf hv).2 hy
  have hnotP : y ∉ inN D V v := by
    intro hp
    exact digonfree hf hq hv hyV (mem_outN.mp hy).2 (mem_inN.mp hp).2
  have hcuts : cutHeads V C y = ∅ := by
    apply eq_empty_of_forall_notMem
    intro z hz
    exact loopfree hf (by omega : 1 ≤ q) hyV (hfunded y z (mem_filter.mp hz).2)
  have hnotH : y ∉ outN D V y ∩ outN D V v := by
    intro h
    exact loopfree hf (by omega : 1 ≤ q) hyV (mem_outN.mp (mem_inter.mp h).1).2
  rw [splitTransfer_other_row hC hyK hnotP a (receiverMass y L)
    (fun z _ hz => receiverMass_supported hy L hz), hcuts, mass_receiverMass, if_neg hnotH]
  simp [receiverMass, mass]

/-- Transfer any L>=a(v) whose new child mass does not exceed the old common
row lower bound. Positive L gives the strict positive receiver coordinate. -/
theorem amplified_receiver_cover_impossible {q : ℕ} (hq : 2 ≤ q)
    {D : CH.Digraph} {V : Finset ℕ} {v y : ℕ} {C : Finset (ℕ × ℕ)}
    (hf : QFree D V q) (hsmall : SmallerSmallRow q V.card)
    (hv : v ∈ V) (hy : y ∈ outN D V v) (hC : RootCuts D V v C)
    (a : ℕ → ℚ) (ha : ∀ z ∈ V, 0 ≤ a z) (L : ℚ) (hL : a v ≤ L) (hpos : 0 < L)
    (c : ℚ) (hc : mass V a + L - a v ≤ c) (hr : ∀ x ∈ V, c ≤ row q D V a x)
    (hfunded : ∀ r s, (r, s) ∈ C → D r y = true)
    (hpaid : ∀ r ∈ V, (cutHeads V C r).Nonempty → mass (cutHeads V C r) a ≤ L)
    (hcover : ∀ x ∈ inN D V v,
      y ∈ splitSafe q D V v C x ∨ a v ≤ mass (splitNew q D V v C x) a) : False := by
  let E := splitTransferGraph q D V v C
  let b := fun z => a z + receiverMass y L z
  have hyK := (root_interfaces_retained (by omega : 1 ≤ q) hf hv).2 hy
  have hfree : QFree E (V.erase v) q := splitTransferGraph_qfree (by omega : 1 ≤ q) hf hv C
  have hnn : ∀ x ∈ V.erase v, 0 ≤ b x :=
    fun x hx => add_nonneg (ha x (mem_erase.mp hx).2) (receiverMass_nonneg hpos.le y x)
  have hsup : SmallRow q E ((V.erase v).filter (fun x => 0 < b x)) :=
    hsmall _ _ ((card_le_card (filter_subset _ _)).trans_lt (card_erase_lt_of_mem hv))
      (hfree.mono_set (filter_subset _ _))
  have hm : mass (V.erase v) b = mass V a + L - a v := receiver_mass_after_delete hv hyK a L
  have hfeas : ∀ x ∈ V.erase v, mass (V.erase v) b ≤ row q E (V.erase v) b x := by
    intro x hx
    rw [hm]
    exact (hc.trans (hr x (mem_erase.mp hx).2)).trans
      (amplified_receiver_rows_nondecreasing hq hf hv hy hC a ha L hL hfunded hpaid hcover x hx)
  have hyp : 0 < b y := by
    simp only [b, receiverMass, ite_true]
    linarith [ha y (outN_subset hy)]
  have he := positive_coordinate_tight_of_support_smallRow hq b hnn hsup hfeas hyK hyp
  change row q (splitTransferGraph q D V v C) (V.erase v) (fun z => a z + receiverMass y L z) y = _ at he
  rw [amplified_receiver_exact_gain hq hf hv hy hC hfunded a L, hm] at he
  linarith [hr y (outN_subset hy)]

theorem amplified_receiver_original_cover_impossible {q : ℕ} (hq : 2 ≤ q)
    {D : CH.Digraph} {V : Finset ℕ} {v y : ℕ} {C : Finset (ℕ × ℕ)}
    (hf : QFree D V q) (hsmall : SmallerSmallRow q V.card)
    (hv : v ∈ V) (hy : y ∈ outN D V v) (hC : RootCuts D V v C)
    (a : ℕ → ℚ) (ha : ∀ z ∈ V, 0 ≤ a z) (L : ℚ) (hL : a v ≤ L) (hpos : 0 < L)
    (c : ℚ) (hc : mass V a + L - a v ≤ c) (hr : ∀ x ∈ V, c ≤ row q D V a x)
    (hfunded : ∀ r s, (r, s) ∈ C → D r y = true)
    (hpaid : ∀ r ∈ V, (cutHeads V C r).Nonempty → mass (cutHeads V C r) a ≤ L)
    (hcover : ReceiverMassCover q D V v y C a) : False := by
  apply amplified_receiver_cover_impossible hq hf hsmall hv hy hC a ha L hL hpos c hc hr hfunded hpaid
  intro x hx
  exact (hcover x hx).imp ((splitSafe_receiver_iff_original hf hy hfunded).mpr) id

theorem full_margin_receiver_cover_impossible {q : ℕ} (hq : 2 ≤ q)
    {D : CH.Digraph} {V : Finset ℕ} {v y : ℕ} {C : Finset (ℕ × ℕ)}
    (hf : QFree D V q) (hsmall : SmallerSmallRow q V.card)
    (hv : v ∈ V) (hy : y ∈ outN D V v) (hC : RootCuts D V v C)
    (a : ℕ → ℚ) (ha : ∀ z ∈ V, 0 ≤ a z) (c : ℚ) (hc : mass V a ≤ c)
    (hpos : 0 < a v + (c - mass V a)) (hr : ∀ x ∈ V, c ≤ row q D V a x)
    (hfunded : ∀ r s, (r, s) ∈ C → D r y = true)
    (hpaid : ∀ r ∈ V, (cutHeads V C r).Nonempty →
      mass (cutHeads V C r) a ≤ a v + (c - mass V a))
    (hcover : ReceiverMassCover q D V v y C a) : False :=
  amplified_receiver_original_cover_impossible hq hf hsmall hv hy hC a ha _ (by linarith)
    hpos c (by linarith) hr hfunded hpaid hcover

end LeanCH.BR.WeightedSD
