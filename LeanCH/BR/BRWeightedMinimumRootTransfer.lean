import LeanCH.BR.BRWeightedMinimumRootLocal

/-! A concrete single-receiver transfer with aggregate new-head credit and its
exact remaining parent cover explicit. Minimum receiver weights are only a
corollary. The constructed child rows are proved before induction. -/
namespace LeanCH.BR.WeightedSD
open Finset BRq2 BRq3 BR45 BRsub

def receiverMass (y : ℕ) (M : ℚ) : ℕ → ℚ := fun z => if z = y then M else 0

theorem mass_receiverMass (A : Finset ℕ) (y : ℕ) (M : ℚ) :
    mass A (receiverMass y M) = if y ∈ A then M else 0 := by
  simp [mass, receiverMass]

theorem receiverMass_nonneg {M : ℚ} (hM : 0 ≤ M) (y z : ℕ) : 0 ≤ receiverMass y M z := by
  unfold receiverMass
  split_ifs <;> linarith

theorem receiverMass_supported {T : Finset ℕ} {y : ℕ} (hy : y ∈ T) (M : ℚ)
    {z : ℕ} (hz : z ∉ T) : receiverMass y M z = 0 := by
  have hn : z ≠ y := fun he => hz (he ▸ hy)
  simp only [receiverMass, if_neg hn]

theorem single_receiver_parent_credit {q : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    {v y x : ℕ} {C : Finset (ℕ × ℕ)} (hy : y ∈ outN D V v)
    (a : ℕ → ℚ) (ha : ∀ z ∈ V, 0 ≤ a z) (hM : 0 ≤ a v)
    (hmin : ∀ z ∈ outN D V v, a v ≤ a z)
    (hcover : y ∈ splitSafe q D V v C x ∨ (splitNew q D V v C x).Nonempty) :
    q * mass (splitBlocked q D V v C x) (receiverMass y (a v)) ≤
      q * mass (splitNew q D V v C x) a := by
  rcases hcover with hsafe | hnew
  · have hn : y ∉ splitBlocked q D V v C x := fun h => (mem_sdiff.mp h).2 hsafe
    rw [mass_receiverMass, if_neg hn, mul_zero]
    apply mul_nonneg (Nat.cast_nonneg _)
    exact mass_nonneg (fun z hz => ha z (outN_subset (mem_filter.mp (mem_sdiff.mp hz).1).1))
  · exact minimum_new_head_pays a (receiverMass y (a v)) ha hmin
      (fun z _ => receiverMass_nonneg hM y z) (by simp [mass_receiverMass, hy]) hnew

theorem single_receiver_parent_credit_of_mass {q : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    {v y x : ℕ} {C : Finset (ℕ × ℕ)}
    (a : ℕ → ℚ) (ha : ∀ z ∈ V, 0 ≤ a z) (hM : 0 ≤ a v)
    (hcover : y ∈ splitSafe q D V v C x ∨ a v ≤ mass (splitNew q D V v C x) a) :
    q * mass (splitBlocked q D V v C x) (receiverMass y (a v)) ≤
      q * mass (splitNew q D V v C x) a := by
  rcases hcover with hsafe | hmass
  · have hn : y ∉ splitBlocked q D V v C x := fun h => (mem_sdiff.mp h).2 hsafe
    rw [mass_receiverMass, if_neg hn, mul_zero]
    apply mul_nonneg (Nat.cast_nonneg _)
    exact mass_nonneg (fun z hz => ha z (outN_subset (mem_filter.mp (mem_sdiff.mp hz).1).1))
  · have hB : mass (splitBlocked q D V v C x) (receiverMass y (a v)) ≤ a v := by
      rw [mass_receiverMass]
      split_ifs <;> linarith
    exact mul_le_mul_of_nonneg_left (hB.trans hmass) (Nat.cast_nonneg q)

/-- The actual new rows are strict; this mass-cover master assumes no IH,
minimum root, receiver floor, or positive root weight. -/
theorem single_receiver_strict_child_rows {q : ℕ} (hq : 2 ≤ q)
    {D : CH.Digraph} {V : Finset ℕ} {v y : ℕ} {C : Finset (ℕ × ℕ)}
    (hf : QFree D V q) (hv : v ∈ V) (hy : y ∈ outN D V v) (hC : RootCuts D V v C)
    (a : ℕ → ℚ) (ha : ∀ z ∈ V, 0 ≤ a z)
    (c : ℚ) (hc : mass V a < c) (hr : ∀ x ∈ V, c ≤ row q D V a x)
    (hfunded : ∀ r s, (r, s) ∈ C → D r y = true)
    (hpaid : ∀ r ∈ V, (cutHeads V C r).Nonempty →
      q * mass (cutHeads V C r) a < c - mass V a + q * a v)
    (hcover : ∀ x ∈ inN D V v,
      y ∈ splitSafe q D V v C x ∨ a v ≤ mass (splitNew q D V v C x) a) :
    ∀ x ∈ V.erase v, mass V a < row q (splitTransferGraph q D V v C) (V.erase v)
      (fun z => a z + receiverMass y (a v) z) x := by
  have hM := ha v hv
  have hα : ∀ z, 0 ≤ receiverMass y (a v) z := receiverMass_nonneg hM y
  have hs : ∀ z ∈ V, z ∉ outN D V v → receiverMass y (a v) z = 0 :=
    fun z _ hz => receiverMass_supported hy (a v) hz
  have hm : mass (outN D V v) (receiverMass y (a v)) = a v := by simp [mass_receiverMass, hy]
  intro x hx
  have hxV := (mem_erase.mp hx).2
  have hrow := hr x hxV
  rw [splitTransfer_row hq hf hv hC a (receiverMass y (a v)) hs hm hx]
  by_cases hp : x ∈ inN D V v
  · rw [splitGain, if_pos hp]
    have hcredit := single_receiver_parent_credit_of_mass a ha hM (hcover x hp)
    linarith
  · rw [splitGain, if_neg hp]
    by_cases hne : (cutHeads V C x).Nonempty
    · obtain ⟨s, hsC⟩ := hne
      have hxy := hfunded x s (mem_filter.mp hsC).2
      have hyH : y ∈ outN D V x ∩ outN D V v :=
        mem_inter.mpr ⟨mem_outN.mpr ⟨outN_subset hy, hxy⟩, hy⟩
      rw [mass_receiverMass, if_pos hyH]
      have hcut := hpaid x hxV ⟨s, hsC⟩
      linarith [hα x]
    · have he := not_nonempty_iff_eq_empty.mp hne
      rw [he]
      simp only [mass, sum_empty, mul_zero, sub_zero]
      have hheads : 0 ≤ mass (outN D V x ∩ outN D V v) (receiverMass y (a v)) :=
        mass_nonneg (fun z _ => hα z)
      have hqQ : (0 : ℚ) ≤ q := Nat.cast_nonneg q
      change mass V a < row q D V a x + (receiverMass y (a v) x +
        q * mass (outN D V x ∩ outN D V v) (receiverMass y (a v)))
      nlinarith [hα x]

theorem single_receiver_cover_impossible {q : ℕ} (hq : 2 ≤ q)
    {D : CH.Digraph} {V : Finset ℕ} {v y : ℕ} {C : Finset (ℕ × ℕ)}
    (hf : QFree D V q) (hsmall : SmallerSmallRow q V.card)
    (hv : v ∈ V) (hy : y ∈ outN D V v) (hC : RootCuts D V v C)
    (a : ℕ → ℚ) (ha : ∀ z ∈ V, 0 ≤ a z)
    (c : ℚ) (hc : mass V a < c) (hr : ∀ x ∈ V, c ≤ row q D V a x)
    (hfunded : ∀ r s, (r, s) ∈ C → D r y = true)
    (hpaid : ∀ r ∈ V, (cutHeads V C r).Nonempty →
      q * mass (cutHeads V C r) a < c - mass V a + q * a v)
    (hcover : ∀ x ∈ inN D V v,
      y ∈ splitSafe q D V v C x ∨ a v ≤ mass (splitNew q D V v C x) a) : False := by
  have hq1 : 1 ≤ q := by omega
  have hyK := (root_interfaces_retained hq1 hf hv).2 hy
  have hchild := hsmall _ _ (card_erase_lt_of_mem hv) (splitTransferGraph_qfree hq1 hf hv C)
  have hnn : ∀ x ∈ V.erase v, 0 ≤ a x + receiverMass y (a v) x := by
    intro x hx
    exact add_nonneg (ha x (mem_erase.mp hx).2) (receiverMass_nonneg (ha v hv) y x)
  have hm := splitTransfer_mass hq1 hf hv a (receiverMass y (a v))
    (fun z _ hz => receiverMass_supported hy (a v) hz) (by simp [mass_receiverMass, hy])
  apply hchild.no_strict ⟨y, hyK⟩ (fun z => a z + receiverMass y (a v) z) hnn
  intro x hx
  rw [hm]
  exact single_receiver_strict_child_rows hq hf hv hy hC a ha c hc hr hfunded hpaid hcover x hx

def ReceiverMassCover (q : ℕ) (D : CH.Digraph) (V : Finset ℕ) (v y : ℕ)
    (C : Finset (ℕ × ℕ)) (a : ℕ → ℚ) : Prop :=
  ∀ x ∈ inN D V v, x ∉ ball D (V.erase v) y (q - 1) ∨ a v ≤ mass (splitNew q D V v C x) a

theorem receiver_mass_original_cover_impossible {q : ℕ} (hq : 2 ≤ q)
    {D : CH.Digraph} {V : Finset ℕ} {v y : ℕ} {C : Finset (ℕ × ℕ)}
    (hf : QFree D V q) (hsmall : SmallerSmallRow q V.card)
    (hv : v ∈ V) (hy : y ∈ outN D V v) (hC : RootCuts D V v C)
    (a : ℕ → ℚ) (ha : ∀ z ∈ V, 0 ≤ a z)
    (c : ℚ) (hc : mass V a < c) (hr : ∀ x ∈ V, c ≤ row q D V a x)
    (hfunded : ∀ r s, (r, s) ∈ C → D r y = true)
    (hpaid : ∀ r ∈ V, (cutHeads V C r).Nonempty →
      q * mass (cutHeads V C r) a < c - mass V a + q * a v)
    (hcover : ReceiverMassCover q D V v y C a) : False := by
  apply single_receiver_cover_impossible hq hf hsmall hv hy hC a ha c hc hr hfunded hpaid
  intro x hx
  exact (hcover x hx).imp ((splitSafe_receiver_iff_original hf hy hfunded).mpr) id

/-- The genuinely unresolved cover: originally blocked parents need another
receiver as an actual new safe head after the selected cuts. -/
def ReceiverHeadCover (q : ℕ) (D : CH.Digraph) (V : Finset ℕ) (v y : ℕ)
    (C : Finset (ℕ × ℕ)) : Prop :=
  ∀ x ∈ inN D V v, x ∉ ball D (V.erase v) y (q - 1) ∨ (splitNew q D V v C x).Nonempty

theorem receiver_bank_original_cover_impossible {q : ℕ} (hq : 2 ≤ q)
    {D : CH.Digraph} {V : Finset ℕ} {v y : ℕ} {C : Finset (ℕ × ℕ)}
    (hf : QFree D V q) (hsmall : SmallerSmallRow q V.card)
    (hv : v ∈ V) (hy : y ∈ outN D V v) (hC : RootCuts D V v C)
    (a : ℕ → ℚ) (ha : ∀ z ∈ V, 0 ≤ a z) (hmin : ∀ z ∈ outN D V v, a v ≤ a z)
    (c : ℚ) (hc : mass V a < c) (hr : ∀ x ∈ V, c ≤ row q D V a x)
    (hfunded : ∀ r s, (r, s) ∈ C → D r y = true)
    (hpaid : ∀ r ∈ V, (cutHeads V C r).Nonempty →
      q * mass (cutHeads V C r) a < c - mass V a + q * a v)
    (hcover : ReceiverHeadCover q D V v y C) : False := by
  apply receiver_mass_original_cover_impossible hq hf hsmall hv hy hC a ha c hc hr hfunded hpaid
  intro x hx
  rcases hcover x hx with hsafe | hnew
  · exact Or.inl hsafe
  · apply Or.inr
    exact nonempty_mass_ge_minimum (fun z hz => (mem_filter.mp (mem_sdiff.mp hz).1).1)
      hnew a (fun z hz => ha z (outN_subset hz)) (a v) hmin

/-- Global minimum-root specialization of the weaker receiver-bank constructor. -/
theorem minimum_root_original_cover_impossible {q : ℕ} (hq : 2 ≤ q)
    {D : CH.Digraph} {V : Finset ℕ} {v y : ℕ} {C : Finset (ℕ × ℕ)}
    (hf : QFree D V q) (hsmall : SmallerSmallRow q V.card)
    (hv : v ∈ V) (hy : y ∈ outN D V v) (hC : RootCuts D V v C)
    (a : ℕ → ℚ) (hM : 0 ≤ a v) (hmin : ∀ z ∈ V, a v ≤ a z)
    (c : ℚ) (hc : mass V a < c) (hr : ∀ x ∈ V, c ≤ row q D V a x)
    (hfunded : ∀ r s, (r, s) ∈ C → D r y = true)
    (hpaid : ∀ r ∈ V, (cutHeads V C r).Nonempty →
      q * mass (cutHeads V C r) a < c - mass V a + q * a v)
    (hcover : ReceiverHeadCover q D V v y C) : False :=
  receiver_bank_original_cover_impossible hq hf hsmall hv hy hC a
    (fun z hz => hM.trans (hmin z hz)) (fun z hz => hmin z (outN_subset hz))
    c hc hr hfunded hpaid hcover

/-- Weak cut costs and aggregate parent coverage make every retained row
nondecreasing, independently of any feasibility or induction premise. -/
theorem single_receiver_child_rows_nondecreasing {q : ℕ} (hq : 2 ≤ q)
    {D : CH.Digraph} {V : Finset ℕ} {v y : ℕ} {C : Finset (ℕ × ℕ)}
    (hf : QFree D V q) (hv : v ∈ V) (hy : y ∈ outN D V v) (hC : RootCuts D V v C)
    (a : ℕ → ℚ) (ha : ∀ z ∈ V, 0 ≤ a z)
    (hfunded : ∀ r s, (r, s) ∈ C → D r y = true)
    (hpaid : ∀ r ∈ V, (cutHeads V C r).Nonempty → mass (cutHeads V C r) a ≤ a v)
    (hcover : ∀ x ∈ inN D V v,
      y ∈ splitSafe q D V v C x ∨ a v ≤ mass (splitNew q D V v C x) a) :
    ∀ x ∈ V.erase v, row q D V a x ≤ row q (splitTransferGraph q D V v C) (V.erase v)
      (fun z => a z + receiverMass y (a v) z) x := by
  have hα := receiverMass_nonneg (ha v hv) y
  have hs : ∀ z ∈ V, z ∉ outN D V v → receiverMass y (a v) z = 0 :=
    fun z _ hz => receiverMass_supported hy (a v) hz
  have hm : mass (outN D V v) (receiverMass y (a v)) = a v := by simp [mass_receiverMass, hy]
  intro x hx
  rw [splitTransfer_row hq hf hv hC a (receiverMass y (a v)) hs hm hx]
  by_cases hp : x ∈ inN D V v
  · rw [splitGain, if_pos hp]
    have hcredit := single_receiver_parent_credit_of_mass a ha (ha v hv) (hcover x hp)
    linarith
  · rw [splitGain, if_neg hp]
    by_cases hne : (cutHeads V C x).Nonempty
    · obtain ⟨s, hsC⟩ := hne
      have hxy := hfunded x s (mem_filter.mp hsC).2
      have hyH : y ∈ outN D V x ∩ outN D V v :=
        mem_inter.mpr ⟨mem_outN.mpr ⟨outN_subset hy, hxy⟩, hy⟩
      rw [mass_receiverMass, if_pos hyH]
      have hcut := mul_le_mul_of_nonneg_left
        (hpaid x (mem_erase.mp hx).2 ⟨s, hsC⟩) (Nat.cast_nonneg q : (0 : ℚ) ≤ q)
      linarith [hα x]
    · have he := not_nonempty_iff_eq_empty.mp hne
      rw [he]
      simp only [mass, sum_empty, mul_zero, sub_zero]
      have hheads : 0 ≤ mass (outN D V x ∩ outN D V v) (receiverMass y (a v)) :=
        mass_nonneg (fun z _ => hα z)
      change row q D V a x ≤ row q D V a x + (receiverMass y (a v) x +
        q * mass (outN D V x ∩ outN D V v) (receiverMass y (a v)))
      nlinarith [hα x, (Nat.cast_nonneg q : (0 : ℚ) ≤ q)]

/-- The active receiver is uncut and gains positive deleted mass. Thus weakly
paid aggregate coverage is impossible even at the feasibility boundary. -/
theorem single_receiver_boundary_cover_impossible {q : ℕ} (hq : 2 ≤ q)
    {D : CH.Digraph} {V : Finset ℕ} {v y : ℕ} {C : Finset (ℕ × ℕ)}
    (hf : QFree D V q) (hsmall : SmallerSmallRow q V.card)
    (hv : v ∈ V) (hy : y ∈ outN D V v) (hC : RootCuts D V v C)
    (a : ℕ → ℚ) (ha : ∀ z ∈ V, 0 ≤ a z) (hM : 0 < a v)
    (hr : ∀ x ∈ V, mass V a ≤ row q D V a x)
    (hfunded : ∀ r s, (r, s) ∈ C → D r y = true)
    (hpaid : ∀ r ∈ V, (cutHeads V C r).Nonempty → mass (cutHeads V C r) a ≤ a v)
    (hcover : ∀ x ∈ inN D V v,
      y ∈ splitSafe q D V v C x ∨ a v ≤ mass (splitNew q D V v C x) a) : False := by
  have hq1 : 1 ≤ q := by omega
  have hyV := outN_subset hy
  have hyK := (root_interfaces_retained hq1 hf hv).2 hy
  have hs : ∀ z ∈ V, z ∉ outN D V v → receiverMass y (a v) z = 0 :=
    fun z _ hz => receiverMass_supported hy (a v) hz
  have hm : mass (outN D V v) (receiverMass y (a v)) = a v := by simp [mass_receiverMass, hy]
  have hnn : ∀ x ∈ V.erase v, 0 ≤ a x + receiverMass y (a v) x :=
    fun x hx => add_nonneg (ha x (mem_erase.mp hx).2) (receiverMass_nonneg hM.le y x)
  have hb : ∀ x ∈ V.erase v, mass V a ≤ row q D V a x + splitGain q D V v C a (receiverMass y (a v)) x := by
    intro x hx
    rw [← splitTransfer_row hq hf hv hC a (receiverMass y (a v)) hs hm hx]
    exact (hr x (mem_erase.mp hx).2).trans
      (single_receiver_child_rows_nondecreasing hq hf hv hy hC a ha hfunded hpaid hcover x hx)
  have hyp : 0 < a y + receiverMass y (a v) y := by
    simp only [receiverMass, ite_true]
    linarith [ha y hyV]
  have he := split_feasible_positive_tight hq hf hv hsmall hC a (receiverMass y (a v)) hs hm hnn hb hyK hyp
  have hnotP : y ∉ inN D V v := by
    intro hp
    exact digonfree hf hq hv hyV (mem_outN.mp hy).2 (mem_inN.mp hp).2
  have hcuts : cutHeads V C y = ∅ := by
    apply eq_empty_of_forall_notMem
    intro z hz
    exact loopfree hf hq1 hyV (hfunded y z (mem_filter.mp hz).2)
  have hnotH : y ∉ outN D V y ∩ outN D V v := by
    intro h
    exact loopfree hf hq1 hyV (mem_outN.mp (mem_inter.mp h).1).2
  rw [splitGain, if_neg hnotP, hcuts, mass_receiverMass, if_neg hnotH] at he
  simp only [receiverMass, ite_true, mass, sum_empty, mul_zero, add_zero, sub_zero] at he
  change row q D V a y + a v = mass V a at he
  linarith [hr y hyV]

theorem receiver_mass_boundary_original_cover_impossible {q : ℕ} (hq : 2 ≤ q)
    {D : CH.Digraph} {V : Finset ℕ} {v y : ℕ} {C : Finset (ℕ × ℕ)}
    (hf : QFree D V q) (hsmall : SmallerSmallRow q V.card)
    (hv : v ∈ V) (hy : y ∈ outN D V v) (hC : RootCuts D V v C)
    (a : ℕ → ℚ) (ha : ∀ z ∈ V, 0 ≤ a z) (hM : 0 < a v)
    (hr : ∀ x ∈ V, mass V a ≤ row q D V a x)
    (hfunded : ∀ r s, (r, s) ∈ C → D r y = true)
    (hpaid : ∀ r ∈ V, (cutHeads V C r).Nonempty → mass (cutHeads V C r) a ≤ a v)
    (hcover : ReceiverMassCover q D V v y C a) : False := by
  apply single_receiver_boundary_cover_impossible hq hf hsmall hv hy hC a ha hM hr hfunded hpaid
  intro x hx
  exact (hcover x hx).imp ((splitSafe_receiver_iff_original hf hy hfunded).mpr) id

end LeanCH.BR.WeightedSD
