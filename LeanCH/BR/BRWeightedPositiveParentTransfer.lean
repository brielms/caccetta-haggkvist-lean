import LeanCH.BR.BRWeightedCommonParentTransfer
import LeanCH.BR.BRWeightedStrictCapstone
import LeanCH.BR.BRWeightedArcGap

/-! Positive feasible weights have tight rows under SmallRow alone. Apply
that existing arithmetic/minimax consequence to the actual transfer child. -/
namespace LeanCH.BR.WeightedSD
open Finset BRq2 BRq3 BR45 BRsub

theorem positive_feasible_rows_tight_of_smallRow {q : ℕ} (hq : 2 ≤ q)
    {D : CH.Digraph} {V : Finset ℕ} (hsmall : SmallRow q D V)
    (a : ℕ → ℚ) (ha : ∀ x ∈ V, 0 < a x)
    (hr : ∀ x ∈ V, mass V a ≤ row q D V a x) :
    ∀ x ∈ V, row q D V a x = mass V a := by
  intro x hx
  have hmpos : 0 < mass V a := sum_pos' (fun z hz => (ha z hz).le) ⟨x, hx, ha x hx⟩
  let w := fun z => a z / mass V a
  have hw : ∀ z ∈ V, 0 < w z := fun z hz => div_pos (ha z hz) hmpos
  have hwm : mass V w = 1 := by
    rw [mass_div]
    exact div_self (ne_of_gt hmpos)
  have hwr : ∀ z ∈ V, 1 ≤ row q D V w z := by
    intro z hz
    rw [row_div]
    exact (le_div_iff₀ hmpos).mpr (by simpa using hr z hz)
  have he := (normalized_pair_of_no_strict hq w hw hwm hwr hsmall.not_strictPositiveRows).1 x hx
  rw [row_div] at he
  have h := (div_eq_iff (ne_of_gt hmpos)).mp he
  simpa using h

theorem parentTransfer_positive {V S : Finset ℕ} {a : ℕ → ℚ} {y : ℕ}
    (hSV : S ⊆ V) (ha : ∀ x ∈ V, 0 ≤ a x) (hpos : ∀ x ∈ V \ S, 0 < a x) :
    ∀ x ∈ V \ S, 0 < addWeightAt a y (mass S a) x := by
  have hA := mass_nonneg (fun s hs => ha s (hSV hs))
  intro x hx
  unfold addWeightAt
  split_ifs <;> linarith [hpos x hx]

theorem parentTransfer_feasible_of_budget {q : ℕ} (hq : 2 ≤ q)
    {D : CH.Digraph} {V S : Finset ℕ} {y : ℕ} (hf : QFree D V q)
    (hy : y ∈ V) (hS : S ⊆ inN D V y)
    (a : ℕ → ℚ) (ha : ∀ t ∈ V, 0 ≤ a t) (c : ℚ)
    (hc : mass V a ≤ c) (hr : ∀ x ∈ V, c ≤ row q D V a x)
    (hbudget : q * mass (firstHeadBank q D V S y) a ≤ mass S a + c - mass V a) :
    ∀ x ∈ V \ S, mass (V \ S) (addWeightAt a y (mass S a)) ≤
      row q (parentTransferGraph q D V S y) (V \ S) (addWeightAt a y (mass S a)) x := by
  intro x hx
  rw [parentTransfer_mass (by omega : 1 ≤ q) hf hy hS a]
  by_cases hxy : x = y
  · subst x
    rw [parentTransfer_receiver_row hq hf hy hS a]
    linarith [hr y hy]
  · exact (hc.trans (hr x (mem_sdiff.mp hx).1)).trans
      (parentTransfer_other_row (by omega : 1 ≤ q) hf hy hS a ha hx hxy)

/-- A genuinely new shortcut gives at least q*a(y) additional row mass. -/
theorem parentTransfer_new_parent_gain {q : ℕ} (hq : 1 ≤ q)
    {D : CH.Digraph} {V S : Finset ℕ} {y x : ℕ} (hf : QFree D V q)
    (hy : y ∈ V) (hS : S ⊆ inN D V y)
    (a : ℕ → ℚ) (ha : ∀ t ∈ V, 0 ≤ a t)
    (hx : x ∈ V \ S) (hxy : x ≠ y) (hparent : ∃ s ∈ S, D x s = true)
    (hnxy : ¬ D x y = true) :
    row q D V a x + q * a y ≤
      row q (parentTransferGraph q D V S y) (V \ S) (addWeightAt a y (mass S a)) x := by
  have hyK := common_parent_receiver_retained hq hf hy hS
  have hSV : S ⊆ V := fun s hs => (mem_inN.mp (hS hs)).1
  have hEy : parentTransferGraph q D V S y x y = true :=
    decide_eq_true ⟨hx, hyK, Or.inr ⟨rfl, hparent⟩⟩
  have hsub : insert y (outN D (V \ S) x) ⊆ outN (parentTransferGraph q D V S y) (V \ S) x := by
    apply insert_subset (mem_outN.mpr ⟨hyK, hEy⟩)
    intro z hz
    obtain ⟨hzK, hxz⟩ := mem_outN.mp hz
    refine mem_outN.mpr ⟨hzK, decide_eq_true ?_⟩
    exact ⟨hx, hzK, Or.inl (decide_eq_true ⟨hxz, fun h => hxy h.1⟩)⟩
  have hyn : y ∉ outN D (V \ S) x := fun h => hnxy (mem_outN.mp h).2
  have hmass := mass_mono hsub (fun z hz => ha z (mem_sdiff.mp (outN_subset hz)).1)
  have hs : mass (insert y (outN D (V \ S) x)) a = a y + mass (outN D (V \ S) x) a := sum_insert hyn
  rw [hs, ← outW_eq_mass, ← outW_eq_mass] at hmass
  have hloss : outW D S a x ≤ mass S a := by
    rw [outW_eq_mass]
    exact mass_mono outN_subset (fun s hs => ha s (hSV hs))
  rw [row, row, outW_split hSV, outW_addWeightAt hyK, if_pos hEy]
  simp only [addWeightAt, if_neg hxy, add_zero]
  have hqQ : (0 : ℚ) ≤ q := Nat.cast_nonneg q
  nlinarith

theorem common_parent_bank_bound_positive {q : ℕ} (hq : 2 ≤ q)
    {D : CH.Digraph} {V S : Finset ℕ} {y : ℕ} (hf : QFree D V q)
    (hsmall : SmallerSmallRow q V.card) (hy : y ∈ V)
    (hS : S ⊆ inN D V y) (hSne : S.Nonempty)
    (a : ℕ → ℚ) (ha : ∀ t ∈ V, 0 ≤ a t) (hpos : ∀ t ∈ V \ S, 0 < a t)
    (c : ℚ) (hc : mass V a ≤ c) (hr : ∀ x ∈ V, c ≤ row q D V a x) :
    mass S a + c - mass V a ≤ q * mass (firstHeadBank q D V S y) a := by
  by_contra hn
  have hSV : S ⊆ V := fun s hs => (mem_inN.mp (hS hs)).1
  have hchild := hsmall _ _ (parentTransfer_card_lt hSV hSne) (parentTransferGraph_qfree hq hf hy hS)
  have ht := positive_feasible_rows_tight_of_smallRow hq hchild _
    (parentTransfer_positive hSV ha hpos)
    (parentTransfer_feasible_of_budget hq hf hy hS a ha c hc hr (by linarith))
    y (common_parent_receiver_retained (by omega : 1 ≤ q) hf hy hS)
  rw [parentTransfer_mass (by omega : 1 ≤ q) hf hy hS a,
    parentTransfer_receiver_row hq hf hy hS a] at ht
  linarith [hr y hy]

theorem common_parent_bank_strict_of_positive_strict_rows {q : ℕ} (hq : 2 ≤ q)
    {D : CH.Digraph} {V S : Finset ℕ} {y : ℕ} (hf : QFree D V q)
    (hsmall : SmallerSmallRow q V.card) (hy : y ∈ V)
    (hS : S ⊆ inN D V y) (hSne : S.Nonempty)
    (a : ℕ → ℚ) (ha : ∀ t ∈ V, 0 ≤ a t) (hpos : ∀ t ∈ V \ S, 0 < a t)
    (c : ℚ) (hc : mass V a < c) (hr : ∀ x ∈ V, c ≤ row q D V a x) :
    mass S a + c - mass V a < q * mass (firstHeadBank q D V S y) a := by
  by_contra hn
  have hSV : S ⊆ V := fun s hs => (mem_inN.mp (hS hs)).1
  have hchild := hsmall _ _ (parentTransfer_card_lt hSV hSne) (parentTransferGraph_qfree hq hf hy hS)
  have ht := positive_feasible_rows_tight_of_smallRow hq hchild _
    (parentTransfer_positive hSV ha hpos)
    (parentTransfer_feasible_of_budget hq hf hy hS a ha c hc.le hr (by linarith))
  have hmin := minOut_one_of_strict a ha (fun x hx => hc.trans_le (hr x hx))
  obtain ⟨x, hxO⟩ := card_pos.mp (hmin y hy)
  obtain ⟨hxV, hyx⟩ := mem_outN.mp hxO
  have hxK : x ∈ V \ S := by
    refine mem_sdiff.mpr ⟨hxV, ?_⟩
    intro hxS
    exact digonfree hf hq hy hxV hyx (mem_inN.mp (hS hxS)).2
  have hxy : x ≠ y := by
    intro he; subst x
    exact loopfree hf (by omega) hy hyx
  have heq := ht x hxK
  rw [parentTransfer_mass (by omega : 1 ≤ q) hf hy hS a] at heq
  have hother := parentTransfer_other_row (by omega : 1 ≤ q) hf hy hS a ha hxK hxy
  linarith [hr x hxV]

/-- At the boundary, nonnegative column weights suffice when the receiver
has positive column weight and its column equals those of the removed parents.
Only retained row coordinates need be positive. -/
theorem common_parent_bank_strict_at_boundary {q : ℕ} (hq : 2 ≤ q)
    {D : CH.Digraph} {V S : Finset ℕ} {y : ℕ} (hf : QFree D V q)
    (hsmall : SmallerSmallRow q V.card) (hy : y ∈ V)
    (hS : S ⊆ inN D V y) (hSne : S.Nonempty)
    (a : ℕ → ℚ) (ha : ∀ t ∈ V, 0 ≤ a t) (hpos : ∀ t ∈ V \ S, 0 < a t)
    (hr : ∀ x ∈ V, row q D V a x = mass V a)
    (p : ℕ → ℚ) (hp : ∀ t ∈ V, 0 ≤ p t) (hpy : 0 < p y)
    (hc : ∀ s ∈ S, col q D V p s = col q D V p y) :
    mass S a < q * mass (firstHeadBank q D V S y) a := by
  by_contra hn
  have hSV : S ⊆ V := fun s hs => (mem_inN.mp (hS hs)).1
  have hyK := common_parent_receiver_retained (by omega : 1 ≤ q) hf hy hS
  have hchild := hsmall _ _ (parentTransfer_card_lt hSV hSne) (parentTransferGraph_qfree hq hf hy hS)
  have ht := positive_feasible_rows_tight_of_smallRow hq hchild _
    (parentTransfer_positive hSV ha hpos)
    (parentTransfer_feasible_of_budget hq hf hy hS a ha (mass V a) le_rfl
      (fun x hx => (hr x hx).ge) (by linarith))
  have htight : ∀ x ∈ V \ S,
      row q (parentTransferGraph q D V S y) (V \ S) (addWeightAt a y (mass S a)) x = mass V a := by
    intro x hx
    exact (ht x hx).trans (parentTransfer_mass (by omega : 1 ≤ q) hf hy hS a)
  obtain ⟨s, hs⟩ := hSne
  have hsV := hSV hs
  have hsy := (mem_inN.mp (hS hs)).2
  have hdom : inN D V s ⊆ inN D V y := by
    intro x hx
    obtain ⟨hxV, hxs⟩ := mem_inN.mp hx
    by_cases hxS : x ∈ S
    · exact hS hxS
    have hxK := mem_sdiff.mpr ⟨hxV, hxS⟩
    have hxy : x ≠ y := by
      intro he; subst x
      exact digonfree hf hq hsV hy hsy hxs
    refine mem_inN.mpr ⟨hxV, ?_⟩
    by_contra hno
    have hgain := parentTransfer_new_parent_gain (by omega : 1 ≤ q) hf hy hS a ha hxK hxy
      ⟨s, hs, hxs⟩ hno
    rw [hr x hxV, htight x hxK] at hgain
    have hqQ : (0 : ℚ) < q := by exact_mod_cast (by omega : 0 < q)
    nlinarith [hpos y hyK]
  have he : row q (fun a b => D b a) V p s = row q (fun a b => D b a) V p y := hc s hs
  obtain ⟨t, htgap⟩ := equal_rows_arc_gap_nonempty (D := fun a b => D b a)
    (by omega : 1 ≤ q) p hp hsV hpy hsy (loopfree hf (by omega) hsV) he
  obtain ⟨htV, hts, hnty⟩ := mem_outGap.mp htgap
  exact hnty (mem_inN.mp (hdom (mem_inN.mpr ⟨htV, hts⟩))).2

/-- Tightness on the positive support; zero-coordinate rows are not asserted
tight. No graph or cardinality restriction is needed beyond support SmallRow. -/
theorem positive_coordinate_tight_of_support_smallRow {q : ℕ} (hq : 2 ≤ q)
    {D : CH.Digraph} {V : Finset ℕ} (a : ℕ → ℚ) (ha : ∀ x ∈ V, 0 ≤ a x)
    (hsmall : SmallRow q D (V.filter (fun x => 0 < a x)))
    (hr : ∀ x ∈ V, mass V a ≤ row q D V a x)
    {x : ℕ} (hx : x ∈ V) (hpos : 0 < a x) : row q D V a x = mass V a := by
  let F := V.filter (fun x => 0 < a x)
  have hFV : F ⊆ V := filter_subset _ _
  have hz : ∀ t ∈ V, t ∉ F → a t = 0 := by
    intro t ht hn
    have hnp : ¬ 0 < a t := fun hp => hn (mem_filter.mpr ⟨ht, hp⟩)
    exact le_antisymm (le_of_not_gt hnp) (ha t ht)
  have hm := mass_subset_zero hFV hz
  have hrows : ∀ t, row q D F a t = row q D V a t := by
    intro t
    rw [row, row, outW_subset_zero hFV hz]
  have h := positive_feasible_rows_tight_of_smallRow hq hsmall a
    (fun t ht => (mem_filter.mp ht).2) (fun t ht => by rw [hm, hrows]; exact hr t (hFV ht))
    x (mem_filter.mpr ⟨hx, hpos⟩)
  rwa [hrows, hm] at h

/-- Strict-source bank payment is strict even with zero weights. The
positive support of the actual edited child is itself a smaller q-free host. -/
theorem common_parent_bank_strict_of_strict_rows {q : ℕ} (hq : 2 ≤ q)
    {D : CH.Digraph} {V S : Finset ℕ} {y : ℕ} (hf : QFree D V q)
    (hsmall : SmallerSmallRow q V.card) (hy : y ∈ V)
    (hS : S ⊆ inN D V y) (hSne : S.Nonempty)
    (a : ℕ → ℚ) (ha : ∀ t ∈ V, 0 ≤ a t)
    (c : ℚ) (hc : mass V a < c) (hr : ∀ x ∈ V, c ≤ row q D V a x) :
    mass S a + c - mass V a < q * mass (firstHeadBank q D V S y) a := by
  by_contra hn
  have hSV : S ⊆ V := fun s hs => (mem_inN.mp (hS hs)).1
  have hA := mass_nonneg (fun s hs => ha s (hSV hs))
  have hfree := parentTransferGraph_qfree hq hf hy hS
  have hnn : ∀ x ∈ V \ S, 0 ≤ addWeightAt a y (mass S a) x :=
    fun x hx => addWeightAt_nonneg ha hA y x (mem_sdiff.mp hx).1
  have hfeasible := parentTransfer_feasible_of_budget hq hf hy hS a ha c hc.le hr (by linarith)
  have hsupSmall : SmallRow q (parentTransferGraph q D V S y)
      ((V \ S).filter (fun x => 0 < addWeightAt a y (mass S a) x)) :=
    hsmall _ _ ((card_le_card (filter_subset _ _)).trans_lt (parentTransfer_card_lt hSV hSne))
      (hfree.mono_set (filter_subset _ _))
  have hay : a y ≤ mass V a := single_le_sum ha hy
  have ho : 0 < outW D V a y := by
    have hrow := hr y hy
    unfold row at hrow
    have hqQ : (0 : ℚ) ≤ q := Nat.cast_nonneg q
    by_contra hno
    have hle : outW D V a y ≤ 0 := le_of_not_gt hno
    nlinarith
  rw [outW_eq_mass] at ho
  obtain ⟨x, hxO, hxpos⟩ := (sum_pos_iff_of_nonneg (fun x hx => ha x (outN_subset hx))).mp ho
  obtain ⟨hxV, hyx⟩ := mem_outN.mp hxO
  have hxK : x ∈ V \ S := by
    refine mem_sdiff.mpr ⟨hxV, ?_⟩
    intro hxS
    exact digonfree hf hq hy hxV hyx (mem_inN.mp (hS hxS)).2
  have hxy : x ≠ y := by
    intro he; subst x
    exact loopfree hf (by omega) hy hyx
  have hxpos' : 0 < addWeightAt a y (mass S a) x := by
    simpa only [addWeightAt, if_neg hxy, add_zero] using hxpos
  have heq := positive_coordinate_tight_of_support_smallRow hq _ hnn hsupSmall hfeasible hxK hxpos'
  rw [parentTransfer_mass (by omega : 1 ≤ q) hf hy hS a] at heq
  have hother := parentTransfer_other_row (by omega : 1 ≤ q) hf hy hS a ha hxK hxy
  linarith [hr x hxV]

end LeanCH.BR.WeightedSD
