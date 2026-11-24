import LeanCH.BR.BRCommonParentTransferGeometry

/-! Exact weight bookkeeping for the actual common-parent transfer child.
The common-value threshold and the smaller edited-graph premise stay explicit. -/
namespace LeanCH.BR.WeightedSD
open Finset BRq2 BRq3 BR45 BRsub

def addWeightAt (a : ℕ → ℚ) (y : ℕ) (A : ℚ) : ℕ → ℚ :=
  fun x => a x + if x = y then A else 0

theorem mass_addWeightAt {K : Finset ℕ} {y : ℕ} (hy : y ∈ K)
    (a : ℕ → ℚ) (A : ℚ) : mass K (addWeightAt a y A) = mass K a + A := by
  simp [mass, addWeightAt, sum_add_distrib, hy]

theorem outW_addWeightAt {D : CH.Digraph} {K : Finset ℕ} {y : ℕ} (hy : y ∈ K)
    (a : ℕ → ℚ) (A : ℚ) (x : ℕ) :
    outW D K (addWeightAt a y A) x = outW D K a x + if D x y = true then A else 0 := by
  calc
    _ = (∑ u ∈ K, if D x u = true then a u else 0) +
        ∑ u ∈ K, if u = y then (if D x y = true then A else 0) else 0 := by
      rw [← sum_add_distrib]
      apply sum_congr rfl
      intro u hu
      by_cases huy : u = y
      · subst u
        by_cases he : D x y = true <;> simp [addWeightAt, he]
      · by_cases he : D x u = true <;> simp [addWeightAt, huy, he]
    _ = _ := by simp [hy, outW]

theorem parentTransfer_mass {q : ℕ} (hq : 1 ≤ q)
    {D : CH.Digraph} {V S : Finset ℕ} {y : ℕ} (hf : QFree D V q)
    (hy : y ∈ V) (hS : S ⊆ inN D V y) (a : ℕ → ℚ) :
    mass (V \ S) (addWeightAt a y (mass S a)) = mass V a := by
  rw [mass_addWeightAt (common_parent_receiver_retained hq hf hy hS)]
  exact sum_sdiff (fun s hs => (mem_inN.mp (hS hs)).1)

theorem parentTransfer_receiver_heads {q : ℕ} (hq : 2 ≤ q)
    {D : CH.Digraph} {V S : Finset ℕ} {y : ℕ} (hf : QFree D V q)
    (hy : y ∈ V) (hS : S ⊆ inN D V y) :
    outN (parentTransferGraph q D V S y) (V \ S) y =
      outN D V y \ firstHeadBank q D V S y := by
  have hyK := common_parent_receiver_retained (by omega : 1 ≤ q) hf hy hS
  have hn : ¬ ∃ s ∈ S, D y s = true := by
    rintro ⟨s, hs, hys⟩
    exact digonfree hf hq hy (mem_inN.mp (hS hs)).1 hys (mem_inN.mp (hS hs)).2
  ext z
  constructor
  · intro hz
    obtain ⟨_, _, h | ⟨_, hs⟩⟩ := of_decide_eq_true (mem_outN.mp hz).2
    · obtain ⟨hyz, hcut⟩ := of_decide_eq_true h
      exact mem_sdiff.mpr ⟨mem_outN.mpr ⟨(mem_sdiff.mp (outN_subset hz)).1, hyz⟩,
        fun hb => hcut ⟨rfl, hb⟩⟩
    · exact (hn hs).elim
  · intro hz
    obtain ⟨hzO, hzB⟩ := mem_sdiff.mp hz
    obtain ⟨hzV, hyz⟩ := mem_outN.mp hzO
    have hzK : z ∈ V \ S := mem_sdiff.mpr ⟨hzV, fun hzS => hn ⟨z, hzS, hyz⟩⟩
    refine mem_outN.mpr ⟨hzK, ?_⟩
    apply decide_eq_true
    exact ⟨hyK, hzK, Or.inl (decide_eq_true ⟨hyz, fun h => hzB h.2⟩)⟩

theorem parentTransfer_receiver_row {q : ℕ} (hq : 2 ≤ q)
    {D : CH.Digraph} {V S : Finset ℕ} {y : ℕ} (hf : QFree D V q)
    (hy : y ∈ V) (hS : S ⊆ inN D V y) (a : ℕ → ℚ) :
    row q (parentTransferGraph q D V S y) (V \ S) (addWeightAt a y (mass S a)) y =
      row q D V a y + mass S a - q * mass (firstHeadBank q D V S y) a := by
  have hyK := common_parent_receiver_retained (by omega : 1 ≤ q) hf hy hS
  have hfE := parentTransferGraph_qfree hq hf hy hS
  have hloop := loopfree hfE (by omega : 1 ≤ q) hyK
  have hBsub : firstHeadBank q D V S y ⊆ outN D V y := fun z hz =>
    mem_outN.mpr ⟨(mem_firstHeadBank.mp hz).1, (mem_firstHeadBank.mp hz).2.1⟩
  have hsplit : mass (outN D V y \ firstHeadBank q D V S y) a +
      mass (firstHeadBank q D V S y) a = outW D V a y := by
    rw [outW_eq_mass]
    exact sum_sdiff hBsub
  rw [row, outW_addWeightAt hyK, if_neg hloop, add_zero, outW_eq_mass,
    parentTransfer_receiver_heads hq hf hy hS]
  simp only [addWeightAt, ite_true, row]
  rw [← hsplit]
  ring

theorem parentTransfer_other_row {q : ℕ} (hq : 1 ≤ q)
    {D : CH.Digraph} {V S : Finset ℕ} {y x : ℕ} (hf : QFree D V q)
    (hy : y ∈ V) (hS : S ⊆ inN D V y) (a : ℕ → ℚ) (ha : ∀ t ∈ V, 0 ≤ a t)
    (hx : x ∈ V \ S) (hxy : x ≠ y) :
    row q D V a x ≤
      row q (parentTransferGraph q D V S y) (V \ S) (addWeightAt a y (mass S a)) x := by
  have hyK := common_parent_receiver_retained hq hf hy hS
  have hSV : S ⊆ V := fun s hs => (mem_inN.mp (hS hs)).1
  have hA : 0 ≤ mass S a := mass_nonneg (fun s hs => ha s (hSV hs))
  have hkeep : outN D (V \ S) x ⊆ outN (parentTransferGraph q D V S y) (V \ S) x := by
    intro z hz
    obtain ⟨hzK, hxz⟩ := mem_outN.mp hz
    refine mem_outN.mpr ⟨hzK, decide_eq_true ?_⟩
    exact ⟨hx, hzK, Or.inl (decide_eq_true ⟨hxz, fun h => hxy h.1⟩)⟩
  have hmono : outW D (V \ S) a x ≤ outW (parentTransferGraph q D V S y) (V \ S) a x := by
    rw [outW_eq_mass, outW_eq_mass]
    exact mass_mono hkeep (fun z hz => ha z (mem_sdiff.mp (outN_subset hz)).1)
  have hgain : outW D S a x ≤
      if parentTransferGraph q D V S y x y = true then mass S a else 0 := by
    by_cases hparent : ∃ s ∈ S, D x s = true
    · have he : parentTransferGraph q D V S y x y = true :=
        decide_eq_true ⟨hx, hyK, Or.inr ⟨rfl, hparent⟩⟩
      rw [if_pos he, outW_eq_mass]
      exact mass_mono outN_subset (fun s hs => ha s (hSV hs))
    · have hzero : outW D S a x = 0 := by
        apply sum_eq_zero
        intro s hs
        have hn : ¬ D x s = true := fun h => hparent ⟨s, hs, h⟩
        simp [hn]
      rw [hzero]
      split_ifs <;> linarith
  rw [row, row, outW_split hSV, outW_addWeightAt hyK]
  simp only [addWeightAt, if_neg hxy, add_zero]
  have hqQ : (0 : ℚ) ≤ q := Nat.cast_nonneg q
  nlinarith

theorem addWeightAt_nonneg {V : Finset ℕ} {a : ℕ → ℚ} {A : ℚ}
    (ha : ∀ x ∈ V, 0 ≤ a x) (hA : 0 ≤ A) (y : ℕ) :
    ∀ x ∈ V, 0 ≤ addWeightAt a y A x := by
  intro x hx
  unfold addWeightAt
  split_ifs <;> linarith [ha x hx]

theorem firstHeadBank_bound_of_child_witness {q : ℕ} (hq : 2 ≤ q)
    {D : CH.Digraph} {V S : Finset ℕ} {y : ℕ} (hf : QFree D V q)
    (hy : y ∈ V) (hS : S ⊆ inN D V y)
    (a : ℕ → ℚ) (ha : ∀ t ∈ V, 0 ≤ a t) (c : ℚ)
    (hc : mass V a < c) (hr : ∀ x ∈ V, c ≤ row q D V a x)
    (hwitness : ∃ x ∈ V \ S,
      row q (parentTransferGraph q D V S y) (V \ S) (addWeightAt a y (mass S a)) x ≤
        mass (V \ S) (addWeightAt a y (mass S a))) :
    mass S a + c - mass V a ≤ q * mass (firstHeadBank q D V S y) a := by
  by_contra hn
  obtain ⟨x, hx, hrow⟩ := hwitness
  rw [parentTransfer_mass (by omega : 1 ≤ q) hf hy hS a] at hrow
  by_cases hxy : x = y
  · subst x
    rw [parentTransfer_receiver_row hq hf hy hS a] at hrow
    linarith [hr y hy]
  · have h := parentTransfer_other_row (by omega : 1 ≤ q) hf hy hS a ha hx hxy
    have hh := hr x (mem_sdiff.mp hx).1
    linarith

theorem parentTransfer_card_lt {V S : Finset ℕ} (hSV : S ⊆ V) (hS : S.Nonempty) :
    (V \ S).card < V.card := by
  apply card_lt_card
  apply ssubset_iff_subset_ne.mpr
  refine ⟨sdiff_subset, ?_⟩
  intro he
  obtain ⟨s, hs⟩ := hS
  have hsK := he.symm ▸ hSV hs
  exact (mem_sdiff.mp hsK).2 hs

/-- Strict lower rows need only the usual all-smaller SmallRow induction. -/
theorem common_parent_bank_bound_strict {q : ℕ} (hq : 2 ≤ q)
    {D : CH.Digraph} {V S : Finset ℕ} {y : ℕ} (hf : QFree D V q)
    (hsmall : SmallerSmallRow q V.card) (hy : y ∈ V)
    (hS : S ⊆ inN D V y) (hSne : S.Nonempty)
    (a : ℕ → ℚ) (ha : ∀ t ∈ V, 0 ≤ a t) (c : ℚ)
    (hc : mass V a < c) (hr : ∀ x ∈ V, c ≤ row q D V a x) :
    mass S a + c - mass V a ≤ q * mass (firstHeadBank q D V S y) a := by
  have hSV : S ⊆ V := fun s hs => (mem_inN.mp (hS hs)).1
  have hA := mass_nonneg (fun s hs => ha s (hSV hs))
  have hchild := hsmall _ _ (parentTransfer_card_lt hSV hSne)
    (parentTransferGraph_qfree hq hf hy hS)
  apply firstHeadBank_bound_of_child_witness hq hf hy hS a ha c hc hr
  exact hchild _ (fun x hx => addWeightAt_nonneg ha hA y x (mem_sdiff.mp hx).1)
    ⟨y, common_parent_receiver_retained (by omega : 1 ≤ q) hf hy hS⟩

/-- Self-duality is required only on the actual smaller edited child. -/
theorem firstHeadBank_bound_of_child_selfDual {q : ℕ} (hq : 2 ≤ q)
    {D : CH.Digraph} {V S : Finset ℕ} {y : ℕ} (hf : QFree D V q)
    (hy : y ∈ V) (hS : S ⊆ inN D V y)
    (hchild : SelfDual q (parentTransferGraph q D V S y) (V \ S))
    (a : ℕ → ℚ) (ha : ∀ t ∈ V, 0 ≤ a t) (c : ℚ)
    (hc : mass V a ≤ c) (hr : ∀ x ∈ V, c ≤ row q D V a x) :
    mass S a + c - mass V a ≤ q * mass (firstHeadBank q D V S y) a := by
  have hSV : S ⊆ V := fun s hs => (mem_inN.mp (hS hs)).1
  have hA := mass_nonneg (fun s hs => ha s (hSV hs))
  have hyK := common_parent_receiver_retained (by omega : 1 ≤ q) hf hy hS
  have hn : ∀ x ∈ V \ S, 0 ≤ addWeightAt a y (mass S a) x :=
    fun x hx => addWeightAt_nonneg ha hA y x (mem_sdiff.mp hx).1
  rcases lt_or_eq_of_le hc with hlt | he
  · exact firstHeadBank_bound_of_child_witness hq hf hy hS a ha c hlt hr
      (exists_small_row hchild ⟨y, hyK⟩ _ hn)
  · by_contra hbad
    have hm := parentTransfer_mass (by omega : 1 ≤ q) hf hy hS a
    have hB : 0 ≤ mass (firstHeadBank q D V S y) a :=
      mass_nonneg (fun h hh => ha h (mem_firstHeadBank.mp hh).1)
    have hqQ : (0 : ℚ) ≤ q := Nat.cast_nonneg q
    have hApos : 0 < mass S a := by nlinarith
    have hyp : 0 < addWeightAt a y (mass S a) y := by
      simp only [addWeightAt, ite_true]
      linarith [ha y hy]
    have hfeasible : ∀ x ∈ V \ S,
        mass (V \ S) (addWeightAt a y (mass S a)) ≤
          row q (parentTransferGraph q D V S y) (V \ S) (addWeightAt a y (mass S a)) x := by
      intro x hx
      rw [hm]
      by_cases hxy : x = y
      · subst x
        rw [parentTransfer_receiver_row hq hf hy hS a]
        linarith [hr y hy]
      · exact (hc.trans (hr x (mem_sdiff.mp hx).1)).trans
          (parentTransfer_other_row (by omega : 1 ≤ q) hf hy hS a ha hx hxy)
    have ht := positive_row_eq hchild hn hfeasible hyK hyp
    rw [hm, parentTransfer_receiver_row hq hf hy hS a] at ht
    linarith [hr y hy]

/-- Entire all-smaller-graphs induction, including edited children. -/
def SmallerSelfDual (q n : ℕ) : Prop :=
  ∀ (E : CH.Digraph) (U : Finset ℕ), U.card < n → QFree E U q → SelfDual q E U

theorem SmallerSelfDual.smallRow {q n : ℕ} (h : SmallerSelfDual q n) : SmallerSmallRow q n :=
  fun E U hlt hf => smallRow_of_selfDual (h E U hlt hf)

theorem SmallerSelfDual.induced {q : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (h : SmallerSelfDual q V.card) (hf : QFree D V q) :
    ∀ U ⊆ V, U ≠ V → SelfDual q D U := by
  intro U hUV hne
  exact h D U (card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hUV, hne⟩)) (hf.mono_set hUV)

theorem SmallerSelfDual.reverse_induced {q : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (h : SmallerSelfDual q V.card) (hf : QFree D V q) :
    ∀ U ⊆ V, U ≠ V → SelfDual q (fun a b => D b a) U := h.induced hf.reverse

theorem common_parent_bank_bound_feasible {q : ℕ} (hq : 2 ≤ q)
    {D : CH.Digraph} {V S : Finset ℕ} {y : ℕ} (hf : QFree D V q)
    (hsmall : SmallerSelfDual q V.card) (hy : y ∈ V)
    (hS : S ⊆ inN D V y) (hSne : S.Nonempty)
    (a : ℕ → ℚ) (ha : ∀ t ∈ V, 0 ≤ a t) (c : ℚ)
    (hc : mass V a ≤ c) (hr : ∀ x ∈ V, c ≤ row q D V a x) :
    mass S a + c - mass V a ≤ q * mass (firstHeadBank q D V S y) a :=
  firstHeadBank_bound_of_child_selfDual hq hf hy hS
    (hsmall _ _ (parentTransfer_card_lt (fun s hs => (mem_inN.mp (hS hs)).1) hSne)
      (parentTransferGraph_qfree hq hf hy hS)) a ha c hc hr

theorem firstHeadBank_subset_outside_common {q : ℕ} (hq : 1 ≤ q)
    {D : CH.Digraph} {V S C : Finset ℕ} {y : ℕ} (hf : QFree D V q)
    (hC : ∀ h ∈ C, ∀ s ∈ S, D s h = true) :
    firstHeadBank q D V S y ⊆ outN D V y \ C := by
  intro h hh
  refine mem_sdiff.mpr ⟨mem_outN.mpr ⟨(mem_firstHeadBank.mp hh).1,
    (mem_firstHeadBank.mp hh).2.1⟩, ?_⟩
  exact fun hhC => firstHeadBank_avoids_common_heads hq hf hh (hC h hhC)

theorem common_parent_outside_common_bound {q : ℕ} (hq : 2 ≤ q)
    {D : CH.Digraph} {V S C : Finset ℕ} {y : ℕ} (hf : QFree D V q)
    (hsmall : SmallerSelfDual q V.card) (hy : y ∈ V)
    (hS : S ⊆ inN D V y) (hSne : S.Nonempty)
    (a : ℕ → ℚ) (ha : ∀ t ∈ V, 0 ≤ a t) (c : ℚ)
    (hc : mass V a ≤ c) (hr : ∀ x ∈ V, c ≤ row q D V a x)
    (hC : ∀ h ∈ C, ∀ s ∈ S, D s h = true) :
    mass S a + c - mass V a ≤ q * mass (outN D V y \ C) a := by
  have hb := common_parent_bank_bound_feasible hq hf hsmall hy hS hSne a ha c hc hr
  have hm := mass_mono (firstHeadBank_subset_outside_common (y := y) (by omega : 1 ≤ q) hf hC)
    (fun x hx => ha x (outN_subset (mem_sdiff.mp hx).1))
  exact hb.trans (mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg q))

theorem arc_return_of_strict_rows {q : ℕ} (hq : 2 ≤ q)
    {D : CH.Digraph} {V : Finset ℕ} {s y : ℕ} (hf : QFree D V q)
    (hsmall : SmallerSmallRow q V.card) (hs : s ∈ V) (hy : y ∈ V) (hsy : D s y = true)
    (a : ℕ → ℚ) (ha : ∀ t ∈ V, 0 ≤ a t) (c : ℚ)
    (hc : mass V a < c) (hr : ∀ x ∈ V, c ≤ row q D V a x) : Walk D V y s q := by
  have hb := common_parent_bank_bound_strict hq hf hsmall hy
    (singleton_subset_iff.mpr (mem_inN.mpr ⟨hs, hsy⟩)) (singleton_nonempty s) a ha c hc hr
  have hn : (firstHeadBank q D V {s} y).Nonempty := by
    by_contra hn
    rw [not_nonempty_iff_eq_empty.mp hn] at hb
    simp only [mass, sum_empty, sum_singleton, mul_zero] at hb
    change a s + c - mass V a ≤ 0 at hb
    linarith [ha s hs]
  obtain ⟨h, hh⟩ := hn
  obtain ⟨hhV, hyh, t, ht, path⟩ := mem_firstHeadBank.mp hh
  have ht' := mem_singleton.mp ht
  subst t
  have w : Walk D V y s ((q - 1) + 1) := .step hhV hyh path
  simpa only [Nat.sub_add_cancel (by omega : 1 ≤ q)] using w

theorem arc_return_of_feasible_rows {q : ℕ} (hq : 2 ≤ q)
    {D : CH.Digraph} {V : Finset ℕ} {s y : ℕ} (hf : QFree D V q)
    (hsmall : SmallerSelfDual q V.card) (hs : s ∈ V) (hy : y ∈ V) (hsy : D s y = true)
    (a : ℕ → ℚ) (ha : ∀ t ∈ V, 0 ≤ a t) (hapos : 0 < a s) (c : ℚ)
    (hc : mass V a ≤ c) (hr : ∀ x ∈ V, c ≤ row q D V a x) : Walk D V y s q := by
  have hb := common_parent_bank_bound_feasible hq hf hsmall hy
    (singleton_subset_iff.mpr (mem_inN.mpr ⟨hs, hsy⟩)) (singleton_nonempty s) a ha c hc hr
  have hn : (firstHeadBank q D V {s} y).Nonempty := by
    by_contra hn
    rw [not_nonempty_iff_eq_empty.mp hn] at hb
    simp only [mass, sum_empty, sum_singleton, mul_zero] at hb
    change a s + c - mass V a ≤ 0 at hb
    linarith
  obtain ⟨h, hh⟩ := hn
  obtain ⟨hhV, hyh, t, ht, path⟩ := mem_firstHeadBank.mp hh
  have ht' := mem_singleton.mp ht
  subst t
  have w : Walk D V y s ((q - 1) + 1) := .step hhV hyh path
  simpa only [Nat.sub_add_cancel (by omega : 1 ≤ q)] using w

end LeanCH.BR.WeightedSD
