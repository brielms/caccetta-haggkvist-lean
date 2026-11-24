import LeanCH.BR.BRWeightedArbitraryFold

/-! Strict feasible fold costs without column weights. Positivity can be
restricted to the receiver and positive removed mass by support restriction. -/
namespace LeanCH.BR.WeightedSD
open Finset BRq2 BRq3 BR45 BRsub

/-- Nonnegative feasibility already gives the weak bank bound under smaller
SmallRow; a failed bound makes the transferred receiver positive and strict. -/
theorem fold_bank_bound_feasible {q : ℕ} (hq : 2 ≤ q)
    {D : CH.Digraph} {V S : Finset ℕ} {y : ℕ} (hf : QFree D V q)
    (hsmall : SmallerSmallRow q V.card) (hSV : S ⊆ V) (hy : y ∈ V \ S)
    (hno : ∀ s ∈ S, ¬ D y s = true) (a : ℕ → ℚ) (ha : ∀ x ∈ V, 0 ≤ a x)
    (hr : ∀ x ∈ V, mass V a ≤ row q D V a x) :
    mass S a ≤ q * mass (foldBank q D V S y) a := by
  by_contra hn
  have hq1 : 1 ≤ q := by omega
  have hBnn : 0 ≤ mass (foldBank q D V S y) a :=
    mass_nonneg (fun z hz => ha z (outN_subset (foldBank_subset_out hz)))
  have hA : 0 < mass S a := by
    have hqQ : (0 : ℚ) ≤ q := Nat.cast_nonneg q
    nlinarith
  have hSne : S.Nonempty := by
    by_contra he
    have heq := not_nonempty_iff_eq_empty.mp he
    simp [heq, mass] at hA
  have hfree := reachFold_qfree hf hSV hno
  have hnn : ∀ x ∈ V \ S, 0 ≤ addWeightAt a y (mass S a) x :=
    fun x hx => addWeightAt_nonneg ha hA.le y x (mem_sdiff.mp hx).1
  have hfeas := fold_feasible_of_budget (q := q) (B := foldBank q D V S y)
    hSV hy hno (loopfree hf hq1 (mem_sdiff.mp hy).1) foldBank_subset_out
    a ha (mass V a) le_rfl hr (by linarith)
  have hsup : SmallRow q (reachFold q D V S y)
      ((V \ S).filter (fun x => 0 < addWeightAt a y (mass S a) x)) :=
    hsmall _ _ ((card_le_card (filter_subset _ _)).trans_lt (parentTransfer_card_lt hSV hSne))
      (hfree.mono_set (filter_subset _ _))
  have hyp : 0 < addWeightAt a y (mass S a) y := by
    simp only [addWeightAt, ite_true]
    linarith [ha y (mem_sdiff.mp hy).1]
  have he := positive_coordinate_tight_of_support_smallRow hq _ hnn hsup hfeas hy hyp
  rw [fold_weight_mass hSV hy a] at he
  change row q (foldGraph D V S (foldBank q D V S y) y) (V \ S)
    (addWeightAt a y (mass S a)) y = mass V a at he
  rw [fold_receiver_row hy hno (loopfree hf hq1 (mem_sdiff.mp hy).1) foldBank_subset_out a] at he
  linarith [hr y (mem_sdiff.mp hy).1]

theorem fold_bank_strict_of_positive_retained {q : ℕ} (hq : 2 ≤ q)
    {D : CH.Digraph} {V S : Finset ℕ} {y : ℕ} (hf : QFree D V q)
    (hsmall : SmallerSmallRow q V.card) (hSV : S ⊆ V) (hy : y ∈ V \ S)
    (hno : ∀ s ∈ S, ¬ D y s = true) (a : ℕ → ℚ) (ha : ∀ x ∈ V, 0 ≤ a x)
    (hpos : ∀ x ∈ V \ S, 0 < a x) (hA : 0 < mass S a)
    (hr : ∀ x ∈ V, mass V a ≤ row q D V a x) :
    mass S a < q * mass (foldBank q D V S y) a := by
  by_contra hn
  have hq1 : 1 ≤ q := by omega
  have hSne : S.Nonempty := by
    by_contra he
    have heq := not_nonempty_iff_eq_empty.mp he
    simp [heq, mass] at hA
  have hfree := reachFold_qfree hf hSV hno
  have hchild := hsmall _ _ (parentTransfer_card_lt hSV hSne) hfree
  have hloopy := loopfree hf hq1 (mem_sdiff.mp hy).1
  have hfeas := fold_feasible_of_budget (B := foldBank q D V S y) hSV hy hno hloopy foldBank_subset_out
    a ha (mass V a) le_rfl hr (by linarith)
  have ht := positive_feasible_rows_tight_of_smallRow hq hchild _
    (parentTransfer_positive hSV ha hpos) hfeas
  have htight : ∀ x ∈ V \ S, row q (reachFold q D V S y) (V \ S)
      (addWeightAt a y (mass S a)) x = mass V a := by
    intro x hx
    exact (ht x hx).trans (fold_weight_mass hSV hy a)
  have hparents : ∀ x ∈ V \ S, (∃ s ∈ S, D x s = true) → D x y = true := by
    intro x hx hp
    by_contra hxy
    have hxne : x ≠ y := by
      intro he; subst x
      obtain ⟨s, hs, he⟩ := hp
      exact hno s hs he
    have hg := fold_new_parent_gain (q := q) (B := foldBank q D V S y) hSV hy a ha hx hxne hp hxy
    change row q D V a x + q * a y ≤ row q (reachFold q D V S y) (V \ S)
      (addWeightAt a y (mass S a)) x at hg
    rw [htight x hx] at hg
    have hqQ : (0 : ℚ) < q := by exact_mod_cast (by omega : 0 < q)
    nlinarith [hr x (mem_sdiff.mp hx).1, hpos y hy]
  have hB := foldBank_empty_of_parents_head_receiver hq1 hf hy hparents
  have he := htight y hy
  change row q (foldGraph D V S (foldBank q D V S y) y) (V \ S)
    (addWeightAt a y (mass S a)) y = mass V a at he
  rw [fold_receiver_row hy hno hloopy foldBank_subset_out a, hB] at he
  simp only [mass, sum_empty, mul_zero, sub_zero] at he
  change row q D V a y + mass S a = mass V a at he
  linarith [hr y (mem_sdiff.mp hy).1]

/-- Only the receiver weight and the total deleted mass must be positive.
All other source weights may vanish. -/
theorem fold_bank_strict_of_positive_receiver {q : ℕ} (hq : 2 ≤ q)
    {D : CH.Digraph} {V S : Finset ℕ} {y : ℕ} (hf : QFree D V q)
    (hsmall : SmallerSmallRow q V.card) (hSV : S ⊆ V) (hy : y ∈ V \ S)
    (hno : ∀ s ∈ S, ¬ D y s = true) (a : ℕ → ℚ) (ha : ∀ x ∈ V, 0 ≤ a x)
    (hay : 0 < a y) (hA : 0 < mass S a)
    (hr : ∀ x ∈ V, mass V a ≤ row q D V a x) :
    mass S a < q * mass (foldBank q D V S y) a := by
  let U := V.filter (fun x => 0 < a x)
  have hUV : U ⊆ V := filter_subset _ _
  have hz : ∀ x ∈ V, x ∉ U → a x = 0 := by
    intro x hx hn
    have hnp : ¬ 0 < a x := fun hp => hn (mem_filter.mpr ⟨hx, hp⟩)
    exact le_antisymm (le_of_not_gt hnp) (ha x hx)
  have hUmass := mass_subset_zero hUV hz
  have hS0mass : mass (S ∩ U) a = mass S a := by
    apply mass_subset_zero inter_subset_left
    intro x hx hn
    exact hz x (hSV hx) (fun hu => hn (mem_inter.mpr ⟨hx, hu⟩))
  have hyU : y ∈ U \ (S ∩ U) := mem_sdiff.mpr
    ⟨mem_filter.mpr ⟨(mem_sdiff.mp hy).1, hay⟩, fun h => (mem_sdiff.mp hy).2 (mem_inter.mp h).1⟩
  have hsmallU : SmallerSmallRow q U.card := fun E K hlt hfree =>
    hsmall E K (hlt.trans_le (card_le_card hUV)) hfree
  have hrowsU : ∀ x ∈ U, mass U a ≤ row q D U a x := by
    intro x hx
    rw [hUmass, row, outW_subset_zero hUV hz]
    exact hr x (hUV hx)
  have hstrict := fold_bank_strict_of_positive_retained hq (hf.mono_set hUV) hsmallU
    inter_subset_right hyU (fun s hs => hno s (mem_inter.mp hs).1) a
    (fun x hx => ha x (hUV hx)) (fun x hx => (mem_filter.mp (mem_sdiff.mp hx).1).2)
    (by rwa [hS0mass]) hrowsU
  rw [hS0mass] at hstrict
  have hmono : mass (foldBank q D U (S ∩ U) y) a ≤ mass (foldBank q D V S y) a :=
    mass_mono (foldBank_mono hUV inter_subset_left)
      (fun z hz => ha z (outN_subset (foldBank_subset_out hz)))
  exact hstrict.trans_le (mul_le_mul_of_nonneg_left hmono (Nat.cast_nonneg q))

/-- Every source vertex reaches every positive coordinate within q, without
saturation or column weights. The starting weight may vanish. -/
theorem feasible_reach_positive_within {q : ℕ} (hq : 2 ≤ q)
    {D : CH.Digraph} {V : Finset ℕ} (hf : QFree D V q)
    (hsmall : SmallerSmallRow q V.card) (a : ℕ → ℚ) (ha : ∀ x ∈ V, 0 ≤ a x)
    (hr : ∀ x ∈ V, mass V a ≤ row q D V a x)
    {y v : ℕ} (hy : y ∈ V) (hv : v ∈ V) (hav : 0 < a v) :
    v ∈ ball D V y q := by
  by_contra hn
  have hyv : y ≠ v := by
    intro he; subst v
    exact hn (mem_ball.mpr ⟨hy, 0, by omega, .refl _⟩)
  have hno : ∀ s ∈ ({v} : Finset ℕ), ¬ D y s = true := by
    intro s hs he
    have hsv := mem_singleton.mp hs
    subst s
    exact hn (mem_ball.mpr ⟨hv, 1, by omega, .step hv he (.refl _)⟩)
  have hB : foldBank q D V {v} y = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro z hz
    obtain ⟨ho, s, hs, hball⟩ := mem_filter.mp hz
    have hsv := mem_singleton.mp hs
    subst s
    obtain ⟨_, k, hk, w⟩ := mem_ball.mp hball
    exact hn (mem_ball.mpr ⟨hv, k + 1, by omega,
      .step (outN_subset ho) (mem_outN.mp ho).2 w⟩)
  have hb := fold_bank_bound_feasible hq hf hsmall
    (singleton_subset_iff.mpr hv) (mem_sdiff.mpr ⟨hy, fun hs => hyv (mem_singleton.mp hs)⟩)
    hno a ha hr
  rw [hB] at hb
  have hb' : a v ≤ 0 := by simpa [mass] using hb
  linarith

theorem positive_feasible_diameter {q : ℕ} (hq : 2 ≤ q)
    {D : CH.Digraph} {V : Finset ℕ} (hf : QFree D V q)
    (hsmall : SmallerSmallRow q V.card) (a : ℕ → ℚ) (ha : ∀ x ∈ V, 0 < a x)
    (hr : ∀ x ∈ V, mass V a ≤ row q D V a x) :
    ∀ y ∈ V, ∀ v ∈ V, v ∈ ball D V y q := by
  intro y hy v hv
  exact feasible_reach_positive_within hq hf hsmall a (fun x hx => (ha x hx).le)
    hr hy hv (ha v hv)

end LeanCH.BR.WeightedSD
