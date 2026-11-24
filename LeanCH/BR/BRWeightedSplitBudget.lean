import LeanCH.BR.BRWeightedSplitTransfer

/-! Exact actual-child consumers; no favorable cut or transfer is supplied. -/
namespace LeanCH.BR.WeightedSD
open Finset BRq2 BRq3 BR45 BRsub

noncomputable def splitGain (q : ℕ) (D : CH.Digraph) (V : Finset ℕ) (v : ℕ)
    (C : Finset (ℕ × ℕ)) (a α : ℕ → ℚ) (x : ℕ) : ℚ :=
  if x ∈ inN D V v then
    q * mass (splitNew q D V v C x) a - q * mass (splitBlocked q D V v C x) α
  else α x + q * mass (outN D V x ∩ outN D V v) α - q * mass (cutHeads V C x) a

theorem splitTransfer_row {q : ℕ} (hq : 2 ≤ q) {D : CH.Digraph}
    {V : Finset ℕ} {v : ℕ} (hf : QFree D V q) (hv : v ∈ V)
    {C : Finset (ℕ × ℕ)} (hC : RootCuts D V v C)
    (a α : ℕ → ℚ) (hs : ∀ z ∈ V, z ∉ outN D V v → α z = 0)
    (hm : mass (outN D V v) α = a v) {x : ℕ} (hx : x ∈ V.erase v) :
    row q (splitTransferGraph q D V v C) (V.erase v) (fun z => a z + α z) x =
      row q D V a x + splitGain q D V v C a α x := by
  by_cases hp : x ∈ inN D V v
  · rw [splitGain, if_pos hp, splitTransfer_parent_row hq hf hv hC hp a α hs hm]
    ring
  · rw [splitGain, if_neg hp, splitTransfer_other_row hC hx hp a α hs]
    ring

/-- The exact budgets cannot all produce strict rows on a nonempty child. -/
theorem split_budget_obstruction {q : ℕ} (hq : 2 ≤ q) {D : CH.Digraph}
    {V : Finset ℕ} {v : ℕ} (hf : QFree D V q) (hv : v ∈ V)
    (hsmall : SmallerSmallRow q V.card) {C : Finset (ℕ × ℕ)}
    (hC : RootCuts D V v C) (a α : ℕ → ℚ)
    (hs : ∀ z ∈ V, z ∉ outN D V v → α z = 0)
    (hm : mass (outN D V v) α = a v)
    (hnn : ∀ x ∈ V.erase v, 0 ≤ a x + α x) (hK : (V.erase v).Nonempty) :
    ∃ x ∈ V.erase v, row q D V a x + splitGain q D V v C a α x ≤ mass V a := by
  have hchild := hsmall _ _ (card_erase_lt_of_mem hv)
    (splitTransferGraph_qfree (by omega : 1 ≤ q) hf hv C)
  obtain ⟨x, hx, hr⟩ := hchild (fun z => a z + α z) hnn hK
  rw [splitTransfer_mass (by omega : 1 ≤ q) hf hv a α hs hm,
    splitTransfer_row hq hf hv hC a α hs hm hx] at hr
  exact ⟨x, hx, hr⟩

theorem split_strict_budgets_impossible {q : ℕ} (hq : 2 ≤ q) {D : CH.Digraph}
    {V : Finset ℕ} {v : ℕ} (hf : QFree D V q) (hv : v ∈ V)
    (hsmall : SmallerSmallRow q V.card) {C : Finset (ℕ × ℕ)}
    (hC : RootCuts D V v C) (a α : ℕ → ℚ)
    (hs : ∀ z ∈ V, z ∉ outN D V v → α z = 0)
    (hm : mass (outN D V v) α = a v)
    (hnn : ∀ x ∈ V.erase v, 0 ≤ a x + α x) (hK : (V.erase v).Nonempty)
    (hbudget : ∀ x ∈ V.erase v,
      mass V a < row q D V a x + splitGain q D V v C a α x) : False := by
  obtain ⟨x, hx, hle⟩ := split_budget_obstruction hq hf hv hsmall hC a α hs hm hnn hK
  exact (not_lt_of_ge hle) (hbudget x hx)

/-- Explicit corrected budgets under any common lower row value c. -/
theorem split_uniform_strict_budgets_impossible {q : ℕ} (hq : 2 ≤ q) {D : CH.Digraph}
    {V : Finset ℕ} {v : ℕ} (hf : QFree D V q) (hv : v ∈ V)
    (hsmall : SmallerSmallRow q V.card) {C : Finset (ℕ × ℕ)}
    (hC : RootCuts D V v C) (a α : ℕ → ℚ)
    (hs : ∀ z ∈ V, z ∉ outN D V v → α z = 0)
    (hm : mass (outN D V v) α = a v)
    (hnn : ∀ x ∈ V.erase v, 0 ≤ a x + α x) (hK : (V.erase v).Nonempty)
    (c : ℚ) (hr : ∀ x ∈ V.erase v, c ≤ row q D V a x)
    (hparents : ∀ x ∈ inN D V v, q * mass (splitBlocked q D V v C x) α <
      c - mass V a + q * mass (splitNew q D V v C x) a)
    (hothers : ∀ x ∈ V.erase v, x ∉ inN D V v → q * mass (cutHeads V C x) a <
      c - mass V a + α x + q * mass (outN D V x ∩ outN D V v) α) : False := by
  apply split_strict_budgets_impossible hq hf hv hsmall hC a α hs hm hnn hK
  intro x hx
  have hrow := hr x hx
  by_cases hp : x ∈ inN D V v
  · rw [splitGain, if_pos hp]
    linarith [hparents x hp]
  · rw [splitGain, if_neg hp]
    linarith [hothers x hx hp]

/-- At every positive child coordinate, feasibility forces equality. The
smaller SmallRow premise is applied to the actual child's positive support. -/
theorem split_feasible_positive_tight {q : ℕ} (hq : 2 ≤ q) {D : CH.Digraph}
    {V : Finset ℕ} {v : ℕ} (hf : QFree D V q) (hv : v ∈ V)
    (hsmall : SmallerSmallRow q V.card) {C : Finset (ℕ × ℕ)}
    (hC : RootCuts D V v C) (a α : ℕ → ℚ)
    (hs : ∀ z ∈ V, z ∉ outN D V v → α z = 0)
    (hm : mass (outN D V v) α = a v)
    (hnn : ∀ x ∈ V.erase v, 0 ≤ a x + α x)
    (hbudget : ∀ x ∈ V.erase v,
      mass V a ≤ row q D V a x + splitGain q D V v C a α x)
    {x : ℕ} (hx : x ∈ V.erase v) (hp : 0 < a x + α x) :
    row q D V a x + splitGain q D V v C a α x = mass V a := by
  have hfree := splitTransferGraph_qfree (by omega : 1 ≤ q) hf hv C
  have hsup : SmallRow q (splitTransferGraph q D V v C)
      ((V.erase v).filter (fun x => 0 < a x + α x)) :=
    hsmall _ _ ((card_le_card (filter_subset _ _)).trans_lt (card_erase_lt_of_mem hv))
      (hfree.mono_set (filter_subset _ _))
  have hrows : ∀ z ∈ V.erase v,
      mass (V.erase v) (fun t => a t + α t) ≤
        row q (splitTransferGraph q D V v C) (V.erase v) (fun t => a t + α t) z := by
    intro z hz
    rw [splitTransfer_mass (by omega : 1 ≤ q) hf hv a α hs hm,
      splitTransfer_row hq hf hv hC a α hs hm hz]
    exact hbudget z hz
  have he := positive_coordinate_tight_of_support_smallRow hq
    (fun t => a t + α t) hnn hsup hrows hx hp
  rwa [splitTransfer_mass (by omega : 1 ≤ q) hf hv a α hs hm,
    splitTransfer_row hq hf hv hC a α hs hm hx] at he

theorem split_semistrict_budgets_impossible {q : ℕ} (hq : 2 ≤ q) {D : CH.Digraph}
    {V : Finset ℕ} {v : ℕ} (hf : QFree D V q) (hv : v ∈ V)
    (hsmall : SmallerSmallRow q V.card) {C : Finset (ℕ × ℕ)}
    (hC : RootCuts D V v C) (a α : ℕ → ℚ)
    (hs : ∀ z ∈ V, z ∉ outN D V v → α z = 0)
    (hm : mass (outN D V v) α = a v)
    (hnn : ∀ x ∈ V.erase v, 0 ≤ a x + α x)
    (hbudget : ∀ x ∈ V.erase v,
      mass V a ≤ row q D V a x + splitGain q D V v C a α x)
    (hstrict : ∃ x ∈ V.erase v, 0 < a x + α x ∧
      mass V a < row q D V a x + splitGain q D V v C a α x) : False := by
  obtain ⟨x, hx, hp, hr⟩ := hstrict
  have he := split_feasible_positive_tight hq hf hv hsmall hC a α hs hm hnn hbudget hx hp
  linarith

/-- Concrete unresolved choice of a physical cut set and a redistribution.
This definition is an obligation, not an existence assertion. -/
def StrictSplitChoice (q : ℕ) (D : CH.Digraph) (V : Finset ℕ) (a : ℕ → ℚ) : Prop :=
  ∃ v ∈ V, ∃ C : Finset (ℕ × ℕ), ∃ α : ℕ → ℚ,
    RootCuts D V v C ∧ (∀ x ∈ V, 0 ≤ α x) ∧
    (∀ x ∈ V, x ∉ outN D V v → α x = 0) ∧ mass (outN D V v) α = a v ∧
    (V.erase v).Nonempty ∧ ∀ x ∈ V.erase v,
      mass V a < row q D V a x + splitGain q D V v C a α x

theorem no_strictSplitChoice {q : ℕ} (hq : 2 ≤ q) {D : CH.Digraph}
    {V : Finset ℕ} (hf : QFree D V q) (hsmall : SmallerSmallRow q V.card)
    (a : ℕ → ℚ) (ha : ∀ x ∈ V, 0 ≤ a x) : ¬ StrictSplitChoice q D V a := by
  rintro ⟨v, hv, C, α, hC, hα, hs, hm, hK, hb⟩
  exact split_strict_budgets_impossible hq hf hv hsmall hC a α hs hm
    (fun x hx => add_nonneg (ha x (mem_erase.mp hx).2) (hα x (mem_erase.mp hx).2)) hK hb

end LeanCH.BR.WeightedSD
