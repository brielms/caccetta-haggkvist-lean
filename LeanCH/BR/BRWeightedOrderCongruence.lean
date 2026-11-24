import LeanCH.BR.BRWeightedOrderArithmetic
import LeanCH.BR.BRWeightedPositiveParentTransfer

/-! Arithmetic concerns any natural q and signed tight weights. Feasibility
consumers use q>=2 and actual SmallRow. Only positive support is counted when
zero weights are present; a nonzero total excludes the empty-support case. -/
namespace LeanCH.BR.WeightedSD
open Finset BRq2 BRq3 BR45 BRsub WeightedArithmetic

theorem normalized_rows_card_mod (q : ℕ) (D : CH.Digraph) (V : Finset ℕ)
    (a : ℕ → ℚ) (hm : mass V a = 1) (hr : ∀ x ∈ V, row q D V a x = 1) :
    (V.card : ZMod q) = 1 := by
  have h := WeightedOrderArithmetic.card_mod q (adjacencyMatrix D V) (fun i : V => a i)
    (fun i => by
      have hi := matrix_row q D V a i
      rw [rational_mulVec_apply] at hi
      exact hi.trans (hr i i.property))
    (by rw [Finset.sum_coe_sort]; exact hm)
  simpa only [Fintype.card_coe] using h

theorem tight_rows_card_mod (q : ℕ) (D : CH.Digraph) (V : Finset ℕ)
    (a : ℕ → ℚ) (hm : mass V a ≠ 0)
    (hr : ∀ x ∈ V, row q D V a x = mass V a) : (V.card : ZMod q) = 1 := by
  apply normalized_rows_card_mod q D V (fun z => a z / mass V a)
  · rw [mass_div]; exact div_self hm
  · intro x hx; rw [row_div, hr x hx]; exact div_self hm

theorem positive_feasible_card_mod {q : ℕ} (hq : 2 ≤ q) {D : CH.Digraph} {V : Finset ℕ}
    (hsmall : SmallRow q D V) (a : ℕ → ℚ) (ha : ∀ x ∈ V, 0 < a x)
    (hne : V.Nonempty) (hr : ∀ x ∈ V, mass V a ≤ row q D V a x) :
    (V.card : ZMod q) = 1 := by
  have hm : 0 < mass V a := sum_pos' (fun z hz => (ha z hz).le)
    (hne.imp (fun z hz => ⟨hz, ha z hz⟩))
  exact tight_rows_card_mod q D V a (ne_of_gt hm)
    (positive_feasible_rows_tight_of_smallRow hq hsmall a ha hr)

/-- Only positive-coordinate feasibility is needed in the support master. -/
theorem positive_support_feasible_card_mod {q : ℕ} (hq : 2 ≤ q)
    {D : CH.Digraph} {V : Finset ℕ} (a : ℕ → ℚ) (ha : ∀ x ∈ V, 0 ≤ a x)
    (hm : mass V a ≠ 0) (hsmall : SmallRow q D (V.filter (fun x => 0 < a x)))
    (hr : ∀ x ∈ V, 0 < a x → mass V a ≤ row q D V a x) :
    ((V.filter (fun x => 0 < a x)).card : ZMod q) = 1 := by
  let F := V.filter (fun x => 0 < a x)
  have hFV : F ⊆ V := filter_subset _ _
  have hz : ∀ x ∈ V, x ∉ F → a x = 0 := by
    intro x hx hn
    exact le_antisymm (le_of_not_gt (fun hp => hn (mem_filter.mpr ⟨hx,hp⟩))) (ha x hx)
  have hmass : mass F a = mass V a := mass_subset_zero hFV hz
  have hne : F.Nonempty := by
    apply nonempty_iff_ne_empty.mpr
    intro he
    apply hm
    rw [← hmass, he]
    simp [mass]
  apply positive_feasible_card_mod hq hsmall a (fun x hx => (mem_filter.mp hx).2) hne
  intro x hx
  rw [hmass, row, outW_subset_zero hFV hz]
  exact hr x (hFV hx) (mem_filter.mp hx).2

theorem SmallerSmallRow.positive_child_card_mod {q n : ℕ} (hq : 2 ≤ q)
    (hsmall : SmallerSmallRow q n) {E : CH.Digraph} {U : Finset ℕ}
    (hcard : U.card < n) (hf : QFree E U q) (b : ℕ → ℚ)
    (hb : ∀ x ∈ U, 0 < b x) (hne : U.Nonempty)
    (hr : ∀ x ∈ U, mass U b ≤ row q E U b x) : (U.card : ZMod q) = 1 :=
  positive_feasible_card_mod hq (hsmall E U hcard hf) b hb hne hr

theorem SmallerSmallRow.positive_support_child_card_mod {q n : ℕ} (hq : 2 ≤ q)
    (hsmall : SmallerSmallRow q n) {E : CH.Digraph} {U : Finset ℕ}
    (hcard : U.card < n) (hf : QFree E U q) (b : ℕ → ℚ)
    (hb : ∀ x ∈ U, 0 ≤ b x) (hm : mass U b ≠ 0)
    (hr : ∀ x ∈ U, 0 < b x → mass U b ≤ row q E U b x) :
    ((U.filter (fun x => 0 < b x)).card : ZMod q) = 1 :=
  positive_support_feasible_card_mod hq b hb hm
    (hsmall E _ ((card_le_card (filter_subset _ _)).trans_lt hcard) (hf.mono_set (filter_subset _ _))) hr

theorem SmallerSmallRow.no_positive_child_of_order {q n : ℕ} (hq : 2 ≤ q)
    (hsmall : SmallerSmallRow q n) {E : CH.Digraph} {U : Finset ℕ}
    (hcard : U.card < n) (hf : QFree E U q) (hmod : (U.card : ZMod q) ≠ 1)
    (b : ℕ → ℚ) (hb : ∀ x ∈ U, 0 < b x) (hne : U.Nonempty)
    (hr : ∀ x ∈ U, mass U b ≤ row q E U b x) : False :=
  hmod (hsmall.positive_child_card_mod hq hcard hf b hb hne hr)

end LeanCH.BR.WeightedSD
