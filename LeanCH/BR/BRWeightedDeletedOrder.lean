import LeanCH.BR.BRWeightedOrderCongruence
import LeanCH.BR.BRWeightedClosedSplit

/-! Actual positive edited children have restricted order. These consumers
do not assume a transfer, floor or surplus ordering. Split-budget wrappers
use only feasibility and retained positivity, allowing zero transfer. -/
namespace LeanCH.BR.WeightedSD
open Finset BRq2 BRq3 BR45 BRsub

theorem SmallerSmallRow.deleted_card_dvd {q : ℕ} (hq : 2 ≤ q)
    {V S : Finset ℕ} (hsmall : SmallerSmallRow q V.card) (hSV : S ⊆ V)
    (hSne : S.Nonempty) (hKne : (V \ S).Nonempty) (hmod : (V.card : ZMod q) = 1)
    (E : CH.Digraph) (hf : QFree E (V \ S) q) (b : ℕ → ℚ)
    (hb : ∀ x ∈ V \ S, 0 < b x)
    (hr : ∀ x ∈ V \ S, mass (V \ S) b ≤ row q E (V \ S) b x) : q ∣ S.card := by
  have hc := card_sdiff_add_card_eq_card hSV
  have hlt : (V \ S).card < V.card := by have hp := card_pos.mpr hSne; omega
  have hchild := hsmall.positive_child_card_mod hq hlt hf b hb hKne hr
  have he : ((V \ S).card : ZMod q) + (S.card : ZMod q) = (V.card : ZMod q) := by
    simpa only [Nat.cast_add] using congrArg (fun n : ℕ => (n : ZMod q)) hc
  rw [hchild, hmod] at he
  apply (ZMod.natCast_eq_zero_iff _ _).mp
  simpa only [add_eq_left] using he

theorem SmallerSmallRow.no_positive_deletion {q : ℕ} (hq : 2 ≤ q)
    {V S : Finset ℕ} (hsmall : SmallerSmallRow q V.card) (hSV : S ⊆ V)
    (hKne : (V \ S).Nonempty) (hmod : (V.card : ZMod q) = 1) (hnd : ¬ q ∣ S.card)
    (E : CH.Digraph) (hf : QFree E (V \ S) q) (b : ℕ → ℚ)
    (hb : ∀ x ∈ V \ S, 0 < b x)
    (hr : ∀ x ∈ V \ S, mass (V \ S) b ≤ row q E (V \ S) b x) : False := by
  have hSne : S.Nonempty := by
    apply nonempty_iff_ne_empty.mpr
    intro he; apply hnd; simp [he]
  exact hnd (hsmall.deleted_card_dvd hq hSV hSne hKne hmod E hf b hb hr)

theorem SmallerSmallRow.no_positive_boundary_deletion {q : ℕ} (hq : 2 ≤ q)
    {D : CH.Digraph} {V S : Finset ℕ} (hsmall : SmallerSmallRow q V.card)
    (a : ℕ → ℚ) (hm : mass V a ≠ 0) (hrows : ∀ x ∈ V, row q D V a x = mass V a)
    (hSV : S ⊆ V) (hKne : (V \ S).Nonempty) (hnd : ¬ q ∣ S.card)
    (E : CH.Digraph) (hf : QFree E (V \ S) q) (b : ℕ → ℚ)
    (hb : ∀ x ∈ V \ S, 0 < b x)
    (hr : ∀ x ∈ V \ S, mass (V \ S) b ≤ row q E (V \ S) b x) : False :=
  hsmall.no_positive_deletion hq hSV hKne (tight_rows_card_mod q D V a hm hrows)
    hnd E hf b hb hr

theorem SmallerSmallRow.erased_positive_child_order {q : ℕ} (hq : 2 ≤ q)
    {V : Finset ℕ} {v : ℕ} (hsmall : SmallerSmallRow q V.card) (hv : v ∈ V)
    (hKne : (V.erase v).Nonempty) (E : CH.Digraph) (hf : QFree E (V.erase v) q)
    (b : ℕ → ℚ) (hb : ∀ x ∈ V.erase v, 0 < b x)
    (hr : ∀ x ∈ V.erase v, mass (V.erase v) b ≤ row q E (V.erase v) b x) :
    (V.card : ZMod q) = 2 := by
  have hchild := hsmall.positive_child_card_mod hq (card_erase_lt_of_mem hv) hf b hb hKne hr
  have he : ((V.erase v).card : ZMod q) + 1 = (V.card : ZMod q) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      congrArg (fun n : ℕ => (n : ZMod q)) (card_erase_add_one hv)
  rw [hchild] at he
  simpa only [one_add_one_eq_two] using he.symm

/-- The deleted source row is irrelevant to exact child feasibility. -/
theorem split_closed_budgets_feasible_on_retained {q : ℕ} (hq : 2 ≤ q)
    {D : CH.Digraph} {V : Finset ℕ} {v : ℕ} {C : Finset (ℕ × ℕ)}
    (hf : QFree D V q) (hv : v ∈ V) (hC : RootCuts D V v C) (a α : ℕ → ℚ) (δ s : ℚ)
    (hs : ∀ z ∈ V, z ∉ outN D V v → α z = 0) (hm : mass (outN D V v) α = a v + s)
    (hr : ∀ x ∈ V.erase v, mass V a + δ ≤ row q D V a x)
    (hparents : ∀ x ∈ inN D V v, q * mass (splitBlocked q D V v C x) α ≤
      δ + ((q : ℚ) - 1) * s + q * mass (splitNew q D V v C x) a)
    (hothers : ∀ x ∈ V.erase v, x ∉ inN D V v → q * mass (cutHeads V C x) a ≤
      δ - s + transferGain q D V (outN D V v) α x) :
    ∀ x ∈ V.erase v, mass (V.erase v) (fun z => a z + α z) ≤
      row q (splitTransferGraph q D V v C) (V.erase v) (fun z => a z + α z) x := by
  intro x hx
  rw [split_surplus_mass (by omega : 1 ≤ q) hf hv a α s hs hm]
  have hrow := hr x hx
  by_cases hp : x ∈ inN D V v
  · rw [split_parent_row_surplus hq hf hv hC hp a α s hs hm]
    have hpay := hparents x hp
    nlinarith
  · rw [splitTransfer_other_row hC hx hp a α hs]
    have hpay := hothers x hx hp
    unfold transferGain at hpay
    linarith

theorem closed_split_positive_order {q : ℕ} (hq : 2 ≤ q)
    {D : CH.Digraph} {V : Finset ℕ} {v : ℕ} {C : Finset (ℕ × ℕ)}
    (hf : QFree D V q) (hv : v ∈ V) (hKne : (V.erase v).Nonempty)
    (hsmall : SmallerSmallRow q V.card) (hC : RootCuts D V v C) (a α : ℕ → ℚ)
    (hpositive : ∀ x ∈ V.erase v, 0 < a x + α x) (δ s : ℚ)
    (hs : ∀ z ∈ V, z ∉ outN D V v → α z = 0) (hm : mass (outN D V v) α = a v + s)
    (hr : ∀ x ∈ V.erase v, mass V a + δ ≤ row q D V a x)
    (hparents : ∀ x ∈ inN D V v, q * mass (splitBlocked q D V v C x) α ≤
      δ + ((q : ℚ) - 1) * s + q * mass (splitNew q D V v C x) a)
    (hothers : ∀ x ∈ V.erase v, x ∉ inN D V v → q * mass (cutHeads V C x) a ≤
      δ - s + transferGain q D V (outN D V v) α x) : (V.card : ZMod q) = 2 :=
  hsmall.erased_positive_child_order hq hv hKne _ (splitTransferGraph_qfree (by omega) hf hv C)
    _ hpositive (split_closed_budgets_feasible_on_retained hq hf hv hC a α δ s hs hm hr hparents hothers)

theorem closed_split_positive_order_exclusion {q : ℕ} (hq : 2 ≤ q)
    {D : CH.Digraph} {V : Finset ℕ} {v : ℕ} {C : Finset (ℕ × ℕ)}
    (hf : QFree D V q) (hv : v ∈ V) (hKne : (V.erase v).Nonempty)
    (hsmall : SmallerSmallRow q V.card) (hC : RootCuts D V v C) (a α : ℕ → ℚ)
    (hpositive : ∀ x ∈ V.erase v, 0 < a x + α x) (δ s : ℚ)
    (hs : ∀ z ∈ V, z ∉ outN D V v → α z = 0) (hm : mass (outN D V v) α = a v + s)
    (hr : ∀ x ∈ V.erase v, mass V a + δ ≤ row q D V a x) (hmod : (V.card : ZMod q) ≠ 2)
    (hparents : ∀ x ∈ inN D V v, q * mass (splitBlocked q D V v C x) α ≤
      δ + ((q : ℚ) - 1) * s + q * mass (splitNew q D V v C x) a)
    (hothers : ∀ x ∈ V.erase v, x ∉ inN D V v → q * mass (cutHeads V C x) a ≤
      δ - s + transferGain q D V (outN D V v) α x) : False :=
  hmod (closed_split_positive_order hq hf hv hKne hsmall hC a α hpositive δ s hs hm hr hparents hothers)

/-- The boundary order can come from a different, unperturbed weighting.
Only the current retained source rows require the displayed lower bound. -/
theorem closed_split_positive_boundary_order_impossible {q : ℕ} (hq : 2 ≤ q)
    {D : CH.Digraph} {V : Finset ℕ} {v : ℕ} {C : Finset (ℕ × ℕ)}
    (hf : QFree D V q) (hv : v ∈ V) (hKne : (V.erase v).Nonempty)
    (hsmall : SmallerSmallRow q V.card) (hC : RootCuts D V v C) (a α : ℕ → ℚ)
    (hpositive : ∀ x ∈ V.erase v, 0 < a x + α x) (δ s : ℚ)
    (hs : ∀ z ∈ V, z ∉ outN D V v → α z = 0) (hm : mass (outN D V v) α = a v + s)
    (hr : ∀ x ∈ V.erase v, mass V a + δ ≤ row q D V a x) (hmod : (V.card : ZMod q) = 1)
    (hparents : ∀ x ∈ inN D V v, q * mass (splitBlocked q D V v C x) α ≤
      δ + ((q : ℚ) - 1) * s + q * mass (splitNew q D V v C x) a)
    (hothers : ∀ x ∈ V.erase v, x ∉ inN D V v → q * mass (cutHeads V C x) a ≤
      δ - s + transferGain q D V (outN D V v) α x) : False := by
  letI : Fact (1 < q) := ⟨by omega⟩
  have horder := closed_split_positive_order hq hf hv hKne hsmall hC a α hpositive δ s hs hm hr hparents hothers
  have he : (1 : ZMod q) + 0 = 1 + 1 := by
    simpa only [add_zero, one_add_one_eq_two] using hmod.symm.trans horder
  exact zero_ne_one (add_left_cancel he)

/-- Boundary contradiction with any signed shift and possibly zero transfer.
Only retained child positivity and nonemptiness are needed for its order. -/
theorem boundary_closed_split_positive_impossible {q : ℕ} (hq : 2 ≤ q)
    {D : CH.Digraph} {V : Finset ℕ} {v : ℕ} {C : Finset (ℕ × ℕ)}
    (hf : QFree D V q) (hv : v ∈ V) (hKne : (V.erase v).Nonempty)
    (hsmall : SmallerSmallRow q V.card) (hC : RootCuts D V v C) (a α : ℕ → ℚ)
    (hpositive : ∀ x ∈ V.erase v, 0 < a x + α x) (s : ℚ)
    (hs : ∀ z ∈ V, z ∉ outN D V v → α z = 0) (hm : mass (outN D V v) α = a v + s)
    (hne : mass V a ≠ 0) (hr : ∀ x ∈ V, row q D V a x = mass V a)
    (hparents : ∀ x ∈ inN D V v, q * mass (splitBlocked q D V v C x) α ≤
      ((q : ℚ) - 1) * s + q * mass (splitNew q D V v C x) a)
    (hothers : ∀ x ∈ V.erase v, x ∉ inN D V v → q * mass (cutHeads V C x) a ≤
      -s + transferGain q D V (outN D V v) α x) : False := by
  have hmod := tight_rows_card_mod q D V a hne hr
  exact closed_split_positive_boundary_order_impossible hq hf hv hKne hsmall hC a α hpositive 0 s hs hm
    (fun x hx => by simpa only [add_zero] using (hr x (mem_erase.mp hx).2).ge) hmod
    (by simpa only [zero_add] using hparents) (by simpa only [zero_sub] using hothers)

end LeanCH.BR.WeightedSD
