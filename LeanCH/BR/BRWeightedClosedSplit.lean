import LeanCH.BR.BRWeightedActiveUncutLocal
import LeanCH.BR.BRWeightedStrictAtomFloor

/-! Closed split budgets suffice under lower old rows. Exact child mass and
actual old New-head credit are retained; strictness comes from a forced
uncut positive-transfer coordinate, not from a strict budget premise. -/
namespace LeanCH.BR.WeightedSD
open Finset BRq2 BRq3 BR45 BRsub

/-- Pure feasibility accounting permits signed weights and both signed
surpluses. No induction, positivity, or head-floor assumption. -/
theorem split_closed_budgets_feasible {q : ℕ} (hq : 2 ≤ q) {D : CH.Digraph}
    {V : Finset ℕ} {v : ℕ} {C : Finset (ℕ × ℕ)} (hf : QFree D V q) (hv : v ∈ V)
    (hC : RootCuts D V v C) (a α : ℕ → ℚ) (δ s : ℚ)
    (hs : ∀ z ∈ V, z ∉ outN D V v → α z = 0) (hm : mass (outN D V v) α = a v + s)
    (hr : ∀ x ∈ V, mass V a + δ ≤ row q D V a x)
    (hparents : ∀ x ∈ inN D V v, q * mass (splitBlocked q D V v C x) α ≤
      δ + ((q : ℚ) - 1) * s + q * mass (splitNew q D V v C x) a)
    (hothers : ∀ x ∈ V.erase v, x ∉ inN D V v → q * mass (cutHeads V C x) a ≤
      δ - s + transferGain q D V (outN D V v) α x) :
    ∀ x ∈ V.erase v, mass (V.erase v) (fun z => a z + α z) ≤
      row q (splitTransferGraph q D V v C) (V.erase v) (fun z => a z + α z) x := by
  intro x hx
  rw [split_surplus_mass (by omega : 1 ≤ q) hf hv a α s hs hm]
  have hrow := hr x (mem_erase.mp hx).2
  by_cases hp : x ∈ inN D V v
  · rw [split_parent_row_surplus hq hf hv hC hp a α s hs hm]
    have hpay := hparents x hp
    nlinarith
  · rw [splitTransfer_other_row hC hx hp a α hs]
    have hpay := hothers x hx hp
    unfold transferGain at hpay
    linarith

/-- Only cut heads of active receiver rows need the discrete floor. -/
theorem closed_split_impossible_of_active_head_floor {q : ℕ} (hq : 2 ≤ q)
    {D : CH.Digraph} {V : Finset ℕ} {v : ℕ} {C : Finset (ℕ × ℕ)}
    (hf : QFree D V q) (hv : v ∈ V) (hsmall : SmallerSmallRow q V.card)
    (hC : RootCuts D V v C) (a α : ℕ → ℚ)
    (ha : ∀ z ∈ V, 0 ≤ a z) (hα : ∀ z ∈ V, 0 ≤ α z)
    (δ s m : ℚ) (horder : s ≤ δ) (hpos : 0 < a v + s) (hbound : a v + δ < q * m)
    (hs : ∀ z ∈ V, z ∉ outN D V v → α z = 0) (hm : mass (outN D V v) α = a v + s)
    (hfloor : ∀ r ∈ outN D V v, 0 < α r → ∀ z ∈ cutHeads V C r, m ≤ a z)
    (hr : ∀ x ∈ V, mass V a + δ ≤ row q D V a x)
    (hparents : ∀ x ∈ inN D V v, q * mass (splitBlocked q D V v C x) α ≤
      δ + ((q : ℚ) - 1) * s + q * mass (splitNew q D V v C x) a)
    (hothers : ∀ x ∈ V.erase v, x ∉ inN D V v → q * mass (cutHeads V C x) a ≤
      δ - s + transferGain q D V (outN D V v) α x) : False := by
  have hq1 : 1 ≤ q := by omega
  have hTK := (root_interfaces_retained hq1 hf hv).2
  let F := (outN D V v).filter (fun z => 0 < α z)
  have hFK : F ⊆ V.erase v := (filter_subset _ _).trans hTK
  have hsupport : SmallRow q D F := hsmall _ _
    ((card_le_card hFK).trans_lt (card_erase_lt_of_mem hv)) (hf.mono_set (hFK.trans (erase_subset v V)))
  have hpayment : ∀ r ∈ outN D V v, 0 < α r → q * mass (cutHeads V C r) a ≤
      δ - s + transferGain q D V (outN D V v) α r := by
    intro r hr hp
    exact hothers r (hTK hr) (fun h => disjoint_left.mp (root_interfaces_disjoint hq hf hv) h hr)
  obtain ⟨r, hrT, hrpos, hrC, hgain⟩ := active_uncut_of_support_smallRow outN_subset a α
    (fun r _ _ z hz => ha z (mem_filter.mp hz).1)
    (fun z hz => hα z (outN_subset hz)) (by rwa [hm]) hsupport (δ - s) m
    (by rw [hm]; linarith) hfloor hpayment
  let E := splitTransferGraph q D V v C
  let b := fun z => a z + α z
  have hfree : QFree E (V.erase v) q := splitTransferGraph_qfree hq1 hf hv C
  have hnn : ∀ x ∈ V.erase v, 0 ≤ b x :=
    fun x hx => add_nonneg (ha x (mem_erase.mp hx).2) (hα x (mem_erase.mp hx).2)
  have hsup : SmallRow q E ((V.erase v).filter (fun z => 0 < b z)) :=
    hsmall _ _ ((card_le_card (filter_subset _ _)).trans_lt (card_erase_lt_of_mem hv))
      (hfree.mono_set (filter_subset _ _))
  have hfeas := split_closed_budgets_feasible hq hf hv hC a α δ s hs hm hr hparents hothers
  have hrP : r ∉ inN D V v := fun h => disjoint_left.mp (root_interfaces_disjoint hq hf hv) h hrT
  have hbr : 0 < b r := by dsimp [b]; linarith [ha r (outN_subset hrT)]
  have he := positive_coordinate_tight_of_support_smallRow hq b hnn hsup hfeas (hTK hrT) hbr
  change row q (splitTransferGraph q D V v C) (V.erase v) (fun z => a z + α z) r = _ at he
  rw [splitTransfer_other_row hC (hTK hrT) hrP a α hs,
    split_surplus_mass hq1 hf hv a α s hs hm, hrC] at he
  simp only [mass, sum_empty, mul_zero, sub_zero] at he
  change row q D V a r + α r + q * mass (outN D V r ∩ outN D V v) α = mass V a + s at he
  have hheads : 0 ≤ mass (outN D V r ∩ outN D V v) α :=
    mass_nonneg (fun z hz => hα z (outN_subset (mem_inter.mp hz).1))
  nlinarith [hr r (outN_subset hrT), (Nat.cast_nonneg q : (0 : ℚ) ≤ q)]

theorem closed_split_impossible {q : ℕ} (hq : 2 ≤ q)
    {D : CH.Digraph} {V : Finset ℕ} {v : ℕ} {C : Finset (ℕ × ℕ)}
    (hf : QFree D V q) (hv : v ∈ V) (hsmall : SmallerSmallRow q V.card)
    (hC : RootCuts D V v C) (a α : ℕ → ℚ)
    (ha : ∀ z ∈ V, 0 ≤ a z) (hα : ∀ z ∈ V, 0 ≤ α z)
    (δ s m : ℚ) (horder : s ≤ δ) (hpos : 0 < a v + s) (hbound : a v + δ < q * m)
    (hs : ∀ z ∈ V, z ∉ outN D V v → α z = 0) (hm : mass (outN D V v) α = a v + s)
    (hfloor : ∀ r z, (r, z) ∈ C → m ≤ a z)
    (hr : ∀ x ∈ V, mass V a + δ ≤ row q D V a x)
    (hparents : ∀ x ∈ inN D V v, q * mass (splitBlocked q D V v C x) α ≤
      δ + ((q : ℚ) - 1) * s + q * mass (splitNew q D V v C x) a)
    (hothers : ∀ x ∈ V.erase v, x ∉ inN D V v → q * mass (cutHeads V C x) a ≤
      δ - s + transferGain q D V (outN D V v) α x) : False :=
  closed_split_impossible_of_active_head_floor hq hf hv hsmall hC a α ha hα δ s m horder hpos hbound
    hs hm (fun r _ _ z hz => hfloor r z (mem_filter.mp hz).2) hr hparents hothers

/-- Strict atom floor supplies the threshold when actual cut heads weigh
at least the deleted root. A global minimum root is sufficient, not needed. -/
theorem strict_root_floor_closed_split_impossible {q : ℕ} (hq : 2 ≤ q)
    {D : CH.Digraph} {V : Finset ℕ} {v : ℕ} {C : Finset (ℕ × ℕ)}
    (hf : QFree D V q) (hv : v ∈ V) (hsmall : SmallerSmallRow q V.card)
    (hC : RootCuts D V v C) (a α : ℕ → ℚ)
    (ha : ∀ z ∈ V, 0 ≤ a z) (hα : ∀ z ∈ V, 0 ≤ α z)
    (c s : ℚ) (hc : mass V a < c) (horder : s ≤ c - mass V a) (hpos : 0 < a v + s)
    (hs : ∀ z ∈ V, z ∉ outN D V v → α z = 0) (hm : mass (outN D V v) α = a v + s)
    (hfloor : ∀ r z, (r, z) ∈ C → a v ≤ a z)
    (hr : ∀ x ∈ V, c ≤ row q D V a x)
    (hparents : ∀ x ∈ inN D V v, q * mass (splitBlocked q D V v C x) α ≤
      c - mass V a + ((q : ℚ) - 1) * s + q * mass (splitNew q D V v C x) a)
    (hothers : ∀ x ∈ V.erase v, x ∉ inN D V v → q * mass (cutHeads V C x) a ≤
      c - mass V a - s + transferGain q D V (outN D V v) α x) : False := by
  have hfloorStrict := strict_atom_floor_of_proper hq hf (hsmall.induced hf) a ha c hc hr v hv
  apply closed_split_impossible hq hf hv hsmall hC a α ha hα (c - mass V a) s (a v)
    horder hpos (by nlinarith) hs hm hfloor
  · intro x hx; have h := hr x hx; linarith
  · exact hparents
  · exact hothers

theorem boundary_root_floor_closed_split_impossible {q : ℕ} (hq : 2 ≤ q)
    {D : CH.Digraph} {V : Finset ℕ} {v : ℕ} {C : Finset (ℕ × ℕ)}
    (hf : QFree D V q) (hv : v ∈ V) (hsmall : SmallerSmallRow q V.card)
    (hC : RootCuts D V v C) (a α : ℕ → ℚ)
    (ha : ∀ z ∈ V, 0 ≤ a z) (hα : ∀ z ∈ V, 0 ≤ α z)
    (s : ℚ) (horder : s ≤ 0) (hpos : 0 < a v + s)
    (hs : ∀ z ∈ V, z ∉ outN D V v → α z = 0) (hm : mass (outN D V v) α = a v + s)
    (hfloor : ∀ r z, (r, z) ∈ C → a v ≤ a z)
    (hr : ∀ x ∈ V, mass V a ≤ row q D V a x)
    (hparents : ∀ x ∈ inN D V v, q * mass (splitBlocked q D V v C x) α ≤
      ((q : ℚ) - 1) * s + q * mass (splitNew q D V v C x) a)
    (hothers : ∀ x ∈ V.erase v, x ∉ inN D V v → q * mass (cutHeads V C x) a ≤
      -s + transferGain q D V (outN D V v) α x) : False := by
  have hM : 0 < a v := by linarith
  have hqQ : (2 : ℚ) ≤ q := by exact_mod_cast hq
  apply closed_split_impossible hq hf hv hsmall hC a α ha hα 0 s (a v)
    horder hpos (by nlinarith) hs hm hfloor
  · simpa only [add_zero] using hr
  · simpa only [zero_add] using hparents
  · simpa only [zero_sub] using hothers

end LeanCH.BR.WeightedSD
