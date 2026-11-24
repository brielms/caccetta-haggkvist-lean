import LeanCH.BR.BRFiniteWalk
import LeanCH.BR.BRStrictPrefixDeficiency

/-! Cycle membership and a nearly sharp deficiency budget bound every row. -/

namespace LeanCH.BR.BRsGen
open BRq2 BRq3 BR45

theorem cyclic_row_degree_cap {D : CH.Digraph} {V : Finset ℕ} {q v m : ℕ}
    (hq : 1 ≤ q) (hf : QFree D V q) (hm : 0 < m) (w : Walk D V v v m) :
    q + (outN D V v).card ≤ V.card := by
  classical
  have hqm : q < m := by
    by_contra hn
    exact hf v m hm (by omega) w
  obtain ⟨f, h0, hend, he⟩ := w.toFun
  let g := fun i => f (m - q + 1 + i)
  have hmem : ∀ i, i < q → g i ∈ V := by
    intro i hi
    have hh := (he (m - q + i) (by omega)).1
    simpa only [g, Nat.add_assoc, Nat.add_comm 1 i] using hh
  have hinj : Set.InjOn g (Finset.range q) := by
    intro i hi j hj hij
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    by_contra hn
    rcases Nat.lt_or_gt_of_ne hn with hlt | hlt
    · have wc := walk_between he
        (by omega : m - q + 1 + i ≤ m - q + 1 + j) (by omega : m - q + 1 + j ≤ m)
      change Walk D V (g i) (g j) _ at wc
      rw [← hij] at wc
      exact hf (g i) _ (by omega) (by omega) wc
    · have wc := walk_between he
        (by omega : m - q + 1 + j ≤ m - q + 1 + i) (by omega : m - q + 1 + i ≤ m)
      change Walk D V (g j) (g i) _ at wc
      rw [hij] at wc
      exact hf (g j) _ (by omega) (by omega) wc
  have hsub : (Finset.range q).image g ⊆ V \ outN D V v := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    have hiq := Finset.mem_range.mp hi
    refine Finset.mem_sdiff.mpr ⟨hmem i hiq, ?_⟩
    intro harc
    have tail := walk_between he (by omega : m - q + 1 + i ≤ m) le_rfl
    change Walk D V (g i) (f m) _ at tail
    rw [hend] at tail
    exact hf v (m - (m - q + 1 + i) + 1) (by omega) (by omega)
      (.step (hmem i hiq) (mem_outN.mp harc).2 tail)
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hinj, Finset.card_range] at hc
  have hpart := Finset.card_sdiff_add_card_eq_card (show outN D V v ⊆ V from outN_subset)
  omega

theorem row_cap_of_near_deficiency {D : CH.Digraph} {V H : Finset ℕ} {q d v : ℕ}
    (hq : 1 ≤ q) (hd : 1 ≤ d) (hb : Ball q d) (hf : QFree D V q)
    (hmin : ∀ x ∈ V, 1 ≤ (outN D V x).card)
    (hHV : H ⊆ V) (hhigh : ∀ x ∈ H, d ≤ (outN D V x).card)
    (hsmall : V.card ≤ q * d + 1)
    (hbudget : V.card + (d - 1) * (V \ H).card ≤ q * d + 2) (hv : v ∈ V) :
    q + (outN D V v).card ≤ V.card := by
  classical
  by_contra hn
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (hmin v hv)
  let R := V.filter (fun x => ∃ m, Walk D V a x m)
  have hRV : R ⊆ V := Finset.filter_subset _ _
  have haR : a ∈ R := Finset.mem_filter.mpr ⟨(mem_outN.mp ha).1, 0, .refl a⟩
  have hvR : v ∉ R := by
    intro hit
    obtain ⟨m, wm⟩ := (Finset.mem_filter.mp hit).2
    have wc : Walk D V v v (m + 1) := .step (mem_outN.mp ha).1 (mem_outN.mp ha).2 wm
    exact hn (cyclic_row_degree_cap hq hf (by omega) wc)
  have hclosed : ∀ x ∈ R, outN D V x ⊆ outN D R x := by
    intro x hx y hy
    obtain ⟨m, wm⟩ := (Finset.mem_filter.mp hx).2
    exact mem_outN.mpr ⟨Finset.mem_filter.mpr ⟨(mem_outN.mp hy).1,
      m + 1, wm.snoc (mem_outN.mp hy).1 (mem_outN.mp hy).2⟩, (mem_outN.mp hy).2⟩
  have hminR : ∀ x ∈ R, 1 ≤ (outN D R x).card :=
    fun x hx => (hmin x (hRV hx)).trans (Finset.card_le_card (hclosed x hx))
  have hKR : R ∩ H ⊆ R := Finset.inter_subset_left
  have hhighR : ∀ x ∈ R ∩ H, d ≤ (outN D R x).card := by
    intro x hx
    exact (hhigh x (Finset.mem_inter.mp hx).2).trans
      (Finset.card_le_card (hclosed x (Finset.mem_inter.mp hx).1))
  have hRsmall : R.card + 1 ≤ V.card := by
    have hsub : insert v R ⊆ V := Finset.insert_subset hv hRV
    have hc := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem hvR] at hc
    omega
  have hLc : (R \ (R ∩ H)).card ≤ (V \ H).card := by
    apply Finset.card_le_card
    intro x hx
    obtain ⟨hxR, hxK⟩ := Finset.mem_sdiff.mp hx
    exact Finset.mem_sdiff.mpr ⟨hRV hxR, fun hxH => hxK (Finset.mem_inter.mpr ⟨hxR, hxH⟩)⟩
  have hcost : (∑ x ∈ R, (d - (outN D R x).card)) ≤ (d - 1) * (V \ H).card := by
    have hz : (∑ x ∈ R ∩ H, (d - (outN D R x).card)) = 0 :=
      Finset.sum_eq_zero (fun x hx => by have hh := hhighR x hx; omega)
    have hs := Finset.sum_le_sum (s := R \ (R ∩ H)) (fun x hx =>
      show d - (outN D R x).card ≤ d - 1 by
        have hh := hminR x (Finset.mem_sdiff.mp hx).1
        omega)
    rw [Finset.sum_const_nat (fun _ _ => rfl)] at hs
    have he := Finset.sum_sdiff hKR (f := fun x => d - (outN D R x).card)
    have hm := Nat.mul_le_mul_left (d - 1) hLc
    nlinarith
  have hstrict := deficiency_strict_of_order_le hq hb (hf.mono_set hRV)
    hminR ⟨a, haR⟩ (by omega)
  omega

end LeanCH.BR.BRsGen
