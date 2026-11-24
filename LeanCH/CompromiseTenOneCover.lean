module

public import LeanCH.CompromiseTenReturns

set_option linter.style.header false

/-! A covering charge for one exceptional column. Rows missing that
column already pay one; seeing a good degree-two column supplies the
second unit for those rows and the first unit for the other rows. -/

open Finset CH.CompromiseSeven
public section

namespace CH.CompromiseTenFrame.Frame

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {adj : V → V → Prop} [DecidableRel adj]

@[expose] def goodTwos (f : Frame adj) := f.good.filter (fun z => f.zOut z = 2)
@[expose] def avoidTwos (f : Frame adj) :=
  f.A.filter (fun a => ∀ z ∈ f.goodTwos, ¬ adj a z)

variable (H : Ambient adj) (f : Frame adj)
include H

theorem good_return_zero (z : V) (hz : z ∈ f.good) : f.aOut z = 0 := by
  apply card_eq_zero.mpr
  apply eq_empty_iff_forall_notMem.mpr
  intro a ha
  exact f.good_avoids_A H z hz a (mem_inter.mp ha).2
    ((mem_outN adj z a).mp (mem_inter.mp ha).1)

theorem avoid_twos_budget : f.goodTwos.card * f.avoidTwos.card ≤ 18 := by
  have lower (z : V) (hz : z ∈ f.goodTwos) : f.avoidTwos.card ≤ f.omission z := by
    apply card_le_card
    intro a ha
    exact mem_sdiff.mpr ⟨(mem_filter.mp ha).1, fun incoming =>
      (mem_filter.mp ha).2 z hz ((mem_inN adj z a).mp incoming)⟩
  have bound := sum_le_sum lower
  simp only [sum_const, smul_eq_mul] at bound
  have subset : f.goodTwos ⊆ f.Z := (filter_subset _ _).trans (filter_subset _ _)
  have upper : (∑ z ∈ f.goodTwos, f.omission z) ≤ f.total := sum_le_sum_of_subset subset
  have total := f.total_le_eighteen H
  omega

theorem one_cover_charge (x : V) (single : f.exceptional = {x})
    (cover : f.avoidTwos.card ≤ f.omission x) :
    10 ≤ ∑ a ∈ f.A, (10 - (inN adj a).card) := by
  have xX : x ∈ f.exceptional := single.symm ▸ mem_singleton_self x
  have xZ := (mem_sdiff.mp xX).1
  let M := f.A \ inN adj x
  let N := f.A \ f.avoidTwos
  have mA : M ⊆ f.A := sdiff_subset
  have nA : N ⊆ f.A := sdiff_subset
  have missed (a : V) (ha : a ∈ M) : ¬ adj a x :=
    fun h => (mem_sdiff.mp ha).2 ((mem_inN adj x a).mpr h)
  have sees (a : V) (ha : a ∈ N) : ∃ z ∈ f.goodTwos, adj a z := by
    by_contra none
    apply (mem_sdiff.mp ha).2
    refine mem_filter.mpr ⟨nA ha, ?_⟩
    intro z hz edge
    exact none ⟨z, hz, edge⟩
  have base (a : V) (ha : a ∈ N) : (inN adj a).card ≤ 9 := by
    obtain ⟨z, hz, edge⟩ := sees a ha
    have inside := f.inside_at_least_two H a (nA ha)
    have bound := f.head_deficit H a (nA ha) z edge 0 (by
      rw [f.good_return_zero H z (mem_filter.mp hz).1, (mem_filter.mp hz).2]
      omega)
    omega
  have bonus (a : V) (haM : a ∈ M) (haN : a ∈ N) : (inN adj a).card ≤ 8 := by
    have extra : 1 ≤ f.extra a := card_pos.mpr ⟨x, mem_sdiff.mpr ⟨xZ,
      fun h => missed a haM ((mem_outN adj a x).mp h)⟩⟩
    have inside := f.inside_extra_positive H a (mA haM) extra
    obtain ⟨z, hz, edge⟩ := sees a haN
    have bound := f.head_deficit H a (mA haM) z edge 1 (by
      rw [f.good_return_zero H z (mem_filter.mp hz).1, (mem_filter.mp hz).2]
      omega)
    omega
  have point (a : V) (_ha : a ∈ f.A) :
      (if a ∈ M then 1 else 0) + (if a ∈ N then 1 else 0) ≤ 10 - (inN adj a).card := by
    by_cases inM : a ∈ M
    · by_cases inN : a ∈ N
      · have := bonus a inM inN
        rw [ite_eq_left inM, ite_eq_left inN]
        omega
      · have := f.one_missing_deficient H x single a (mA inM) (missed a inM)
        rw [ite_eq_left inM, ite_eq_right inN]
        omega
    · by_cases inN : a ∈ N
      · have := base a inN
        rw [ite_eq_right inM, ite_eq_left inN]
        omega
      · simp only [ite_eq_right inM, ite_eq_right inN, Nat.add_zero, Nat.zero_le]
  have bound := sum_le_sum point
  have countM : (∑ a ∈ f.A, if a ∈ M then 1 else 0 : ℕ) = M.card := by
    simp [sum_ite_mem, inter_eq_right.mpr mA]
  have countN : (∑ a ∈ f.A, if a ∈ N then 1 else 0 : ℕ) = N.card := by
    simp [sum_ite_mem, inter_eq_right.mpr nA]
  rw [sum_add_distrib, countM, countN] at bound
  have subset : f.avoidTwos ⊆ f.A := filter_subset _ _
  have count := card_sdiff_of_subset subset
  change N.card = f.A.card - f.avoidTwos.card at count
  have cap := card_le_card subset
  rw [f.cardA] at count cap
  change f.avoidTwos.card ≤ M.card at cover
  omega

theorem one_product_charge (x : V) (single : f.exceptional = {x})
    (enough : 18 < f.goodTwos.card * (f.omission x + 1)) :
    10 ≤ ∑ a ∈ f.A, (10 - (inN adj a).card) := by
  apply f.one_cover_charge H x single
  by_contra large
  have lower : f.omission x + 1 ≤ f.avoidTwos.card := by omega
  have product := Nat.mul_le_mul_left f.goodTwos.card lower
  have budget := f.avoid_twos_budget H
  omega

theorem one_good_two_charge (x : V) (single : f.exceptional = {x})
    (existsTwo : f.goodTwos.Nonempty) :
    10 ≤ ∑ a ∈ f.A, (10 - (inN adj a).card) := by
  obtain ⟨z, hz⟩ := existsTwo
  have subset : f.avoidTwos ⊆ f.A \ inN adj z := by
    intro a ha
    exact mem_sdiff.mpr ⟨(mem_filter.mp ha).1, fun incoming =>
      (mem_filter.mp ha).2 z hz ((mem_inN adj z a).mp incoming)⟩
  have bound := card_le_card subset
  change f.avoidTwos.card ≤ f.omission z at bound
  have goodBound := (mem_filter.mp (mem_filter.mp hz).1).2
  have xX : x ∈ f.exceptional := single.symm ▸ mem_singleton_self x
  have xZ := (mem_sdiff.mp xX).1
  have notGood := (mem_sdiff.mp xX).2
  simp only [good, mem_filter, xZ, true_and] at notGood
  apply f.one_cover_charge H x single
  omega

theorem one_all_deficient_of_twos (x : V) (single : f.exceptional = {x}) (r : ℕ)
    (many : r ≤ f.goodTwos.card)
    (cost : ∀ e : ℕ, r ≤ e → e ≤ 7 →
      f.aOut x + f.zOut x + (e + 1) / 3 ≤ 2 + e) :
    10 ≤ ∑ a ∈ f.A, (10 - (inN adj a).card) := by
  have point (a : V) (ha : a ∈ f.A) : 1 ≤ 10 - (inN adj a).card := by
    by_cases edge : adj a x
    · by_cases sees : ∃ z ∈ f.goodTwos, adj a z
      · obtain ⟨z, hz, az⟩ := sees
        have inside := f.inside_at_least_two H a ha
        have bound := f.head_deficit H a ha z az 0 (by
          rw [f.good_return_zero H z (mem_filter.mp hz).1, (mem_filter.mp hz).2]
          omega)
        omega
      · have subset : f.goodTwos ⊆ f.missing a := by
          intro z hz
          exact mem_sdiff.mpr ⟨(mem_filter.mp (mem_filter.mp hz).1).1,
            fun h => sees ⟨z, hz, (mem_outN adj a z).mp h⟩⟩
        have lower : r ≤ f.extra a := many.trans (card_le_card subset)
        have upper := f.extra_le_seven H a ha
        have boundCost := cost (f.extra a) lower upper
        have inside := f.full_inside_growth H a ha
        have bound := f.head_deficit H a ha x edge 0 (by omega)
        omega
    · have := f.one_missing_deficient H x single a ha edge
      omega
  have bound := sum_le_sum point
  simpa only [sum_const, smul_eq_mul, Nat.mul_one, f.cardA] using bound

end CH.CompromiseTenFrame.Frame

#print axioms CH.CompromiseTenFrame.Frame.avoid_twos_budget
#print axioms CH.CompromiseTenFrame.Frame.one_cover_charge
#print axioms CH.CompromiseTenFrame.Frame.one_product_charge
#print axioms CH.CompromiseTenFrame.Frame.one_good_two_charge
