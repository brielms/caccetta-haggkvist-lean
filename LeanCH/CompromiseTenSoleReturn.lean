module

public import LeanCH.CompromiseTenTwoReturns

set_option linter.style.header false

/-! Package the remaining undercharged two-exception configuration,
with exactly one returning exception. -/

open Finset CH.CompromiseSeven CH.CompromiseTenLocal
public section

namespace CH.CompromiseTenFrame.Frame

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {adj : V → V → Prop} [DecidableRel adj]

structure SoleReturn (f : Frame adj) where
  x : V
  y : V
  different : x ≠ y
  exceptions : f.exceptional = {x, y}
  xPositive : 1 ≤ f.aOut x
  yZero : f.aOut y = 0
  under : (∑ a ∈ f.A, (10 - (inN adj a).card)) ≤ 9

namespace SoleReturn

variable {f : Frame adj} (s : SoleReturn f) (H : Ambient adj)
include s

theorem two : f.exceptional.card = 2 := by rw [s.exceptions]; simp [s.different]
theorem x_mem : s.x ∈ f.exceptional := by rw [s.exceptions]; simp
theorem y_mem : s.y ∈ f.exceptional := by rw [s.exceptions]; simp
theorem x_Z : s.x ∈ f.Z := (mem_sdiff.mp s.x_mem).1
theorem y_Z : s.y ∈ f.Z := (mem_sdiff.mp s.y_mem).1

include H

theorem good_minimum : ∀ g ∈ f.good, 3 ≤ f.zOut g :=
  f.undercharged_two_good_minimum H s.two s.under

theorem common : 2 ≤ f.goodOnes.card ∧
    ∀ g ∈ f.goodOnes, f.zOut g = 3 ∧ f.exceptional ⊆ outN adj g :=
  f.two_high_common_heads H s.two (s.good_minimum H)

omit H in
theorem good_or_xy (z : V) (hz : z ∈ f.Z) : z ∈ f.good ∨ z = s.x ∨ z = s.y := by
  by_cases good : z ∈ f.good
  · exact Or.inl good
  · have ex : z ∈ f.exceptional := mem_sdiff.mpr ⟨hz, good⟩
    rw [s.exceptions, mem_insert, mem_singleton] at ex
    exact Or.inr ex

theorem only_return (z : V) (hz : z ∈ f.Z) (different : z ≠ s.x) : f.aOut z = 0 := by
  rcases s.good_or_xy z hz with good | equal | equal
  · exact f.good_return_zero H z good
  · exact False.elim (different equal)
  · rw [equal]
    exact s.yZero

theorem missing_x_deficient (a : V) (ha : a ∈ f.A) (misses : ¬ adj a s.x) :
    (inN adj a).card ≤ 9 := by
  apply f.zero_return_heads_deficient H a ha
  intro z hz
  apply s.only_return H z (mem_inter.mp hz).2
  intro equal
  subst z
  exact misses ((mem_outN adj a s.x).mp (mem_inter.mp hz).1)

theorem y_low : f.zOut s.y ≤ 2 := by
  by_contra high
  let T := f.Z.erase s.x
  have size : T.card = 7 := by dsimp [T]; rw [card_erase_of_mem s.x_Z, f.cardZ]
  have minZ (z : V) (hz : z ∈ T) : 3 ≤ f.zOut z := by
    rcases s.good_or_xy z (mem_erase.mp hz).2 with good | equal | equal
    · exact s.good_minimum H z good
    · exact False.elim ((mem_erase.mp hz).1 equal)
    · rw [equal]
      omega
  have degreeBound (z : V) : f.zOut z ≤ (outN adj z ∩ T).card + 1 := by
    have subset : outN adj z ∩ f.Z ⊆ T ∪ {s.x} := by
      intro b hb
      by_cases equal : b = s.x
      · exact mem_union_right _ (mem_singleton.mpr equal)
      · exact mem_union_left _ (mem_erase.mpr ⟨equal, (mem_inter.mp hb).2⟩)
    have bound := degree_bound (outN adj z ∩ f.Z) T {s.x} subset
    have equal : (outN adj z ∩ f.Z) ∩ T = outN adj z ∩ T := by
      ext b
      simp only [mem_inter]
      exact ⟨fun h => ⟨h.1.1, h.2⟩,
        fun h => ⟨⟨h.1, (mem_erase.mp h.2).2⟩, h.2⟩⟩
    rw [equal, card_singleton] at bound
    exact bound
  have minimum (z : V) (hz : z ∈ T) : 2 ≤ (outN adj z ∩ T).card := by
    have := minZ z hz
    have := degreeBound z
    omega
  have rigid := rigid_small adj H.loopless H.noDigon H.noTri H.small T 2
    (by omega) (by omega) (by omega) minimum
  have parent (z : V) (hz : z ∈ T) : adj z s.x := by
    by_contra misses
    have subset : outN adj z ∩ f.Z ⊆ outN adj z ∩ T := by
      intro b hb
      refine mem_inter.mpr ⟨(mem_inter.mp hb).1, mem_erase.mpr ⟨?_, (mem_inter.mp hb).2⟩⟩
      intro equal
      subst b
      exact misses ((mem_outN adj z s.x).mp (mem_inter.mp hb).1)
    have bound := card_le_card subset
    have low := (rigid z hz).1
    have high := minZ z hz
    change f.zOut z ≤ (outN adj z ∩ T).card at bound
    omega
  obtain ⟨b, hb⟩ := card_pos.mp s.xPositive
  have edge := (mem_outN adj s.x b).mp (mem_inter.mp hb).1
  have subset : f.Z ⊆ f.missing b := by
    intro z hz
    refine mem_sdiff.mpr ⟨hz, ?_⟩
    intro outgoing
    have bz := (mem_outN adj b z).mp outgoing
    by_cases equal : z = s.x
    · subst z
      exact H.noDigon s.x b edge bz
    · exact H.noTri s.x b z edge bz (parent z (mem_erase.mpr ⟨equal, hz⟩))
  have lower := card_le_card subset
  rw [f.cardZ] at lower
  change 8 ≤ f.extra b at lower
  have upper := f.extra_le_seven H b (mem_inter.mp hb).2
  omega

theorem cover_point (c : ℕ) (positive : 1 ≤ c) (small : f.zOut s.y + c ≤ 3)
    (a : V) (ha : a ∈ f.A) :
    (if a ∈ f.A \ inN adj s.x then 1 else 0) +
      (if a ∈ inN adj s.y ∩ f.A then c else 0) ≤ 10 - (inN adj a).card := by
  by_cases inM : a ∈ f.A \ inN adj s.x
  · have misses : ¬ adj a s.x := fun edge => (mem_sdiff.mp inM).2 ((mem_inN adj s.x a).mpr edge)
    by_cases inP : a ∈ inN adj s.y ∩ f.A
    · have extra : 1 ≤ f.extra a := card_pos.mpr ⟨s.x, mem_sdiff.mpr ⟨s.x_Z,
        fun edge => misses ((mem_outN adj a s.x).mp edge)⟩⟩
      have inside := f.inside_extra_positive H a ha extra
      have edge := (mem_inN adj s.y a).mp (mem_inter.mp inP).1
      have bound := f.head_deficit H a ha s.y edge c (by rw [s.yZero]; omega)
      rw [ite_eq_left inM, ite_eq_left inP]
      omega
    · have bound := s.missing_x_deficient H a ha misses
      rw [ite_eq_left inM, ite_eq_right inP]
      omega
  · by_cases inP : a ∈ inN adj s.y ∩ f.A
    · have inside := f.inside_at_least_two H a ha
      have edge := (mem_inN adj s.y a).mp (mem_inter.mp inP).1
      have bound := f.head_deficit H a ha s.y edge (c - 1) (by rw [s.yZero]; omega)
      rw [ite_eq_right inM, ite_eq_left inP]
      omega
    · simp only [ite_eq_right inM, ite_eq_right inP, Nat.add_zero, Nat.zero_le]

theorem cover (c : ℕ) (positive : 1 ≤ c) (small : f.zOut s.y + c ≤ 3) :
    f.omission s.x + (inN adj s.y ∩ f.A).card * c ≤
      ∑ a ∈ f.A, (10 - (inN adj a).card) := by
  have countM : (∑ a ∈ f.A, if a ∈ f.A \ inN adj s.x then 1 else 0 : ℕ) = f.omission s.x := by
    simp only [sum_ite_mem, sum_const, smul_eq_mul, Nat.mul_one]
    exact congrArg Finset.card (inter_eq_right.mpr sdiff_subset)
  have countP : (∑ a ∈ f.A, if a ∈ inN adj s.y ∩ f.A then c else 0 : ℕ) =
      (inN adj s.y ∩ f.A).card * c := by
    simp only [sum_ite_mem, sum_const, smul_eq_mul]
    rw [inter_eq_right.mpr inter_subset_right]
  have lower := sum_le_sum (fun a ha => s.cover_point H c positive small a ha)
  rwa [sum_add_distrib, countM, countP] at lower

theorem omission_order : f.omission s.x + 1 ≤ f.omission s.y := by
  have low := s.y_low H
  have charge := s.cover H 1 (by omega) (by omega)
  have under := s.under
  have column := card_sdiff_add_card_inter f.A (inN adj s.y)
  rw [inter_comm, f.cardA] at column
  change f.omission s.y + (inN adj s.y ∩ f.A).card = 10 at column
  omega

end SoleReturn
end CH.CompromiseTenFrame.Frame

#print axioms CH.CompromiseTenFrame.Frame.SoleReturn.y_low
#print axioms CH.CompromiseTenFrame.Frame.SoleReturn.cover
#print axioms CH.CompromiseTenFrame.Frame.SoleReturn.omission_order
