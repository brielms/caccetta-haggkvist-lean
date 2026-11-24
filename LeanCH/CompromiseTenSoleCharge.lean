module

public import LeanCH.CompromiseTenSoleHeads

set_option linter.style.header false

/-! The sole return target supplies the final charge in the remaining
two-exception configuration. -/

open Finset CH.CompromiseSeven
public section

namespace CH.CompromiseTenFrame.Frame

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {adj : V → V → Prop} [DecidableRel adj]

namespace SoleReturn

variable {f : Frame adj} (s : SoleReturn f) (H : Ambient adj)
include s H

theorem missing_x_bonus (b : V) (hb : b ∈ f.A) (xb : adj s.x b) (t : ℕ)
    (bonus : 1 + t ≤ 10 - (inN adj b).card) :
    f.omission s.x + t ≤ ∑ a ∈ f.A, (10 - (inN adj a).card) := by
  let M := f.A \ inN adj s.x
  have bM : b ∈ M := mem_sdiff.mpr ⟨hb, fun incoming =>
    H.noDigon s.x b xb ((mem_inN adj s.x b).mp incoming)⟩
  have point (a : V) (ha : a ∈ M) : 1 + (if a = b then t else 0) ≤ 10 - (inN adj a).card := by
    by_cases equal : a = b
    · subst a
      simpa only [ite_true] using bonus
    · have bound := s.missing_x_deficient H a (mem_sdiff.mp ha).1
        (fun edge => (mem_sdiff.mp ha).2 ((mem_inN adj s.x a).mpr edge))
      rw [ite_eq_right equal]
      omega
  have count : (∑ a ∈ M, if a = b then t else 0 : ℕ) = t := by simp [bM]
  have lower := sum_le_sum point
  simp only [sum_add_distrib, sum_const, smul_eq_mul, Nat.mul_one, count] at lower
  have upper := sum_le_sum_of_subset (f := fun a => 10 - (inN adj a).card)
    (sdiff_subset : M ⊆ f.A)
  change (∑ a ∈ M, (10 - (inN adj a).card)) ≤ ∑ a ∈ f.A, (10 - (inN adj a).card) at upper
  change f.omission s.x + t ≤ _ at lower
  omega

theorem cover_bonus (b : V) (hb : b ∈ f.A) (xb : adj s.x b) (misses : ¬ adj b s.y)
    (c : ℕ) (positive : 1 ≤ c) (small : f.zOut s.y + c ≤ 3)
    (t : ℕ) (bonus : 1 + t ≤ 10 - (inN adj b).card) :
    f.omission s.x + (inN adj s.y ∩ f.A).card * c + t ≤
      ∑ a ∈ f.A, (10 - (inN adj a).card) := by
  have bM : b ∈ f.A \ inN adj s.x := mem_sdiff.mpr ⟨hb, fun incoming =>
    H.noDigon s.x b xb ((mem_inN adj s.x b).mp incoming)⟩
  have bNotP : b ∉ inN adj s.y ∩ f.A :=
    fun h => misses ((mem_inN adj s.y b).mp (mem_inter.mp h).1)
  have point (a : V) (ha : a ∈ f.A) :
      (if a ∈ f.A \ inN adj s.x then 1 else 0) +
        (if a ∈ inN adj s.y ∩ f.A then c else 0) +
        (if a = b then t else 0) ≤ 10 - (inN adj a).card := by
    by_cases equal : a = b
    · subst a
      simpa only [ite_eq_left bM, ite_eq_right bNotP, ite_true, Nat.add_zero] using bonus
    · have bound := s.cover_point H c positive small a ha
      rw [ite_eq_right equal, Nat.add_zero]
      exact bound
  have countM : (∑ a ∈ f.A, if a ∈ f.A \ inN adj s.x then 1 else 0 : ℕ) = f.omission s.x := by
    simp only [sum_ite_mem, sum_const, smul_eq_mul, Nat.mul_one]
    exact congrArg Finset.card (inter_eq_right.mpr sdiff_subset)
  have countP : (∑ a ∈ f.A, if a ∈ inN adj s.y ∩ f.A then c else 0 : ℕ) =
      (inN adj s.y ∩ f.A).card * c := by
    simp only [sum_ite_mem, sum_const, smul_eq_mul]
    rw [inter_eq_right.mpr inter_subset_right]
  have countB : (∑ a ∈ f.A, if a = b then t else 0 : ℕ) = t := by simp [hb]
  have lower := sum_le_sum point
  rwa [sum_add_distrib, sum_add_distrib, countM, countP, countB] at lower

theorem target_misses_y_shape (b : V) (hb : b ∈ f.A) (xb : adj s.x b) (misses : ¬ adj b s.y) :
    f.goodOnes.card = 2 ∧ f.extra b = 4 ∧ f.omission s.x = 7 ∧
      f.missing b = f.goodOnes ∪ f.exceptional := by
  have subset : f.goodOnes ∪ f.exceptional ⊆ f.missing b := by
    apply union_subset (s.target_missing_common H b hb xb)
    intro z hz
    have zZ := (mem_sdiff.mp hz).1
    rw [s.exceptions, mem_insert, mem_singleton] at hz
    refine mem_sdiff.mpr ⟨zZ, ?_⟩
    intro outgoing
    rcases hz with equal | equal
    · subst z
      exact H.noDigon s.x b xb ((mem_outN adj b s.x).mp outgoing)
    · subst z
      exact misses ((mem_outN adj b s.y).mp outgoing)
  have disj : Disjoint f.goodOnes f.exceptional :=
    f.good_exceptional_disjoint.mono_left (filter_subset _ _)
  have count := card_le_card subset
  rw [card_union_of_disjoint disj, s.two] at count
  change f.goodOnes.card + 2 ≤ f.extra b at count
  have upper := s.target_extra_upper H b hb xb
  have shape := s.small_shape H
  have heads := s.target_head_count H b hb xb
  have ones : f.goodOnes.card = 2 := by omega
  have extra : f.extra b = 4 := by omega
  refine ⟨ones, extra, by omega, ?_⟩
  symm
  apply eq_of_subset_of_card_le subset
  rw [card_union_of_disjoint disj, s.two, ones]
  change f.extra b ≤ 4
  omega

theorem target_misses_y_deficit (b : V) (hb : b ∈ f.A) (xb : adj s.x b) (misses : ¬ adj b s.y) :
    3 ≤ 10 - (inN adj b).card := by
  obtain ⟨ones, extra, _, equal⟩ := s.target_misses_y_shape H b hb xb misses
  have many := f.two_high_three_internal_twos H s.two (s.good_minimum H) ones
  obtain ⟨g, hg⟩ := card_pos.mp (show 0 < f.goodInternalTwos.card by omega)
  have good := (mem_filter.mp hg).1
  have degree := (mem_filter.mp hg).2
  have bg : adj b g := by
    by_contra notEdge
    have member : g ∈ f.missing b := mem_sdiff.mpr ⟨(mem_filter.mp good).1,
      fun outgoing => notEdge ((mem_outN adj b g).mp outgoing)⟩
    rw [equal, mem_union] at member
    rcases member with one | ex
    · have := (mem_filter.mp one).2
      omega
    · exact (mem_sdiff.mp ex).2 good
  have noX : ¬ adj g s.x := fun gx => H.noTri g s.x b gx xb bg
  have subset : outN adj g ∩ f.exceptional ⊆ {s.y} := by
    intro z hz
    have member := (mem_inter.mp hz).2
    rw [s.exceptions, mem_insert, mem_singleton] at member
    rcases member with zx | zy
    · subst z
      exact False.elim (noX ((mem_outN adj g s.x).mp (mem_inter.mp hz).1))
    · exact mem_singleton.mpr zy
  have cap := card_le_card subset
  rw [card_singleton] at cap
  have split := f.good_exceptional_degrees g
  have inside := f.full_inside_growth H b hb
  rw [extra] at inside
  have bound := f.head_deficit H b hb g bg 2 (by rw [f.good_return_zero H g good]; omega)
  omega

theorem impossible : False := by
  obtain ⟨b, hb⟩ := card_pos.mp s.xPositive
  have bA := (mem_inter.mp hb).2
  have xb := (mem_outN adj s.x b).mp (mem_inter.mp hb).1
  have under := s.under
  have shape := s.small_shape H
  by_cases sees : adj b s.y
  · have zero := s.y_zero_of_target_sees H b bA xb sees
    have extra := s.target_extra_lower H b bA xb
    have inside := f.full_inside_growth H b bA
    have bound := f.head_deficit H b bA s.y sees 4 (by rw [s.yZero, zero]; omega)
    have charge := s.missing_x_bonus H b bA xb 4 (by omega)
    omega
  · obtain ⟨ones, _, omission, _⟩ := s.target_misses_y_shape H b bA xb sees
    have bonus := s.target_misses_y_deficit H b bA xb sees
    have low := s.y_at_most_one H b bA xb
    have charge := s.cover_bonus H b bA xb sees 2 (by omega) (by omega) 2 (by omega)
    have budget := s.budget H
    have good := s.common_target_budget H
    rw [ones, s.x_one H] at good
    have column := card_sdiff_add_card_inter f.A (inN adj s.y)
    rw [inter_comm, f.cardA] at column
    change f.omission s.y + (inN adj s.y ∩ f.A).card = 10 at column
    omega

end SoleReturn

variable (H : Ambient adj) (f : Frame adj)
include H

theorem two_exception_charge (exceptions : f.exceptional.card = 2) :
    10 ≤ ∑ a ∈ f.A, (10 - (inN adj a).card) := by
  by_contra failure
  have under : (∑ a ∈ f.A, (10 - (inN adj a).card)) ≤ 9 := by omega
  obtain ⟨y, hy, zero⟩ := f.undercharged_two_nonreturn H exceptions under
  obtain ⟨a, _, _, x, hx, _, omission, b, hb, xb⟩ := f.undercharged_return_path H under
  have xX : x ∈ f.exceptional := by
    rw [f.exceptional_eq_filter]
    exact mem_filter.mpr ⟨hx, omission⟩
  have positive : 1 ≤ f.aOut x :=
    card_pos.mpr ⟨b, mem_inter.mpr ⟨(mem_outN adj x b).mpr xb, hb⟩⟩
  have different : x ≠ y := by intro equal; subst y; omega
  have subset : ({x, y} : Finset V) ⊆ f.exceptional :=
    insert_subset xX (singleton_subset_iff.mpr hy)
  have equal : ({x, y} : Finset V) = f.exceptional := eq_of_subset_of_card_le subset (by
    rw [exceptions]
    simp [different])
  let s : SoleReturn f := ⟨x, y, different, equal.symm, positive, zero, under⟩
  exact s.impossible H

theorem undercharged_three_exceptions
    (under : (∑ a ∈ f.A, (10 - (inN adj a).card)) ≤ 9) :
    3 ≤ f.exceptional.card ∧ f.exceptional.card ≤ 4 := by
  have bounds := f.undercharged_two_exceptions H under
  refine ⟨?_, bounds.2⟩
  by_contra small
  have two : f.exceptional.card = 2 := by omega
  have charge := f.two_exception_charge H two
  omega

end CH.CompromiseTenFrame.Frame

#print axioms CH.CompromiseTenFrame.Frame.SoleReturn.impossible
#print axioms CH.CompromiseTenFrame.Frame.two_exception_charge
#print axioms CH.CompromiseTenFrame.Frame.undercharged_three_exceptions
