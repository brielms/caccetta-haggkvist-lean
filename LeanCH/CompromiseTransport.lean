module

public import LeanCH.CompromiseEight

set_option linter.style.header false

/-! Deficit-weighted degree transport. This is a counting lemma for the
degree-nine candidate; it does not assert that candidate's local dichotomy. -/

open Finset CH.CompromiseSeven
public section

namespace CH.CompromiseTransport

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (adj : V → V → Prop) [DecidableRel adj]

def deficit (R : ℕ) (v : V) : ℕ := R - (inN adj v).card

theorem weighted_count (H : Finset V) (f : V → ℕ) :
    ∑ v ∈ H, ∑ a ∈ outN adj v, f a =
      ∑ a, f a * (inN adj a ∩ H).card := by
  have ho (v : V) : outN adj v = univ.filter (adj v ·) := by ext; simp
  have hi (a : V) : inN adj a ∩ H = H.filter (adj · a) := by ext; simp; tauto
  have hout (v : V) : ∑ a ∈ outN adj v, f a = ∑ a, if adj v a then f a else 0 := by
    rw [ho, sum_filter]
  have hin (a : V) : f a * (inN adj a ∩ H).card =
      ∑ v ∈ H, if adj v a then f a else 0 := by
    rw [hi, card_eq_sum_ones, mul_sum, sum_filter]
    simp
  simp_rw [hout, hin]
  exact sum_comm

omit [DecidableEq V] in
theorem deficit_balance (R : ℕ)
    (regular : ∀ v, (outN adj v).card = R)
    (cap : ∀ v, (inN adj v).card ≤ R + 1) :
    ∑ v, deficit adj R v = (univ.filter (fun v => (inN adj v).card = R + 1)).card := by
  classical
  have hp (v : V) : (inN adj v).card + deficit adj R v =
      R + (if (inN adj v).card = R + 1 then 1 else 0) := by
    have := cap v
    dsimp [deficit]
    split_ifs <;> omega
  have hs := sum_congr (s₁ := (univ : Finset V)) rfl (fun v _ => hp v)
  simp only [sum_add_distrib, total_indegree adj R regular, sum_const,
    card_univ, smul_eq_mul] at hs
  have he : (∑ v, if (inN adj v).card = R + 1 then 1 else 0 : ℕ) =
      (univ.filter (fun v => (inN adj v).card = R + 1)).card := by simp
  omega

omit [DecidableEq V] in
/-- A surplus row cannot always carry at least R units of head deficit:
the total receiving capacity is at most (R-1) times the number of surplus rows. -/
theorem deficit_transport (R : ℕ) (hR : 1 ≤ R)
    (regular : ∀ v, (outN adj v).card = R)
    (cap : ∀ v, (inN adj v).card ≤ R + 1)
    (heads : ∀ v, (inN adj v).card = R + 1 →
      R ≤ ∑ a ∈ outN adj v, deficit adj R a) :
    ∀ v, (inN adj v).card = R := by
  classical
  let H := univ.filter (fun v => (inN adj v).card = R + 1)
  have hbudget : ∑ v, deficit adj R v = H.card := deficit_balance adj R regular cap
  have hlow : H.card * R ≤ ∑ v ∈ H, ∑ a ∈ outN adj v, deficit adj R a := by
    calc
      _ = ∑ _v ∈ H, R := by simp
      _ ≤ _ := sum_le_sum (fun v hv => heads v (by simpa [H] using hv))
  have hpoint (v : V) : deficit adj R v * (inN adj v ∩ H).card ≤
      deficit adj R v * (R - 1) := by
    by_cases hd : (inN adj v).card < R
    · have hc := card_le_card (inter_subset_left : inN adj v ∩ H ⊆ inN adj v)
      exact Nat.mul_le_mul_left _ (by omega)
    · have hz : deficit adj R v = 0 := by dsimp [deficit]; omega
      simp [hz]
  have hhigh := sum_le_sum (s := (univ : Finset V)) (fun v _ => hpoint v)
  rw [← weighted_count adj H (deficit adj R), ← sum_mul, hbudget] at hhigh
  have hzero : H.card = 0 := by nlinarith [Nat.sub_add_cancel hR]
  have hcapR (v : V) : (inN adj v).card ≤ R := by
    have hc := cap v
    have hn : v ∉ H := by rw [card_eq_zero.mp hzero]; simp
    simp only [H, mem_filter, mem_univ, true_and] at hn
    omega
  intro v
  have hsum : ∑ a, (inN adj a).card = ∑ _a : V, R := by
    simp [total_indegree adj R regular]
  exact (sum_eq_sum_iff_of_le (fun a _ => hcapR a)).mp hsum v (mem_univ _)

theorem nine_charge_of_dichotomy (v : V) (regular : (outN adj v).card = 9)
    (dichotomy : (∀ a ∈ outN adj v, (inN adj a).card ≤ 8) ∨
      5 ≤ (outN adj v ∩ univ.filter (fun a => (inN adj a).card ≤ 7)).card) :
    9 ≤ ∑ a ∈ outN adj v, deficit adj 9 a := by
  rcases dichotomy with hall | hmany
  · have hs : ∑ a ∈ outN adj v, 1 ≤ ∑ a ∈ outN adj v, deficit adj 9 a := by
      apply sum_le_sum
      intro a ha
      have := hall a ha
      dsimp [deficit]
      omega
    simpa [regular] using hs
  · let L := outN adj v ∩ univ.filter (fun a => (inN adj a).card ≤ 7)
    have hL : 5 ≤ L.card := hmany
    have hs : L.card * 2 ≤ ∑ a ∈ L, deficit adj 9 a := by
      calc
        _ = ∑ _a ∈ L, 2 := by simp
        _ ≤ _ := sum_le_sum (fun a ha => by
          have hh : (inN adj a).card ≤ 7 := (mem_filter.mp (mem_inter.mp ha).2).2
          dsimp [deficit]
          omega)
    have hsub : ∑ a ∈ L, deficit adj 9 a ≤ ∑ a ∈ outN adj v, deficit adj 9 a :=
      sum_le_sum_of_subset (inter_subset_left : L ⊆ outN adj v)
    omega

end CH.CompromiseTransport

#print axioms CH.CompromiseTransport.deficit_transport
#print axioms CH.CompromiseTransport.nine_charge_of_dichotomy
