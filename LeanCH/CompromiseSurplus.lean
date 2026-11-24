module

public import LeanCH.CompromiseTransport

set_option linter.style.header false

/-! Degree transport without an in-degree cap. The local surplus charge
condition is explicit; this module does not prove it for arbitrary graphs. -/

open Finset CH.CompromiseSeven CH.CompromiseTransport
public section

namespace CH.CompromiseSurplus

variable {V : Type*} [Fintype V]
variable (adj : V → V → Prop) [DecidableRel adj]

theorem balance (R : ℕ) (regular : ∀ v, (outN adj v).card = R) :
    (∑ v, (R - (inN adj v).card)) = ∑ v, ((inN adj v).card - R) := by
  have hp (v : V) : (inN adj v).card + (R - (inN adj v).card) =
      R + ((inN adj v).card - R) := by omega
  have hs := sum_congr (s₁ := (univ : Finset V)) rfl (fun v _ => hp v)
  simp only [sum_add_distrib, total_indegree adj R regular, sum_const,
    card_univ, smul_eq_mul] at hs
  omega

/-- Charging R times each vertex's entire surplus eliminates every surplus,
even when in-degrees may exceed R+1. -/
theorem transport (R : ℕ) (hR : 1 ≤ R)
    (regular : ∀ v, (outN adj v).card = R)
    (heads : ∀ v, R < (inN adj v).card →
      R * ((inN adj v).card - R) ≤ ∑ a ∈ outN adj v, (R - (inN adj a).card)) :
    ∀ v, (inN adj v).card = R := by
  classical
  have row (v : V) : R * ((inN adj v).card - R) ≤
      ∑ a ∈ outN adj v, (R - (inN adj a).card) := by
    by_cases hh : R < (inN adj v).card
    · exact heads v hh
    · have he : (inN adj v).card - R = 0 := by omega
      simp [he]
  have hs := sum_le_sum (s := (univ : Finset V)) (fun v _ => row v)
  rw [← mul_sum] at hs
  have hc := weighted_count adj univ (fun v => R - (inN adj v).card)
  simp only [inter_univ] at hc
  rw [hc] at hs
  have point (v : V) : (R - (inN adj v).card) * (inN adj v).card ≤
      (R - (inN adj v).card) * (R - 1) := by
    by_cases hh : (inN adj v).card < R
    · exact Nat.mul_le_mul_left _ (by omega)
    · have he : R - (inN adj v).card = 0 := by omega
      simp [he]
  have ht := sum_le_sum (s := (univ : Finset V)) (fun v _ => point v)
  rw [← sum_mul, balance adj R regular] at ht
  have hz : (∑ v, ((inN adj v).card - R)) = 0 := by
    let E := ∑ v, ((inN adj v).card - R)
    have h := hs.trans ht
    change R * E ≤ E * (R - 1) at h
    rw [Nat.mul_comm R E] at h
    have he := congrArg (fun k : ℕ => E * k) (Nat.sub_add_cancel hR)
    rw [Nat.mul_add, Nat.mul_one] at he
    change E = 0
    omega
  have cap (v : V) : (inN adj v).card ≤ R := by
    have hh := single_le_sum (s := (univ : Finset V))
      (f := fun a => (inN adj a).card - R) (fun _ _ => Nat.zero_le _) (mem_univ v)
    omega
  intro v
  have hsum : ∑ a, (inN adj a).card = ∑ _a : V, R := by
    simp [total_indegree adj R regular]
  exact (sum_eq_sum_iff_of_le (fun a _ => cap a)).mp hsum v (mem_univ _)

end CH.CompromiseSurplus

#print axioms CH.CompromiseSurplus.transport
