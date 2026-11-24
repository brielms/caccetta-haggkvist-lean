import LeanCH.BR.BRFiniteInverseNotBayes
import Mathlib.Data.Rat.Floor

/-! Rational coefficients already exclude Bayesian inverse refresh. Integer
incidence counts, not an integer coefficient, are the arithmetic input. -/
namespace LeanCH.BR.InverseTransport
open Finset Matrix TwoLawTransport
open scoped Matrix

theorem rational_le_one_of_quadratic (t : ℚ) (ht : 0 < t) (z m : ℤ)
    (h : 1 = (z : ℚ)*t+(m : ℚ)*t^2) : t ≤ 1 := by
  have hr : (t.den : ℚ)^2 = (t.num : ℚ)*((z : ℚ)*t.den+(m : ℚ)*t.num) := by
    rw [← t.num_div_den] at h
    field_simp at h
    nlinarith [h]
  have hi : (t.den : ℤ)^2 = t.num*(z*t.den+m*t.num) := by exact_mod_cast hr
  have hdiv : t.num.natAbs ∣ t.den^2 := by
    refine ⟨(z*t.den+m*t.num).natAbs, ?_⟩
    have hh := congrArg Int.natAbs hi
    simpa only [Int.natAbs_pow, Int.natAbs_natCast, Int.natAbs_mul] using hh
  have habs : t.num.natAbs = 1 :=
    Nat.eq_one_of_dvd_coprimes (t.reduced.pow_right 2) dvd_rfl hdiv
  have hnum : t.num = 1 := by
    have hp := Rat.num_pos.mpr ht
    have hh := Int.natAbs_of_nonneg hp.le
    rw [habs] at hh
    simpa using hh.symm
  rw [← t.num_div_den, hnum]
  norm_num only [Int.cast_one]
  exact (div_le_one (by exact_mod_cast t.den_pos)).mpr
    (by exact_mod_cast t.den_pos)

section Matrix
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The off-diagonal Gram entry counts the two incidences between i,j and
the common-head incidences. A is an integer matrix; binary adjacency is a
special case. No orientation or sign condition is needed for this identity. -/
theorem off_diagonal_integer_gram (C : Matrix V V ℝ) (A : Matrix V V ℤ) (t : ℝ)
    (hA : ∀ i, A i i = 0)
    (hC : ∀ i j, C i j = (if i = j then 1 else 0)+t*(A i j : ℝ))
    (i j : V) (hij : i ≠ j) :
    (∑ k, C i k*C j k) = t*((A i j+A j i : ℤ) : ℝ)+
      t^2*((∑ k, A i k*A j k : ℤ) : ℝ) := by
  have he (k : V) : C i k*C j k =
      (if k = i then t*(A j i : ℝ) else 0)+
      (if k = j then t*(A i j : ℝ) else 0)+t^2*((A i k*A j k : ℤ) : ℝ) := by
    rw [hC, hC]
    by_cases hki : k = i
    · subst k
      simp [hA, hij, Ne.symm hij]
    · by_cases hkj : k = j
      · subst k
        simp [hA, hij, Ne.symm hij]
      · simp only [Ne.symm hki, Ne.symm hkj, hki, hkj, ite_false, zero_add, Int.cast_mul]
        ring
  rw [sum_congr rfl (fun k _ => he k)]
  simp only [sum_add_distrib, sum_ite_eq', mem_univ, ite_true, ← mul_sum,
    Int.cast_sum, Int.cast_add]
  ring

theorem rational_bayesian_refresh_impossible (t : ℚ) (C : Matrix V V ℝ)
    (hd : ∀ i, C i i = 1)
    (he : ∀ i j, i ≠ j → C i j = 0 ∨ C i j = (t : ℝ))
    (a p : V → ℝ) (ha : ∀ i, 0 ≤ a i) (hm : ∑ i, a i = 1)
    (c : ℝ) (hc : 1 < c)
    (hr : ∀ i, ∑ j, C i j*a j = c) (hp : ∀ j, ∑ i, p i*C i j = c)
    (hPQ : ∀ i j, (forward C a c * backward C p c) i j =
      ((c-1)*(if i = j then 1 else 0)+p j)/c)
    (hQP : ∀ i, (backward C p c * forward C a c) i i = ((c-1)+a i)/c) : False := by
  have hnV : Nonempty V := by
    by_contra hn
    have : IsEmpty V := not_nonempty_iff.mp hn
    simp at hm
  have ht : (1 : ℝ) < t := by
    by_contra ht
    have ht1 : (t : ℝ) ≤ 1 := le_of_not_gt ht
    let i : V := Classical.choice hnV
    have hC (j : V) : C i j ≤ 1 := by
      by_cases hij : i = j
      · subst j; rw [hd]
      · rcases he i j hij with h | h <;> rw [h] <;> linarith
    have h := sum_le_sum (fun j (_ : j ∈ (univ : Finset V)) =>
      mul_le_mul_of_nonneg_right (hC j) (ha j))
    simp only [one_mul, hr, hm] at h
    linarith
  have hcon := bayesian_diagonal_constraints C t hd he a p c (by linarith) hr hp
    (fun i => by simpa using hPQ i i) hQP
  obtain ⟨hpa, hua⟩ := uniform_of_diagonal_constraints t c ht hc a p ha hm hcon
  have hnt : Nontrivial V := by
    apply not_subsingleton_iff_nontrivial.mp
    intro hss
    have : Subsingleton V := hss
    let i : V := Classical.choice hnV
    have hsum : (∑ j, C i j*a j) = ∑ j, a j := by
      apply sum_congr rfl
      intro j _
      have hji : j = i := Subsingleton.elim _ _
      subst j
      rw [hd, one_mul]
    rw [hr, hm] at hsum
    linarith
  obtain ⟨i,j,hij⟩ := exists_pair_ne V
  let n := Fintype.card V
  have hn : 0 < n := Fintype.card_pos_iff.mpr hnV
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hau : ∀ k, a k = 1/(n : ℝ) := by
    have hs0 : (∑ k, a k) = (n : ℝ)*a i := by
      calc
        _ = ∑ k : V, a i := sum_congr rfl (fun k _ => hua k i)
        _ = _ := by simp [n]
    have hs := hs0.symm.trans hm
    intro k
    rw [hua k i]
    exact (eq_div_iff hnr.ne').mpr (by linarith)
  let A : Matrix V V ℤ := fun i j => if i = j then 0 else if C i j = (t : ℝ) then 1 else 0
  have hAd (k : V) : A k k = 0 := by simp [A]
  have hrep (k l : V) : C k l = (if k = l then 1 else 0)+(t : ℝ)*(A k l : ℝ) := by
    by_cases hkl : k = l
    · subst l; simp [A, hd]
    · rcases he k l hkl with h | h
      · simp [A, hkl, h, (by linarith : (0 : ℝ) ≠ t)]
      · simp [A, hkl, h]
  let d : ℤ := ∑ k, A i k
  let m : ℤ := ∑ k, A i k*A j k
  let s : ℤ := A i j+A j i
  have hrowC : (∑ k, C i k) = 1+(t : ℝ)*(d : ℝ) := by
    rw [sum_congr rfl (fun k _ => hrep i k)]
    simp only [sum_add_distrib, sum_ite_eq, mem_univ, ite_true, ← mul_sum, ← Int.cast_sum]
    rfl
  have hnc : (n : ℝ)*c = 1+(t : ℝ)*(d : ℝ) := by
    have h := hr i
    simp_rw [hau] at h
    rw [← sum_mul, hrowC] at h
    field_simp at h
    nlinarith
  have hgram : (∑ k, C i k*C j k) = (n : ℝ)*c := by
    have h := hPQ i j
    rw [forward_backward_entry, hpa] at h
    simp_rw [hau] at h
    rw [← sum_mul] at h
    simp only [hij, ite_false, mul_zero, zero_add] at h
    field_simp at h
    nlinarith
  have hcount := off_diagonal_integer_gram C A t hAd hrep i j hij
  change (∑ k, C i k*C j k) = (t : ℝ)*(s : ℝ)+(t : ℝ)^2*(m : ℝ) at hcount
  have hreal : (1 : ℝ) = ((s-d : ℤ) : ℝ)*(t : ℝ)+(m : ℝ)*(t : ℝ)^2 := by
    rw [hgram, hnc] at hcount
    push_cast
    nlinarith [hcount]
  have hrat : (1 : ℚ) = ((s-d : ℤ) : ℚ)*t+(m : ℚ)*t^2 := by
    apply (Rat.cast_injective (α := ℝ))
    push_cast
    simpa only [Int.cast_sub, pow_two, Rat.cast_mul] using hreal
  have htle := rational_le_one_of_quadratic t (by exact_mod_cast (show (0 : ℝ) < t by linarith)) (s-d) m hrat
  have htt : (1 : ℚ) < t := by exact_mod_cast ht
  exact (not_lt_of_ge htle) htt

theorem rational_channel_ne_bayesian (t : ℚ)
    {C H : Matrix V V ℝ} (hH : centered C * H = 1)
    (hd : ∀ i, C i i = 1) (he : ∀ i j, i ≠ j → C i j = 0 ∨ C i j = (t : ℝ))
    (a p : V → ℝ) (ha : ∀ i, 0 < a i) (hm : ∑ i, a i = 1)
    (hpm : ∑ i, p i = 1) (c : ℝ) (hc : 1 < c)
    (hr : ∀ i, ∑ j, C i j*a j = c) (hp : ∀ j, ∑ i, p i*C i j = c) :
    channel H a c ≠ backward C p c := by
  intro h
  apply rational_bayesian_refresh_impossible t C hd he a p (fun i => (ha i).le) hm c hc hr hp
  · intro i j
    simpa only [h] using forward_channel hH a p (fun i => (ha i).ne') hpm c hp i j
  · intro i
    simpa [h] using channel_forward hH a (fun i => (ha i).ne') hm c hr i i

end Matrix
end LeanCH.BR.InverseTransport
