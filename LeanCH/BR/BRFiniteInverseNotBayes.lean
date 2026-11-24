import LeanCH.BR.BRFiniteInverseTransport

/-! Integer graph coefficients rule out identifying the inverse channel with
the Bayesian reverse. No girth, induction, or inverse sign is assumed. -/
namespace LeanCH.BR.InverseTransport
open Finset Matrix TwoLawTransport
open scoped Matrix
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem square_row_sum (C : Matrix V V ℝ) (q : ℝ)
    (hd : ∀ i, C i i = 1) (he : ∀ i j, i ≠ j → C i j = 0 ∨ C i j = q)
    (a : V → ℝ) (c : ℝ) (hr : ∀ i, ∑ j, C i j * a j = c) (i : V) :
    ∑ j, C i j * C i j * a j = q*c-(q-1)*a i := by
  have hs (j : V) : C i j * C i j * a j =
      q*(C i j*a j)-(if j = i then (q-1)*a i else 0) := by
    by_cases hij : i = j
    · subst j; rw [hd]; simp; ring
    · rcases he i j hij with h | h <;> simp [h, Ne.symm hij, mul_assoc]
  simp_rw [hs]
  rw [sum_sub_distrib, ← mul_sum, hr]
  simp

theorem bayesian_diagonal_constraints (C : Matrix V V ℝ) (q : ℝ)
    (hd : ∀ i, C i i = 1) (he : ∀ i j, i ≠ j → C i j = 0 ∨ C i j = q)
    (a p : V → ℝ) (c : ℝ) (hc : c ≠ 0)
    (hr : ∀ i, ∑ j, C i j*a j = c) (hp : ∀ j, ∑ i, p i*C i j = c)
    (hPQ : ∀ i, (forward C a c * backward C p c) i i = ((c-1)+p i)/c)
    (hQP : ∀ i, (backward C p c * forward C a c) i i = ((c-1)+a i)/c) (i : V) :
    c*(c-1) = (q-1)*p i*(c-a i) ∧ c*(c-1) = (q-1)*a i*(c-p i) := by
  have hs := square_row_sum C q hd he a c hr i
  have ht := square_row_sum C.transpose q hd
    (fun i j hij => he j i hij.symm) p c (fun i => by
      simpa [Matrix.transpose_apply, mul_comm] using hp i) i
  have h1 := hPQ i
  have h2 := hQP i
  rw [forward_backward_entry, hs] at h1
  rw [backward_forward_entry] at h2
  change (∑ j, C j i*C j i*p j) = _ at ht
  rw [ht] at h2
  field_simp [hc] at h1 h2
  constructor <;> nlinarith

theorem uniform_of_diagonal_constraints (q c : ℝ) (hq : 1 < q) (hc : 1 < c)
    (a p : V → ℝ) (ha : ∀ i, 0 ≤ a i) (hm : ∑ i, a i = 1)
    (he : ∀ i, c*(c-1) = (q-1)*p i*(c-a i) ∧
      c*(c-1) = (q-1)*a i*(c-p i)) :
    p = a ∧ ∀ i j, a i = a j := by
  have hpa : p = a := by
    funext i
    have h := he i
    have hmul : (q-1)*c*(p i-a i) = 0 := by nlinarith [h.1, h.2]
    exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left
      (mul_pos (sub_pos.mpr hq) (by linarith)).ne')
  refine ⟨hpa, ?_⟩
  intro i j
  by_cases hij : i = j
  · exact congrArg a hij
  have hsum : a i+a j ≤ 1 := by
    have h := sum_le_sum_of_subset_of_nonneg (subset_univ ({i,j} : Finset V))
      (fun k _ _ => ha k)
    simpa [hm, hij] using h
  have hi := (he i).1
  have hj := (he j).1
  rw [hpa] at hi hj
  have hprod : (q-1)*(a i-a j)*(c-a i-a j) = 0 := by nlinarith
  have hz : (q-1)*(a i-a j) = 0 :=
    (mul_eq_zero.mp hprod).resolve_right (by linarith)
  exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left (by linarith))

theorem bayesian_refresh_impossible (q : ℕ) (hq : 2 ≤ q)
    (C : Matrix V V ℝ) (hd : ∀ i, C i i = 1)
    (he : ∀ i j, i ≠ j → C i j = 0 ∨ C i j = (q : ℝ))
    (a p : V → ℝ) (ha : ∀ i, 0 ≤ a i) (hm : ∑ i, a i = 1)
    (c : ℝ) (hc : 1 < c)
    (hr : ∀ i, ∑ j, C i j*a j = c) (hp : ∀ j, ∑ i, p i*C i j = c)
    (hPQ : ∀ i, (forward C a c * backward C p c) i i = ((c-1)+p i)/c)
    (hQP : ∀ i, (backward C p c * forward C a c) i i = ((c-1)+a i)/c) : False := by
  have hqr : (1 : ℝ) < q := by exact_mod_cast (show 1 < q by omega)
  have hcon := bayesian_diagonal_constraints C q hd he a p c (by linarith) hr hp hPQ hQP
  obtain ⟨hpa, hua⟩ := uniform_of_diagonal_constraints q c hqr hc a p ha hm hcon
  have hnV : Nonempty V := by
    by_contra hn
    have : IsEmpty V := not_nonempty_iff.mp hn
    simp at hm
  let i : V := Classical.choice hnV
  let n := Fintype.card V
  have hn : 0 < n := Fintype.card_pos_iff.mpr hnV
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hnr1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hau : ∀ j, a j = 1/(n : ℝ) := by
    have hs0 : (∑ j, a j) = (n : ℝ)*a i := by
      calc
        _ = ∑ j : V, a i := sum_congr rfl (fun j _ => hua j i)
        _ = _ := by simp [n]
    have hs : (n : ℝ)*a i = 1 := hs0.symm.trans hm
    intro j
    rw [hua j i]
    exact (eq_div_iff hnr.ne').mpr (by linarith)
  let F := univ.filter (fun j => C i j = (q : ℝ))
  let d := F.card
  have hentry (j : V) : C i j =
      (if j = i then 1 else 0)+(if C i j = (q : ℝ) then (q : ℝ) else 0) := by
    by_cases hij : i = j
    · subst j; simp [hd, ne_of_lt hqr]
    · rcases he i j hij with h | h
      · simp [h, Ne.symm hij, (by linarith : (0 : ℝ) ≠ q)]
      · simp [h, Ne.symm hij]
  have hsum : (∑ j, C i j) = 1+(q : ℝ)*d := by
    rw [sum_congr rfl (fun j _ => hentry j)]
    rw [sum_add_distrib]
    simp only [sum_ite_eq', mem_univ, ite_true]
    have hf : (∑ j, if C i j = (q : ℝ) then (q : ℝ) else 0) = (d : ℝ)*q := by
      rw [← sum_filter]
      simp only [sum_const, nsmul_eq_mul]
      rfl
    rw [hf, mul_comm (d : ℝ)]
  have hnc : (n : ℝ)*c = 1+(q : ℝ)*d := by
    have h := hr i
    simp_rw [hau] at h
    rw [← sum_mul, hsum] at h
    field_simp at h
    nlinarith
  have hdpos : 0 < d := by
    by_contra hn
    have hd0 : d = 0 := by omega
    rw [hd0, Nat.cast_zero, mul_zero, add_zero] at hnc
    nlinarith
  have hquad := (hcon i).1
  rw [hpa, hau] at hquad
  have heq : (1+(q : ℝ)*d)*((1+(q : ℝ)*d)-(n : ℝ)) = ((q : ℝ)-1)*q*d := by
    field_simp at hquad
    calc
      _ = c*(c-1)*(n : ℝ)^2 := by rw [← hnc]; ring
      _ = ((q : ℝ)-1)*(c*(n : ℝ)-1) := hquad
      _ = _ := by rw [mul_comm c (n : ℝ), hnc]; ring
  have hiz : (1+(q : ℤ)*d)*((n : ℤ)+(q : ℤ)-2-(q : ℤ)*d) = (q : ℤ)-1 := by
    have hh : (1+(q : ℝ)*d)*((n : ℝ)+(q : ℝ)-2-(q : ℝ)*d) = (q : ℝ)-1 := by
      nlinarith [heq]
    exact_mod_cast hh
  have hqz : (2 : ℤ) ≤ q := by exact_mod_cast hq
  have hdz : (1 : ℤ) ≤ d := by exact_mod_cast hdpos
  have hfac : 0 < (n : ℤ)+(q : ℤ)-2-(q : ℤ)*d := by
    by_contra hn
    have hle : (n : ℤ)+(q : ℤ)-2-(q : ℤ)*d ≤ 0 := by omega
    have hm0 := mul_nonpos_of_nonneg_of_nonpos
      (show (0 : ℤ) ≤ 1+(q : ℤ)*d by positivity) hle
    omega
  have hfac1 : 1 ≤ (n : ℤ)+(q : ℤ)-2-(q : ℤ)*d := by omega
  have hb := mul_le_mul_of_nonneg_left hfac1
    (show (0 : ℤ) ≤ 1+(q : ℤ)*d by positivity)
  rw [mul_one, hiz] at hb
  have hdq := mul_le_mul_of_nonneg_left hdz (show (0 : ℤ) ≤ q by omega)
  linarith

theorem coefficient_two_le_of_strict (q : ℕ) (C : Matrix V V ℝ)
    (hd : ∀ i, C i i = 1) (he : ∀ i j, i ≠ j → C i j = 0 ∨ C i j = (q : ℝ))
    (a : V → ℝ) (ha : ∀ i, 0 ≤ a i) (hm : ∑ i, a i = 1)
    (c : ℝ) (hc : 1 < c) (hr : ∀ i, ∑ j, C i j*a j = c) : 2 ≤ q := by
  by_contra hq
  have hq1 : (q : ℝ) ≤ 1 := by exact_mod_cast (show q ≤ 1 by omega)
  have hn : Nonempty V := by
    by_contra h
    have : IsEmpty V := not_nonempty_iff.mp h
    simp at hm
  let i : V := Classical.choice hn
  have hC (j : V) : C i j ≤ 1 := by
    by_cases hij : i = j
    · subst j; rw [hd]
    · rcases he i j hij with h | h <;> rw [h] <;> linarith
  have h := sum_le_sum (fun j (_ : j ∈ (univ : Finset V)) =>
    mul_le_mul_of_nonneg_right (hC j) (ha j))
  simp only [one_mul, hr, hm] at h
  linarith

theorem channel_ne_bayesian (q : ℕ)
    {C H : Matrix V V ℝ} (hH : centered C * H = 1)
    (hd : ∀ i, C i i = 1) (he : ∀ i j, i ≠ j → C i j = 0 ∨ C i j = (q : ℝ))
    (a p : V → ℝ) (ha : ∀ i, 0 < a i) (hm : ∑ i, a i = 1)
    (hpm : ∑ i, p i = 1) (c : ℝ) (hc : 1 < c)
    (hr : ∀ i, ∑ j, C i j*a j = c) (hp : ∀ j, ∑ i, p i*C i j = c) :
    channel H a c ≠ backward C p c := by
  have hq := coefficient_two_le_of_strict q C hd he a (fun i => (ha i).le) hm c hc hr
  intro h
  apply bayesian_refresh_impossible q hq C hd he a p (fun i => (ha i).le) hm c hc hr hp
  · intro i
    have hh := forward_channel hH a p (fun i => (ha i).ne') hpm c hp i i
    simpa [h] using hh
  · intro i
    have hh := channel_forward hH a (fun i => (ha i).ne') hm c hr i i
    simpa [h] using hh

end LeanCH.BR.InverseTransport
