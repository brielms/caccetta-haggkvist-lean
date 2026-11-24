import LeanCH.BR.BRWeightedCommonCut

/-! Scalar controls for the strict ball-prefix inequalities. These are NOT
graphs or CH counterexamples. They show that the prefix recurrence, even
with integral counts and the endpoint accounting, does not force value<=1. -/
namespace LeanCH.BR.WeightedPrefixControl

def ballCount (q d k : ℕ) : ℚ :=
  if k + 1 < q then (k : ℚ) * d + 1 else ((q : ℚ) - 1) * d

theorem prefix_zero {q d : ℕ} (hq : 3 ≤ q) : ballCount q d 0 = 1 := by
  simp [ballCount, show 0 + 1 < q by omega]

theorem prefix_one {q d : ℕ} (hq : 3 ≤ q) : ballCount q d 1 = d + 1 := by
  simp [ballCount, show 1 + 1 < q by omega]

theorem prefix_last {q d : ℕ} (hq : 3 ≤ q) :
    ballCount q d (q - 1) = ((q : ℚ) - 1) * d := by
  simp [ballCount, show ¬ q - 1 + 1 < q by omega]

theorem prefix_integral {q d : ℕ} (hq : 3 ≤ q) (k : ℕ) :
    ∃ m : ℕ, ballCount q d k = m := by
  unfold ballCount
  split_ifs
  · exact ⟨k * d + 1, by push_cast; rfl⟩
  · refine ⟨(q - 1) * d, ?_⟩
    rw [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ q), Nat.cast_one]

theorem prefix_bounds {q d k : ℕ} (hq : 3 ≤ q) (hd : 4 ≤ d) (hk : k < q) :
    0 < ballCount q d k ∧ ballCount q d k < (q : ℚ) * d := by
  have hdQ : (4 : ℚ) ≤ d := by exact_mod_cast hd
  have hqQ : (3 : ℚ) ≤ q := by exact_mod_cast hq
  have hkQ : (0 : ℚ) ≤ k := Nat.cast_nonneg k
  by_cases h : k + 1 < q
  · rw [ballCount, if_pos h]
    have hgap : (k : ℚ) + 2 ≤ q := by exact_mod_cast (show k + 2 ≤ q by omega)
    have hm := mul_le_mul_of_nonneg_right hgap (by linarith : (0 : ℚ) ≤ d)
    constructor <;> nlinarith [mul_nonneg hkQ (by linarith : (0 : ℚ) ≤ d)]
  · rw [ballCount, if_neg h]
    constructor
    · exact mul_pos (by linarith) (by linarith)
    · nlinarith

theorem prefix_step_pos {q d k : ℕ} (hq : 3 ≤ q) (hd : 4 ≤ d) (hk : k + 1 < q) :
    ballCount q d k < ballCount q d (k + 1) := by
  have hdQ : (4 : ℚ) ≤ d := by exact_mod_cast hd
  rw [ballCount, if_pos hk]
  by_cases hn : k + 1 + 1 < q
  · rw [ballCount, if_pos hn]
    push_cast
    nlinarith
  · have hqk : q = k + 2 := by omega
    rw [ballCount, if_neg hn, hqk]
    push_cast
    nlinarith

/-- Every noninitial proper prefix satisfies the STRICT common-value cut
recurrence, despite the positive endpoint deficiency. -/
theorem strict_prefix_cut {q d k : ℕ} (hq : 3 ≤ q) (hd : 4 ≤ d)
    (hk0 : 1 ≤ k) (hk : k + 1 < q) :
    (q : ℚ) * d + 1 + ((q : ℚ) - 1) * ballCount q d k <
      q * ballCount q d (k + 1) := by
  have hdQ : (4 : ℚ) ≤ d := by exact_mod_cast hd
  have hkQ : (1 : ℚ) ≤ k := by exact_mod_cast hk0
  rw [ballCount, if_pos hk]
  by_cases hn : k + 1 + 1 < q
  · rw [ballCount, if_pos hn]
    push_cast
    nlinarith [mul_pos (by linarith : (0 : ℚ) < k) (by linarith : (0 : ℚ) < d)]
  · have hqk : q = k + 2 := by omega
    rw [ballCount, if_neg hn, hqk]
    push_cast
    have hprod := mul_le_mul_of_nonneg_left hdQ (by linarith : (0 : ℚ) ≤ k)
    nlinarith

theorem endpoint_deficiency {q d : ℕ} (hq : 3 ≤ q) :
    ((q : ℚ) - 1) * (ballCount q d 1 - ballCount q d 0) -
      (ballCount q d (q - 1) - ballCount q d 0) = 1 := by
  rw [prefix_zero hq, prefix_one hq, prefix_last hq]
  ring

/-- Normalized scalar candidate for EVERY q>=3,d>=4. The properties model
only prefix cuts and endpoint/atom accounting; no adjacency is supplied. -/
theorem scalar_prefix_candidate {q d : ℕ} (hq : 3 ≤ q) (hd : 4 ≤ d) :
    ∃ b : ℕ → ℚ, ∃ c : ℚ,
      1 < c ∧ b 0 = 1 / ((q : ℚ) * d) ∧
      (∀ k, k < q → 0 < b k ∧ b k < 1) ∧
      (∀ k, ∃ m : ℕ, b k = m / ((q : ℚ) * d)) ∧
      q * b 1 - ((q : ℚ) - 1) * b 0 = c ∧
      b (q - 1) + d / ((q : ℚ) * d) = 1 ∧
      (∀ k, k + 1 < q → b k < b (k + 1)) ∧
      (∀ k, 1 ≤ k → k + 1 < q → c + ((q : ℚ) - 1) * b k < q * b (k + 1)) ∧
      ((q : ℚ) - 1) * (b 1 - b 0) - (b (q - 1) - b 0) = c - 1 ∧
      (q : ℚ) * d * (c - 1) ≤ (q : ℚ) - 1 := by
  let n : ℚ := (q : ℚ) * d
  have hqQ : (3 : ℚ) ≤ q := by exact_mod_cast hq
  have hdQ : (4 : ℚ) ≤ d := by exact_mod_cast hd
  have hn : 0 < n := mul_pos (by linarith) (by linarith)
  let b : ℕ → ℚ := fun k => ballCount q d k / n
  let c : ℚ := (n + 1) / n
  have hc : 1 < c := (lt_div_iff₀ hn).mpr (by linarith)
  refine ⟨b, c, hc, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp only [b, n]
    rw [prefix_zero hq]
  · intro k hk
    obtain ⟨hlo, hhi⟩ := prefix_bounds hq hd hk
    exact ⟨div_pos hlo hn, (div_lt_one hn).mpr hhi⟩
  · intro k
    obtain ⟨m, hm⟩ := prefix_integral (d := d) hq k
    exact ⟨m, congrArg (fun x : ℚ => x / n) hm⟩
  · dsimp only [b, c]
    rw [prefix_one hq, prefix_zero hq]
    field_simp [ne_of_gt hn]
    dsimp [n]
    ring
  · change ballCount q d (q - 1) / n + (d : ℚ) / n = 1
    rw [prefix_last hq]
    field_simp [ne_of_gt hn]
    dsimp [n]
    ring
  · intro k hk
    exact (div_lt_div_iff_of_pos_right hn).mpr (prefix_step_pos hq hd hk)
  · intro k hk0 hk
    have h := (div_lt_div_iff_of_pos_right hn).mpr (strict_prefix_cut hq hd hk0 hk)
    simpa only [b, c, n, add_div, mul_div_assoc] using h
  · dsimp only [b, c]
    have he := endpoint_deficiency (d := d) hq
    field_simp [ne_of_gt hn]
    nlinarith [he]
  · change n * ((n + 1) / n - 1) ≤ (q : ℚ) - 1
    have he : n * ((n + 1) / n - 1) = 1 := by
      field_simp [ne_of_gt hn]
      ring
    rw [he]
    linarith

end LeanCH.BR.WeightedPrefixControl
