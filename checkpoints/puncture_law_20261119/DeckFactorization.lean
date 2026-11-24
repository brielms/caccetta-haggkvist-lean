import checkpoints.puncture_law_20261119.PunctureLaw

/-! Deck factorization. Stack one puncture certificate per vertex into a matrix P (the
deck). Then Θ := P N is a nonsingular M-matrix with Θ H = P, so H = Θ⁻¹ P: the centered
inverse is a nonnegative mixture of the deck rows. A tail bound for the flat branch
closes the file. -/
namespace LeanCH.BR.Closure.DeckFactorization
open Finset Matrix FiniteCutInverse WeightedSD BRq2 LeanCH.BR.Closure.PunctureLaw
open scoped Matrix

section MatrixLevel
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- A deck for N: row m of P certifies that the puncture at m is payable. -/
structure Deck (N P : Matrix I I ℝ) : Prop where
  nonneg : ∀ m k, 0 ≤ P m k
  diag : ∀ m, P m m = 0
  rows : ∀ m, ∑ k, P m k = 1
  slack : ∀ m j, j ≠ m → (P * N) m j ≤ 0

/-- All conclusions of the matrix-level factorization, with Θ = P * N. -/
structure Factorization (N H P : Matrix I I ℝ) : Prop where
  theta_mul : P * N * H = P
  theta_row : (P * N) *ᵥ (H *ᵥ 1) = fun _ => 1
  diag_pos : ∀ m, 0 < (P * N) m m
  minimum : ∀ z : I → ℝ, (∀ i, 0 ≤ ((P * N) *ᵥ z) i) → ∀ i, 0 ≤ z i
  unit : IsUnit (P * N).det
  inv_nonneg : ∀ i j, 0 ≤ (P * N)⁻¹ i j
  factor : H = (P * N)⁻¹ * P
  kelly : ∀ k, ∑ i, H i k = ∑ m, (∑ i, (P * N)⁻¹ i m) * P m k
  mass : ∑ i, ∑ k, H i k = ∑ i, ∑ m, (P * N)⁻¹ i m

omit [DecidableEq I] in
private theorem ones_apply (H : Matrix I I ℝ) (i : I) : (H *ᵥ 1) i = ∑ k, H i k := by
  simp [Matrix.mulVec, dotProduct]

private theorem split_row (Θ : Matrix I I ℝ) (z : I → ℝ) (i : I) :
    (Θ *ᵥ z) i = Θ i i * z i + ∑ j ∈ univ.erase i, Θ i j * z j := by
  show ∑ j, Θ i j * z j = _
  exact (Finset.add_sum_erase univ (fun j => Θ i j * z j) (mem_univ i)).symm

/-- (a) Θ H = P. -/
theorem theta_mul {N H P : Matrix I I ℝ} (inv : N * H = 1) : P * N * H = P := by
  rw [Matrix.mul_assoc, inv, Matrix.mul_one]

/-- (b) Θ r = 1 with r = H 1. -/
theorem theta_row {N H P : Matrix I I ℝ} (inv : N * H = 1) (deck : Deck N P) :
    (P * N) *ᵥ (H *ᵥ 1) = fun _ => 1 := by
  rw [Matrix.mulVec_mulVec, theta_mul inv]
  funext m
  rw [← deck.rows m]
  simp [Matrix.mulVec, dotProduct]

/-- (c) The diagonal of Θ is positive. -/
theorem diag_pos {N H P : Matrix I I ℝ} (inv : N * H = 1) (deck : Deck N P)
    (rpos : ∀ i, 0 < ∑ k, H i k) (m : I) : 0 < (P * N) m m := by
  have h : ((P * N) *ᵥ (H *ᵥ 1)) m = 1 := congrFun (theta_row inv deck) m
  rw [split_row] at h
  have off : ∑ j ∈ univ.erase m, (P * N) m j * (H *ᵥ 1) j ≤ 0 :=
    Finset.sum_nonpos fun j hj => mul_nonpos_iff.mpr (Or.inr
      ⟨deck.slack m j (ne_of_mem_erase hj), by rw [ones_apply]; exact (rpos j).le⟩)
  have rm : 0 < (H *ᵥ 1) m := by rw [ones_apply]; exact rpos m
  by_contra! hle
  have := mul_nonpos_iff.mpr (Or.inr ⟨hle, rm.le⟩)
  linarith

/-- (d) Minimum principle: Θ z ≥ 0 forces z ≥ 0. -/
theorem minimum {N H P : Matrix I I ℝ} (inv : N * H = 1) (deck : Deck N P)
    (rpos : ∀ i, 0 < ∑ k, H i k) (z : I → ℝ) (hz : ∀ i, 0 ≤ ((P * N) *ᵥ z) i) (a : I) :
    0 ≤ z a := by
  have rp : ∀ j, 0 < (H *ᵥ 1) j := fun j => by rw [ones_apply]; exact rpos j
  obtain ⟨i, _, least⟩ := exists_min_image univ (fun j => z j / (H *ᵥ 1) j) ⟨a, mem_univ a⟩
  let t := z i / (H *ᵥ 1) i
  have atI : t * (H *ᵥ 1) i = z i := div_mul_cancel₀ _ (rp i).ne'
  have bound (j : I) : t * (H *ᵥ 1) j ≤ z j := (le_div_iff₀ (rp j)).mp (least j (mem_univ j))
  by_contra! negative
  have neg : t < 0 :=
    lt_of_le_of_lt (least a (mem_univ a)) (div_neg_of_neg_of_pos negative (rp a))
  have le : ((P * N) *ᵥ z) i ≤ t * ((P * N) *ᵥ (H *ᵥ 1)) i := by
    show ∑ j, (P * N) i j * z j ≤ t * ∑ j, (P * N) i j * (H *ᵥ 1) j
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    by_cases hj : j = i
    · rw [hj, ← atI]
      exact le_of_eq (by ring)
    · calc
        (P * N) i j * z j ≤ (P * N) i j * (t * (H *ᵥ 1) j) :=
          mul_le_mul_of_nonpos_left (bound j) (deck.slack i j hj)
        _ = _ := by ring
  have e : ((P * N) *ᵥ (H *ᵥ 1)) i = 1 := congrFun (theta_row inv deck) i
  rw [e, mul_one] at le
  have := hz i
  linarith

/-- (e) Θ is invertible. -/
theorem theta_unit {N H P : Matrix I I ℝ} (inv : N * H = 1) (deck : Deck N P)
    (rpos : ∀ i, 0 < ∑ k, H i k) : IsUnit (P * N).det := by
  have inj : Function.Injective (P * N).mulVec := by
    intro v u eq
    have hi (i : I) : 0 ≤ (v - u) i :=
      minimum inv deck rpos (v - u) (fun k => by rw [Matrix.mulVec_sub, eq, sub_self]; simp) i
    have lo (i : I) : 0 ≤ (u - v) i :=
      minimum inv deck rpos (u - v) (fun k => by rw [Matrix.mulVec_sub, eq, sub_self]; simp) i
    exact funext fun i => le_antisymm (sub_nonneg.mp (lo i)) (sub_nonneg.mp (hi i))
  exact (Matrix.isUnit_iff_isUnit_det _).mp (Matrix.mulVec_injective_iff_isUnit.mp inj)

/-- (e) Θ⁻¹ ≥ 0. -/
theorem theta_inv_nonneg {N H P : Matrix I I ℝ} (inv : N * H = 1) (deck : Deck N P)
    (rpos : ∀ i, 0 < ∑ k, H i k) (i j : I) : 0 ≤ (P * N)⁻¹ i j := by
  have right := Matrix.mul_nonsing_inv (P * N) (theta_unit inv deck rpos)
  refine minimum inv deck rpos (fun k => (P * N)⁻¹ k j) (fun k => ?_) i
  change 0 ≤ ((P * N) * (P * N)⁻¹) k j
  rw [right, Matrix.one_apply]
  split <;> norm_num

/-- (e) H = Θ⁻¹ P. -/
theorem factor {N H P : Matrix I I ℝ} (inv : N * H = 1) (deck : Deck N P)
    (rpos : ∀ i, 0 < ∑ k, H i k) : H = (P * N)⁻¹ * P := by
  have left := Matrix.nonsing_inv_mul (P * N) (theta_unit inv deck rpos)
  calc
    H = (P * N)⁻¹ * (P * N) * H := by rw [left, Matrix.one_mul]
    _ = (P * N)⁻¹ * P := by rw [Matrix.mul_assoc, theta_mul inv]

/-- (f) Kelly mixture: column sums of H are a nonnegative mixture of deck rows. -/
theorem kelly {N H P : Matrix I I ℝ} (inv : N * H = 1) (deck : Deck N P)
    (rpos : ∀ i, 0 < ∑ k, H i k) (k : I) :
    ∑ i, H i k = ∑ m, (∑ i, (P * N)⁻¹ i m) * P m k := by
  rw [factor inv deck rpos]
  simp only [Matrix.mul_apply]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun m _ => (Finset.sum_mul _ _ _).symm

/-- (f) Total mass of H equals total mass of Θ⁻¹. -/
theorem mass_eq {N H P : Matrix I I ℝ} (inv : N * H = 1) (deck : Deck N P)
    (rpos : ∀ i, 0 < ∑ k, H i k) :
    ∑ i, ∑ k, H i k = ∑ i, ∑ m, (P * N)⁻¹ i m := by
  rw [factor inv deck rpos]
  simp only [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [← Finset.mul_sum, deck.rows m, mul_one]

/-- Matrix level, items (a)–(f) together. -/
theorem factorization {N H P : Matrix I I ℝ} (inv : N * H = 1) (deck : Deck N P)
    (rpos : ∀ i, 0 < ∑ k, H i k) : Factorization N H P :=
  ⟨theta_mul inv, theta_row inv deck, diag_pos inv deck rpos, minimum inv deck rpos,
    theta_unit inv deck rpos, theta_inv_nonneg inv deck rpos, factor inv deck rpos,
    kelly inv deck rpos, mass_eq inv deck rpos⟩

end MatrixLevel

/-- Graph level. At least support (two or more vertices), one payable-puncture
certificate per vertex forms a deck, and the factorization holds. -/
theorem graph_deck {q : ℕ} {G : CH.Digraph} {V : Finset ℕ} {H : Matrix V V ℝ}
    (inv : CommonInverse (realMatrix q G V) H) (small : SmallerSmallRow q V.card)
    (free : QFree G V q) (two : ∃ i j : V, i ≠ j) :
    ∃ P : Matrix V V ℝ, Deck (excess (realMatrix q G V)) P ∧
      Factorization (excess (realMatrix q G V)) H P := by
  obtain ⟨i0, j0, hij⟩ := two
  have each : ∀ m : V, ∃ p : V → ℝ, (∀ i, 0 ≤ p i) ∧ p m = 0 ∧ (∑ i, p i) = 1 ∧
      ∀ i, i ≠ m → (p ᵥ* excess (realMatrix q G V)) i ≤ 0 := by
    intro m
    have ne : V.erase (m : ℕ) ≠ V := fun e =>
      Finset.notMem_erase (m : ℕ) V (by rw [e]; exact m.property)
    have other : ∃ j : V, j ≠ m := by
      by_cases h : m = i0
      · exact ⟨j0, by rw [h]; exact hij.symm⟩
      · exact ⟨i0, Ne.symm h⟩
    obtain ⟨j, hj⟩ := other
    exact certificate m (small.induced free _ (Finset.erase_subset _ _) ne) j hj
  choose P hP using each
  have deck : Deck (excess (realMatrix q G V)) P :=
    ⟨fun m k => (hP m).1 k, fun m => (hP m).2.1, fun m => (hP m).2.2.1,
      fun m j hj => (hP m).2.2.2 j hj⟩
  exact ⟨P, deck, factorization inv.right deck (inverse_row_sum_pos inv)⟩

/-- Tail bound in the flat branch. R' is the centered matrix of E plus the arc a→b. -/
theorem tail_bound {q : ℕ} {E : CH.Digraph} {V : Finset ℕ} (a b : V) (off : E a b = false)
    {w p : ℕ → ℚ} (wp : ∀ i ∈ V, 0 < w i ∧ 0 < p i) (wm : mass V w = 1)
    (wr : ∀ i ∈ V, WeightedSD.row q E V w i = 1) (m : V) (c : V → ℝ) (ct : ∑ i, c i = 1)
    (slack : ∀ j, j ≠ m → (c ᵥ* realMatrix q (insertArc E a b) V) j ≤ 1) :
    (q : ℝ) * (w b : ℝ) * c a ≤
      ((c ᵥ* realMatrix q (insertArc E a b) V) m - 1) * (w m : ℝ) := by
  have hab : ¬ E a b = true := by rw [off]; decide
  have rows : ∀ i : V, (realMatrix q E V *ᵥ fun v : V => (w v : ℝ)) i = 1 := fun i => by
    simpa using realMatrix_rational_rows w 1 wr i
  have rowsNew (i : V) : (realMatrix q (insertArc E a b) V *ᵥ fun v : V => (w v : ℝ)) i =
      1 + if i = a then (q : ℝ) * (w b : ℝ) else 0 := by
    have e (y : V) : realMatrix q (insertArc E a b) V i y * (w y : ℝ) =
        realMatrix q E V i y * (w y : ℝ) +
          (if i = a ∧ y = b then (q : ℝ) else 0) * (w y : ℝ) := by
      rw [← realMatrix_insert_difference (q := q) a b hab i y]; ring
    show ∑ y, realMatrix q (insertArc E a b) V i y * (w y : ℝ) = _
    rw [Finset.sum_congr rfl fun y _ => e y, Finset.sum_add_distrib]
    rw [show ∑ y, realMatrix q E V i y * (w y : ℝ) = 1 from rows i]
    by_cases h : i = a
    · simp [h]
    · simp [h]
  have total : ∑ j, (c ᵥ* realMatrix q (insertArc E a b) V) j * (w j : ℝ) =
      1 + (q : ℝ) * (w b : ℝ) * c a := by
    calc
      ∑ j, (c ᵥ* realMatrix q (insertArc E a b) V) j * (w j : ℝ) =
          dotProduct (c ᵥ* realMatrix q (insertArc E a b) V) (fun v : V => (w v : ℝ)) := rfl
      _ = dotProduct c (realMatrix q (insertArc E a b) V *ᵥ fun v : V => (w v : ℝ)) :=
          (dotProduct_mulVec _ _ _).symm
      _ = ∑ i, c i * (1 + if i = a then (q : ℝ) * (w b : ℝ) else 0) :=
          Finset.sum_congr rfl fun i _ => by rw [rowsNew i]
      _ = ∑ i, c i + ∑ i, (if i = a then c i * ((q : ℝ) * (w b : ℝ)) else 0) := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun i _ => by split_ifs <;> ring
      _ = 1 + (q : ℝ) * (w b : ℝ) * c a := by
          simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, ct]
          ring
  have s1 : (c ᵥ* realMatrix q (insertArc E a b) V) m * (w m : ℝ) +
      ∑ j ∈ univ.erase m, (c ᵥ* realMatrix q (insertArc E a b) V) j * (w j : ℝ) =
      ∑ j, (c ᵥ* realMatrix q (insertArc E a b) V) j * (w j : ℝ) :=
    Finset.add_sum_erase univ
      (fun j => (c ᵥ* realMatrix q (insertArc E a b) V) j * (w j : ℝ)) (mem_univ m)
  have s2 : (w m : ℝ) + ∑ j ∈ univ.erase m, (w j : ℝ) = ∑ j : V, (w j : ℝ) :=
    Finset.add_sum_erase univ (fun j : V => (w j : ℝ)) (mem_univ m)
  have wsum := real_mass_of_rational_probability w wm
  have le : ∑ j ∈ univ.erase m, (c ᵥ* realMatrix q (insertArc E a b) V) j * (w j : ℝ) ≤
      ∑ j ∈ univ.erase m, (w j : ℝ) :=
    Finset.sum_le_sum fun j hj => by
      have sj := slack j (ne_of_mem_erase hj)
      have wj : (0 : ℝ) ≤ (w j : ℝ) := by exact_mod_cast (wp j j.property).1.le
      nlinarith
  nlinarith

/-- Corollary: if c also vanishes at m and is nonnegative, (cR')_m ≤ q, so
q w_b c_a ≤ (q - 1) w_m. -/
theorem tail_bound_zero {q : ℕ} {E : CH.Digraph} {V : Finset ℕ} (a b : V)
    (off : E a b = false) {w p : ℕ → ℚ} (wp : ∀ i ∈ V, 0 < w i ∧ 0 < p i)
    (wm : mass V w = 1) (wr : ∀ i ∈ V, WeightedSD.row q E V w i = 1) (m : V) (c : V → ℝ)
    (cn : ∀ i, 0 ≤ c i) (cm : c m = 0) (ct : ∑ i, c i = 1)
    (slack : ∀ j, j ≠ m → (c ᵥ* realMatrix q (insertArc E a b) V) j ≤ 1) :
    (q : ℝ) * (w b : ℝ) * c a ≤ ((q : ℝ) - 1) * (w m : ℝ) := by
  have tb := tail_bound a b off wp wm wr m c ct slack
  have col : (c ᵥ* realMatrix q (insertArc E a b) V) m ≤ q := by
    show ∑ i, c i * realMatrix q (insertArc E a b) V i m ≤ q
    calc
      _ ≤ ∑ i, c i * (q : ℝ) := Finset.sum_le_sum fun i _ => by
          by_cases h : i = m
          · rw [h, cm, zero_mul, zero_mul]
          · apply mul_le_mul_of_nonneg_left _ (cn i)
            rw [realMatrix_entry]
            split_ifs <;> simp_all
      _ = q := by rw [← Finset.sum_mul, ct, one_mul]
  have wmn : (0 : ℝ) ≤ (w m : ℝ) := by exact_mod_cast (wp m m.property).1.le
  have := mul_le_mul_of_nonneg_right (show (c ᵥ* realMatrix q (insertArc E a b) V) m - 1 ≤
    (q : ℝ) - 1 by linarith) wmn
  linarith

end LeanCH.BR.Closure.DeckFactorization

#print axioms LeanCH.BR.Closure.DeckFactorization.factorization
#print axioms LeanCH.BR.Closure.DeckFactorization.graph_deck
#print axioms LeanCH.BR.Closure.DeckFactorization.tail_bound
#print axioms LeanCH.BR.Closure.DeckFactorization.tail_bound_zero
