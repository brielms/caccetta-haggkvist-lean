import LeanCH.BR.BRWeightedStrictPrime
import LeanCH.BR.BRWeightedInverseComparison
import LeanCH.BR.BRWeightedDeletionThreshold
import checkpoints.shen_extension.SharedArcFlatResponse
import checkpoints.shen_extension.InverseOffDiagonal

/-! Every vertex deletion of a least-support strict graph is payable. Written in the
entries of the centered inverse H, this is a law on the 2x2 minors through each
diagonal entry, and an anti-dominance law for the diagonal. All statements hold for
every order and every cutoff. -/
namespace LeanCH.BR.Closure.PunctureLaw
open Finset Matrix FiniteCutInverse WeightedSD BRq2
open scoped Matrix

section Abstract
variable {I : Type*} [Fintype I] [DecidableEq I]

private theorem recover {N H : Matrix I I ℝ} (inv : N * H = 1) (m : I) (p : I → ℝ) (k : I) :
    p k = (p ᵥ* N) m * H m k + ∑ i ∈ univ.erase m, (p ᵥ* N) i * H i k := by
  have back : (p ᵥ* N) ᵥ* H = p := by rw [vecMul_vecMul, inv, vecMul_one]
  calc
    p k = ((p ᵥ* N) ᵥ* H) k := by rw [back]
    _ = ∑ i, (p ᵥ* N) i * H i k := rfl
    _ = _ := (Finset.add_sum_erase univ (fun i => (p ᵥ* N) i * H i k) (mem_univ m)).symm

/-- Exact identity. A vector p vanishing at m pairs its own column slacks -(pN)_i with
the minors of H through (m,m); the result is p_j H_mm. No sign hypothesis is used. -/
theorem identity {N H : Matrix I I ℝ} (inv : N * H = 1) (m : I) (p : I → ℝ)
    (pm : p m = 0) (j : I) :
    ∑ i ∈ univ.erase m, (-(p ᵥ* N) i) * (H i m * H m j - H i j * H m m) = p j * H m m := by
  have hm := recover inv m p m
  have hj := recover inv m p j
  rw [pm] at hm
  have expand : ∑ i ∈ univ.erase m, (-(p ᵥ* N) i) * (H i m * H m j - H i j * H m m) =
      -(∑ i ∈ univ.erase m, (p ᵥ* N) i * H i m) * H m j +
        (∑ i ∈ univ.erase m, (p ᵥ* N) i * H i j) * H m m := by
    rw [neg_mul, Finset.sum_mul, Finset.sum_mul, ← Finset.sum_neg_distrib,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [expand]
  linear_combination (H m j) * hm - (H m m) * hj

/-- The same identity summed over the columns: the minors become comparisons of the
diagonal with its column, each scaled by the row sums of H. -/
theorem row_sum_identity {N H : Matrix I I ℝ} (inv : N * H = 1) (m : I) (p : I → ℝ)
    (pm : p m = 0) :
    ∑ i ∈ univ.erase m,
        (-(p ᵥ* N) i) * (H i m * (∑ k, H m k) - H m m * ∑ k, H i k) =
      (∑ k, p k) * H m m := by
  calc
    _ = ∑ i ∈ univ.erase m, ∑ j, (-(p ᵥ* N) i) * (H i m * H m j - H i j * H m m) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      have e1 : ∑ j, H i m * H m j = H i m * ∑ k, H m k := (Finset.mul_sum _ _ _).symm
      have e2 : ∑ j, H i j * H m m = (∑ k, H i k) * H m m := (Finset.sum_mul _ _ _).symm
      rw [← Finset.mul_sum, Finset.sum_sub_distrib, e1, e2]
      ring
    _ = ∑ j, ∑ i ∈ univ.erase m, (-(p ᵥ* N) i) * (H i m * H m j - H i j * H m m) :=
      Finset.sum_comm
    _ = ∑ j, p j * H m m := Finset.sum_congr rfl fun j _ => identity inv m p pm j
    _ = _ := (Finset.sum_mul _ _ _).symm

/-- Column form. If the puncture at m has a certificate, then in every other column j
some row i has a nonnegative minor: H_ij H_mm ≤ H_im H_mj. -/
theorem column {N H : Matrix I I ℝ} (inv : N * H = 1) (hn : ∀ i j, 0 ≤ H i j)
    (m : I) (p : I → ℝ) (pn : ∀ i, 0 ≤ p i) (pm : p m = 0)
    (slack : ∀ i, i ≠ m → (p ᵥ* N) i ≤ 0) (live : ∃ i, 0 < p i) (j : I) :
    ∃ i, i ≠ m ∧ H i j * H m m ≤ H i m * H m j := by
  by_contra! no
  have id := identity inv m p pm j
  have term (i : I) (hi : i ∈ univ.erase m) :
      (-(p ᵥ* N) i) * (H i m * H m j - H i j * H m m) ≤ 0 :=
    mul_nonpos_iff.mpr (Or.inl ⟨neg_nonneg.mpr (slack i (ne_of_mem_erase hi)),
      (sub_neg.mpr (no i (ne_of_mem_erase hi))).le⟩)
  have total : ∑ i ∈ univ.erase m, (-(p ᵥ* N) i) * (H i m * H m j - H i j * H m m) = 0 :=
    le_antisymm (Finset.sum_nonpos term) (id ▸ mul_nonneg (pn j) (hn m m))
  have each := (Finset.sum_eq_zero_iff_of_nonpos term).mp total
  have rz (i : I) (hi : i ≠ m) : (p ᵥ* N) i = 0 := by
    rcases mul_eq_zero.mp (each i (mem_erase.mpr ⟨hi, mem_univ i⟩)) with h | h
    · exact neg_eq_zero.mp h
    · exact absurd h (sub_neg.mpr (no i hi)).ne
  have only (k : I) : p k = (p ᵥ* N) m * H m k := by
    rw [recover inv m p k,
      Finset.sum_eq_zero fun i hi => by rw [rz i (ne_of_mem_erase hi), zero_mul], add_zero]
  obtain ⟨i0, hi0⟩ := live
  have i0m : i0 ≠ m := fun e => by rw [e, pm] at hi0; exact lt_irrefl _ hi0
  have rm : (p ᵥ* N) m ≠ 0 := fun z => by
    rw [only i0, z, zero_mul] at hi0; exact lt_irrefl _ hi0
  have hmm : H m m = 0 := by
    have z : (p ᵥ* N) m * H m m = 0 := by rw [← only m, pm]
    exact (mul_eq_zero.mp z).resolve_left rm
  have bad := no i0 i0m
  rw [hmm, mul_zero] at bad
  exact (mul_nonneg (hn i0 m) (hn m j)).not_gt bad

/-- Anti-dominance. Scale every row of H by its row sum. Then the diagonal entry at m
is strictly below some other entry of its own column. -/
theorem anti_dominance {N H : Matrix I I ℝ} (inv : N * H = 1) (hn : ∀ i j, 0 ≤ H i j)
    (m : I) (p : I → ℝ) (pm : p m = 0) (total : ∑ k, p k = 1)
    (slack : ∀ i, i ≠ m → (p ᵥ* N) i ≤ 0) (rpos : 0 < ∑ k, H m k)
    (other : ∃ i, i ≠ m ∧ 0 < H i m) :
    ∃ i, i ≠ m ∧ H m m * (∑ k, H i k) < H i m * ∑ k, H m k := by
  by_cases z : H m m = 0
  · obtain ⟨i, hi, pos⟩ := other
    exact ⟨i, hi, by rw [z, zero_mul]; exact mul_pos pos rpos⟩
  · have hmm : 0 < H m m := lt_of_le_of_ne (hn m m) (Ne.symm z)
    have id := row_sum_identity inv m p pm
    rw [total, one_mul] at id
    by_contra! no
    have le : ∑ i ∈ univ.erase m,
        (-(p ᵥ* N) i) * (H i m * (∑ k, H m k) - H m m * ∑ k, H i k) ≤ 0 :=
      Finset.sum_nonpos fun i hi => mul_nonpos_iff.mpr (Or.inl
        ⟨neg_nonneg.mpr (slack i (ne_of_mem_erase hi)),
          sub_nonpos.mpr (no i (ne_of_mem_erase hi))⟩)
    linarith

end Abstract

/-- A payable puncture at m, as a vector on the whole support that vanishes at m. -/
theorem certificate {q : ℕ} {G : CH.Digraph} {V : Finset ℕ} (m : V)
    (small : SmallRow q G (V.erase m)) (j : V) (hj : j ≠ m) :
    ∃ p : V → ℝ, (∀ i, 0 ≤ p i) ∧ p m = 0 ∧ (∑ i, p i) = 1 ∧
      ∀ i, i ≠ m → (p ᵥ* excess (realMatrix q G V)) i ≤ 0 := by
  classical
  have jU : (j : ℕ) ∈ V.erase m := mem_erase.mpr ⟨fun e => hj (Subtype.ext e), j.property⟩
  obtain ⟨d, hd⟩ := realDual_of_smallRow small ⟨j, jU⟩
  let P : ℕ → ℝ := fun v => if v = (m : ℕ) then 0 else d v
  let p : V → ℝ := fun i => P i
  have Pm : P m = 0 := by simp [P]
  have off (v : ℕ) (hv : v ∈ V.erase m) : P v = d v := by simp [P, (mem_erase.mp hv).1]
  have pn (i : V) : 0 ≤ p i := by
    by_cases h : (i : ℕ) = m
    · have z : p i = 0 := by
        show P (i : ℕ) = 0
        rw [h]; exact Pm
      rw [z]
    · rw [show p i = d i from off i (mem_erase.mpr ⟨h, i.property⟩)]
      exact hd.nonneg i (mem_erase.mpr ⟨h, i.property⟩)
  have total : ∑ i : V, p i = 1 := by
    have e : ∑ i : V, p i = ∑ v ∈ V, P v := Finset.sum_coe_sort V P
    rw [e, ← Finset.add_sum_erase V P m.property, Pm, zero_add]
    exact (Finset.sum_congr rfl off).trans hd.normalized
  have slack (i : V) (hi : i ≠ m) : (p ᵥ* excess (realMatrix q G V)) i ≤ 0 := by
    have iU : (i : ℕ) ∈ V.erase m := mem_erase.mpr ⟨fun e => hi (Subtype.ext e), i.property⟩
    have c : (p ᵥ* realMatrix q G V) i = realCol q G V P i := realMatrix_col q G V P i
    have s : (∑ v ∈ V, if G v i = true then P v else 0) =
        ∑ v ∈ V.erase m, if G v i = true then d v else 0 := by
      have z : (if G m i = true then P m else 0) = 0 := by simp [Pm]
      calc
        (∑ v ∈ V, if G v i = true then P v else 0) =
            (if G m i = true then P m else 0) +
              ∑ v ∈ V.erase m, if G v i = true then P v else 0 :=
          (Finset.add_sum_erase V (fun v => if G v i = true then P v else 0) m.property).symm
        _ = _ := by
          rw [z, zero_add]
          exact Finset.sum_congr rfl fun v hv => by rw [off v hv]
    have e : realCol q G V P i = realCol q G (V.erase m) d i := by
      unfold realCol realInW
      rw [off i iU, s]
    rw [vecMul_excess, total, sub_nonpos, c, e]
    exact hd.columns i iU
  exact ⟨p, pn, by simpa [p] using Pm, total, slack⟩

/-- Graph form. One payable puncture at m gives the column law at m. -/
theorem graph_column {q : ℕ} {G : CH.Digraph} {V : Finset ℕ} {H : Matrix V V ℝ}
    (inv : CommonInverse (realMatrix q G V) H) (m : V)
    (small : SmallRow q G (V.erase m)) (j : V) (hj : j ≠ m) :
    ∃ i : V, i ≠ m ∧ H i j * H m m ≤ H i m * H m j := by
  obtain ⟨p, pn, pm, total, slack⟩ := certificate m small j hj
  have live : ∃ i, 0 < p i := by
    by_contra! none
    have : ∑ i : V, p i ≤ 0 := Finset.sum_nonpos fun i _ => none i
    linarith
  exact column inv.right inv.nonneg m p pn pm slack live j

/-- Row form, from the reversed graph and the transposed inverse. -/
theorem graph_row {q : ℕ} {G : CH.Digraph} {V : Finset ℕ} {H : Matrix V V ℝ}
    (inv : CommonInverse (realMatrix q G V) H) (m : V)
    (small : SmallRow q (fun a b => G b a) (V.erase m)) (j : V) (hj : j ≠ m) :
    ∃ i : V, i ≠ m ∧ H j i * H m m ≤ H j m * H m i := by
  obtain ⟨i, hi, h⟩ := graph_column (commonInverse_reverse inv) m small j hj
  have h' : H j i * H m m ≤ H m i * H j m := h
  exact ⟨i, hi, by rw [mul_comm (H j m)]; exact h'⟩

/-- Column anti-dominance on a graph: with rows scaled by their sums, the diagonal
entry at m is strictly below another entry of column m. -/
theorem graph_anti_column {q : ℕ} (hq : 2 ≤ q) {G : CH.Digraph} {V : Finset ℕ}
    {H : Matrix V V ℝ} (inv : CommonInverse (realMatrix q G V) H) (m : V)
    (small : SmallRow q G (V.erase m)) (j : V) (hj : j ≠ m) :
    ∃ i : V, i ≠ m ∧ H m m * (∑ k, H i k) < H i m * ∑ k, H m k := by
  obtain ⟨p, _, pm, total, slack⟩ := certificate m small j hj
  exact anti_dominance inv.right inv.nonneg m p pm total slack (inverse_row_sum_pos inv m)
    ⟨j, hj, InverseOffDiagonal.graph_positive hq inv hj⟩

/-- Row anti-dominance: with columns scaled by their sums, the diagonal entry at m is
strictly below another entry of row m. -/
theorem graph_anti_row {q : ℕ} (hq : 2 ≤ q) {G : CH.Digraph} {V : Finset ℕ}
    {H : Matrix V V ℝ} (inv : CommonInverse (realMatrix q G V) H) (m : V)
    (small : SmallRow q (fun a b => G b a) (V.erase m)) (j : V) (hj : j ≠ m) :
    ∃ i : V, i ≠ m ∧ H m m * (∑ k, H k i) < H m i * ∑ k, H k m :=
  graph_anti_column hq (commonInverse_reverse inv) m small j hj

/-- At least support both minor laws hold at every vertex of every q-free graph that
has a centered inverse. Only the induction hypothesis on smaller orders is used. -/
theorem least_support {q : ℕ} {G : CH.Digraph} {V : Finset ℕ} {H : Matrix V V ℝ}
    (inv : CommonInverse (realMatrix q G V) H) (small : SmallerSmallRow q V.card)
    (free : QFree G V q) (m j : V) (hj : j ≠ m) :
    (∃ i : V, i ≠ m ∧ H i j * H m m ≤ H i m * H m j) ∧
      ∃ i : V, i ≠ m ∧ H j i * H m m ≤ H j m * H m i := by
  have ne : V.erase (m : ℕ) ≠ V := fun e =>
    Finset.notMem_erase (m : ℕ) V (by rw [e]; exact m.property)
  exact ⟨graph_column inv m (small.induced free _ (Finset.erase_subset _ _) ne) j hj,
    graph_row inv m (small.reverse_induced free _ (Finset.erase_subset _ _) ne) j hj⟩

/-- At least support no diagonal entry of the centered inverse dominates: scaled by
row sums it is strictly below its column, scaled by column sums strictly below its row. -/
theorem least_support_anti {q : ℕ} (hq : 2 ≤ q) {G : CH.Digraph} {V : Finset ℕ}
    {H : Matrix V V ℝ} (inv : CommonInverse (realMatrix q G V) H)
    (small : SmallerSmallRow q V.card) (free : QFree G V q) (m j : V) (hj : j ≠ m) :
    (∃ i : V, i ≠ m ∧ H m m * (∑ k, H i k) < H i m * ∑ k, H m k) ∧
      ∃ i : V, i ≠ m ∧ H m m * (∑ k, H k i) < H m i * ∑ k, H k m := by
  have ne : V.erase (m : ℕ) ≠ V := fun e =>
    Finset.notMem_erase (m : ℕ) V (by rw [e]; exact m.property)
  exact ⟨graph_anti_column hq inv m (small.induced free _ (Finset.erase_subset _ _) ne) j hj,
    graph_anti_row hq inv m (small.reverse_induced free _ (Finset.erase_subset _ _) ne) j hj⟩

open SharedArcFlatResponse in
/-- Flat branch. For a flat old graph and a safe insertion a→b the four-index test T
obeys both minor laws at every label m, with every entry computed from the old graph. -/
theorem tensor {q : ℕ} (hq : 2 ≤ q) {E : CH.Digraph} {V : Finset ℕ}
    (small : SmallerSmallRow q V.card) (a b : V) (off : E a b = false)
    (safe : QFree (insertArc E a b) V q) {w p : ℕ → ℚ}
    (wp : ∀ i ∈ V, 0 < w i ∧ 0 < p i) (wm : mass V w = 1)
    (wr : ∀ i ∈ V, WeightedSD.row q E V w i = 1) (pc : ∀ i ∈ V, WeightedSD.col q E V p i = 1)
    (m j : V) (hj : j ≠ m) :
    let T := test (realMatrix q E V)⁻¹ (fun i : V => (w i : ℝ)) (fun i : V => (p i : ℝ)) q a b
    (∃ i : V, i ≠ m ∧ T i j * T m m ≤ T i m * T m j) ∧
      ∃ i : V, i ≠ m ∧ T j i * T m m ≤ T j m * T m i := by
  intro T
  obtain ⟨H, inv, eq⟩ := inverse_test hq small a b off safe wp wm wr pc
  have eqT : ∀ v k : V, T v k = ((q : ℝ) * (p a : ℝ) * (w b : ℝ)) * H v k := eq
  obtain ⟨⟨i, hi, c⟩, ⟨i', hi', r⟩⟩ := least_support inv small safe m j hj
  have pa : (0 : ℝ) ≤ (p a : ℝ) := by exact_mod_cast (wp a a.property).2.le
  have wb : (0 : ℝ) ≤ (w b : ℝ) := by exact_mod_cast (wp b b.property).1.le
  have sn : 0 ≤ (q : ℝ) * (p a : ℝ) * (w b : ℝ) :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) pa) wb
  refine ⟨⟨i, hi, ?_⟩, ⟨i', hi', ?_⟩⟩
  · rw [eqT i j, eqT m m, eqT i m, eqT m j]
    have := mul_le_mul_of_nonneg_left c (mul_nonneg sn sn)
    nlinarith [this]
  · rw [eqT j i', eqT m m, eqT j m, eqT m i']
    have := mul_le_mul_of_nonneg_left r (mul_nonneg sn sn)
    nlinarith [this]

open SharedArcFlatResponse in
/-- At the tail a the column a of T is p_a w. So in every column the weighted entry of
row a is at least the least weighted entry of the other rows. -/
theorem tail_row {q : ℕ} (hq : 2 ≤ q) {E : CH.Digraph} {V : Finset ℕ}
    (small : SmallerSmallRow q V.card) (a b : V) (off : E a b = false)
    (safe : QFree (insertArc E a b) V q) {w p : ℕ → ℚ}
    (wp : ∀ i ∈ V, 0 < w i ∧ 0 < p i) (wm : mass V w = 1)
    (wr : ∀ i ∈ V, WeightedSD.row q E V w i = 1) (pc : ∀ i ∈ V, WeightedSD.col q E V p i = 1)
    (j : V) (hj : j ≠ a) :
    let T := test (realMatrix q E V)⁻¹ (fun i : V => (w i : ℝ)) (fun i : V => (p i : ℝ)) q a b
    ∃ i : V, i ≠ a ∧ T i j * (w a : ℝ) ≤ (w i : ℝ) * T a j := by
  intro T
  obtain ⟨i, hi, h⟩ := (tensor hq small a b off safe wp wm wr pc a j hj).1
  have col (v : V) : T v a = (w v : ℝ) * (p a : ℝ) := by simp only [T, test]; ring
  have pa : (0 : ℝ) < (p a : ℝ) := by exact_mod_cast (wp a a.property).2
  refine ⟨i, hi, ?_⟩
  have h' : T i j * ((w a : ℝ) * (p a : ℝ)) ≤ (w i : ℝ) * (p a : ℝ) * T a j := by
    rw [← col a, ← col i]; exact h
  have : (T i j * (w a : ℝ)) * (p a : ℝ) ≤ ((w i : ℝ) * T a j) * (p a : ℝ) := by
    nlinarith [h']
  exact le_of_mul_le_mul_right this pa

open SharedArcFlatResponse in
/-- At the head b the row b of T is w_b p. So in every row the weighted entry of
column b is at least the least weighted entry of the other columns. -/
theorem head_column {q : ℕ} (hq : 2 ≤ q) {E : CH.Digraph} {V : Finset ℕ}
    (small : SmallerSmallRow q V.card) (a b : V) (off : E a b = false)
    (safe : QFree (insertArc E a b) V q) {w p : ℕ → ℚ}
    (wp : ∀ i ∈ V, 0 < w i ∧ 0 < p i) (wm : mass V w = 1)
    (wr : ∀ i ∈ V, WeightedSD.row q E V w i = 1) (pc : ∀ i ∈ V, WeightedSD.col q E V p i = 1)
    (j : V) (hj : j ≠ b) :
    let T := test (realMatrix q E V)⁻¹ (fun i : V => (w i : ℝ)) (fun i : V => (p i : ℝ)) q a b
    ∃ i : V, i ≠ b ∧ T j i * (p b : ℝ) ≤ T j b * (p i : ℝ) := by
  intro T
  obtain ⟨i, hi, h⟩ := (tensor hq small a b off safe wp wm wr pc b j hj).2
  have rowb (k : V) : T b k = (w b : ℝ) * (p k : ℝ) := by simp only [T, test]; ring
  have wb : (0 : ℝ) < (w b : ℝ) := by exact_mod_cast (wp b b.property).1
  refine ⟨i, hi, ?_⟩
  have h' : T j i * ((w b : ℝ) * (p b : ℝ)) ≤ T j b * ((w b : ℝ) * (p i : ℝ)) := by
    rw [← rowb b, ← rowb i]; exact h
  have : (T j i * (p b : ℝ)) * (w b : ℝ) ≤ (T j b * (p i : ℝ)) * (w b : ℝ) := by
    nlinarith [h']
  exact le_of_mul_le_mul_right this wb

open SharedArcFlatResponse in
/-- No dominant diagonal in the flat tensor, column side. Divide row v of T by w_v.
For every label m other than the tail, the diagonal entry is at most another entry of
column m. At m = b this reads T(i,b) ≥ w_i p_b for some i. -/
theorem diagonal_column {q : ℕ} (hq : 2 ≤ q) {E : CH.Digraph} {V : Finset ℕ}
    (small : SmallerSmallRow q V.card) (a b : V) (off : E a b = false)
    (safe : QFree (insertArc E a b) V q) {w p : ℕ → ℚ}
    (wp : ∀ i ∈ V, 0 < w i ∧ 0 < p i) (wm : mass V w = 1)
    (wr : ∀ i ∈ V, WeightedSD.row q E V w i = 1) (pc : ∀ i ∈ V, WeightedSD.col q E V p i = 1)
    (m : V) (hm : m ≠ a) :
    let T := test (realMatrix q E V)⁻¹ (fun i : V => (w i : ℝ)) (fun i : V => (p i : ℝ)) q a b
    ∃ i : V, i ≠ m ∧ T m m * (w i : ℝ) ≤ T i m * (w m : ℝ) := by
  intro T
  obtain ⟨i, hi, h⟩ := (tensor hq small a b off safe wp wm wr pc m a (Ne.symm hm)).1
  have col (v : V) : T v a = (w v : ℝ) * (p a : ℝ) := by simp only [T, test]; ring
  have pa : (0 : ℝ) < (p a : ℝ) := by exact_mod_cast (wp a a.property).2
  refine ⟨i, hi, ?_⟩
  have h' : (w i : ℝ) * (p a : ℝ) * T m m ≤ T i m * ((w m : ℝ) * (p a : ℝ)) := by
    rw [← col i, ← col m]; exact h
  have : (T m m * (w i : ℝ)) * (p a : ℝ) ≤ (T i m * (w m : ℝ)) * (p a : ℝ) := by
    nlinarith [h']
  exact le_of_mul_le_mul_right this pa

open SharedArcFlatResponse in
/-- No dominant diagonal in the flat tensor, row side. Divide column k of T by p_k.
For every label m other than the head, the diagonal entry is at most another entry of
row m. At m = a this reads T(a,i) ≥ w_a p_i for some i. -/
theorem diagonal_row {q : ℕ} (hq : 2 ≤ q) {E : CH.Digraph} {V : Finset ℕ}
    (small : SmallerSmallRow q V.card) (a b : V) (off : E a b = false)
    (safe : QFree (insertArc E a b) V q) {w p : ℕ → ℚ}
    (wp : ∀ i ∈ V, 0 < w i ∧ 0 < p i) (wm : mass V w = 1)
    (wr : ∀ i ∈ V, WeightedSD.row q E V w i = 1) (pc : ∀ i ∈ V, WeightedSD.col q E V p i = 1)
    (m : V) (hm : m ≠ b) :
    let T := test (realMatrix q E V)⁻¹ (fun i : V => (w i : ℝ)) (fun i : V => (p i : ℝ)) q a b
    ∃ i : V, i ≠ m ∧ T m m * (p i : ℝ) ≤ T m i * (p m : ℝ) := by
  intro T
  obtain ⟨i, hi, h⟩ := (tensor hq small a b off safe wp wm wr pc m b (Ne.symm hm)).2
  have rowb (k : V) : T b k = (w b : ℝ) * (p k : ℝ) := by simp only [T, test]; ring
  have wb : (0 : ℝ) < (w b : ℝ) := by exact_mod_cast (wp b b.property).1
  refine ⟨i, hi, ?_⟩
  have h' : (w b : ℝ) * (p i : ℝ) * T m m ≤ (w b : ℝ) * (p m : ℝ) * T m i := by
    rw [← rowb i, ← rowb m]; exact h
  have : (T m m * (p i : ℝ)) * (w b : ℝ) ≤ (T m i * (p m : ℝ)) * (w b : ℝ) := by
    nlinarith [h']
  exact le_of_mul_le_mul_right this wb

/-! ## The flat graph itself

The old graph E is flat: R w = 1, p R = 1. Its centered matrix is singular, so there is
no inverse H. The punctures of E are still payable, and the same elimination gives an
additive law on L = R⁻¹, with no inserted arc anywhere in the statement. -/

section Flat
variable {I : Type*} [Fintype I] [DecidableEq I]

private theorem flat_recover {R L : Matrix I I ℝ} (inv : R * L = 1) (p c : I → ℝ)
    (cols : ∀ j, (p ᵥ* R) j = 1) (m k : I) :
    c k = p k + (((c ᵥ* R) m - 1) * L m k +
      ∑ i ∈ univ.erase m, ((c ᵥ* R) i - 1) * L i k) := by
  have cb : (c ᵥ* R) ᵥ* L = c := by rw [vecMul_vecMul, inv, vecMul_one]
  have pb : (p ᵥ* R) ᵥ* L = p := by rw [vecMul_vecMul, inv, vecMul_one]
  have ck : c k = ∑ i, (c ᵥ* R) i * L i k := by
    calc
      c k = ((c ᵥ* R) ᵥ* L) k := by rw [cb]
      _ = _ := rfl
  have pk : p k = ∑ i, L i k := by
    calc
      p k = ((p ᵥ* R) ᵥ* L) k := by rw [pb]
      _ = ∑ i, (p ᵥ* R) i * L i k := rfl
      _ = _ := Finset.sum_congr rfl fun i _ => by rw [cols i, one_mul]
  calc
    c k = ∑ i, (c ᵥ* R) i * L i k := ck
    _ = ∑ i, L i k + ∑ i, ((c ᵥ* R) i - 1) * L i k := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    _ = _ := by
      rw [pk, Finset.add_sum_erase univ (fun i => ((c ᵥ* R) i - 1) * L i k) (mem_univ m)]

private theorem flat_weight {R : Matrix I I ℝ} (w c : I → ℝ)
    (rows : ∀ i, (R *ᵥ w) i = 1) (wm : ∑ i, w i = 1) (ct : ∑ i, c i = 1) (m : I) :
    ((c ᵥ* R) m - 1) * w m + ∑ i ∈ univ.erase m, ((c ᵥ* R) i - 1) * w i = 0 := by
  rw [Finset.add_sum_erase univ (fun i => ((c ᵥ* R) i - 1) * w i) (mem_univ m)]
  have e : ∑ i, (c ᵥ* R) i * w i = 1 := by
    calc
      ∑ i, (c ᵥ* R) i * w i = dotProduct (c ᵥ* R) w := rfl
      _ = dotProduct c (R *ᵥ w) := (dotProduct_mulVec c R w).symm
      _ = ∑ i, c i * (R *ᵥ w) i := rfl
      _ = ∑ i, c i := Finset.sum_congr rfl fun i _ => by rw [rows i, mul_one]
      _ = 1 := ct
  calc
    ∑ i, ((c ᵥ* R) i - 1) * w i = ∑ i, (c ᵥ* R) i * w i - ∑ i, w i := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    _ = 0 := by rw [e, wm, sub_self]

/-- Exact identity on a flat matrix. A vector c vanishing at m pairs its column slacks
with the additive second differences of L through (m,m), weighted by the flat laws. -/
theorem flat_identity {R L : Matrix I I ℝ} (inv : R * L = 1) (w p c : I → ℝ)
    (rows : ∀ i, (R *ᵥ w) i = 1) (cols : ∀ j, (p ᵥ* R) j = 1) (wm : ∑ i, w i = 1)
    (ct : ∑ i, c i = 1) (m : I) (cm : c m = 0) (j : I) :
    ∑ i ∈ univ.erase m, (-((c ᵥ* R) i - 1)) *
        (L i m * (w m * p j) + L m j * (w i * p m) - L i j * (w m * p m) -
          L m m * (w i * p j)) = c j * (w m * p m) := by
  have h1 := flat_recover inv p c cols m m
  have h2 := flat_recover inv p c cols m j
  have h3 := flat_weight w c rows wm ct m
  rw [cm] at h1
  have expand : ∑ i ∈ univ.erase m, (-((c ᵥ* R) i - 1)) *
        (L i m * (w m * p j) + L m j * (w i * p m) - L i j * (w m * p m) -
          L m m * (w i * p j)) =
      -(∑ i ∈ univ.erase m, ((c ᵥ* R) i - 1) * L i m) * (w m * p j) -
        (∑ i ∈ univ.erase m, ((c ᵥ* R) i - 1) * w i) * (L m j * p m) +
        (∑ i ∈ univ.erase m, ((c ᵥ* R) i - 1) * L i j) * (w m * p m) +
        (∑ i ∈ univ.erase m, ((c ᵥ* R) i - 1) * w i) * (L m m * p j) := by
    rw [neg_mul, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul,
      ← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [expand]
  linear_combination (w m * p j) * h1 - (w m * p m) * h2 +
    (L m m * p j - L m j * p m) * h3

/-- Additive law. In every column j some row i has
L_ij w_m p_m + L_mm w_i p_j ≤ L_mj w_i p_m + L_im w_m p_j. -/
theorem flat_column {R L : Matrix I I ℝ} (inv : R * L = 1) (w p c : I → ℝ)
    (rows : ∀ i, (R *ᵥ w) i = 1) (cols : ∀ j, (p ᵥ* R) j = 1) (wm : ∑ i, w i = 1)
    (ct : ∑ i, c i = 1) (m : I) (cm : c m = 0) (cn : ∀ i, 0 ≤ c i)
    (slack : ∀ i, i ≠ m → (c ᵥ* R) i ≤ 1) (wpos : 0 < w m) (ppos : 0 < p m) (j : I) :
    ∃ i, i ≠ m ∧ L i j * (w m * p m) + L m m * (w i * p j) ≤
      L m j * (w i * p m) + L i m * (w m * p j) := by
  by_contra! no
  have id := flat_identity inv w p c rows cols wm ct m cm j
  have term (i : I) (hi : i ∈ univ.erase m) : (-((c ᵥ* R) i - 1)) *
      (L i m * (w m * p j) + L m j * (w i * p m) - L i j * (w m * p m) -
        L m m * (w i * p j)) ≤ 0 :=
    mul_nonpos_iff.mpr (Or.inl ⟨by linarith [slack i (ne_of_mem_erase hi)],
      by linarith [no i (ne_of_mem_erase hi)]⟩)
  have total : ∑ i ∈ univ.erase m, (-((c ᵥ* R) i - 1)) *
      (L i m * (w m * p j) + L m j * (w i * p m) - L i j * (w m * p m) -
        L m m * (w i * p j)) = 0 :=
    le_antisymm (Finset.sum_nonpos term)
      (id ▸ mul_nonneg (cn j) (mul_nonneg wpos.le ppos.le))
  have each := (Finset.sum_eq_zero_iff_of_nonpos term).mp total
  have rz (i : I) (hi : i ≠ m) : (c ᵥ* R) i - 1 = 0 := by
    rcases mul_eq_zero.mp (each i (mem_erase.mpr ⟨hi, mem_univ i⟩)) with h | h
    · exact neg_eq_zero.mp h
    · exact absurd h (ne_of_lt (by linarith [no i hi]))
  have h1 := flat_recover inv p c cols m m
  have h3 := flat_weight w c rows wm ct m
  rw [cm, Finset.sum_eq_zero fun i hi => by rw [rz i (ne_of_mem_erase hi), zero_mul],
    add_zero] at h1
  rw [Finset.sum_eq_zero fun i hi => by rw [rz i (ne_of_mem_erase hi), zero_mul],
    add_zero] at h3
  have t0 : (c ᵥ* R) m - 1 = 0 := (mul_eq_zero.mp h3).resolve_right wpos.ne'
  rw [t0, zero_mul, add_zero] at h1
  exact ppos.ne h1

/-- Flat anti-dominance. Divide row i of L by w_i. The diagonal entry at m is strictly
below another entry of its own column. -/
theorem flat_anti {R L : Matrix I I ℝ} (inv : R * L = 1) (w p c : I → ℝ)
    (rows : ∀ i, (R *ᵥ w) i = 1) (cols : ∀ j, (p ᵥ* R) j = 1) (wm : ∑ i, w i = 1)
    (ct : ∑ i, c i = 1) (m : I) (cm : c m = 0)
    (slack : ∀ i, i ≠ m → (c ᵥ* R) i ≤ 1) (wpos : 0 < w m) (ppos : 0 < p m) :
    ∃ i, i ≠ m ∧ L m m * w i < L i m * w m := by
  have h1 := flat_recover inv p c cols m m
  have h3 := flat_weight w c rows wm ct m
  rw [cm] at h1
  have id : ∑ i ∈ univ.erase m, (-((c ᵥ* R) i - 1)) * (L i m * w m - L m m * w i) =
      w m * p m := by
    have expand : ∑ i ∈ univ.erase m, (-((c ᵥ* R) i - 1)) * (L i m * w m - L m m * w i) =
        -(∑ i ∈ univ.erase m, ((c ᵥ* R) i - 1) * L i m) * w m +
          (∑ i ∈ univ.erase m, ((c ᵥ* R) i - 1) * w i) * L m m := by
      rw [neg_mul, Finset.sum_mul, Finset.sum_mul, ← Finset.sum_neg_distrib,
        ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [expand]
    linear_combination (w m) * h1 + (L m m) * h3
  by_contra! no
  have le : ∑ i ∈ univ.erase m, (-((c ᵥ* R) i - 1)) * (L i m * w m - L m m * w i) ≤ 0 :=
    Finset.sum_nonpos fun i hi => mul_nonpos_iff.mpr (Or.inl
      ⟨by linarith [slack i (ne_of_mem_erase hi)], by linarith [no i (ne_of_mem_erase hi)]⟩)
  have pos : 0 < w m * p m := mul_pos wpos ppos
  linarith

end Flat

open SharedArcFlatResponse in
/-- Flat graph, column side. For a flat q-free graph with a payable puncture at m:
the additive law in every column j, and strict anti-dominance of the diagonal of L. -/
theorem flat_laws {q : ℕ} (hq : 2 ≤ q) {E : CH.Digraph} {V : Finset ℕ} {w p : ℕ → ℚ}
    (wp : ∀ i ∈ V, 0 < w i ∧ 0 < p i) (wm : mass V w = 1)
    (wr : ∀ i ∈ V, WeightedSD.row q E V w i = 1) (pc : ∀ i ∈ V, WeightedSD.col q E V p i = 1)
    (m : V) (small : SmallRow q E (V.erase m)) (j : V) (hj : j ≠ m) :
    let L := (realMatrix q E V)⁻¹
    (∃ i : V, i ≠ m ∧ L i j * ((w m : ℝ) * (p m : ℝ)) + L m m * ((w i : ℝ) * (p j : ℝ)) ≤
        L m j * ((w i : ℝ) * (p m : ℝ)) + L i m * ((w m : ℝ) * (p j : ℝ))) ∧
      ∃ i : V, i ≠ m ∧ L m m * (w i : ℝ) < L i m * (w m : ℝ) := by
  intro L
  have inv : realMatrix q E V * L = 1 := Matrix.mul_nonsing_inv _ (matrix_unit hq E V)
  obtain ⟨c, cn, cm, ct, slack⟩ := certificate m small j hj
  have rows : ∀ i : V, (realMatrix q E V *ᵥ fun v : V => (w v : ℝ)) i = 1 := fun i => by
    simpa using realMatrix_rational_rows w 1 wr i
  have cols : ∀ i : V, ((fun v : V => (p v : ℝ)) ᵥ* realMatrix q E V) i = 1 := fun i => by
    simpa using realMatrix_rational_columns p 1 pc i
  have wmr := real_mass_of_rational_probability w wm
  have sl : ∀ i, i ≠ m → (c ᵥ* realMatrix q E V) i ≤ 1 := fun i hi => by
    have h := slack i hi
    rw [vecMul_excess, ct] at h
    linarith
  have wpos : (0 : ℝ) < (w m : ℝ) := by exact_mod_cast (wp m m.property).1
  have ppos : (0 : ℝ) < (p m : ℝ) := by exact_mod_cast (wp m m.property).2
  exact ⟨flat_column inv _ _ c rows cols wmr ct m cm cn sl wpos ppos j,
    flat_anti inv _ _ c rows cols wmr ct m cm sl wpos ppos⟩

open SharedArcFlatResponse in
/-- Flat graph, row side, from the payable puncture of the reversed graph. -/
theorem flat_laws_row {q : ℕ} (hq : 2 ≤ q) {E : CH.Digraph} {V : Finset ℕ} {w p : ℕ → ℚ}
    (wp : ∀ i ∈ V, 0 < w i ∧ 0 < p i) (wm : mass V w = 1)
    (wr : ∀ i ∈ V, WeightedSD.row q E V w i = 1) (pc : ∀ i ∈ V, WeightedSD.col q E V p i = 1)
    (m : V) (small : SmallRow q (fun a b => E b a) (V.erase m)) (j : V) (hj : j ≠ m) :
    let L := (realMatrix q E V)⁻¹
    (∃ i : V, i ≠ m ∧ L j i * ((p m : ℝ) * (w m : ℝ)) + L m m * ((p i : ℝ) * (w j : ℝ)) ≤
        L j m * ((p i : ℝ) * (w m : ℝ)) + L m i * ((p m : ℝ) * (w j : ℝ))) ∧
      ∃ i : V, i ≠ m ∧ L m m * (p i : ℝ) < L m i * (p m : ℝ) := by
  intro L
  have inv0 : realMatrix q E V * L = 1 := Matrix.mul_nonsing_inv _ (matrix_unit hq E V)
  have inv : (realMatrix q E V).transpose * L.transpose = 1 := by
    rw [← Matrix.transpose_mul, mul_eq_one_comm.mp inv0, Matrix.transpose_one]
  obtain ⟨c, cn, cm, ct, slack⟩ := certificate m small j hj
  have rows0 : ∀ i : V, (realMatrix q E V *ᵥ fun v : V => (w v : ℝ)) i = 1 := fun i => by
    simpa using realMatrix_rational_rows w 1 wr i
  have cols0 : ∀ i : V, ((fun v : V => (p v : ℝ)) ᵥ* realMatrix q E V) i = 1 := fun i => by
    simpa using realMatrix_rational_columns p 1 pc i
  have rows : ∀ i : V, ((realMatrix q E V).transpose *ᵥ fun v : V => (p v : ℝ)) i = 1 :=
    fun i => by rw [Matrix.mulVec_transpose]; exact cols0 i
  have cols : ∀ i : V, ((fun v : V => (w v : ℝ)) ᵥ* (realMatrix q E V).transpose) i = 1 :=
    fun i => by rw [Matrix.vecMul_transpose]; exact rows0 i
  have wmr := real_mass_of_rational_probability w wm
  have pmr : ∑ i : V, (p i : ℝ) = 1 := by
    calc
      ∑ i : V, (p i : ℝ) =
          ∑ i : V, (p i : ℝ) * (realMatrix q E V *ᵥ fun v : V => (w v : ℝ)) i :=
        Finset.sum_congr rfl fun i _ => by rw [rows0 i, mul_one]
      _ = dotProduct (fun v : V => (p v : ℝ)) (realMatrix q E V *ᵥ fun v : V => (w v : ℝ)) :=
        rfl
      _ = dotProduct ((fun v : V => (p v : ℝ)) ᵥ* realMatrix q E V) (fun v : V => (w v : ℝ)) :=
        dotProduct_mulVec _ _ _
      _ = ∑ i : V, ((fun v : V => (p v : ℝ)) ᵥ* realMatrix q E V) i * (w i : ℝ) := rfl
      _ = ∑ i : V, (w i : ℝ) := Finset.sum_congr rfl fun i _ => by rw [cols0 i, one_mul]
      _ = 1 := wmr
  have sl : ∀ i, i ≠ m → (c ᵥ* (realMatrix q E V).transpose) i ≤ 1 := fun i hi => by
    have h := slack i hi
    rw [vecMul_excess, ct, realMatrix_reverse] at h
    linarith
  have wpos : (0 : ℝ) < (w m : ℝ) := by exact_mod_cast (wp m m.property).1
  have ppos : (0 : ℝ) < (p m : ℝ) := by exact_mod_cast (wp m m.property).2
  exact ⟨flat_column inv _ _ c rows cols pmr ct m cm cn sl ppos wpos j,
    flat_anti inv _ _ c rows cols pmr ct m cm sl ppos wpos⟩

open SharedArcFlatResponse in
/-- The additive law for the four-index test, at every label m and for every ordered
pair (a,b), safe or not: the test differs from L by terms that cancel in this
combination. Together with `tensor` the same table obeys an additive and a
multiplicative law. -/
theorem tensor_additive {q : ℕ} (hq : 2 ≤ q) {E : CH.Digraph} {V : Finset ℕ}
    {w p : ℕ → ℚ} (wp : ∀ i ∈ V, 0 < w i ∧ 0 < p i) (wm : mass V w = 1)
    (wr : ∀ i ∈ V, WeightedSD.row q E V w i = 1) (pc : ∀ i ∈ V, WeightedSD.col q E V p i = 1)
    (a b m : V) (small : SmallRow q E (V.erase m)) (j : V) (hj : j ≠ m) :
    let T := test (realMatrix q E V)⁻¹ (fun i : V => (w i : ℝ)) (fun i : V => (p i : ℝ)) q a b
    ∃ i : V, i ≠ m ∧ T i j * ((w m : ℝ) * (p m : ℝ)) + T m m * ((w i : ℝ) * (p j : ℝ)) ≤
      T m j * ((w i : ℝ) * (p m : ℝ)) + T i m * ((w m : ℝ) * (p j : ℝ)) := by
  intro T
  obtain ⟨i, hi, h⟩ := (flat_laws hq wp wm wr pc m small j hj).1
  refine ⟨i, hi, ?_⟩
  have pa : (0 : ℝ) ≤ (p a : ℝ) := by exact_mod_cast (wp a a.property).2.le
  have wb : (0 : ℝ) ≤ (w b : ℝ) := by exact_mod_cast (wp b b.property).1.le
  have sn : 0 ≤ (q : ℝ) * (p a : ℝ) * (w b : ℝ) :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) pa) wb
  have key : (T m j * ((w i : ℝ) * (p m : ℝ)) + T i m * ((w m : ℝ) * (p j : ℝ))) -
      (T i j * ((w m : ℝ) * (p m : ℝ)) + T m m * ((w i : ℝ) * (p j : ℝ))) =
      ((q : ℝ) * (p a : ℝ) * (w b : ℝ)) *
        (((realMatrix q E V)⁻¹ m j * ((w i : ℝ) * (p m : ℝ)) +
            (realMatrix q E V)⁻¹ i m * ((w m : ℝ) * (p j : ℝ))) -
          ((realMatrix q E V)⁻¹ i j * ((w m : ℝ) * (p m : ℝ)) +
            (realMatrix q E V)⁻¹ m m * ((w i : ℝ) * (p j : ℝ)))) := by
    simp only [T, test]; ring
  have := mul_nonneg sn (sub_nonneg.mpr h)
  linarith

end LeanCH.BR.Closure.PunctureLaw

#print axioms LeanCH.BR.Closure.PunctureLaw.flat_laws
#print axioms LeanCH.BR.Closure.PunctureLaw.flat_laws_row
#print axioms LeanCH.BR.Closure.PunctureLaw.tensor_additive
#print axioms LeanCH.BR.Closure.PunctureLaw.identity
#print axioms LeanCH.BR.Closure.PunctureLaw.least_support
#print axioms LeanCH.BR.Closure.PunctureLaw.least_support_anti
#print axioms LeanCH.BR.Closure.PunctureLaw.tensor
#print axioms LeanCH.BR.Closure.PunctureLaw.tail_row
#print axioms LeanCH.BR.Closure.PunctureLaw.head_column
#print axioms LeanCH.BR.Closure.PunctureLaw.diagonal_column
#print axioms LeanCH.BR.Closure.PunctureLaw.diagonal_row
