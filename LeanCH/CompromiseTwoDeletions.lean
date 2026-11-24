module

public import LeanCH.CompromiseRegainedSlack

set_option linter.style.header false

/-! Two genuine vertex-deletion certificates repair their omitted
columns when their cross-slack product pays both deficits. In an
oriented graph, regained paths alone cannot make this product positive. -/

open Finset CH.CompromiseGame CH.CompromiseSeven CH.CompromiseWeighted
open CH.CompromiseFair CH.CompromiseDeletion CH.CompromiseCritical
open CH.CompromiseCertificateCone CH.CompromisePerturbation
public section

namespace CH.CompromiseTwoDeletions

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (adj : V → V → Prop) [DecidableRel adj]

/-- The linear combination is explicit and uses the same two actual
certificates in every column. -/
theorem two_deleted_compromise (j k : V) (jk : j ≠ k) (r s : V → ℝ)
    (rf : FairOn adj (univ.erase j) r) (sf : FairOn adj (univ.erase k) s)
    (sk : col (coefficient adj) s k < 0)
    (pays : (-col (coefficient adj) r j) * (-col (coefficient adj) s k) ≤
      col (coefficient adj) r k * col (coefficient adj) s j)
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) : ∃ v, 0 ≤ surplus adj w v := by
  let t := -col (coefficient adj) s k
  let a := col (coefficient adj) r k
  let p : V → ℝ := fun v => t * r v + a * s v
  have tp : 0 < t := neg_pos.mpr sk
  have an : 0 ≤ a := retained_column adj j r rf k (Ne.symm jk)
  have pn (v : V) : 0 ≤ p v := add_nonneg (mul_nonneg tp.le (rf.1 v))
    (mul_nonneg an (sf.1 v))
  have positive : ∃ v, 0 < p v := by
    obtain ⟨v, _, hv⟩ := rf.2.2.1
    refine ⟨v, ?_⟩
    dsimp [p]
    nlinarith [mul_nonneg an (sf.1 v)]
  have cols (u : V) : 0 ≤ col (coefficient adj) p u := by
    have he : col (coefficient adj) p u =
        t * col (coefficient adj) r u + a * col (coefficient adj) s u := by
      simp only [col, p, add_mul, sum_add_distrib, mul_assoc, ← mul_sum]
    rw [he]
    by_cases uj : u = j
    · subst u
      dsimp [t, a]
      nlinarith
    by_cases uk : u = k
    · subst u
      dsimp [t, a]
      nlinarith
    · exact add_nonneg
        (mul_nonneg tp.le (retained_column adj j r rf u uj))
        (mul_nonneg an (retained_column adj k s sf u uk))
  obtain ⟨v, hv⟩ := good_of_left (coefficient adj) p pn positive cols w hw
  exact ⟨v, by simpa only [row_coefficient] using hv⟩

/-- Every pair of actual certificates in a strict counterexample has
cross product strictly below the omitted-slack product. -/
theorem cross_product_strict (w : V → ℝ) (hw : ∀ v, 0 ≤ w v)
    (bad : ∀ v, surplus adj w v < 0) (j k : V) (jk : j ≠ k) (r s : V → ℝ)
    (rf : FairOn adj (univ.erase j) r) (sf : FairOn adj (univ.erase k) s) :
    col (coefficient adj) r k * col (coefficient adj) s j <
      (-col (coefficient adj) r j) * (-col (coefficient adj) s k) := by
  have sk := (singleton_fair_budget adj w hw bad k s sf).2.1
  rw [← col_coefficient] at sk
  by_contra hn
  obtain ⟨v, hv⟩ := two_deleted_compromise adj j k jk r s rf sf sk (le_of_not_gt hn) w hw
  linarith [bad v]

theorem flat_cross_product_zero (noDigon : ∀ v u, adj v u → ¬ adj u v)
    (j k : V) (r s : V → ℝ)
    (rf : FairOn adj (univ.erase j) r) (sf : FairOn adj (univ.erase k) s)
    (rk : localSlack adj r (univ.erase j) k = 0)
    (sj : localSlack adj s (univ.erase k) j = 0) :
    col (coefficient adj) r k * col (coefficient adj) s j = 0 := by
  by_cases edge : adj j k
  · have empty := gained_singleton_empty adj k j (noDigon j k edge)
    have ident := fair_deletion_identity adj s (univ.erase k) sf.2.1 j
    rw [sj, empty] at ident
    simp only [mass, sum_empty, add_zero] at ident
    rw [col_coefficient, col_coefficient, ident, mul_zero]
  · have empty := gained_singleton_empty adj j k edge
    have ident := fair_deletion_identity adj r (univ.erase j) rf.2.1 k
    rw [rk, empty] at ident
    simp only [mass, sum_empty, add_zero] at ident
    rw [col_coefficient, ident, zero_mul]

/-- A positive cross product requires genuinely positive induced
slack at one of the two other omitted vertices. -/
theorem positive_product_requires_induced (noDigon : ∀ v u, adj v u → ¬ adj u v)
    (j k : V) (jk : j ≠ k) (r s : V → ℝ)
    (rf : FairOn adj (univ.erase j) r) (sf : FairOn adj (univ.erase k) s)
    (positive : 0 < col (coefficient adj) r k * col (coefficient adj) s j) :
    0 < localSlack adj r (univ.erase j) k ∨ 0 < localSlack adj s (univ.erase k) j := by
  have rn : 0 ≤ localSlack adj r (univ.erase j) k := by
    have h := rf.2.2.2 k (by simp [Ne.symm jk])
    dsimp [localSlack]
    linarith
  have sn : 0 ≤ localSlack adj s (univ.erase k) j := by
    have h := sf.2.2.2 j (by simp [jk])
    dsimp [localSlack]
    linarith
  by_contra hn
  push Not at hn
  have rz : localSlack adj r (univ.erase j) k = 0 := le_antisymm hn.1 rn
  have sz : localSlack adj s (univ.erase k) j = 0 := le_antisymm hn.2 sn
  have zero := flat_cross_product_zero adj noDigon j k r s rf sf rz sz
  linarith

end CH.CompromiseTwoDeletions

#print axioms CH.CompromiseTwoDeletions.two_deleted_compromise
#print axioms CH.CompromiseTwoDeletions.cross_product_strict
#print axioms CH.CompromiseTwoDeletions.flat_cross_product_zero
#print axioms CH.CompromiseTwoDeletions.positive_product_requires_induced
