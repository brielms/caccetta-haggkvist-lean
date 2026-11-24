import LeanCH.BR.BRFiniteDeletionThreshold
import LeanCH.BR.BRWeightedInverseComparison

/-! An exact all-cutoff characterization of individual arc criticality. -/
namespace LeanCH.BR.WeightedSD
open Finset Matrix FiniteCutInverse WeightedArithmetic
open scoped Matrix

theorem realMatrix_erase_difference {q : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (a b : V) (hab : D a b = true) (x y : V) :
    realMatrix q D V x y - realMatrix q (eraseArc D a b) V x y =
      if x = a ∧ y = b then (q : ℝ) else 0 := by
  by_cases hxa : x = a <;> by_cases hyb : y = b
  · subst x; subst y
    simp [realMatrix_entry, eraseArc, hab]
  · have hn : (y : ℕ) ≠ b := fun he => hyb (Subtype.ext he)
    simp [realMatrix_entry, eraseArc, hyb, hn]
  · have hn : (x : ℕ) ≠ a := fun he => hxa (Subtype.ext he)
    simp [realMatrix_entry, eraseArc, hxa, hn]
  · have hn : (x : ℕ) ≠ a := fun he => hxa (Subtype.ext he)
    simp [realMatrix_entry, eraseArc, hxa, hn]

theorem deletion_smallRow_iff {q : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    {H : Matrix V V ℝ} (hH : CommonInverse (realMatrix q D V) H)
    (a b : V) (hab : D a b = true) :
    SmallRow q (eraseArc D a b) V ↔ 1 ≤ (q : ℝ) * H b a := by
  constructor
  · intro hs
    obtain ⟨p, hp⟩ := realDual_of_smallRow hs ⟨a, a.property⟩
    have hm : (∑ v : V, p v) = 1 := by rw [Finset.sum_coe_sort]; exact hp.normalized
    exact deletion_arc_threshold hH (fun v : V => p v)
      (fun v => hp.nonneg v v.property) hm q a b (arc_deletion_columns a b hab hp)
  · intro ht
    obtain ⟨p, hp, hm, hc⟩ := decrement_dual_of_threshold hH a b q
      (realMatrix_erase_difference a b hab) ht
    apply smallRow_of_realDual (p := realExtendWeight V p)
    constructor
    · intro v hv
      rw [realExtendWeight_on V p ⟨v, hv⟩]
      exact hp ⟨v, hv⟩
    · rw [realMass_extendWeight]; exact hm
    · intro v hv
      have he : (fun k : V => realExtendWeight V p k) = p := by
        funext k; exact realExtendWeight_on V p k
      rw [← realMatrix_col q (eraseArc D a b) V (realExtendWeight V p) ⟨v, hv⟩, he]
      exact hc ⟨v, hv⟩

theorem arcCritical_iff_inverse_thresholds {q : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    {H : Matrix V V ℝ} (hH : CommonInverse (realMatrix q D V) H) :
    ArcCritical q D V ↔ ∀ a b : V, D a b = true → 1 ≤ (q : ℝ) * H b a := by
  constructor
  · exact fun hc a b hab => (deletion_smallRow_iff hH a b hab).mp
      (hc a a.property b b.property hab)
  · intro hc a ha b hb hab
    exact (deletion_smallRow_iff hH ⟨a, ha⟩ ⟨b, hb⟩ hab).mpr (hc ⟨a, ha⟩ ⟨b, hb⟩ hab)

theorem deletion_not_smallRow_iff {q : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    {H : Matrix V V ℝ} (hH : CommonInverse (realMatrix q D V) H)
    (a b : V) (hab : D a b = true) :
    ¬ SmallRow q (eraseArc D a b) V ↔ (q : ℝ) * H b a < 1 := by
  rw [deletion_smallRow_iff hH a b hab, not_le]

end LeanCH.BR.WeightedSD
