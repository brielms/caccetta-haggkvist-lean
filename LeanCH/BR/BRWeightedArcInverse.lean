import LeanCH.BR.BRWeightedArcCore
import LeanCH.BR.BRFiniteArcInverse

/-! Derived inverse charges on an actual minimal-arc core, at every cutoff.
No saturation hypothesis is transferred from an ambient graph to its core. -/
namespace LeanCH.BR.WeightedSD
open Finset BRq2 BRq3 BR45 BRsub Matrix FiniteCutInverse
open scoped Matrix

theorem realInW_eraseArc {D : CH.Digraph} {V : Finset ℕ} {a b : ℕ}
    (ha : a ∈ V) (hab : D a b = true) (p : ℕ → ℝ) (z : ℕ) :
    realInW D V p z = realInW (eraseArc D a b) V p z + if z = b then p a else 0 := by
  unfold realInW
  have he : (∑ v ∈ V, if D v z = true then p v else 0) =
      (∑ v ∈ V, if eraseArc D a b v z = true then p v else 0) +
      ∑ v ∈ V, if v = a ∧ z = b then p a else 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v hv
    by_cases hva : v = a <;> by_cases hzb : z = b <;>
      simp [eraseArc, hva, hzb, hab]
  rw [he]
  by_cases hzb : z = b <;> simp [hzb, ha]

theorem realCol_eraseArc {q : ℕ} {D : CH.Digraph} {V : Finset ℕ} {a b : ℕ}
    (ha : a ∈ V) (hab : D a b = true) (p : ℕ → ℝ) (z : ℕ) :
    realCol q D V p z = realCol q (eraseArc D a b) V p z +
      if z = b then (q : ℝ) * p a else 0 := by
  rw [realCol, realInW_eraseArc ha hab]
  by_cases he : z = b <;> simp only [realCol, he, ite_true, ite_false] <;> ring

theorem arc_deletion_columns {q : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (a b : V) (hab : D a b = true) {p : ℕ → ℝ}
    (hp : RealDual q (eraseArc D a b) V 1 p) :
    ∀ z : V, ((fun v : V => p v) ᵥ* realMatrix q D V) z ≤
      1 + if z = b then (q : ℝ) * p a else 0 := by
  intro z
  rw [realMatrix_col, realCol_eraseArc a.property hab]
  have hh := add_le_add_right (hp.columns z z.property)
    (if (z : ℕ) = b then (q : ℝ) * p a else 0)
  simpa only [Subtype.ext_iff, add_comm] using hh

theorem realCol_edge_floor {q : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (p : ℕ → ℝ) (hp : ∀ v ∈ V, 0 ≤ p v)
    {a u : ℕ} (ha : a ∈ V) (hu : u ∈ V) (hau : D a u = true) :
    (q : ℝ) * p a ≤ realCol q D V p u := by
  have hs := Finset.single_le_sum (s := V)
    (f := fun v => if D v u = true then p v else 0)
    (fun v hv => by split_ifs <;> simp [hp v hv]) ha
  simp only [hau, ite_true] at hs
  change p a ≤ realInW D V p u at hs
  have hh := mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg q : (0 : ℝ) ≤ q)
  change _ ≤ p u + (q : ℝ) * realInW D V p u
  linarith [hp u hu]

theorem branch_deletion_tail_bound {q : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (a b u : V) (hne : u ≠ b) (hau : D a u = true) {p : ℕ → ℝ}
    (hp : RealDual q (eraseArc D a b) V 1 p) : (q : ℝ) * p a ≤ 1 := by
  have hne' : (u : ℕ) ≠ b := fun he => hne (Subtype.ext he)
  have hkeep : eraseArc D a b a u = true := by simp [eraseArc, hne', hau]
  exact (realCol_edge_floor p hp.nonneg a.property u.property hkeep).trans
    (hp.columns u u.property)

theorem inverse_arc_charge {q : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hcritical : ArcCritical q D V) {H : Matrix V V ℝ}
    (hH : CommonInverse (realMatrix q D V) H)
    (a b : V) (hab : D a b = true) : 1 ≤ (q : ℝ) * H b a := by
  obtain ⟨p, hp⟩ := realDual_of_smallRow
    (hcritical a a.property b b.property hab) ⟨a, a.property⟩
  have hm : (∑ v : V, p v) = 1 := by
    rw [Finset.sum_coe_sort]
    exact hp.normalized
  exact deletion_arc_threshold hH (fun v : V => p v)
    (fun v => hp.nonneg v v.property) hm q a b (arc_deletion_columns a b hab hp)

/-- An actual certificate of deleting a->b is dominated by inverse row b
when the old tail a retains a different successor. -/
theorem branch_certificate_dominated {q : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    {H : Matrix V V ℝ} (hH : CommonInverse (realMatrix q D V) H)
    (a b u : V) (hab : D a b = true) (hne : u ≠ b) (hau : D a u = true)
    {p : ℕ → ℝ} (hp : RealDual q (eraseArc D a b) V 1 p) :
    ∀ k : V, p k ≤ H b k := by
  have hm : (∑ v : V, p v) = 1 := by
    rw [Finset.sum_coe_sort]
    exact hp.normalized
  exact bounded_deletion_dominates hH (fun v : V => p v) hm ((q : ℝ) * p a) b
    (arc_deletion_columns a b hab hp) (branch_deletion_tail_bound a b u hne hau hp)

theorem realInW_eq_mass_inN (D : CH.Digraph) (V : Finset ℕ) (p : ℕ → ℝ) (b : ℕ) :
    realInW D V p b = realMass (inN D V b) p := by
  simp only [realInW, realMass, inN, Finset.sum_filter]

theorem inverse_branch_row_mass {q : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hcritical : ArcCritical q D V) {H : Matrix V V ℝ}
    (hH : CommonInverse (realMatrix q D V) H)
    (a b u : V) (hab : D a b = true) (hne : u ≠ b) (hau : D a u = true) :
    1 ≤ ∑ k : V, H b k := by
  obtain ⟨p, hp⟩ := realDual_of_smallRow
    (hcritical a a.property b b.property hab) ⟨a, a.property⟩
  have hm : (∑ k : V, p k) = 1 := by rw [Finset.sum_coe_sort]; exact hp.normalized
  rw [← hm]
  exact Finset.sum_le_sum (fun k _ => branch_certificate_dominated hH a b u hab hne hau hp k)

theorem branch_certificate_outside {q : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (a b u : V) (hab : D a b = true) (hne : u ≠ b) (hau : D a u = true)
    {p : ℕ → ℝ} (hp : RealDual q (eraseArc D a b) V 1 p) :
    (q : ℝ) - 2 ≤ (q : ℝ) * realMass (V \ inN D V b) p := by
  have ht := branch_deletion_tail_bound a b u hne hau hp
  have hc : realCol q D V p b ≤ 2 := by
    rw [realCol_eraseArc a.property hab]
    simp only [ite_true]
    linarith [hp.columns b b.property]
  rw [realCol, realInW_eq_mass_inN] at hc
  have hsplit : realMass (V \ inN D V b) p + realMass (inN D V b) p = 1 := by
    rw [← hp.normalized]
    exact Finset.sum_sdiff (Finset.filter_subset _ _)
  have hnonneg := hp.nonneg b b.property
  nlinarith

/-- Branching gives a genuine budget outside the old incoming set,
in addition to the separate charges on every old incoming arc. -/
theorem inverse_branch_row_charge {q : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hcritical : ArcCritical q D V) {H : Matrix V V ℝ}
    (hH : CommonInverse (realMatrix q D V) H)
    (a b u : V) (hab : D a b = true) (hne : u ≠ b) (hau : D a u = true) :
    ((inN D V b).card : ℝ) + q - 2 ≤ (q : ℝ) * ∑ k : V, H b k := by
  obtain ⟨p, hp⟩ := realDual_of_smallRow
    (hcritical a a.property b b.property hab) ⟨a, a.property⟩
  let r : ℕ → ℝ := realExtendWeight V (fun k : V => H b k)
  have hr : ∀ (v : ℕ) (hv : v ∈ V), r v = H b ⟨v, hv⟩ := by
    intro v hv
    exact realExtendWeight_on V (fun k : V => H b k) ⟨v, hv⟩
  have hdom := branch_certificate_dominated hH a b u hab hne hau hp
  have hout := branch_certificate_outside a b u hab hne hau hp
  have houtsum : realMass (V \ inN D V b) p ≤ realMass (V \ inN D V b) r := by
    apply Finset.sum_le_sum
    intro v hv
    rw [hr v (Finset.mem_sdiff.mp hv).1]
    exact hdom ⟨v, (Finset.mem_sdiff.mp hv).1⟩
  have houtH : (q : ℝ) - 2 ≤ (q : ℝ) * realMass (V \ inN D V b) r :=
    hout.trans (mul_le_mul_of_nonneg_left houtsum (Nat.cast_nonneg q))
  have hinH : ((inN D V b).card : ℝ) ≤ (q : ℝ) * realMass (inN D V b) r := by
    calc
      _ = ∑ _v ∈ inN D V b, (1 : ℝ) := by simp
      _ ≤ ∑ v ∈ inN D V b, (q : ℝ) * r v := by
        apply Finset.sum_le_sum
        intro v hv
        obtain ⟨hvV, hvb⟩ := mem_inN.mp hv
        rw [hr v hvV]
        exact inverse_arc_charge hcritical hH ⟨v, hvV⟩ b hvb
      _ = _ := by rw [← Finset.mul_sum]; rfl
  have hsplit : realMass (V \ inN D V b) r + realMass (inN D V b) r = realMass V r :=
    Finset.sum_sdiff (Finset.filter_subset _ _)
  have htotal : realMass V r = ∑ k : V, H b k := realMass_extendWeight V _
  rw [htotal] at hsplit
  nlinarith

/-- All minimality and inverse hypotheses in the charges are obtained from
the given strict host and the genuine smaller-order induction class. -/
theorem exists_arc_core_with_charges {q : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hsmall : SmallerSmallRow q V.card) (hf : QFree D V q)
    (hbad : ¬ SmallRow q D V) :
    ∃ E : CH.Digraph, (∀ a b, E a b = true → D a b = true) ∧ QFree E V q ∧
      ArcCritical q E V ∧ StrictPositiveRows q E V ∧
      ∃ H : Matrix V V ℝ, CommonInverse (realMatrix q E V) H ∧
        (∀ a b : V, E a b = true → 1 ≤ (q : ℝ) * H b a) ∧
        (∀ a b u : V, E a b = true → u ≠ b → E a u = true →
          ((inN E V b).card : ℝ) + q - 2 ≤ (q : ℝ) * ∑ k : V, H b k) := by
  obtain ⟨E, hED, hEf, hcritical, w, p, c, hc, hw, hp, hm, hpm, hr, hpc, H, hH⟩ :=
    arc_core_normal_form hsmall hf hbad
  refine ⟨E, hED, hEf, hcritical,
    ⟨w, hw, hm, fun v hv => by rw [hr v hv]; exact hc⟩, H, hH, ?_, ?_⟩
  · exact inverse_arc_charge hcritical hH
  · exact inverse_branch_row_charge hcritical hH

theorem inverse_reverse_branch_charge {q : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hsmall : SmallerSmallRow q V.card) (hf : QFree D V q)
    (hcritical : ArcCritical q D V) {H : Matrix V V ℝ}
    (hH : CommonInverse (realMatrix q D V) H)
    (a b u : V) (hba : D b a = true) (hne : u ≠ b) (hua : D u a = true) :
    ((outN D V b).card : ℝ) + q - 2 ≤ (q : ℝ) * ∑ k : V, H k b :=
  inverse_branch_row_charge (hcritical.reverse hsmall hf)
    (commonInverse_reverse hH) a b u hba hne hua

theorem inverse_row_sum_of_equalizer {q : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    {H : Matrix V V ℝ} (hH : CommonInverse (realMatrix q D V) H)
    (w : ℕ → ℚ) (hm : mass V w = 1) (c : ℚ)
    (hr : ∀ v ∈ V, row q D V w v = c) (k : V) :
    (w k : ℝ) = ((c : ℝ) - 1) * ∑ z : V, H k z := by
  apply equalizer_inverse_row_sum hH (fun v : V => (w v : ℝ)) _ (c : ℝ) _ k
  · have hh : (∑ v : V, w v) = 1 := by rw [Finset.sum_coe_sort]; exact hm
    exact_mod_cast hh
  · intro i
    have he : (WeightedArithmetic.rationalMatrix q (adjacencyMatrix D V) *ᵥ
        (fun v : V => w v)) i = c := by
      rw [matrix_row, hr i i.property]
    change (∑ j : V, WeightedArithmetic.rationalMatrix q (adjacencyMatrix D V) i j * w j) = c at he
    have hh := congrArg (fun x : ℚ => (x : ℝ)) he
    push_cast at hh
    exact hh

theorem branch_weight_degree_charge {q : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hcritical : ArcCritical q D V) {H : Matrix V V ℝ}
    (hH : CommonInverse (realMatrix q D V) H)
    (w : ℕ → ℚ) (hm : mass V w = 1) (c : ℚ) (hc : 1 < c)
    (hr : ∀ v ∈ V, row q D V w v = c)
    (a b u : V) (hab : D a b = true) (hne : u ≠ b) (hau : D a u = true) :
    ((c : ℝ) - 1) * (((inN D V b).card : ℝ) + q - 2) ≤ (q : ℝ) * (w b : ℝ) := by
  have hmargin : 0 ≤ (c : ℝ) - 1 := by
    have hh : (1 : ℝ) < c := by exact_mod_cast hc
    linarith
  have hh := mul_le_mul_of_nonneg_left
    (inverse_branch_row_charge hcritical hH a b u hab hne hau) hmargin
  rw [inverse_row_sum_of_equalizer hH w hm c hr b]
  nlinarith

theorem branch_weight_floor {q : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hcritical : ArcCritical q D V) {H : Matrix V V ℝ}
    (hH : CommonInverse (realMatrix q D V) H)
    (w : ℕ → ℚ) (hm : mass V w = 1) (c : ℚ) (hc : 1 < c)
    (hr : ∀ v ∈ V, row q D V w v = c)
    (a b u : V) (hab : D a b = true) (hne : u ≠ b) (hau : D a u = true) :
    (c : ℝ) - 1 ≤ (w b : ℝ) := by
  have hmargin : 0 ≤ (c : ℝ) - 1 := by
    have hh : (1 : ℝ) < c := by exact_mod_cast hc
    linarith
  have hh := mul_le_mul_of_nonneg_left
    (inverse_branch_row_mass hcritical hH a b u hab hne hau) hmargin
  rw [inverse_row_sum_of_equalizer hH w hm c hr b]
  simpa only [mul_one] using hh

end LeanCH.BR.WeightedSD
