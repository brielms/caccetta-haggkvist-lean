import LeanCH.BR.BRWeightedStrictPrime

/-! Actual minimal-arc subgraphs for the strict weighted induction.
The selected core is not asserted to be saturated. -/
namespace LeanCH.BR.WeightedSD
open Finset BRq2 BRq3 BR45 BRsub

def eraseArc (D : CH.Digraph) (a b : ℕ) : CH.Digraph :=
  fun x y => if x = a ∧ y = b then false else D x y

def arcSet (D : CH.Digraph) (V : Finset ℕ) : Finset (ℕ × ℕ) :=
  (V ×ˢ V).filter (fun e => D e.1 e.2 = true)

def ArcCritical (q : ℕ) (D : CH.Digraph) (V : Finset ℕ) : Prop :=
  ∀ a ∈ V, ∀ b ∈ V, D a b = true → SmallRow q (eraseArc D a b) V

theorem eraseArc_sub (D : CH.Digraph) (a b x y : ℕ)
    (h : eraseArc D a b x y = true) : D x y = true := by
  by_cases he : x = a ∧ y = b <;> simp_all [eraseArc]

theorem arcSet_erase (D : CH.Digraph) (V : Finset ℕ) (a b : ℕ) :
    arcSet (eraseArc D a b) V = (arcSet D V).erase (a, b) := by
  ext e
  rcases e with ⟨x, y⟩
  by_cases hxa : x = a <;> by_cases hyb : y = b <;>
    simp [arcSet, eraseArc, hxa, hyb, and_assoc, and_left_comm, and_comm]

theorem strict_witness_of_not_smallRow {q : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (h : ¬ SmallRow q D V) :
    ∃ w : ℕ → ℚ, (∀ v ∈ V, 0 ≤ w v) ∧ V.Nonempty ∧
      ∀ v ∈ V, mass V w < row q D V w v := by
  unfold SmallRow at h
  push_neg at h
  exact h

/-- Minimize the number of actual host arcs among strict subgraphs of D.
Every single-arc deletion of the chosen core satisfies SmallRow. -/
theorem exists_arc_critical_subgraph {q : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V q) (hbad : ¬ SmallRow q D V) :
    ∃ E : CH.Digraph, (∀ a b, E a b = true → D a b = true) ∧
      QFree E V q ∧ ¬ SmallRow q E V ∧ ArcCritical q E V := by
  classical
  let P : ℕ → Prop := fun n => ∃ E : CH.Digraph,
    (∀ a b, E a b = true → D a b = true) ∧ ¬ SmallRow q E V ∧ (arcSet E V).card = n
  have hex : ∃ n, P n := ⟨(arcSet D V).card, D, (fun _ _ h => h), hbad, rfl⟩
  obtain ⟨E, hED, hEbad, hcount⟩ := Nat.find_spec hex
  refine ⟨E, hED, qfree_sub hED hf, hEbad, ?_⟩
  intro a ha b hb hab
  by_contra hdel
  have hP : P (arcSet (eraseArc E a b) V).card := by
    refine ⟨eraseArc E a b, ?_, hdel, rfl⟩
    intro x y hxy
    exact hED x y (eraseArc_sub E a b x y hxy)
  have hle := Nat.find_min' hex hP
  have hmem : (a, b) ∈ arcSet E V :=
    Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha, hb⟩, hab⟩
  rw [arcSet_erase, Finset.card_erase_of_mem hmem] at hle
  have hpos := Finset.card_pos.mpr ⟨(a, b), hmem⟩
  omega

/-- Global smaller-order induction remains available on the selected core;
it supplies positive equalizers and the same nonnegative inverse there. -/
theorem arc_core_normal_form {q : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hsmall : SmallerSmallRow q V.card) (hf : QFree D V q)
    (hbad : ¬ SmallRow q D V) :
    ∃ E : CH.Digraph, (∀ a b, E a b = true → D a b = true) ∧ QFree E V q ∧
      ArcCritical q E V ∧ ∃ w p : ℕ → ℚ, ∃ c : ℚ,
        1 < c ∧ (∀ v ∈ V, 0 < w v) ∧ (∀ v ∈ V, 0 < p v) ∧
        mass V w = 1 ∧ mass V p = 1 ∧
        (∀ v ∈ V, row q E V w v = c) ∧ (∀ v ∈ V, col q E V p v = c) ∧
        ∃ H : Matrix V V ℝ, FiniteCutInverse.CommonInverse (realMatrix q E V) H := by
  obtain ⟨E, hED, hEf, hEbad, hcritical⟩ := exists_arc_critical_subgraph hf hbad
  obtain ⟨z, hz, hV, hzr⟩ := strict_witness_of_not_smallRow hEbad
  have hproper := hsmall.induced hEf
  obtain ⟨w, p, c, hc, hw, hp, hm, hpm, hr, hpc⟩ :=
    strict_pair_of_proper_smallRow hproper hV z hz hzr
  obtain ⟨H, hH⟩ := strict_inverse_of_proper_smallRow hproper z hz hzr
  exact ⟨E, hED, hEf, hcritical, w, p, c, hc, hw, hp, hm, hpm, hr, hpc, H, hH⟩

/-- Reversal of SmallRow is justified here by smaller-order induction;
it is not asserted as a formal property of arbitrary matrix games. -/
theorem smallRow_reverse_of_smaller {q : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hsmall : SmallerSmallRow q V.card) (hf : QFree D V q)
    (h : SmallRow q D V) : SmallRow q (fun x y => D y x) V := by
  by_contra hn
  obtain ⟨z, hz, hV, hzr⟩ := strict_witness_of_not_smallRow hn
  obtain ⟨w, p, c, hc, hw, hp, hm, hpm, hr, hpc⟩ :=
    strict_pair_of_proper_smallRow (hsmall.induced hf.reverse) hV z hz hzr
  apply h.no_strict hV p (fun v hv => (hp v hv).le)
  intro v hv
  have he : row q D V p v = c := hpc v hv
  rw [hpm, he]
  exact hc

theorem eraseArc_reverse (D : CH.Digraph) (a b : ℕ) :
    eraseArc (fun x y => D y x) a b = fun x y => eraseArc D b a y x := by
  funext x y
  simp only [eraseArc, and_comm]

theorem ArcCritical.reverse {q : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (h : ArcCritical q D V) (hsmall : SmallerSmallRow q V.card) (hf : QFree D V q) :
    ArcCritical q (fun x y => D y x) V := by
  intro a ha b hb hba
  rw [eraseArc_reverse]
  exact smallRow_reverse_of_smaller hsmall
    (qfree_sub (eraseArc_sub D b a) hf) (h b hb a ha hba)

end LeanCH.BR.WeightedSD
