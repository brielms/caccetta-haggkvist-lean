import LeanCH.BR.BRFiniteInverseComparison
import LeanCH.BR.BRWeightedArcCapstone

/-! Exact inverse budgets for graph extensions, and return obstructions
derived by applying smaller-order induction to a safe single-arc addition. -/
namespace LeanCH.BR.WeightedSD
open Finset BRq2 BRq3 BR45 BRsub Matrix FiniteCutInverse WeightedArithmetic
open scoped Matrix

theorem realMatrix_entry (q : ℕ) (D : CH.Digraph) (V : Finset ℕ) (a b : V) :
    realMatrix q D V a b = (if a = b then 1 else 0) +
      if D a b = true then (q : ℝ) else 0 := by
  by_cases hab : a = b
  · subst b
    by_cases he : D a a = true <;>
      simp [realMatrix, rationalMatrix, closedMatrix, adjacencyMatrix, he]
  · by_cases he : D a b = true <;>
      simp [realMatrix, rationalMatrix, closedMatrix, adjacencyMatrix, hab, he]

theorem realMatrix_added_difference {q : ℕ} {E D : CH.Digraph} {V : Finset ℕ}
    (hED : ∀ a ∈ V, ∀ b ∈ V, E a b = true → D a b = true) (a b : V) :
    realMatrix q D V a b - realMatrix q E V a b =
      if D a b = true ∧ ¬ E a b = true then (q : ℝ) else 0 := by
  by_cases he : E a b = true
  · have hd := hED a a.property b b.property he
    simp [realMatrix_entry, he, hd]
  · by_cases hd : D a b = true <;>
      simp [realMatrix_entry, he, hd]

theorem realMatrix_mono_graph {q : ℕ} {E D : CH.Digraph} {V : Finset ℕ}
    (hED : ∀ a ∈ V, ∀ b ∈ V, E a b = true → D a b = true) (a b : V) :
    realMatrix q E V a b ≤ realMatrix q D V a b := by
  have hn : 0 ≤ realMatrix q D V a b - realMatrix q E V a b := by
    rw [realMatrix_added_difference hED]
    split_ifs <;> positivity
  linarith

theorem graph_inverse_antitone {q : ℕ} {E D : CH.Digraph} {V : Finset ℕ}
    (hED : ∀ a ∈ V, ∀ b ∈ V, E a b = true → D a b = true)
    {H K : Matrix V V ℝ} (hH : CommonInverse (realMatrix q E V) H)
    (hK : CommonInverse (realMatrix q D V) K) : ∀ i j, K i j ≤ H i j :=
  inverse_antitone hH hK (realMatrix_mono_graph hED)

theorem added_arcs_inverse_identity {q : ℕ} {E D : CH.Digraph} {V : Finset ℕ}
    (hED : ∀ a ∈ V, ∀ b ∈ V, E a b = true → D a b = true)
    {H K : Matrix V V ℝ} (hH : CommonInverse (realMatrix q E V) H)
    (hK : CommonInverse (realMatrix q D V) K) (i j : V) :
    H i j - K i j = ∑ a : V, ∑ b : V,
      if D a b = true ∧ ¬ E a b = true then (q : ℝ) * H i a * K b j else 0 := by
  rw [inverse_difference_apply hH hK]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [realMatrix_added_difference hED]
  split_ifs <;> ring

theorem added_arc_inverse_budget {q : ℕ} {E D : CH.Digraph} {V : Finset ℕ}
    (hED : ∀ a ∈ V, ∀ b ∈ V, E a b = true → D a b = true)
    {H K : Matrix V V ℝ} (hH : CommonInverse (realMatrix q E V) H)
    (hK : CommonInverse (realMatrix q D V) K) (i j a b : V)
    (hd : D a b = true) (he : ¬ E a b = true) :
    (q : ℝ) * H i a * K b j ≤ H i j - K i j := by
  have hh := inverse_increment_budget hH hK (realMatrix_mono_graph hED) i j a b
  rw [realMatrix_added_difference hED, if_pos ⟨hd, he⟩] at hh
  nlinarith

theorem StrictPositiveRows.mono_graph {q : ℕ} {E D : CH.Digraph} {V : Finset ℕ}
    (h : StrictPositiveRows q E V)
    (hED : ∀ a ∈ V, ∀ b ∈ V, E a b = true → D a b = true) :
    StrictPositiveRows q D V := by
  obtain ⟨w, hw, hm, hr⟩ := h
  refine ⟨w, hw, hm, ?_⟩
  intro v hv
  apply (hr v hv).trans_le
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
    (outW_mono_graph hED (fun u hu => (hw u hu).le) hv) (Nat.cast_nonneg q))

theorem common_inverse_of_smaller_strict {q : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hsmall : SmallerSmallRow q V.card) (hf : QFree D V q) (hs : StrictPositiveRows q D V) :
    ∃ H : Matrix V V ℝ, CommonInverse (realMatrix q D V) H := by
  obtain ⟨w, hw, hm, hr⟩ := hs
  exact strict_inverse_of_proper_smallRow (hsmall.induced hf) w
    (fun v hv => (hw v hv).le) (fun v hv => by rw [hm]; exact hr v hv)

/-- A saturation of the strict core has its own derived inverse. The
comparison is an exact added-arc budget, not inheritance of arc charges. -/
theorem exists_sat_inverse_comparison {q : ℕ} {E : CH.Digraph} {V : Finset ℕ}
    (hsmall : SmallerSmallRow q V.card) (hf : QFree E V q) (hs : StrictPositiveRows q E V)
    {H : Matrix V V ℝ} (hH : CommonInverse (realMatrix q E V) H) :
    ∃ D : CH.Digraph, (∀ a ∈ V, ∀ b ∈ V, E a b = true → D a b = true) ∧
      QFree D V q ∧ Sat q D V ∧ StrictPositiveRows q D V ∧
      ∃ K : Matrix V V ℝ, CommonInverse (realMatrix q D V) K ∧
        (∀ i j, K i j ≤ H i j) ∧
        ∀ i j, H i j - K i j = ∑ a : V, ∑ b : V,
          if D a b = true ∧ ¬ E a b = true then (q : ℝ) * H i a * K b j else 0 := by
  obtain ⟨D, hED, hDf, hsat⟩ := exists_satQ hf
  have hsD := hs.mono_graph hED
  obtain ⟨K, hK⟩ := common_inverse_of_smaller_strict hsmall hDf hsD
  exact ⟨D, hED, hDf, hsat, hsD, K, hK,
    graph_inverse_antitone hED hH hK, added_arcs_inverse_identity hED hH hK⟩

def insertArc (D : CH.Digraph) (a b : ℕ) : CH.Digraph :=
  fun x y => if x = a ∧ y = b then true else D x y

theorem insertArc_mono (D : CH.Digraph) (a b x y : ℕ) (h : D x y = true) :
    insertArc D a b x y = true := by simp [insertArc, h]

theorem qfree_insertArc {q : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V q) (a b : V) (hsafe : (a : ℕ) ∉ ball D V b (q - 1)) :
    QFree (insertArc D a b) V q := by
  apply qfree_insertQ hf a.property _ hsafe
  intro x y hxy
  by_cases he : x = a ∧ y = b
  · exact Or.inr he
  · exact Or.inl (by simpa only [insertArc, he, ite_false] using hxy)

theorem realMatrix_insert_difference {q : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (a b : V) (hab : ¬ D a b = true) (x y : V) :
    realMatrix q (insertArc D a b) V x y - realMatrix q D V x y =
      if x = a ∧ y = b then (q : ℝ) else 0 := by
  by_cases hxa : x = a <;> by_cases hyb : y = b
  · subst x; subst y
    simp [realMatrix_entry, insertArc, hab]
  · have hn : (y : ℕ) ≠ b := fun he => hyb (Subtype.ext he)
    simp [realMatrix_entry, insertArc, hyb, hn]
  · have hn : (x : ℕ) ≠ a := fun he => hxa (Subtype.ext he)
    simp [realMatrix_entry, insertArc, hxa, hn]
  · have hn : (x : ℕ) ≠ a := fun he => hxa (Subtype.ext he)
    simp [realMatrix_entry, insertArc, hxa, hn]

/-- The new inverse is derived from genuine induction on the legally
extended graph. The resulting rectangle bound uses the old inverse alone. -/
theorem safe_addition_inverse_rectangle {q : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hsmall : SmallerSmallRow q V.card) (hf : QFree D V q) (hs : StrictPositiveRows q D V)
    {H : Matrix V V ℝ} (hH : CommonInverse (realMatrix q D V) H)
    (a b : V) (hab : ¬ D a b = true) (hsafe : (a : ℕ) ∉ ball D V b (q - 1))
    (i j : V) :
    (q : ℝ) * H i a * H b j ≤ (1 + (q : ℝ) * H b a) * H i j := by
  have hf' := qfree_insertArc hf a b hsafe
  have hs' := hs.mono_graph (fun x _ y _ hxy => insertArc_mono D a b x y hxy)
  obtain ⟨K, hK⟩ := common_inverse_of_smaller_strict hsmall hf' hs'
  exact single_increment_rectangle hH hK a b q (Nat.cast_nonneg q)
    (realMatrix_insert_difference a b hab) i j

theorem inverse_rectangle_forces_return {q : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hsmall : SmallerSmallRow q V.card) (hf : QFree D V q) (hs : StrictPositiveRows q D V)
    {H : Matrix V V ℝ} (hH : CommonInverse (realMatrix q D V) H)
    (a b i j : V) (hab : ¬ D a b = true)
    (hviol : (1 + (q : ℝ) * H b a) * H i j < (q : ℝ) * H i a * H b j) :
    (a : ℕ) ∈ ball D V b (q - 1) := by
  by_contra hn
  exact (not_lt_of_ge (safe_addition_inverse_rectangle hsmall hf hs hH a b hab hn i j)) hviol

theorem inverse_zero_forces_return {q : ℕ} (hq : 0 < q)
    {D : CH.Digraph} {V : Finset ℕ}
    (hsmall : SmallerSmallRow q V.card) (hf : QFree D V q) (hs : StrictPositiveRows q D V)
    {H : Matrix V V ℝ} (hH : CommonInverse (realMatrix q D V) H)
    (a b i j : V) (hab : ¬ D a b = true)
    (hz : H i j = 0) (hia : 0 < H i a) (hbj : 0 < H b j) :
    (a : ℕ) ∈ ball D V b (q - 1) := by
  apply inverse_rectangle_forces_return hsmall hf hs hH a b i j hab
  rw [hz, mul_zero]
  exact mul_pos (mul_pos (by exact_mod_cast hq) hia) hbj

theorem realMatrix_rational_rows {q : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (w : ℕ → ℚ) (c : ℚ) (hr : ∀ v ∈ V, row q D V w v = c) :
    ∀ i : V, (realMatrix q D V *ᵥ (fun v : V => (w v : ℝ))) i = c := by
  intro i
  have he : (rationalMatrix q (adjacencyMatrix D V) *ᵥ (fun v : V => w v)) i = c := by
    rw [matrix_row, hr i i.property]
  change (∑ j : V, rationalMatrix q (adjacencyMatrix D V) i j * w j) = c at he
  have hh := congrArg (fun x : ℚ => (x : ℝ)) he
  push_cast at hh
  exact hh

theorem realMatrix_rational_columns {q : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (p : ℕ → ℚ) (c : ℚ) (hc : ∀ v ∈ V, col q D V p v = c) :
    ∀ i : V, ((fun v : V => (p v : ℝ)) ᵥ* realMatrix q D V) i = c := by
  intro i
  have he : ((fun v : V => p v) ᵥ* rationalMatrix q (adjacencyMatrix D V)) i = c := by
    rw [matrix_col, hc i i.property]
  change (∑ j : V, p j * rationalMatrix q (adjacencyMatrix D V) j i) = c at he
  have hh := congrArg (fun x : ℚ => (x : ℝ)) he
  push_cast at hh
  exact hh

theorem real_mass_of_rational_probability {V : Finset ℕ} (w : ℕ → ℚ) (hm : mass V w = 1) :
    (∑ v : V, (w v : ℝ)) = 1 := by
  have hh : (∑ v : V, w v) = 1 := by rw [Finset.sum_coe_sort]; exact hm
  exact_mod_cast hh

/-- The value increment is charged using the NEW dual and OLD primal. -/
theorem graph_mixed_value_gain {q : ℕ} {E D : CH.Digraph} {V : Finset ℕ}
    (hED : ∀ a ∈ V, ∀ b ∈ V, E a b = true → D a b = true)
    (w p : ℕ → ℚ) (hm : mass V w = 1) (hpm : mass V p = 1) (c d : ℚ)
    (hr : ∀ v ∈ V, row q E V w v = c) (hc : ∀ v ∈ V, col q D V p v = d) :
    (d : ℝ) - c = ∑ a : V, ∑ b : V,
      if D a b = true ∧ ¬ E a b = true then (q : ℝ) * (p a : ℝ) * (w b : ℝ) else 0 := by
  rw [mixed_equalizer_gain (fun v : V => (w v : ℝ)) (fun v : V => (p v : ℝ))
    (real_mass_of_rational_probability w hm) (real_mass_of_rational_probability p hpm)
    (c : ℝ) (d : ℝ) (realMatrix_rational_rows w c hr) (realMatrix_rational_columns p d hc)]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [realMatrix_added_difference hED]
  split_ifs <;> ring

/-- Equivalently, use the OLD dual and NEW primal; neither formula permits
replacing both weights by the old pair. -/
theorem graph_other_mixed_value_gain {q : ℕ} {E D : CH.Digraph} {V : Finset ℕ}
    (hED : ∀ a ∈ V, ∀ b ∈ V, E a b = true → D a b = true)
    (p w : ℕ → ℚ) (hpm : mass V p = 1) (hm : mass V w = 1) (c d : ℚ)
    (hc : ∀ v ∈ V, col q E V p v = c) (hr : ∀ v ∈ V, row q D V w v = d) :
    (d : ℝ) - c = ∑ a : V, ∑ b : V,
      if D a b = true ∧ ¬ E a b = true then (q : ℝ) * (p a : ℝ) * (w b : ℝ) else 0 := by
  have he := graph_mixed_value_gain
    (E := fun a b => E b a) (D := fun a b => D b a)
    (fun a ha b hb hab => hED b hb a ha hab) p w hpm hm c d hc hr
  rw [he, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  split_ifs <;> ring

theorem strict_value_gain_of_added_arc {q : ℕ} (hq : 0 < q)
    {E D : CH.Digraph} {V : Finset ℕ}
    (hED : ∀ a ∈ V, ∀ b ∈ V, E a b = true → D a b = true)
    (w p : ℕ → ℚ) (hw : ∀ v ∈ V, 0 < w v) (hp : ∀ v ∈ V, 0 < p v)
    (hm : mass V w = 1) (hpm : mass V p = 1) (c d : ℚ)
    (hr : ∀ v ∈ V, row q E V w v = c) (hc : ∀ v ∈ V, col q D V p v = d)
    (a b : V) (hd : D a b = true) (he : ¬ E a b = true) : c < d := by
  have hpos : realMatrix q E V a b < realMatrix q D V a b := by
    have hh := realMatrix_added_difference (q := q) hED a b
    rw [if_pos ⟨hd, he⟩] at hh
    have hqR : (0 : ℝ) < q := by exact_mod_cast hq
    linarith
  have hgain := mixed_equalizer_strict_gain
    (fun v : V => (w v : ℝ)) (fun v : V => (p v : ℝ))
    (fun v => by exact_mod_cast (hw v v.property).le)
    (fun v => by exact_mod_cast (hp v v.property).le)
    (real_mass_of_rational_probability w hm) (real_mass_of_rational_probability p hpm)
    (c : ℝ) (d : ℝ) (realMatrix_rational_rows w c hr) (realMatrix_rational_columns p d hc)
    (realMatrix_mono_graph hED) a b
    (by exact_mod_cast hp a a.property) (by exact_mod_cast hw b b.property) hpos
  exact_mod_cast hgain

theorem equal_value_extension_eq {q : ℕ} (hq : 0 < q)
    {E D : CH.Digraph} {V : Finset ℕ}
    (hED : ∀ a ∈ V, ∀ b ∈ V, E a b = true → D a b = true)
    (w p : ℕ → ℚ) (hw : ∀ v ∈ V, 0 < w v) (hp : ∀ v ∈ V, 0 < p v)
    (hm : mass V w = 1) (hpm : mass V p = 1) (c : ℚ)
    (hr : ∀ v ∈ V, row q E V w v = c) (hc : ∀ v ∈ V, col q D V p v = c) :
    ∀ a ∈ V, ∀ b ∈ V, E a b = D a b := by
  intro a ha b hb
  apply Bool.eq_iff_iff.mpr
  refine ⟨hED a ha b hb, ?_⟩
  intro hd
  by_contra he
  exact (lt_irrefl c) (strict_value_gain_of_added_arc hq hED w p hw hp hm hpm c c hr hc
    ⟨a, ha⟩ ⟨b, hb⟩ hd he)

end LeanCH.BR.WeightedSD
