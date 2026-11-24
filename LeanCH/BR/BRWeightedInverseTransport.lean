import LeanCH.BR.BRFiniteRationalInverseNotBayes
import LeanCH.BR.BRWeightedInverseComparison

/-! Each actual strict host supplies its own inverse channel and refresh
products. No inverse or weight is transferred to a different graph. -/
namespace LeanCH.BR.WeightedSD
open Finset Matrix InverseTransport TwoLawTransport
open scoped Matrix

theorem graph_inverse_transport {q : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    {H : Matrix V V ℝ} (hH : FiniteCutInverse.CommonInverse (realMatrix q D V) H)
    (a p : ℕ → ℚ) (ha : ∀ i ∈ V, 0 < a i) (hm : mass V a = 1)
    (hpm : mass V p = 1) (c : ℚ) (hc : 1 < c)
    (hr : ∀ i ∈ V, row q D V a i = c) (hp : ∀ j ∈ V, col q D V p j = c) :
    let C := realMatrix q D V
    let av := fun i : V => (a i : ℝ)
    let pv := fun i : V => (p i : ℝ)
    let T := channel H av (c : ℝ)
    (∀ i, ((c : ℝ)-1)*(∑ j, H i j) = av i) ∧
    (∀ j, ((c : ℝ)-1)*(∑ i, H i j) = pv j) ∧
    (∀ i j, 0 ≤ T i j) ∧ (∀ i, ∑ j, T i j = 1) ∧
    av ᵥ* T = pv ∧
    (∀ i j, 0 ≤ forward C av (c : ℝ) i j) ∧
    (∀ i, ∑ j, forward C av (c : ℝ) i j = 1) ∧
    pv ᵥ* forward C av (c : ℝ) = av ∧
    (∀ i k, (forward C av (c : ℝ) * T) i k =
      (((c : ℝ)-1)*(if i = k then 1 else 0)+pv k)/(c : ℝ)) ∧
    (∀ i k, (T * forward C av (c : ℝ)) i k =
      (((c : ℝ)-1)*(if i = k then 1 else 0)+av k)/(c : ℝ)) := by
  dsimp only
  have hright : centered (realMatrix q D V) * H = 1 := hH.right
  have har : ∀ i : V, (0 : ℝ) < a i := fun i => by exact_mod_cast ha i i.property
  have hcr : (1 : ℝ) < c := by exact_mod_cast hc
  have ham := real_mass_of_rational_probability a hm
  have hpmr := real_mass_of_rational_probability p hpm
  have hrow := realMatrix_rational_rows a c hr
  have hcol := realMatrix_rational_columns p c hp
  have ht := channel_stochastic hright hH.nonneg _ har ham (c : ℝ) hcr.le hrow
  have hCn : ∀ i j : V, 0 ≤ realMatrix q D V i j := by
    intro i j
    rw [realMatrix_entry]
    split_ifs <;> positivity
  have hP := forward_stochastic _ _ (c : ℝ) hCn (fun i => (har i).le)
    (by linarith) hrow
  refine ⟨?_, ?_, ht.1, ht.2, ?_, hP.1, hP.2, ?_, ?_, ?_⟩
  · intro i
    exact (inverse_row_sum_of_equalizer hH a hm c hr i).symm
  · exact column_mass hright _ hpmr _ hcol
  · exact channel_transport hright _ _ (fun i => (har i).ne') hpmr _ hcol
  · exact transport_forward _ _ _ _ (by linarith) hcol
  · exact forward_channel hright _ _ (fun i => (har i).ne') hpmr _ hcol
  · exact channel_forward hright _ (fun i => (har i).ne') ham _ hrow

/-- A natural coefficient suffices: strictness itself rules out zero and one.
Only the inverse equation is used, not nonnegativity of that inverse. -/
theorem graph_inverse_ne_bayesian {q : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    {H : Matrix V V ℝ} (hH : FiniteCutInverse.excess (realMatrix q D V) * H = 1)
    (hloop : ∀ i ∈ V, ¬ D i i = true)
    (a p : ℕ → ℚ) (ha : ∀ i ∈ V, 0 < a i) (hm : mass V a = 1)
    (hpm : mass V p = 1) (c : ℚ) (hc : 1 < c)
    (hr : ∀ i ∈ V, row q D V a i = c) (hp : ∀ j ∈ V, col q D V p j = c) :
    channel H (fun i : V => (a i : ℝ)) (c : ℝ) ≠
      backward (realMatrix q D V) (fun i : V => (p i : ℝ)) (c : ℝ) := by
  have hd (i : V) : realMatrix q D V i i = 1 := by
    rw [realMatrix_entry]
    simp [hloop i i.property]
  have he (i j : V) (hij : i ≠ j) :
      realMatrix q D V i j = 0 ∨ realMatrix q D V i j = (q : ℝ) := by
    rw [realMatrix_entry]
    by_cases h : D i j = true <;> simp [hij, h]
  exact rational_channel_ne_bayesian (q : ℚ) hH hd (fun i j hij => by simpa using he i j hij) _ _
    (fun i => by exact_mod_cast ha i i.property)
    (real_mass_of_rational_probability a hm) (real_mass_of_rational_probability p hpm)
    (c : ℝ) (by exact_mod_cast hc)
    (realMatrix_rational_rows a c hr) (realMatrix_rational_columns p c hp)

end LeanCH.BR.WeightedSD
