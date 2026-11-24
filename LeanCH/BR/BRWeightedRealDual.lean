import LeanCH.BR.BRFiniteDual
import LeanCH.BR.BRWeightedCommonCut

/-! Real internal dual certificates derived from rational self-duality.
The ambient CH weights may remain rational; real duals are used only for
finite weighted identities and inequalities. -/
namespace LeanCH.BR.WeightedSD
open Finset Matrix WeightedArithmetic
open scoped Matrix

def realMass (V : Finset ℕ) (w : ℕ → ℝ) : ℝ := ∑ v ∈ V, w v
def realOutW (D : CH.Digraph) (V : Finset ℕ) (w : ℕ → ℝ) (v : ℕ) : ℝ :=
  ∑ u ∈ V, if D v u = true then w u else 0
def realInW (D : CH.Digraph) (V : Finset ℕ) (p : ℕ → ℝ) (u : ℕ) : ℝ :=
  ∑ v ∈ V, if D v u = true then p v else 0
def realRow (q : ℕ) (D : CH.Digraph) (V : Finset ℕ) (w : ℕ → ℝ) (v : ℕ) : ℝ :=
  w v + q * realOutW D V w v
def realCol (q : ℕ) (D : CH.Digraph) (V : Finset ℕ) (p : ℕ → ℝ) (v : ℕ) : ℝ :=
  p v + q * realInW D V p v

structure RealDual (q : ℕ) (D : CH.Digraph) (M : Finset ℕ) (alpha : ℝ) (p : ℕ → ℝ) : Prop where
  nonneg : ∀ v ∈ M, 0 ≤ p v
  normalized : realMass M p = 1
  columns : ∀ v ∈ M, realCol q D M p v ≤ alpha

def realExtendWeight (M : Finset ℕ) (p : M → ℝ) : ℕ → ℝ :=
  fun v => if hv : v ∈ M then p ⟨v, hv⟩ else 0

theorem realExtendWeight_on (M : Finset ℕ) (p : M → ℝ) (i : M) :
    realExtendWeight M p i = p i := by simp [realExtendWeight, i.property]

theorem realMass_extendWeight (M : Finset ℕ) (p : M → ℝ) :
    realMass M (realExtendWeight M p) = ∑ i : M, p i := by
  rw [realMass, ← Finset.sum_coe_sort]
  exact Finset.sum_congr rfl (fun i hi => realExtendWeight_on M p i)

theorem realCol_extendWeight (q : ℕ) (D : CH.Digraph) (M : Finset ℕ)
    (p : M → ℝ) (i : M) :
    realCol q D M (realExtendWeight M p) i =
      ∑ j : M, p j * (rationalMatrix q (adjacencyMatrix D M) j i : ℝ) := by
  have hs : realInW D M (realExtendWeight M p) i =
      ∑ j : M, if D j i = true then p j else 0 := by
    rw [realInW, ← Finset.sum_coe_sort]
    apply Finset.sum_congr rfl
    intro j hj
    rw [realExtendWeight_on]
  rw [realCol, realExtendWeight_on, hs]
  have he (j : M) : (rationalMatrix q (adjacencyMatrix D M) j i : ℝ) =
      (if j = i then 1 else 0) + (q : ℝ) * (if D j i = true then 1 else 0) := by
    by_cases hj : j = i
    · subst j
      by_cases ha : D i i = true <;>
        simp [rationalMatrix, closedMatrix, adjacencyMatrix, ha]
    · by_cases ha : D j i = true <;>
        simp [rationalMatrix, closedMatrix, adjacencyMatrix, hj, ha]
  simp_rw [he, mul_add]
  rw [Finset.sum_add_distrib]
  have hd : (∑ j : M, p j * (if j = i then 1 else 0)) = p i := by simp
  rw [hd]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  split_ifs <;> ring

/-- Every nonempty rationally self-dual host has a real probability dual.
Certificate existence is derived, not added as an LP assumption. -/
theorem realDual_of_selfDual {q : ℕ} {D : CH.Digraph} {M : Finset ℕ}
    (hSD : SelfDual q D M) (hM : M.Nonempty) : ∃ p, RealDual q D M 1 p := by
  letI : Nonempty M := ⟨⟨hM.choose, hM.choose_spec⟩⟩
  let R := rationalMatrix q (adjacencyMatrix D M)
  have good : ∀ w : M → ℚ, (∀ v, 0 ≤ w v) →
      ∃ v : M, (∑ u : M, R v u * w u) ≤ ∑ u : M, w u := by
    intro w hw
    have hn : ∀ v ∈ M, 0 ≤ extendWeight M w v := by
      intro v hv
      simpa only [extendWeight_on M w ⟨v, hv⟩] using hw ⟨v, hv⟩
    obtain ⟨v, hv, hs⟩ := exists_small_row hSD hM (extendWeight M w) hn
    refine ⟨⟨v, hv⟩, ?_⟩
    rw [row_extendWeight q D M w ⟨v, hv⟩, mass_extendWeight] at hs
    exact hs
  obtain ⟨p, hp, hm, hc⟩ := FiniteDual.dual_of_rational_small R good
  refine ⟨realExtendWeight M p, ?_, ?_, ?_⟩
  · intro v hv
    simpa only [realExtendWeight_on M p ⟨v, hv⟩] using hp ⟨v, hv⟩
  · rw [realMass_extendWeight]; exact hm
  · intro v hv
    rw [realCol_extendWeight q D M p ⟨v, hv⟩]
    exact hc ⟨v, hv⟩

theorem realMass_rat (V : Finset ℕ) (w : ℕ → ℚ) :
    realMass V (fun v => (w v : ℝ)) = (mass V w : ℝ) := by simp [realMass, mass]

theorem realRow_rat (q : ℕ) (D : CH.Digraph) (V : Finset ℕ) (w : ℕ → ℚ) (v : ℕ) :
    realRow q D V (fun u => (w u : ℝ)) v = (row q D V w v : ℝ) := by
  simp [realRow, row, realOutW, outW, apply_ite]

theorem realCol_rat (q : ℕ) (D : CH.Digraph) (V : Finset ℕ) (w : ℕ → ℚ) (v : ℕ) :
    realCol q D V (fun u => (w u : ℝ)) v = (col q D V w v : ℝ) := by
  simp [realCol, col, realInW, inW, apply_ite]

end LeanCH.BR.WeightedSD
