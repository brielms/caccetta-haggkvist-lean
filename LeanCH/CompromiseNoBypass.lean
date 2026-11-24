module

public import LeanCH.CompromiseMinimumWeight

set_option linter.style.header false

/-! Incoming arcs without a surviving two-step bypass pay twice the
outside inverse mass. This retains the exact deleted-head coefficient. -/

open Finset CH.CompromiseGame CH.CompromiseSeven CH.CompromiseWeighted
open CH.CompromiseDeletion CH.CompromiseCritical CH.CompromiseInverse
open CH.CompromisePerturbation CH.CompromiseArcMinimal CH.CompromiseLostArc
open CH.CompromiseRowRepair CH.CompromiseColumnCoupling CH.CompromiseArcLoss
open CH.CompromiseSharedPaths CH.CompromiseCertificateCharge CH.CompromiseMinimumWeight
public section

namespace CH.CompromiseNoBypass

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (adj : V → V → Prop) [DecidableRel adj]

@[expose] def noBypassParents (j : V) : Finset V :=
  (inN adj j).filter (fun i => j ∉ second (CH.ArcMinimal.eraseArc adj i j) i)

theorem no_bypass_subset (j : V) : noBypassParents adj j ⊆ inN adj j := filter_subset _ _

theorem no_bypass_zero (j i : V) (h : i ∈ noBypassParents adj j) : newHead adj i j = 0 := by
  simp only [newHead, ite_eq_right (mem_filter.mp h).2]

/-- These are exactly the sinks in the old incoming subgraph. -/
theorem no_bypass_iff (noLoop : ∀ v, ¬ adj v v) (j i : V) :
    i ∈ noBypassParents adj j ↔ adj i j ∧ ∀ a ∈ inN adj j, ¬ adj i a := by
  constructor
  · intro h
    obtain ⟨hi, hn⟩ := mem_filter.mp h
    have hij := (mem_inN adj j i).mp hi
    refine ⟨hij, ?_⟩
    intro a ha hia
    apply hn
    apply (new_head_iff adj noLoop i j hij).mpr
    exact mem_filter.mpr ⟨(mem_outN adj i j).mpr hij,
      a, (mem_outN adj i a).mpr hia, (mem_inN adj j a).mp ha⟩
  · rintro ⟨hij, hs⟩
    apply mem_filter.mpr
    refine ⟨(mem_inN adj j i).mpr hij, ?_⟩
    intro h
    obtain ⟨_, _, a, hia, haj⟩ := (mem_second _ i j).mp h
    exact hs a ((mem_inN adj j a).mpr haj.1) hia.1

/-- At the deleted head, the precise gain is two plus the bypass
indicator, rather than the coarser universal bound of three. -/
theorem deleted_head_budget (noDigon : ∀ v u, adj v u → ¬ adj u v)
    (noTri : ∀ v u z, adj v u → adj u z → ¬ adj z v)
    (i j : V) (edge : adj i j) (p : V → ℝ) (hp : p ∈ simplex)
    (fair : ∀ u, 0 ≤ col (coefficient (CH.ArcMinimal.eraseArc adj i j)) p u) :
    p j + 3 * inWeight adj p j ≤ 1 + (2 + newHead adj i j) * p i := by
  have hne : i ≠ j := by intro h; subst j; exact noDigon i i edge edge
  have jl : j ∉ lostSecond adj i j := fun h =>
    ((mem_second adj i j).mp (mem_sdiff.mp h).1).2.1 edge
  have hc : changeRow adj i j j = 2 + newHead adj i j := by simp [changeRow, jl]
  have pointwise (v : V) : coefficient (CH.ArcMinimal.eraseArc adj i j) v j ≤
      CH.LinearProgram.matrix adj v j + if v = i then 2 + newHead adj i j else 0 := by
    have h := coefficient_bound adj i j hne edge v j
    simp only [shiftRow, hc] at h
    linarith [coefficient_le_ch adj noDigon noTri v j]
  have hh : col (coefficient (CH.ArcMinimal.eraseArc adj i j)) p j ≤
      col (CH.LinearProgram.matrix adj) p j + p i * (2 + newHead adj i j) := by
    calc
      _ ≤ ∑ v, p v * (CH.LinearProgram.matrix adj v j +
          if v = i then 2 + newHead adj i j else 0) :=
        sum_le_sum (fun v _ => mul_le_mul_of_nonneg_left (pointwise v) (hp.1 v))
      _ = _ := by simp [col, mul_add, sum_add_distrib, mul_ite]
  rw [CH.LinearProgram.col_matrix, hp.2] at hh
  linarith [fair j]

theorem outside_no_bypass_charge (noDigon : ∀ v u, adj v u → ¬ adj u v)
    (noTri : ∀ v u z, adj v u → adj u z → ¬ adj z v)
    (deleted : DeletedFair adj) (minimal : WeightedArcMinimal adj)
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) (bad : ∀ v, surplus adj w v < 0)
    (i j u : V) (edge : adj i j) (other : adj i u) (hne : u ≠ j)
    (noBypass : newHead adj i j = 0) :
    2 ≤ 3 * mass (fun k => Q adj j k) (univ \ inN adj j) := by
  have noLoop (v : V) : ¬ adj v v := fun h => noDigon v v h h
  obtain ⟨p, hp, fair, _, ht⟩ :=
    deleted_certificate_coupling adj noLoop deleted minimal w hw bad i j edge
  have qn : ∀ v k, 0 ≤ Q adj v k := negativeInverse_nonneg _
    (graph_inverse_nonpos adj deleted w hw bad).2
  have nd : ∀ v z, CH.ArcMinimal.eraseArc adj i j v z →
      ¬ CH.ArcMinimal.eraseArc adj i j z v := fun v z h hh => noDigon v z h.1 hh.1
  have nt : ∀ v z a, CH.ArcMinimal.eraseArc adj i j v z →
      CH.ArcMinimal.eraseArc adj i j z a → ¬ CH.ArcMinimal.eraseArc adj i j a v :=
    fun v z a h hz hh => noTri v z a h.1 hz.1 hh.1
  have er : CH.ArcMinimal.eraseArc adj i j i u := ⟨other, fun h => hne h.2⟩
  have tb := fair_tail_bound _ nd nt p hp fair i u er
  have ti : 3 * p i ≤ 1 := by linarith [hp.1 u]
  have head := deleted_head_budget adj noDigon noTri i j edge p hp fair
  rw [noBypass] at head
  have total : mass p (univ \ inN adj j) + inWeight adj p j = 1 := by
    have hh := sum_sdiff (f := p) (subset_univ (inN adj j))
    simpa only [mass, inWeight, hp.2] using hh
  have outside : 2 ≤ 3 * mass p (univ \ inN adj j) + 2 * p i := by
    linarith [hp.1 j]
  have dominate (k : V) : p k ≤ (2 * p i) * Q adj j k := by
    have hl := payoff_nonnegative _ (arc_loss_nonnegative adj noLoop i j edge)
      (fun a => Q adj a k) p (fun a => qn a k) hp.1
    have ml := weight_nonneg (fun a => Q adj a k) (fun a => qn a k) (lostSecond adj i j)
    have hm := mul_nonneg (hp.1 i) ml
    have hh := ht k
    rw [noBypass] at hh
    nlinarith
  have hs := sum_le_sum (s := univ \ inN adj j) (fun k _ => dominate k)
  rw [← mul_sum] at hs
  change mass p (univ \ inN adj j) ≤ (2 * p i) *
    mass (fun k => Q adj j k) (univ \ inN adj j) at hs
  have outnn := weight_nonneg (fun k => Q adj j k) (fun k => qn j k) (univ \ inN adj j)
  nlinarith

/-- Each no-bypass parent costs one extra unit after the common
denominator six is cleared. Distinct parents are counted once. -/
theorem incoming_weighted_charge (noLoop : ∀ v, ¬ adj v v)
    (deleted : DeletedFair adj) (minimal : WeightedArcMinimal adj)
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) (bad : ∀ v, surplus adj w v < 0) (j : V) :
    2 * ((inN adj j).card : ℝ) + ((noBypassParents adj j).card : ℝ) ≤
      6 * mass (fun k => Q adj j k) (inN adj j) := by
  have qn : ∀ v k, 0 ≤ Q adj v k := negativeInverse_nonneg _
    (graph_inverse_nonpos adj deleted w hw bad).2
  have term (i : V) (hi : i ∈ inN adj j) :
      2 + (if i ∈ noBypassParents adj j then (1 : ℝ) else 0) ≤ 6 * Q adj j i := by
    have edge := (mem_inN adj j i).mp hi
    by_cases hn : i ∈ noBypassParents adj j
    · have hs := sharp_arc_charge adj noLoop deleted minimal w hw bad i j edge
      rw [no_bypass_zero adj j i hn] at hs
      have hl := weight_nonneg (fun a => Q adj a i) (fun a => qn a i) (lostSecond adj i j)
      simp only [ite_eq_left hn]
      linarith
    · have hs := arc_lower adj deleted minimal w hw bad i j edge
      simp only [ite_eq_right hn]
      linarith
  have count : (∑ i ∈ inN adj j, if i ∈ noBypassParents adj j then (1 : ℝ) else 0) =
      ((noBypassParents adj j).card : ℝ) := by
    rw [← sum_filter]
    have he : (inN adj j).filter (fun i => i ∈ noBypassParents adj j) = noBypassParents adj j := by
      ext i
      simp only [mem_filter]
      exact and_iff_right_of_imp (fun h => no_bypass_subset adj j h)
    rw [he]
    simp
  have hs := sum_le_sum term
  rw [sum_add_distrib, count, ← mul_sum] at hs
  simp only [sum_const, nsmul_eq_mul] at hs
  change _ ≤ 6 * mass (fun k => Q adj j k) (inN adj j) at hs
  nlinarith

theorem no_bypass_row_bound (noDigon : ∀ v u, adj v u → ¬ adj u v)
    (noTri : ∀ v u z, adj v u → adj u z → ¬ adj z v)
    (deleted : DeletedFair adj) (minimal : WeightedArcMinimal adj)
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) (bad : ∀ v, surplus adj w v < 0)
    (j : V) (ne : (noBypassParents adj j).Nonempty)
    (branches : ∀ i, adj i j → ∃ u, adj i u ∧ u ≠ j) :
    2 * ((inN adj j).card : ℝ) + ((noBypassParents adj j).card : ℝ) + 4 ≤
      6 * ∑ k, Q adj j k := by
  obtain ⟨i, hi⟩ := ne
  have edge := (mem_inN adj j i).mp (no_bypass_subset adj j hi)
  obtain ⟨u, other, hne⟩ := branches i edge
  have outside := outside_no_bypass_charge adj noDigon noTri deleted minimal w hw bad
    i j u edge other hne (no_bypass_zero adj j i hi)
  have noLoop (v : V) : ¬ adj v v := fun h => noDigon v v h h
  have inside := incoming_weighted_charge adj noLoop deleted minimal w hw bad j
  have split := sum_sdiff (f := fun k => Q adj j k) (subset_univ (inN adj j))
  change mass (fun k => Q adj j k) (univ \ inN adj j) +
    mass (fun k => Q adj j k) (inN adj j) = ∑ k, Q adj j k at split
  linarith

end CH.CompromiseNoBypass

#print axioms CH.CompromiseNoBypass.no_bypass_iff
#print axioms CH.CompromiseNoBypass.deleted_head_budget
#print axioms CH.CompromiseNoBypass.outside_no_bypass_charge
#print axioms CH.CompromiseNoBypass.no_bypass_row_bound
