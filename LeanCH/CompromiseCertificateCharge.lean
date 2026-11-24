module

public import LeanCH.CompromiseArcLoss

set_option linter.style.header false

/-! Why the deleted-graph fairness condition must be retained.
Without it the apparent joint coupling is equivalent to the separate
column bounds. With it, a tail retaining an arc has certificate mass
at most one third and forces a three-deficit repair cost. -/

open Finset CH.CompromiseGame CH.CompromiseSeven CH.CompromiseWeighted
open CH.CompromiseCritical CH.CompromiseInverse CH.CompromisePerturbation
open CH.CompromiseDeletion
open CH.CompromiseRowRepair CH.CompromiseArcMinimal CH.CompromiseLostArc
open CH.CompromiseColumnCoupling CH.CompromiseArcLoss
public section

namespace CH.CompromiseCertificateCharge

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Omitting fairness loses the apparent coupling: the point mass at
the tail already witnesses these inequalities. -/
theorem bare_coupling_iff (Q : V → V → ℝ) (qn : ∀ v u, 0 ≤ Q v u)
    (L H : Finset V) (i j : V) (hne : j ≠ i) (hi : i ∉ H) (a : ℝ) :
    (∃ p ∈ simplex, 0 < p i ∧ ∀ k,
      p k + p j * Q i k + p i * mass (fun u => Q u k) L ≤
        (a * p i - mass p H) * Q j k) ↔
      ∀ k, (if k = i then (1 : ℝ) else 0) + mass (fun u => Q u k) L ≤ a * Q j k := by
  constructor
  · rintro ⟨p, hp, pp, ht⟩ k
    have hh := mul_nonneg (weight_nonneg p hp.1 H) (qn j k)
    have hj := mul_nonneg (hp.1 j) (qn i k)
    have hc := ht k
    by_cases hk : k = i
    · subst k
      simp only [ite_true]
      nlinarith
    · simp only [ite_eq_right hk]
      have pn := hp.1 k
      nlinarith
  · intro hb
    refine ⟨point i, point_mem i, by simp [point], ?_⟩
    intro k
    have hm : mass (point i) H = 0 := by simp [mass, point, hi]
    simpa [point, hne, hm] using hb k

variable (adj : V → V → Prop) [DecidableRel adj]

/-- The compromise matrix is bounded above by the CH matrix, with
the difference accounting for vertices outside the local ball. -/
theorem coefficient_le_ch (noDigon : ∀ v u, adj v u → ¬ adj u v)
    (noTri : ∀ v u z, adj v u → adj u z → ¬ adj z v) (v u : V) :
    coefficient adj v u ≤ CH.LinearProgram.matrix adj v u := by
  have noLoop (x : V) : ¬ adj x x := fun h => noDigon x x h h
  by_cases he : u = v
  · subst u
    simp [coefficient, CH.CompromisePacking.capacity, CH.LinearProgram.matrix, noLoop]
  · by_cases ho : adj v u
    · have hi : ¬ adj u v := noDigon v u ho
      have hs : u ∉ second adj v := fun h => ((mem_second adj v u).mp h).2.1 ho
      norm_num [coefficient, CH.CompromisePacking.capacity, CH.LinearProgram.matrix,
        he, ho, hi, hs]
    · have hs : u ∈ second adj v → ¬ adj u v := by
        intro h
        obtain ⟨_, _, b, hvb, hbu⟩ := (mem_second adj v u).mp h
        exact noTri v b u hvb hbu
      by_cases hb : u ∈ second adj v
      · simp [coefficient, CH.CompromisePacking.capacity, CH.LinearProgram.matrix,
          he, ho, hb, hs hb]
      · by_cases hi : adj u v <;>
          simp [coefficient, CH.CompromisePacking.capacity, CH.LinearProgram.matrix, he, ho, hb, hi]

theorem fair_closed_in (noDigon : ∀ v u, adj v u → ¬ adj u v)
    (noTri : ∀ v u z, adj v u → adj u z → ¬ adj z v)
    (p : V → ℝ) (hp : p ∈ simplex) (fair : ∀ u, 0 ≤ col (coefficient adj) p u) (u : V) :
    p u + 3 * inWeight adj p u ≤ 1 := by
  have h : col (coefficient adj) p u ≤ col (CH.LinearProgram.matrix adj) p u :=
    sum_le_sum (fun v _ => mul_le_mul_of_nonneg_left
      (coefficient_le_ch adj noDigon noTri v u) (hp.1 v))
  rw [CH.LinearProgram.col_matrix, hp.2] at h
  linarith [fair u]

/-- A fair probability puts at most one third of its mass at any
vertex with an outgoing arc. -/
theorem fair_tail_bound (noDigon : ∀ v u, adj v u → ¬ adj u v)
    (noTri : ∀ v u z, adj v u → adj u z → ¬ adj z v)
    (p : V → ℝ) (hp : p ∈ simplex) (fair : ∀ u, 0 ≤ col (coefficient adj) p u)
    (i u : V) (edge : adj i u) : 3 * p i + p u ≤ 1 := by
  have hh := fair_closed_in adj noDigon noTri p hp fair u
  have hi : p i ≤ inWeight adj p u :=
    single_le_sum (fun v _ => hp.1 v) ((mem_inN adj u i).mpr edge)
  linarith

/-- The actual deleted-graph certificate, paired with a counterweight
of at least the stated deficit, pays that deficit and every arc loss. -/
theorem deficit_budget (i j : V) (hne : i ≠ j) (edge : adj i j)
    (p w : V → ℝ) (hw : ∀ v, 0 ≤ w v)
    (fair : ∀ u, 0 ≤ col (coefficient (CH.ArcMinimal.eraseArc adj i j)) p u)
    (hp : p ∈ simplex) (kappa : ℝ) (rows : ∀ v, surplus adj w v ≤ -kappa) :
    kappa + p j * w i + mass p (lostParents adj i j) * w j ≤
      p i * ((2 + newHead adj i j) * w j - mass w (lostSecond adj i j)) := by
  have hn : 0 ≤ payoff (coefficient (CH.ArcMinimal.eraseArc adj i j)) w p := by
    rw [payoff_transpose]
    exact sum_nonneg (fun u _ => mul_nonneg (hw u) (fair u))
  have hm : payoff (coefficient adj) w p ≤ -kappa := by
    calc
      _ = ∑ v, p v * surplus adj w v := by simp [payoff, row_coefficient]
      _ ≤ ∑ v, p v * (-kappa) := sum_le_sum (fun v _ =>
        mul_le_mul_of_nonneg_left (rows v) (hp.1 v))
      _ = -kappa := by simp [← sum_mul, hp.2]
  have hl := payoff_loss (coefficient adj) (coefficient (CH.ArcMinimal.eraseArc adj i j))
    i (changeRow adj i j) w p
  change payoff (arcLoss adj i j) w p = _ at hl
  rw [arc_loss_payoff adj i j hne edge, payoff_shift, change_pairing] at hl
  linarith

/-- Retaining another outgoing arc makes the required gain at least
three times the canonical defect, rather than merely one times it. -/
theorem three_deficit_charge (noDigon : ∀ v u, adj v u → ¬ adj u v)
    (noTri : ∀ v u z, adj v u → adj u z → ¬ adj z v)
    (minimal : WeightedArcMinimal adj) (w : V → ℝ) (hw : ∀ v, 0 ≤ w v)
    (kappa : ℝ) (kp : 0 < kappa) (rows : ∀ v, surplus adj w v ≤ -kappa)
    (i j u : V) (edge : adj i j) (other : adj i u) (hne : u ≠ j) :
    3 * kappa + mass w (lostSecond adj i j) ≤ (2 + newHead adj i j) * w j := by
  let : Nonempty V := ⟨i⟩
  have hij : i ≠ j := by intro h; subst j; exact noDigon i i edge edge
  have good : ¬ ∃ y ∈ simplex, ∀ v,
      row (coefficient (CH.ArcMinimal.eraseArc adj i j)) y v < 0 := by
    rintro ⟨y, hy, hb⟩
    obtain ⟨v, hv⟩ := minimal i j edge y hy.1
    have hh := hb v
    rw [row_coefficient] at hh
    linarith
  obtain ⟨p, hp, fair⟩ := (fair_iff_no_bad _).mpr good
  have nd : ∀ v z, CH.ArcMinimal.eraseArc adj i j v z →
      ¬ CH.ArcMinimal.eraseArc adj i j z v := fun v z h hh => noDigon v z h.1 hh.1
  have nt : ∀ v z a, CH.ArcMinimal.eraseArc adj i j v z →
      CH.ArcMinimal.eraseArc adj i j z a → ¬ CH.ArcMinimal.eraseArc adj i j a v :=
    fun v z a h hz hh => noTri v z a h.1 hz.1 hh.1
  have er : CH.ArcMinimal.eraseArc adj i j i u := ⟨other, fun h => hne h.2⟩
  have bound := fair_tail_bound _ nd nt p hp fair i u er
  have budget := deficit_budget adj i j hij edge p w hw fair hp kappa rows
  have loss1 := mul_nonneg (hp.1 j) (hw i)
  have loss2 := mul_nonneg (weight_nonneg p hp.1 (lostParents adj i j)) (hw j)
  have gainpos : 0 < (2 + newHead adj i j) * w j - mass w (lostSecond adj i j) := by
    by_contra hn
    have hh := mul_nonpos_of_nonneg_of_nonpos (hp.1 i) (le_of_not_gt hn)
    linarith
  have pn := hp.1 u
  nlinarith

end CH.CompromiseCertificateCharge

#print axioms CH.CompromiseCertificateCharge.bare_coupling_iff
#print axioms CH.CompromiseCertificateCharge.fair_closed_in
#print axioms CH.CompromiseCertificateCharge.deficit_budget
#print axioms CH.CompromiseCertificateCharge.three_deficit_charge
