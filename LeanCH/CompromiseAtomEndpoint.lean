module

public import LeanCH.CompromiseSmallIncoming

set_option linter.style.header false

/-! Equality at the three-halves atom floor forces an exact deleted-arc
certificate and a rigid inverse row. These are necessary conditions,
not an exclusion of the equality case. -/

open Finset CH.CompromiseGame CH.CompromiseSeven CH.CompromiseWeighted
open CH.CompromiseDeletion CH.CompromiseCritical CH.CompromiseInverse
open CH.CompromisePerturbation CH.CompromiseArcMinimal CH.CompromiseLostArc
open CH.CompromiseRowRepair CH.CompromiseColumnCoupling CH.CompromiseArcLoss
open CH.CompromiseCertificateCharge
open CH.CompromiseNoBypass CH.CompromiseSmallIncoming CH.CompromiseUnitMinimal
open CH.CompromiseMinimumWeight
public section

namespace CH.CompromiseAtomEndpoint

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (adj : V → V → Prop) [DecidableRel adj]

theorem arc_payoff_identity (i j : V) (hne : i ≠ j) (edge : adj i j)
    (w p : V → ℝ) :
    payoff (coefficient (CH.ArcMinimal.eraseArc adj i j)) w p =
      payoff (coefficient adj) w p +
      p i * ((2 + newHead adj i j) * w j - mass w (lostSecond adj i j)) -
      p j * w i - mass p (lostParents adj i j) * w j := by
  have h := payoff_loss (coefficient adj) (coefficient (CH.ArcMinimal.eraseArc adj i j))
    i (changeRow adj i j) w p
  change payoff (arcLoss adj i j) w p = _ at h
  rw [arc_loss_payoff adj i j hne edge, payoff_shift, change_pairing] at h
  linarith

/-- Every fair probability of this deletion has the stated equality
properties. Positivity of w is explicit in this local theorem. -/
theorem endpoint_certificate (noDigon : ∀ v u, adj v u → ¬ adj u v)
    (noTri : ∀ v u z, adj v u → adj u z → ¬ adj z v)
    (w : V → ℝ) (wp : ∀ v, 0 < w v) (kappa : ℝ) (kp : 0 < kappa)
    (rows : ∀ v, surplus adj w v ≤ -kappa)
    (i j u : V) (edge : adj i j) (other : adj i u) (hne : u ≠ j)
    (noBypass : newHead adj i j = 0) (boundary : 2 * w j = 3 * kappa)
    (p : V → ℝ) (hp : p ∈ simplex)
    (fair : ∀ v, 0 ≤ col (coefficient (CH.ArcMinimal.eraseArc adj i j)) p v) :
    p i = 1 / 3 ∧ p j = 0 ∧ mass p (lostParents adj i j) = 0 ∧
      lostSecond adj i j = ∅ ∧
      ∀ v, col (coefficient (CH.ArcMinimal.eraseArc adj i j)) p v = 0 := by
  have hw : ∀ v, 0 ≤ w v := fun v => (wp v).le
  have ij : i ≠ j := by intro h; subst j; exact noDigon i i edge edge
  have nd : ∀ v z, CH.ArcMinimal.eraseArc adj i j v z →
      ¬ CH.ArcMinimal.eraseArc adj i j z v := fun v z h hh => noDigon v z h.1 hh.1
  have nt : ∀ v z a, CH.ArcMinimal.eraseArc adj i j v z →
      CH.ArcMinimal.eraseArc adj i j z a → ¬ CH.ArcMinimal.eraseArc adj i j a v :=
    fun v z a h hz hh => noTri v z a h.1 hz.1 hh.1
  have er : CH.ArcMinimal.eraseArc adj i j i u := ⟨other, fun h => hne h.2⟩
  have tb := fair_tail_bound _ nd nt p hp fair i u er
  have ti : 3 * p i ≤ 1 := by linarith [hp.1 u]
  have budget := deficit_budget adj i j ij edge p w hw fair hp kappa rows
  rw [noBypass] at budget
  have ln := weight_nonneg w hw (lostSecond adj i j)
  have hn := weight_nonneg p hp.1 (lostParents adj i j)
  have t1 := mul_nonneg (hp.1 j) (hw i)
  have t2 := mul_nonneg hn (hw j)
  have t3 := mul_nonneg (hp.1 i) ln
  have wi : p i = 1 / 3 := by nlinarith
  have wj : p j = 0 := by nlinarith [wp i]
  have hz : mass p (lostParents adj i j) = 0 := by nlinarith [wp j]
  have lz : mass w (lostSecond adj i j) = 0 := by nlinarith
  have le : lostSecond adj i j = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro a ha
    have hh : w a ≤ mass w (lostSecond adj i j) := single_le_sum (fun v _ => hw v) ha
    linarith [wp a]
  refine ⟨wi, wj, hz, le, ?_⟩
  have old : payoff (coefficient adj) w p ≤ -kappa := by
    calc
      _ = ∑ v, p v * surplus adj w v := by simp [payoff, row_coefficient]
      _ ≤ ∑ v, p v * (-kappa) := sum_le_sum (fun v _ =>
        mul_le_mul_of_nonneg_left (rows v) (hp.1 v))
      _ = -kappa := by simp [← sum_mul, hp.2]
  have ident := arc_payoff_identity adj i j ij edge w p
  rw [noBypass, wi, wj, hz, lz] at ident
  have value : payoff (coefficient (CH.ArcMinimal.eraseArc adj i j)) w p ≤ 0 := by
    linarith
  rw [payoff_transpose] at value
  intro v
  have term : w v * col (coefficient (CH.ArcMinimal.eraseArc adj i j)) p v ≤ 0 := by
    exact (single_le_sum (fun a _ => mul_nonneg (hw a) (fair a)) (mem_univ v)).trans value
  exact le_antisymm (by nlinarith [wp v]) (fair v)

theorem endpoint_inverse_row (noDigon : ∀ v u, adj v u → ¬ adj u v)
    (noTri : ∀ v u z, adj v u → adj u z → ¬ adj z v)
    (deleted : DeletedFair adj) (minimal : WeightedArcMinimal adj)
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) (kappa : ℝ) (kp : 0 < kappa)
    (rows : ∀ v, surplus adj w v ≤ -kappa)
    (i j u : V) (edge : adj i j) (other : adj i u) (hne : u ≠ j)
    (noBypass : newHead adj i j = 0) (boundary : 2 * w j = 3 * kappa) :
    Q adj j i = 1 / 2 ∧ Q adj j j = 0 ∧ (∑ k, Q adj j k) = 3 / 2 ∧
      (∀ v, adj i v → Q adj j v = 0) ∧
      ∃ p ∈ simplex, (∀ k, p k = (2 / 3) * Q adj j k) ∧
        ∀ k, col (coefficient (CH.ArcMinimal.eraseArc adj i j)) p k = 0 := by
  have noLoop (v : V) : ¬ adj v v := fun h => noDigon v v h h
  have bad : ∀ v, surplus adj w v < 0 := fun v => lt_of_le_of_lt (rows v) (by linarith)
  have wp := deleted_fair_full_support adj deleted w hw bad
  obtain ⟨p, hp, fair, _, _⟩ :=
    deleted_certificate_coupling adj noLoop deleted minimal w hw bad i j edge
  obtain ⟨pi, pj, ph, le, flat⟩ :=
    endpoint_certificate adj noDigon noTri w wp kappa kp rows i j u edge other hne
      noBypass boundary p hp fair
  have ij : i ≠ j := by intro h; subst j; exact noLoop i edge
  have unit := (graph_inverse_nonpos adj deleted w hw bad).1
  have shape (k : V) : p k = (2 / 3) * Q adj j k := by
    have old : payoff (coefficient adj) (fun v => Q adj v k) p = -p k := by
      change payoff (CH.CompromiseInverse.matrix adj)
        (fun v => negativeInverse (CH.CompromiseInverse.matrix adj) v k) p = _
      simp [payoff, inverse_column _ unit, mul_ite]
    have now : payoff (coefficient (CH.ArcMinimal.eraseArc adj i j))
        (fun v => Q adj v k) p = 0 := by
      rw [payoff_transpose]
      simp [flat]
    have ident := arc_payoff_identity adj i j ij edge (fun v => Q adj v k) p
    rw [old, now, pi, pj, ph, noBypass, le] at ident
    simp only [mass, sum_empty] at ident
    linarith
  have qi : Q adj j i = 1 / 2 := by linarith [shape i]
  have qj : Q adj j j = 0 := by linarith [shape j]
  have qs : (∑ k, Q adj j k) = 3 / 2 := by
    have hh := hp.2
    simp_rw [shape] at hh
    rw [← mul_sum] at hh
    linarith
  refine ⟨qi, qj, qs, ?_, p, hp, shape, flat⟩
  intro v hv
  by_cases vj : v = j
  · subst v
    exact qj
  · have nd : ∀ a b, CH.ArcMinimal.eraseArc adj i j a b →
        ¬ CH.ArcMinimal.eraseArc adj i j b a := fun a b h hh => noDigon a b h.1 hh.1
    have nt : ∀ a b c, CH.ArcMinimal.eraseArc adj i j a b →
        CH.ArcMinimal.eraseArc adj i j b c → ¬ CH.ArcMinimal.eraseArc adj i j c a :=
      fun a b c h hh hhh => noTri a b c h.1 hh.1 hhh.1
    have he : CH.ArcMinimal.eraseArc adj i j i v := ⟨hv, fun h => vj h.2⟩
    have bound := fair_tail_bound _ nd nt p hp fair i v he
    have pv : p v = 0 := by linarith [hp.1 v]
    linarith [shape v]

/-- At any atom attaining the floor, the previous small-incoming
classification supplies the no-bypass arc required above. -/
theorem atom_endpoint_structure [Nonempty V]
    (noDigon : ∀ v u, adj v u → ¬ adj u v)
    (noTri : ∀ v u z, adj v u → adj u z → ¬ adj z v)
    (deleted : DeletedFair adj) (minimal : WeightedArcMinimal adj)
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) (kappa : ℝ) (kp : 0 < kappa)
    (rows : ∀ v, surplus adj w v ≤ -kappa) (j : V)
    (boundary : 2 * w j = 3 * kappa) :
    Q adj j j = 0 ∧ (∑ k, Q adj j k) = 3 / 2 ∧
      ∃ i, adj i j ∧ newHead adj i j = 0 ∧ Q adj j i = 1 / 2 ∧
        ∀ v, adj i v → Q adj j v = 0 := by
  have bad : ∀ v, surplus adj w v < 0 := fun v => lt_of_le_of_lt (rows v) (by linarith)
  obtain ⟨unit, sign⟩ := graph_inverse_nonpos adj deleted w hw bad
  have qn : ∀ v u, 0 ≤ Q adj v u := negativeInverse_nonneg _ sign
  have ip (v : V) : (inN adj v).Nonempty := card_pos.mp (in_positive adj unit qn v)
  have counts := below_five_thirds_counts adj noDigon noTri deleted minimal w hw kappa kp
    rows j (by linarith)
  have nz : (noBypassParents adj j).Nonempty := by
    by_contra hn
    have four := four_of_no_sink adj noDigon noTri j (ip j) (not_nonempty_iff_eq_empty.mp hn)
    rcases counts with hc | ⟨hc, _⟩ <;> omega
  obtain ⟨i, hi⟩ := nz
  have edge := (mem_inN adj j i).mp (no_bypass_subset adj j hi)
  have floor := minimum_weight_bound adj noDigon noTri deleted minimal w hw kappa kp rows
  obtain ⟨u, other, hne⟩ := low_weight_branches adj noDigon w hw kappa kp rows floor ip
    j (by linarith) i edge
  have nb := no_bypass_zero adj j i hi
  obtain ⟨qi, qj, qs, zeros, _⟩ := endpoint_inverse_row adj noDigon noTri deleted minimal
    w hw kappa kp rows i j u edge other hne nb boundary
  exact ⟨qj, qs, i, edge, nb, qi, zeros⟩

end CH.CompromiseAtomEndpoint

#print axioms CH.CompromiseAtomEndpoint.arc_payoff_identity
#print axioms CH.CompromiseAtomEndpoint.endpoint_certificate
#print axioms CH.CompromiseAtomEndpoint.endpoint_inverse_row
#print axioms CH.CompromiseAtomEndpoint.atom_endpoint_structure
