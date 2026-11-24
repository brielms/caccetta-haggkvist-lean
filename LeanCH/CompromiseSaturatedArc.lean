module

public import LeanCH.CompromiseAtomEndpoint

set_option linter.style.header false

/-! An arc whose net tail gain is exactly three common deficits has a
fully saturated fair certificate. The gain can include a private loss,
so this extends the no-bypass atom-endpoint calculation. -/

open Finset CH.CompromiseGame CH.CompromiseSeven CH.CompromiseWeighted
open CH.CompromiseDeletion CH.CompromiseCritical CH.CompromiseInverse
open CH.CompromisePerturbation CH.CompromiseArcMinimal CH.CompromiseLostArc
open CH.CompromiseColumnCoupling CH.CompromiseArcLoss CH.CompromiseCertificateCharge
open CH.CompromiseAtomEndpoint
public section

namespace CH.CompromiseSaturatedArc

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (adj : V → V → Prop) [DecidableRel adj]

theorem saturated_certificate (noDigon : ∀ v u, adj v u → ¬ adj u v)
    (noTri : ∀ v u z, adj v u → adj u z → ¬ adj z v)
    (w : V → ℝ) (wp : ∀ v, 0 < w v) (kappa : ℝ) (kp : 0 < kappa)
    (rows : ∀ v, surplus adj w v ≤ -kappa)
    (i j u : V) (edge : adj i j) (other : adj i u) (hne : u ≠ j)
    (gain : (2 + newHead adj i j) * w j - mass w (lostSecond adj i j) = 3 * kappa)
    (p : V → ℝ) (hp : p ∈ simplex)
    (fair : ∀ v, 0 ≤ col (coefficient (CH.ArcMinimal.eraseArc adj i j)) p v) :
    p i = 1 / 3 ∧ p j = 0 ∧ mass p (lostParents adj i j) = 0 ∧
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
  rw [gain] at budget
  have hn := weight_nonneg p hp.1 (lostParents adj i j)
  have t1 := mul_nonneg (hp.1 j) (hw i)
  have t2 := mul_nonneg hn (hw j)
  have pi : p i = 1 / 3 := by nlinarith
  have pj : p j = 0 := by nlinarith [wp i]
  have ph : mass p (lostParents adj i j) = 0 := by nlinarith [wp j]
  refine ⟨pi, pj, ph, ?_⟩
  have old : payoff (coefficient adj) w p ≤ -kappa := by
    calc
      _ = ∑ v, p v * surplus adj w v := by simp [payoff, row_coefficient]
      _ ≤ ∑ v, p v * (-kappa) := sum_le_sum (fun v _ =>
        mul_le_mul_of_nonneg_left (rows v) (hp.1 v))
      _ = -kappa := by simp [← sum_mul, hp.2]
  have ident := arc_payoff_identity adj i j ij edge w p
  rw [gain, pi, pj, ph] at ident
  have value : payoff (coefficient (CH.ArcMinimal.eraseArc adj i j)) w p ≤ 0 := by
    linarith
  rw [payoff_transpose] at value
  intro v
  have term : w v * col (coefficient (CH.ArcMinimal.eraseArc adj i j)) p v ≤ 0 :=
    (single_le_sum (fun a _ => mul_nonneg (hw a) (fair a)) (mem_univ v)).trans value
  exact le_antisymm (by nlinarith [wp v]) (fair v)

/-- The actual fair certificate is a difference of inverse rows, with
one row for every private lost endpoint. -/
theorem saturated_inverse_certificate (noDigon : ∀ v u, adj v u → ¬ adj u v)
    (noTri : ∀ v u z, adj v u → adj u z → ¬ adj z v)
    (deleted : DeletedFair adj) (minimal : WeightedArcMinimal adj)
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) (kappa : ℝ) (kp : 0 < kappa)
    (rows : ∀ v, surplus adj w v ≤ -kappa)
    (i j u : V) (edge : adj i j) (other : adj i u) (hne : u ≠ j)
    (gain : (2 + newHead adj i j) * w j - mass w (lostSecond adj i j) = 3 * kappa) :
    ∃ p ∈ simplex, p i = 1 / 3 ∧ p j = 0 ∧
      (∀ k, col (coefficient (CH.ArcMinimal.eraseArc adj i j)) p k = 0) ∧
      (∀ k, p k = ((2 + newHead adj i j) * Q adj j k -
        mass (fun v => Q adj v k) (lostSecond adj i j)) / 3) ∧
      ∀ v, adj i v → v ≠ j → p v = 0 := by
  have noLoop (v : V) : ¬ adj v v := fun h => noDigon v v h h
  have bad : ∀ v, surplus adj w v < 0 := fun v => lt_of_le_of_lt (rows v) (by linarith)
  have wp := deleted_fair_full_support adj deleted w hw bad
  obtain ⟨p, hp, fair, _, _⟩ :=
    deleted_certificate_coupling adj noLoop deleted minimal w hw bad i j edge
  obtain ⟨pi, pj, ph, flat⟩ := saturated_certificate adj noDigon noTri w wp kappa kp rows
    i j u edge other hne gain p hp fair
  have ij : i ≠ j := by intro h; subst j; exact noLoop i edge
  have unit := (graph_inverse_nonpos adj deleted w hw bad).1
  refine ⟨p, hp, pi, pj, flat, ?_, ?_⟩
  · intro k
    have old : payoff (coefficient adj) (fun v => Q adj v k) p = -p k := by
      change payoff (CH.CompromiseInverse.matrix adj)
        (fun v => negativeInverse (CH.CompromiseInverse.matrix adj) v k) p = _
      simp [payoff, inverse_column _ unit, mul_ite]
    have now : payoff (coefficient (CH.ArcMinimal.eraseArc adj i j))
        (fun v => Q adj v k) p = 0 := by rw [payoff_transpose]; simp [flat]
    have ident := arc_payoff_identity adj i j ij edge (fun v => Q adj v k) p
    rw [old, now, pi, pj, ph] at ident
    linarith
  · intro v hv vj
    have nd : ∀ a b, CH.ArcMinimal.eraseArc adj i j a b →
        ¬ CH.ArcMinimal.eraseArc adj i j b a := fun a b h hh => noDigon a b h.1 hh.1
    have nt : ∀ a b c, CH.ArcMinimal.eraseArc adj i j a b →
        CH.ArcMinimal.eraseArc adj i j b c → ¬ CH.ArcMinimal.eraseArc adj i j c a :=
      fun a b c h hh hhh => noTri a b c h.1 hh.1 hhh.1
    have he : CH.ArcMinimal.eraseArc adj i j i v := ⟨hv, fun h => vj h.2⟩
    have bound := fair_tail_bound _ nd nt p hp fair i v he
    linarith [hp.1 v]

/-- A row of total mass 3/2 cannot put all that mass at a nonsink:
its product with M at an outgoing head would be -3, not 0 or -1. -/
theorem inverse_row_not_concentrated (noDigon : ∀ v u, adj v u → ¬ adj u v)
    (unit : IsUnit (CH.CompromiseInverse.matrix adj)) (qn : ∀ v u, 0 ≤ Q adj v u)
    (x b j : V) (edge : adj b j)
    (total : (∑ k, Q adj x k) = 3 / 2) : Q adj x b ≠ 3 / 2 := by
  intro entry
  have rest : ∑ k ∈ univ.erase b, Q adj x k = 0 := by
    have hs := sum_erase_add (univ : Finset V) (fun k => Q adj x k) (mem_univ b)
    rw [total, entry] at hs
    linarith
  have zero (k : V) (hk : k ≠ b) : Q adj x k = 0 := by
    have hh : Q adj x k ≤ ∑ a ∈ univ.erase b, Q adj x a :=
      single_le_sum (fun a _ => qn x a) (by simp [hk])
    rw [rest] at hh
    exact le_antisymm hh (qn x k)
  have inv := inverse_row (CH.CompromiseInverse.matrix adj) unit x j
  change col (coefficient adj) (fun k => Q adj x k) j = if j = x then -1 else 0 at inv
  have collapse : col (coefficient adj) (fun k => Q adj x k) j =
      Q adj x b * coefficient adj b j := by
    apply sum_eq_single b
    · intro k _ hk
      exact mul_eq_zero.mpr (Or.inl (zero k hk))
    · simp
  have hs : j ∉ second adj b := fun h => ((mem_second adj b j).mp h).2.1 edge
  have coeff : coefficient adj b j = -2 := by
    simp [coefficient, CH.CompromisePacking.capacity, edge, noDigon b j edge, hs]
  rw [collapse, entry, coeff] at inv
  split_ifs at inv <;> norm_num at inv

end CH.CompromiseSaturatedArc

#print axioms CH.CompromiseSaturatedArc.saturated_certificate
#print axioms CH.CompromiseSaturatedArc.saturated_inverse_certificate
#print axioms CH.CompromiseSaturatedArc.inverse_row_not_concentrated
