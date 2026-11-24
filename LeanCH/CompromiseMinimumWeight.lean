module

public import LeanCH.CompromiseUnitMinimal

set_option linter.style.header false

/-! Weighted arc minimality strengthens the atom floor. A counterweight
with every surplus at most -kappa must put at least 3*kappa/2 at every
vertex. All minimality inputs remain explicit. -/

open Finset CH.CompromiseGame CH.CompromiseSeven CH.CompromiseWeighted
open CH.CompromiseDeletion CH.CompromiseCritical CH.CompromiseInverse
open CH.CompromisePerturbation CH.CompromiseArcMinimal CH.CompromiseLostArc
open CH.CompromiseColumnCoupling CH.CompromiseArcLoss
open CH.CompromiseSharedPaths CH.CompromiseCertificateCharge CH.CompromiseUnitMinimal
public section

namespace CH.CompromiseMinimumWeight

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (adj : V → V → Prop) [DecidableRel adj]

theorem inverse_weighted_row_bound (unit : IsUnit (CH.CompromiseInverse.matrix adj))
    (qn : ∀ v u, 0 ≤ Q adj v u) (w : V → ℝ) (kappa : ℝ)
    (rows : ∀ v, surplus adj w v ≤ -kappa) (v : V) :
    kappa * (∑ u, Q adj v u) ≤ w v := by
  have he : payoff (CH.CompromiseInverse.matrix adj) w (fun u => Q adj v u) = -w v := by
    erw [payoff_transpose]
    simp only [Q, inverse_row (CH.CompromiseInverse.matrix adj) unit]
    simp [mul_ite]
  have h : payoff (CH.CompromiseInverse.matrix adj) w (fun u => Q adj v u) ≤
      -kappa * (∑ u, Q adj v u) := by
    change (∑ u, Q adj v u * row (coefficient adj) w u) ≤ _
    simp only [row_coefficient]
    calc
      _ ≤ ∑ u, Q adj v u * (-kappa) := sum_le_sum (fun u _ =>
        mul_le_mul_of_nonneg_left (rows u) (qn v u))
      _ = _ := by rw [← sum_mul]; ring
  linarith

/-- A branching predecessor forces inverse-row mass outside the old
incoming set of its head. This uses actual deleted-graph fairness. -/
theorem outside_incoming_charge (noDigon : ∀ v u, adj v u → ¬ adj u v)
    (noTri : ∀ v u z, adj v u → adj u z → ¬ adj z v)
    (deleted : DeletedFair adj) (minimal : WeightedArcMinimal adj)
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) (bad : ∀ v, surplus adj w v < 0)
    (i j u : V) (edge : adj i j) (other : adj i u) (hne : u ≠ j) :
    1 ≤ 3 * mass (fun k => Q adj j k) (univ \ inN adj j) := by
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
  have cj := fair_closed_in _ nd nt p hp fair j
  have inc : inN (CH.ArcMinimal.eraseArc adj i j) j = (inN adj j).erase i := by
    ext v
    simp only [mem_inN, mem_erase, CH.ArcMinimal.eraseArc]
    tauto
  have split := sum_erase_add (inN adj j) p ((mem_inN adj j i).mpr edge)
  change mass p ((inN adj j).erase i) + p i = mass p (inN adj j) at split
  change p j + 3 * mass p (inN (CH.ArcMinimal.eraseArc adj i j) j) ≤ 1 at cj
  rw [inc] at cj
  have total : mass p (univ \ inN adj j) + mass p (inN adj j) = 1 := by
    have hh := sum_sdiff (f := p) (subset_univ (inN adj j))
    simpa only [mass, hp.2] using hh
  have outside : 1 ≤ 3 * mass p (univ \ inN adj j) := by linarith [hp.1 j]
  have nh : newHead adj i j ≤ 1 := by unfold newHead; split_ifs <;> norm_num
  have dominate (k : V) : p k ≤ (3 * p i) * Q adj j k := by
    have hl := payoff_nonnegative _ (arc_loss_nonnegative adj noLoop i j edge)
      (fun a => Q adj a k) p (fun a => qn a k) hp.1
    have ml := weight_nonneg (fun a => Q adj a k) (fun a => qn a k) (lostSecond adj i j)
    have hg : (2 + newHead adj i j) * Q adj j k -
        mass (fun a => Q adj a k) (lostSecond adj i j) ≤ 3 * Q adj j k := by
      nlinarith [qn j k]
    have hm := mul_le_mul_of_nonneg_left hg (hp.1 i)
    have hh := ht k
    nlinarith
  have hs := sum_le_sum (s := univ \ inN adj j) (fun k _ => dominate k)
  rw [← mul_sum] at hs
  change mass p (univ \ inN adj j) ≤ (3 * p i) *
    mass (fun k => Q adj j k) (univ \ inN adj j) at hs
  have outnn := weight_nonneg (fun k => Q adj j k) (fun k => qn j k) (univ \ inN adj j)
  nlinarith

theorem branch_row_bound (noDigon : ∀ v u, adj v u → ¬ adj u v)
    (noTri : ∀ v u z, adj v u → adj u z → ¬ adj z v)
    (deleted : DeletedFair adj) (minimal : WeightedArcMinimal adj)
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) (bad : ∀ v, surplus adj w v < 0)
    (i j u : V) (edge : adj i j) (other : adj i u) (hne : u ≠ j) :
    ((inN adj j).card : ℝ) + 1 ≤ 3 * ∑ k, Q adj j k := by
  have outside := outside_incoming_charge adj noDigon noTri deleted minimal w hw bad
    i j u edge other hne
  have charge := arc_lower adj deleted minimal w hw bad
  have inside := sum_le_sum (s := inN adj j)
    (fun k hk => charge k j ((mem_inN adj j k).mp hk))
  simp only [sum_const, nsmul_eq_mul, mul_one, ← mul_sum] at inside
  have split := sum_sdiff (f := fun k => Q adj j k) (subset_univ (inN adj j))
  change mass (fun k => Q adj j k) (univ \ inN adj j) +
    mass (fun k => Q adj j k) (inN adj j) = ∑ k, Q adj j k at split
  change ((inN adj j).card : ℝ) ≤ 3 * mass (fun k => Q adj j k) (inN adj j) at inside
  linarith

theorem minimum_predecessor_branches (noDigon : ∀ v u, adj v u → ¬ adj u v)
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) (bad : ∀ v, surplus adj w v < 0)
    (ip : ∀ v, (inN adj v).Nonempty) (j : V) (small : ∀ v, w j ≤ w v)
    (i : V) (edge : adj i j) : ∃ u, adj i u ∧ u ≠ j := by
  by_contra hn
  push Not at hn
  have singleton : outN adj i = {j} := by
    ext u
    simp only [mem_outN, mem_singleton]
    exact ⟨hn u, fun h => h ▸ edge⟩
  have outj : (outN adj j).Nonempty := by
    by_contra hh
    have he : outN adj j = ∅ := not_nonempty_iff_eq_empty.mp hh
    have zero : outWeight adj w j = 0 := by simp [outWeight, mass, he]
    have hs := weight_nonneg w hw (second adj j)
    have hi := weight_nonneg w hw (inN adj j)
    have hb := bad j
    dsimp [surplus, secondWeight, inWeight] at hb
    rw [zero] at hb
    linarith
  obtain ⟨a, ha⟩ := outj
  have hja : adj j a := (mem_outN adj j a).mp ha
  have secondA : a ∈ second adj i := by
    apply (mem_second adj i a).mpr
    refine ⟨?_, ?_, j, edge, hja⟩
    · intro he
      subst a
      exact noDigon i j edge hja
    · intro hia
      have he := hn a hia
      subst a
      exact noDigon j j hja hja
  obtain ⟨b, hb⟩ := ip i
  have so : w a ≤ secondWeight adj w i := single_le_sum (fun v _ => hw v) secondA
  have si : w b ≤ inWeight adj w i := single_le_sum (fun v _ => hw v) hb
  have oo : outWeight adj w i = w j := by simp [outWeight, mass, singleton]
  have hh := bad i
  dsimp [surplus] at hh
  rw [oo] at hh
  linarith [small a, small b]

/-- Three times the common deficit is at most twice every vertex mass.
The proof uses the minimum-weight vertex and its actual incoming arcs. -/
theorem minimum_weight_bound [Nonempty V]
    (noDigon : ∀ v u, adj v u → ¬ adj u v)
    (noTri : ∀ v u z, adj v u → adj u z → ¬ adj z v)
    (deleted : DeletedFair adj) (minimal : WeightedArcMinimal adj)
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) (kappa : ℝ) (kp : 0 < kappa)
    (rows : ∀ v, surplus adj w v ≤ -kappa) : ∀ v, 3 * kappa ≤ 2 * w v := by
  have bad : ∀ v, surplus adj w v < 0 := fun v => lt_of_le_of_lt (rows v) (by linarith)
  obtain ⟨unit, sign⟩ := graph_inverse_nonpos adj deleted w hw bad
  have qn : ∀ v u, 0 ≤ Q adj v u := negativeInverse_nonneg _ sign
  have ip (v : V) : (inN adj v).Nonempty := card_pos.mp (in_positive adj unit qn v)
  obtain ⟨j, _, small⟩ := exists_min_image univ w univ_nonempty
  have sj : ∀ v, w j ≤ w v := fun v => small v (mem_univ v)
  have branch := minimum_predecessor_branches adj noDigon w hw bad ip j sj
  have floor : 3 * kappa ≤ 2 * w j := by
    by_contra hn
    have below : 2 * w j < 3 * kappa := lt_of_not_ge hn
    have bypass (i : V) (edge : adj i j) : ∃ a ∈ inN adj j, adj i a := by
      obtain ⟨u, other, hne⟩ := branch i edge
      have gain := three_deficit_charge adj noDigon noTri minimal w hw kappa kp rows
        i j u edge other hne
      have secondJ : j ∈ second (CH.ArcMinimal.eraseArc adj i j) i := by
        by_contra hs
        have ln := weight_nonneg w hw (lostSecond adj i j)
        simp only [newHead, ite_eq_right hs] at gain
        linarith
      obtain ⟨_, _, a, hia, haj⟩ := (mem_second _ i j).mp secondJ
      exact ⟨a, (mem_inN adj j a).mpr haj.1, hia.1⟩
    have revOut : outN (fun a b => adj b a) j = inN adj j := by ext; simp
    have four : 4 ≤ (inN adj j).card := by
      have nd : ∀ v u, adj u v → ¬ adj v u := fun v u => noDigon u v
      have nt : ∀ v u z, adj u v → adj z u → ¬ adj v z :=
        fun v u z huv hzu hvz => noTri z u v hzu huv hvz
      have hh := four_of_internal (fun a b => adj b a) nd nt j
        (by simpa [revOut] using ip j) (by
          intro i hi
          rw [revOut] at hi
          obtain ⟨a, ha, hia⟩ := bypass i ((mem_inN adj j i).mp hi)
          exact ⟨a, by simpa [revOut] using ha, hia⟩)
      simpa [revOut] using hh
    obtain ⟨i, hi⟩ := ip j
    have edge := (mem_inN adj j i).mp hi
    obtain ⟨u, other, hne⟩ := branch i edge
    have count := branch_row_bound adj noDigon noTri deleted minimal w hw bad i j u edge other hne
    have budget := inverse_weighted_row_bound adj unit qn w kappa rows j
    have fr : (4 : ℝ) ≤ (inN adj j).card := by exact_mod_cast four
    nlinarith
  intro v
  linarith [sj v]

theorem normalized_deficit_bound [Nonempty V]
    (noDigon : ∀ v u, adj v u → ¬ adj u v)
    (noTri : ∀ v u z, adj v u → adj u z → ¬ adj z v)
    (deleted : DeletedFair adj) (minimal : WeightedArcMinimal adj)
    (w : V → ℝ) (hw : w ∈ simplex) (kappa : ℝ) (kp : 0 < kappa)
    (rows : ∀ v, surplus adj w v ≤ -kappa) :
    3 * (Fintype.card V : ℝ) * kappa ≤ 2 := by
  have h := sum_le_sum (s := (univ : Finset V))
    (fun v _ => minimum_weight_bound adj noDigon noTri deleted minimal w hw.1 kappa kp rows v)
  simp only [sum_const, card_univ, nsmul_eq_mul, ← mul_sum, hw.2] at h
  nlinarith

end CH.CompromiseMinimumWeight

#print axioms CH.CompromiseMinimumWeight.outside_incoming_charge
#print axioms CH.CompromiseMinimumWeight.minimum_weight_bound
#print axioms CH.CompromiseMinimumWeight.normalized_deficit_bound
