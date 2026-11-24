module

public import LeanCH.CompromiseTailCut

set_option linter.style.header false

/-! Every middle witness contributes an inverse arc charge. This counts
two-step paths with multiplicity, rather than only their distinct endpoints. -/

open Finset CH.CompromiseGame CH.CompromiseSeven CH.CompromiseWeighted
open CH.CompromiseDeletion CH.CompromiseCritical CH.CompromiseInverse
open CH.CompromisePerturbation CH.CompromiseArcMinimal CH.CompromiseTailCut
public section

namespace CH.CompromiseWitnessMultiplicity

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (adj : V → V → Prop) [DecidableRel adj]

@[expose] def middles (i u : V) : Finset V := outN adj i ∩ inN adj u

@[expose] def witnesses (i : V) (S : Finset V) : ℕ := ∑ u ∈ S, (middles adj i u).card

@[expose] noncomputable def block (S T : Finset V) : ℝ := ∑ a ∈ S, mass (Q adj a) T

theorem block_columns (S T : Finset V) :
    block adj S T = ∑ k ∈ T, mass (fun u => Q adj u k) S := by
  exact sum_comm

theorem middle_charge (qn : ∀ v u, 0 ≤ Q adj v u)
    (charge : ∀ a u, adj a u → 1 ≤ 3 * Q adj u a)
    (i u : V) (C : Finset V) (subset : middles adj i u ⊆ C) :
    ((middles adj i u).card : ℝ) ≤ 3 * mass (Q adj u) C := by
  have lower := sum_le_sum (s := middles adj i u) (fun a ha =>
    charge a u ((mem_inN adj u a).mp (mem_inter.mp ha).2))
  simp only [sum_const, nsmul_eq_mul, mul_one, ← mul_sum] at lower
  have mono := weight_mono (Q adj u) (qn u) _ _ subset
  change ((middles adj i u).card : ℝ) ≤ 3 * mass (Q adj u) (middles adj i u) at lower
  linarith

theorem lost_middles_removed (noDigon : ∀ v u, adj v u → ¬ adj u v)
    (i : V) (B : Finset V) (subset : B ⊆ outN adj i)
    (u : V) (lost : u ∈ lostEndpoints adj i B) :
    middles adj i u ⊆ removedHeads adj i B := by
  have excluded := ((mem_lost_endpoints adj noDigon i B subset u).mp lost).2
  intro a ha
  obtain ⟨hia, hau⟩ := mem_inter.mp ha
  exact mem_sdiff.mpr ⟨hia, excluded a ((mem_outN adj i a).mp hia)
    ((mem_inN adj u a).mp hau)⟩

/-- The full set of collectively lost two-step paths pays into the
same block as the earlier distinct-endpoint count. -/
theorem collective_witness_bound (noDigon : ∀ v u, adj v u → ¬ adj u v)
    (deleted : DeletedFair adj) (minimal : WeightedArcMinimal adj)
    (w0 : V → ℝ) (hw0 : ∀ v, 0 ≤ w0 v) (bad0 : ∀ v, surplus adj w0 v < 0)
    (i : V) (B : Finset V) (subset : B ⊆ outN adj i)
    (good : ∀ w : V → ℝ, (∀ v, 0 ≤ w v) → ∃ v, 0 ≤ surplus (retain adj i B) w v) :
    (witnesses adj i (lostEndpoints adj i B) : ℝ) ≤
      6 * block adj (removedHeads adj i B) (removedHeads adj i B) +
        3 * block adj (gainedEndpoints adj i B) (removedHeads adj i B) := by
  have qn : ∀ v u, 0 ≤ Q adj v u := negativeInverse_nonneg _
    (graph_inverse_nonpos adj deleted w0 hw0 bad0).2
  have charge := arc_lower adj deleted minimal w0 hw0 bad0
  have lower := sum_le_sum (s := lostEndpoints adj i B) (fun u hu =>
    middle_charge adj qn charge i u (removedHeads adj i B)
      (lost_middles_removed adj noDigon i B subset u hu))
  have upper := sum_le_sum (s := removedHeads adj i B) (fun k _ =>
    all_column_charge adj noDigon deleted w0 hw0 bad0 i B subset good k)
  have nonneg : 0 ≤ ∑ k ∈ removedHeads adj i B, if k = i then (1 : ℝ) else 0 := by
    apply sum_nonneg
    intro k _
    split_ifs <;> norm_num
  have commute : (∑ u ∈ lostEndpoints adj i B, mass (Q adj u) (removedHeads adj i B)) =
      ∑ k ∈ removedHeads adj i B, mass (fun u => Q adj u k) (lostEndpoints adj i B) := by
    exact sum_comm
  have count : (witnesses adj i (lostEndpoints adj i B) : ℝ) =
      ∑ u ∈ lostEndpoints adj i B, ((middles adj i u).card : ℝ) := by
    simp only [witnesses, Nat.cast_sum]
  rw [← count] at lower
  simp only [sum_add_distrib, ← mul_sum] at lower upper
  rw [commute] at lower
  rw [block_columns, block_columns]
  linarith

/-- Cutting the whole tail is automatically good, so single-arc
minimality suffices for the multiplicity bound on its out-neighbourhood. -/
theorem full_witness_bound (noDigon : ∀ v u, adj v u → ¬ adj u v)
    (deleted : DeletedFair adj) (minimal : WeightedArcMinimal adj)
    (w0 : V → ℝ) (hw0 : ∀ v, 0 ≤ w0 v) (bad0 : ∀ v, surplus adj w0 v < 0) (i : V) :
    (witnesses adj i (second adj i) : ℝ) ≤ 6 * block adj (outN adj i) (outN adj i) := by
  have emptySecond : second (retain adj i ∅) i = ∅ := by
    rw [second_retained adj noDigon i ∅ (empty_subset _)]
    simp [CH.CompromiseSubset.boundary, CH.CompromiseSubset.reach]
  have good (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) :
      ∃ v, 0 ≤ surplus (retain adj i ∅) w v := by
    refine ⟨i, ?_⟩
    rw [tail_surplus adj noDigon i ∅ (empty_subset _)]
    simpa [CH.CompromiseSubset.boundary, CH.CompromiseSubset.reach, mass, inWeight]
      using weight_nonneg w hw (inN adj i)
  have bound := collective_witness_bound adj noDigon deleted minimal w0 hw0 bad0
    i ∅ (empty_subset _) good
  simpa only [removedHeads, sdiff_empty, lostEndpoints, gainedEndpoints, emptySecond,
    empty_sdiff, block, sum_empty, mul_zero, add_zero] using bound

theorem witnesses_as_outgoing (i : V) (S : Finset V) :
    witnesses adj i S = ∑ a ∈ outN adj i, (outN adj a ∩ S).card := by
  rw [double_count]
  simp only [witnesses, middles, inter_comm]

theorem full_witnesses_as_cut (noDigon : ∀ v u, adj v u → ¬ adj u v) (i : V) :
    witnesses adj i (second adj i) = ∑ a ∈ outN adj i, (outN adj a \ outN adj i).card := by
  rw [witnesses_as_outgoing]
  apply sum_congr rfl
  intro a ha
  congr 1
  ext u
  constructor
  · intro h
    obtain ⟨hau, hs⟩ := mem_inter.mp h
    exact mem_sdiff.mpr ⟨hau, fun hia => ((mem_second adj i u).mp hs).2.1
      ((mem_outN adj i u).mp hia)⟩
  · intro h
    obtain ⟨hau, hia⟩ := mem_sdiff.mp h
    have ia := (mem_outN adj i a).mp ha
    have au := (mem_outN adj a u).mp hau
    refine mem_inter.mpr ⟨hau, (mem_second adj i u).mpr ⟨?_, ?_, a, ia, au⟩⟩
    · intro he
      exact noDigon i a ia (by simpa only [he] using au)
    · exact fun he => hia ((mem_outN adj i u).mpr he)

theorem internal_arc_count (noDigon : ∀ v u, adj v u → ¬ adj u v) (S : Finset V) :
    2 * (∑ a ∈ S, (outN adj a ∩ S).card) ≤ S.card * (S.card - 1) := by
  have each (a : V) (ha : a ∈ S) :
      (outN adj a ∩ S).card + (inN adj a ∩ S).card ≤ S.card - 1 := by
    have disjoint : Disjoint (outN adj a ∩ S) (inN adj a ∩ S) := by
      apply disjoint_left.mpr
      intro u hu hv
      exact noDigon a u ((mem_outN adj a u).mp (mem_inter.mp hu).1)
        ((mem_inN adj a u).mp (mem_inter.mp hv).1)
    have subset : (outN adj a ∩ S) ∪ (inN adj a ∩ S) ⊆ S.erase a := by
      intro u hu
      rcases mem_union.mp hu with hu | hu
      · have h := (mem_outN adj a u).mp (mem_inter.mp hu).1
        exact mem_erase.mpr ⟨fun he => by subst u; exact noDigon a a h h, (mem_inter.mp hu).2⟩
      · have h := (mem_inN adj a u).mp (mem_inter.mp hu).1
        exact mem_erase.mpr ⟨fun he => by subst u; exact noDigon a a h h, (mem_inter.mp hu).2⟩
    have count := card_le_card subset
    rwa [card_union_of_disjoint disjoint, card_erase_of_mem ha] at count
  have bound := sum_le_sum each
  rw [sum_add_distrib, ← double_count adj S S, sum_const, nsmul_eq_mul] at bound
  simpa only [two_mul, Nat.cast_id] using bound

/-- At a minimum-outdegree vertex, at least R(R+1)/2 two-step paths
leave its out-neighbourhood, counting every middle witness. -/
theorem minimum_degree_witnesses (noDigon : ∀ v u, adj v u → ¬ adj u v)
    (R : ℕ) (positive : 0 < R) (degrees : ∀ v, R ≤ (outN adj v).card)
    (i : V) (degree : (outN adj i).card = R) :
    R * (R + 1) ≤ 2 * witnesses adj i (second adj i) := by
  have internal := internal_arc_count adj noDigon (outN adj i)
  have outgoing := sum_le_sum (s := outN adj i) (fun a _ => degrees a)
  simp only [sum_const, nsmul_eq_mul, degree] at outgoing internal
  have split : (∑ a ∈ outN adj i, (outN adj a \ outN adj i).card) +
      (∑ a ∈ outN adj i, (outN adj a ∩ outN adj i).card) =
      ∑ a ∈ outN adj i, (outN adj a).card := by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro a _
    exact card_sdiff_add_card_inter _ _
  rw [← full_witnesses_as_cut adj noDigon i] at split
  have pred : R - 1 + 1 = R := by omega
  nlinarith

end CH.CompromiseWitnessMultiplicity

#print axioms CH.CompromiseWitnessMultiplicity.collective_witness_bound
#print axioms CH.CompromiseWitnessMultiplicity.full_witness_bound
#print axioms CH.CompromiseWitnessMultiplicity.full_witnesses_as_cut
#print axioms CH.CompromiseWitnessMultiplicity.minimum_degree_witnesses
