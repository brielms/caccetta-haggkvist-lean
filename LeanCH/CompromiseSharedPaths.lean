module

public import LeanCH.CompromiseLostArc

set_option linter.style.header false

/-! Cancellation of second neighbours with a unique middle vertex.
The remaining inverse-column charge consists of in-neighbours, shared
second neighbours, and heads inside the first out-neighbourhood. -/

open Finset CH.CompromiseSeven CH.CompromiseWeighted CH.CompromiseGame
open CH.CompromiseDeletion CH.CompromiseCritical CH.CompromiseInverse
open CH.CompromisePerturbation CH.CompromiseArcMinimal CH.CompromiseLostArc
public section

namespace CH.CompromiseSharedPaths

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (adj : V → V → Prop) [DecidableRel adj]

@[expose] def privateSecond (i : V) : Finset V :=
  (outN adj i).biUnion (lostSecond adj i)

@[expose] def sharedSecond (i : V) : Finset V := second adj i \ privateSecond adj i

@[expose] def internalHeads (i : V) : Finset V :=
  (outN adj i).filter (fun j => ∃ a ∈ outN adj i, adj a j)

theorem mem_lost_iff (i j u : V) :
    u ∈ lostSecond adj i j ↔ u ∈ second adj i ∧
      ∀ a, adj i a → adj a u → a = j := by
  constructor
  · intro h
    obtain ⟨hs, hn⟩ := mem_sdiff.mp h
    obtain ⟨hne, hnon, _, _, _⟩ := (mem_second adj i u).mp hs
    refine ⟨hs, ?_⟩
    intro a hia hau
    by_contra haj
    apply hn
    apply (mem_second _ i u).mpr
    refine ⟨hne, fun h => hnon h.1, a, ⟨hia, ?_⟩, ⟨hau, ?_⟩⟩
    · intro h
      exact haj h.2
    · rintro ⟨hai, _⟩
      exact hnon (by simpa [hai] using hau)
  · rintro ⟨hs, hall⟩
    apply mem_sdiff.mpr
    refine ⟨hs, ?_⟩
    intro h
    obtain ⟨_, _, a, hia, hau⟩ := (mem_second _ i u).mp h
    exact hia.2 ⟨rfl, hall a hia.1 hau.1⟩

theorem lost_disjoint (i j k : V) (hne : j ≠ k) :
    Disjoint (lostSecond adj i j) (lostSecond adj i k) := by
  apply disjoint_left.mpr
  intro u hj hk
  obtain ⟨hs, hj⟩ := (mem_lost_iff adj i j u).mp hj
  obtain ⟨_, hk⟩ := (mem_lost_iff adj i k u).mp hk
  obtain ⟨_, _, a, hia, hau⟩ := (mem_second adj i u).mp hs
  exact hne ((hj a hia hau).symm.trans (hk a hia hau))

theorem private_subset (i : V) : privateSecond adj i ⊆ second adj i := by
  intro u hu
  obtain ⟨j, _, hj⟩ := mem_biUnion.mp hu
  exact (mem_sdiff.mp hj).1

/-- The retained set is exactly the set of endpoints with two distinct
middle vertices, not merely a convenient superset. -/
theorem mem_shared_iff (i u : V) :
    u ∈ sharedSecond adj i ↔ u ∈ second adj i ∧
      ∃ a b, a ≠ b ∧ adj i a ∧ adj a u ∧ adj i b ∧ adj b u := by
  constructor
  · intro h
    obtain ⟨hs, hn⟩ := mem_sdiff.mp h
    obtain ⟨_, _, a, hia, hau⟩ := (mem_second adj i u).mp hs
    have hna : u ∉ lostSecond adj i a := fun hh =>
      hn (mem_biUnion.mpr ⟨a, (mem_outN adj i a).mpr hia, hh⟩)
    have hb : ∃ b, adj i b ∧ adj b u ∧ b ≠ a := by
      by_contra h
      push Not at h
      apply hna
      exact (mem_lost_iff adj i a u).mpr ⟨hs, h⟩
    obtain ⟨b, hib, hbu, hba⟩ := hb
    exact ⟨hs, a, b, hba.symm, hia, hau, hib, hbu⟩
  · rintro ⟨hs, a, b, hab, hia, hau, hib, hbu⟩
    apply mem_sdiff.mpr
    refine ⟨hs, ?_⟩
    intro h
    obtain ⟨j, _, hj⟩ := mem_biUnion.mp h
    have hall := ((mem_lost_iff adj i j u).mp hj).2
    exact hab ((hall a hia hau).trans (hall b hib hbu).symm)

theorem new_head_iff (noLoop : ∀ v, ¬ adj v v) (i j : V) (edge : adj i j) :
    j ∈ second (CH.ArcMinimal.eraseArc adj i j) i ↔ j ∈ internalHeads adj i := by
  constructor
  · intro h
    obtain ⟨_, _, a, hia, haj⟩ := (mem_second _ i j).mp h
    exact mem_filter.mpr ⟨(mem_outN adj i j).mpr edge,
      a, (mem_outN adj i a).mpr hia.1, haj.1⟩
  · intro h
    obtain ⟨_, a, ha, haj⟩ := mem_filter.mp h
    have hia : adj i a := (mem_outN adj i a).mp ha
    have hji : j ≠ i := by
      intro he
      subst j
      exact noLoop i edge
    apply (mem_second _ i j).mpr
    refine ⟨hji, fun h => h.2 ⟨rfl, rfl⟩, a, ⟨hia, ?_⟩, ⟨haj, ?_⟩⟩
    · rintro ⟨_, he⟩
      exact noLoop j (by simpa [he] using haj)
    · rintro ⟨he, _⟩
      exact noLoop i (by simpa [he] using hia)

theorem new_head_indicator (noLoop : ∀ v, ¬ adj v v) (i j : V) (edge : adj i j) :
    newHead adj i j = if j ∈ internalHeads adj i then 1 else 0 := by
  simp only [newHead, new_head_iff adj noLoop i j edge]

theorem sum_lost_mass (i : V) (f : V → ℝ) :
    (∑ j ∈ outN adj i, mass f (lostSecond adj i j)) = mass f (privateSecond adj i) := by
  have hd : Set.PairwiseDisjoint (↑(outN adj i) : Set V) (lostSecond adj i) :=
    fun j _ k _ hne => lost_disjoint adj i j k hne
  exact (sum_biUnion hd).symm

theorem second_mass_split (i : V) (f : V → ℝ) :
    mass f (privateSecond adj i) + mass f (sharedSecond adj i) = secondWeight adj f i := by
  have h := sum_sdiff (f := f) (private_subset adj i)
  change mass f (sharedSecond adj i) + mass f (privateSecond adj i) = secondWeight adj f i at h
  linarith

theorem sum_head_gain (noLoop : ∀ v, ¬ adj v v) (i : V) (f : V → ℝ) :
    (∑ j ∈ outN adj i, (2 + newHead adj i j) * f j) =
      2 * outWeight adj f i + mass f (internalHeads adj i) := by
  have he : (∑ j ∈ outN adj i, (2 + newHead adj i j) * f j) =
      ∑ j ∈ outN adj i, (2 * f j + if j ∈ internalHeads adj i then f j else 0) := by
    apply sum_congr rfl
    intro j hj
    rw [new_head_indicator adj noLoop i j ((mem_outN adj i j).mp hj)]
    by_cases hh : j ∈ internalHeads adj i
    · simp [hh]
      ring
    · simp [hh]
  rw [he, sum_add_distrib, ← mul_sum, ← sum_filter]
  have hf : (outN adj i).filter (fun j => j ∈ internalHeads adj i) = internalHeads adj i := by
    ext j
    simp only [mem_filter]
    exact and_iff_right_of_imp (fun h => (mem_filter.mp h).1)
  rw [hf]
  rfl

/-- The unique-middle mass cancels exactly. This is a necessary
structural charge, not a proof of the general compromise conjecture. -/
theorem shared_path_charge (noLoop : ∀ v, ¬ adj v v)
    (unit : IsUnit (CH.CompromiseInverse.matrix adj)) (i : V)
    (charge : ∀ j, adj i j →
      1 + mass (fun u => Q adj u i) (lostSecond adj i j) ≤
        (2 + newHead adj i j) * Q adj j i) :
    ((outN adj i).card : ℝ) - 1 ≤
      inWeight adj (fun u => Q adj u i) i +
        mass (fun u => Q adj u i) (sharedSecond adj i) +
        mass (fun u => Q adj u i) (internalHeads adj i) := by
  have h := sum_le_sum (s := outN adj i)
    (fun j hj => charge j ((mem_outN adj i j).mp hj))
  rw [sum_add_distrib, sum_lost_mass, sum_head_gain adj noLoop] at h
  simp only [sum_const, nsmul_eq_mul, mul_one] at h
  have hs := second_mass_split adj i (fun u => Q adj u i)
  have hr := inverse_column (CH.CompromiseInverse.matrix adj) unit i i
  rw [ite_eq_left (by rfl)] at hr
  change row (coefficient adj) (fun u => Q adj u i) i = -1 at hr
  rw [row_coefficient] at hr
  dsimp [surplus] at hr
  linarith

theorem shared_path_charge_of_minimal (noLoop : ∀ v, ¬ adj v v)
    (deleted : DeletedFair adj) (minimal : WeightedArcMinimal adj)
    (w0 : V → ℝ) (hw0 : ∀ v, 0 ≤ w0 v) (bad0 : ∀ v, surplus adj w0 v < 0) (i : V) :
    ((outN adj i).card : ℝ) - 1 ≤
      inWeight adj (fun u => Q adj u i) i +
        mass (fun u => Q adj u i) (sharedSecond adj i) +
        mass (fun u => Q adj u i) (internalHeads adj i) := by
  have unit := (graph_inverse_nonpos adj deleted w0 hw0 bad0).1
  exact shared_path_charge adj noLoop unit i
    (fun j edge => sharp_arc_charge adj noLoop deleted minimal w0 hw0 bad0 i j edge)

end CH.CompromiseSharedPaths

#print axioms CH.CompromiseSharedPaths.mem_lost_iff
#print axioms CH.CompromiseSharedPaths.mem_shared_iff
#print axioms CH.CompromiseSharedPaths.sum_lost_mass
#print axioms CH.CompromiseSharedPaths.shared_path_charge_of_minimal
