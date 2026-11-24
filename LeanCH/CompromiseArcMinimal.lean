module

public import LeanCH.CHArcMinimal
public import LeanCH.CHWeightSeparation

set_option linter.style.header false

/-! Necessary inverse-entry bounds for weighted arc-minimal compromise
counterexamples. Deleting an arc changes second neighbourhoods, so the
CH exact threshold becomes a one-way necessary bound here. -/

open Finset CH.CompromiseSeven CH.CompromiseWeighted CH.CompromiseGame
open CH.CompromiseDeletion CH.CompromiseCritical CH.CompromiseInverse
open CH.CompromisePacking CH.CompromisePerturbation
public section

namespace CH.CompromiseArcMinimal

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (adj : V → V → Prop) [DecidableRel adj]

@[expose] noncomputable def Q : Matrix V V ℝ := negativeInverse (CH.CompromiseInverse.matrix adj)

@[expose] def WeightedArcMinimal : Prop :=
  ∀ i j, adj i j → ∀ w : V → ℝ, (∀ v, 0 ≤ w v) →
    ∃ v, 0 ≤ surplus (CH.ArcMinimal.eraseArc adj i j) w v

theorem second_after_erase (i j v u : V)
    (h : u ∈ second (CH.ArcMinimal.eraseArc adj i j) v) :
    u ∈ second adj v ∨ (v = i ∧ u = j) := by
  obtain ⟨hne, hnon, a, hva, hau⟩ := (mem_second _ v u).mp h
  by_cases hadj : adj v u
  · right
    by_contra hs
    exact hnon ⟨hadj, hs⟩
  · left
    exact (mem_second adj v u).mpr ⟨hne, hadj, a, hva.1, hau.1⟩

/-- All positive change is confined to the removed arc's matrix entry,
and is at most three. Lost paths and lost incoming arcs only decrease it. -/
theorem coefficient_after_erase_le (i j v u : V) :
    coefficient (CH.ArcMinimal.eraseArc adj i j) v u ≤
      raiseEntry (coefficient adj) i j 3 v u := by
  let cut := CH.ArcMinimal.eraseArc adj i j
  have hs : (if u ∈ second cut v then (1 : ℝ) else 0) ≤
      (if u ∈ second adj v then 1 else 0) + (if v = i ∧ u = j then 1 else 0) := by
    by_cases hc : v = i ∧ u = j
    · split_ifs <;> norm_num
    · have hm : u ∈ second cut v → u ∈ second adj v := fun h =>
        (second_after_erase adj i j v u h).resolve_right hc
      by_cases hb : u ∈ second cut v
      · simp [hb, hm hb, hc]
      · by_cases hd : u ∈ second adj v <;> simp [hb, hd, hc]
  have hi : (if cut u v then (1 : ℝ) else 0) ≤ (if adj u v then 1 else 0) := by
    by_cases hb : cut u v
    · simp [hb, hb.1]
    · by_cases hd : adj u v <;> simp [hb, hd]
  have ho : (if adj v u then (2 : ℝ) else 0) ≤
      (if cut v u then 2 else 0) + (if v = i ∧ u = j then 2 else 0) := by
    by_cases hc : v = i ∧ u = j
    · have hb : ¬ cut v u := fun h => h.2 hc
      rw [ite_eq_left hc, ite_eq_right hb]
      by_cases hd : adj v u <;> norm_num [hd]
    · have he : cut v u ↔ adj v u := and_iff_left hc
      simp [he, hc]
  change (if u ∈ second cut v then 1 else 0) + (if cut u v then 1 else 0) -
    (if cut v u then 2 else 0) ≤
    (if u ∈ second adj v then 1 else 0) + (if adj u v then 1 else 0) -
    (if adj v u then 2 else 0) + (if v = i ∧ u = j then 3 else 0)
  by_cases hc : v = i ∧ u = j
  · rw [ite_eq_left hc] at hs ho ⊢
    linarith
  · rw [ite_eq_right hc] at hs ho ⊢
    linarith

theorem arc_lower (deleted : DeletedFair adj) (minimal : WeightedArcMinimal adj)
    (w0 : V → ℝ) (hw0 : ∀ v, 0 ≤ w0 v) (bad0 : ∀ v, surplus adj w0 v < 0) :
    ∀ i j, adj i j → 1 ≤ 3 * Q adj j i := by
  obtain ⟨unit, sign⟩ := graph_inverse_nonpos adj deleted w0 hw0 bad0
  have qn : ∀ v u, 0 ≤ Q adj v u := negativeInverse_nonneg _ sign
  have bad (v : V) : row (CH.CompromiseInverse.matrix adj) w0 v < 0 := by
    change row (coefficient adj) w0 v < 0
    rw [row_coefficient]
    exact bad0 v
  intro i j edge
  by_contra h
  obtain ⟨y, hy, hb⟩ := survive_below (CH.CompromiseInverse.matrix adj) i j 3 (by norm_num)
    w0 hw0 bad (fun u => Q adj u i) (fun u => qn u i)
    (inverse_column _ unit i) (lt_of_not_ge h)
  obtain ⟨v, hv⟩ := minimal i j edge y hy
  have hle : row (coefficient (CH.ArcMinimal.eraseArc adj i j)) y v ≤
      row (raiseEntry (coefficient adj) i j 3) y v := by
    exact sum_le_sum (fun u _ =>
      mul_le_mul_of_nonneg_right (coefficient_after_erase_le adj i j v u) (hy u))
  rw [row_coefficient] at hle
  have hn := hb v
  change row (raiseEntry (coefficient adj) i j 3) y v < 0 at hn
  linarith

theorem outgoing_degree_atom (noDigon : ∀ u v, adj u v → ¬ adj v u)
    (noTri : ∀ u v z, adj u v → adj v z → ¬ adj z u)
    (unit : IsUnit (CH.CompromiseInverse.matrix adj)) (sign : ∀ v u, 0 ≤ Q adj v u)
    (charge : ∀ i j, adj i j → 1 ≤ 3 * Q adj j i)
    (p : V → ℝ) (eta : ℝ) (hn : 0 ≤ eta)
    (cols : ∀ u, col (coefficient adj) p u = -eta) (v : V) :
    eta * (((outN adj v).card : ℝ) - 1 + Q adj v v) ≤ p v := by
  have hr := inverse_column (CH.CompromiseInverse.matrix adj) unit v v
  rw [ite_eq_left (by rfl)] at hr
  change row (coefficient adj) (fun u => Q adj u v) v = -1 at hr
  rw [row_coefficient] at hr
  have ball := CH.WeightSeparation.ball_weight_le adj noDigon noTri
    (fun u => Q adj u v) (fun u => sign u v) v
  have hd : ((outN adj v).card : ℝ) ≤ 3 * outWeight adj (fun u => Q adj u v) v := by
    have h := sum_le_sum (s := outN adj v)
      (fun u hu => charge v u (by simpa using hu))
    simpa [outWeight, mass, ← mul_sum] using h
  dsimp [surplus] at hr
  have htotal : ((outN adj v).card : ℝ) - 1 + Q adj v v ≤ ∑ u, Q adj u v := by linarith
  have hm := mul_le_mul_of_nonneg_left htotal hn
  have he := inverse_col_mass (CH.CompromiseInverse.matrix adj) unit p eta cols v
  change eta * (∑ u, Q adj u v) = p v at he
  rwa [he] at hm

theorem arc_trace_bound (noDigon : ∀ u v, adj u v → ¬ adj v u)
    (noTri : ∀ u v z, adj u v → adj v z → ¬ adj z u)
    (unit : IsUnit (CH.CompromiseInverse.matrix adj)) (sign : ∀ v u, 0 ≤ Q adj v u)
    (charge : ∀ i j, adj i j → 1 ≤ 3 * Q adj j i)
    (p : V → ℝ) (hp : p ∈ simplex) (eta : ℝ) (hn : 0 ≤ eta)
    (cols : ∀ u, col (coefficient adj) p u = -eta) :
    eta * ((CH.ArcMinimal.arcCount adj : ℝ) - (Fintype.card V : ℝ) + ∑ v, Q adj v v) ≤ 1 := by
  have h := sum_le_sum (s := (univ : Finset V))
    (fun v _ => outgoing_degree_atom adj noDigon noTri unit sign charge p eta hn cols v)
  simpa [← mul_sum, sum_add_distrib, sum_sub_distrib, hp.2, CH.ArcMinimal.arcCount] using h

end CH.CompromiseArcMinimal

#print axioms CH.CompromiseArcMinimal.coefficient_after_erase_le
#print axioms CH.CompromiseArcMinimal.arc_lower
#print axioms CH.CompromiseArcMinimal.outgoing_degree_atom
#print axioms CH.CompromiseArcMinimal.arc_trace_bound
