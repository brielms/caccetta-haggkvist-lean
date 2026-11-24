module

public import LeanCH.CompromiseDeletion
public import LeanCH.CompromiseGame
public import LeanCH.CompromisePacking

set_option linter.style.header false

/-! Graph minimax duality and constant negative surplus in both directions.
Deleted-graph fair certificates are explicit hypotheses. For a minimum
counterexample in an induced- and reversal-closed class they are supplied
by smaller graphs; no general compromise theorem is assumed here. -/

open Finset CH.CompromiseSeven CH.CompromiseWeighted CH.CompromiseFair
open CH.CompromiseDeletion CH.CompromiseGame CH.CompromisePacking
public section

namespace CH.CompromiseCritical

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (adj : V → V → Prop) [DecidableRel adj]

@[expose] def coefficient (v u : V) : ℝ :=
  capacity adj v u - if adj v u then 2 else 0

theorem row_coefficient (w : V → ℝ) (v : V) :
    row (coefficient adj) w v = surplus adj w v := by
  have pointwise (u : V) : coefficient adj v u * w u =
      (if u ∈ second adj v then w u else 0) + (if adj u v then w u else 0) -
        2 * (if adj v u then w u else 0) := by
    unfold coefficient capacity
    split_ifs <;> ring
  have hs : (∑ u, if u ∈ second adj v then w u else 0) = mass w (second adj v) := by
    rw [← sum_filter]
    have he : univ.filter (fun u => u ∈ second adj v) = second adj v := by ext; simp
    rw [he]
    rfl
  have hi : (∑ u, if adj u v then w u else 0) = mass w (inN adj v) := by
    rw [← sum_filter]
    have he : univ.filter (adj · v) = inN adj v := by ext; simp
    rw [he]
    rfl
  have ho : (∑ u, if adj v u then w u else 0) = mass w (outN adj v) := by
    rw [← sum_filter]
    have he : univ.filter (adj v ·) = outN adj v := by ext; simp
    rw [he]
    rfl
  simp only [row, pointwise, sum_sub_distrib, sum_add_distrib, ← mul_sum, hs, hi, ho]
  rfl

theorem col_coefficient (p : V → ℝ) (u : V) :
    col (coefficient adj) p u = slack adj p u := by
  have hn : (∑ v, p v * (if adj v u then 2 else 0)) = 2 * mass p (inN adj u) := by
    calc
      _ = 2 * ∑ v, if adj v u then p v else 0 := by
        rw [mul_sum]
        apply sum_congr rfl
        intro v _
        split_ifs <;> ring
      _ = _ := by
        rw [← sum_filter]
        have he : univ.filter (adj · u) = inN adj u := by ext; simp
        rw [he]
        rfl
  simp only [col, coefficient, mul_sub, sum_sub_distrib]
  rw [capacity_transpose adj p u, hn]
  dsimp [slack]
  ring

theorem slack_reverse (p : V → ℝ) (u : V) :
    slack adj p u = surplus (fun a b => adj b a) p u := by
  have ho : outN (fun a b => adj b a) u = inN adj u := by ext; simp
  have hi : inN (fun a b => adj b a) u = outN adj u := by ext; simp
  have hs : second (fun a b => adj b a) u = secondIn adj u := rfl
  simp only [slack, surplus, secondWeight, inWeight, outWeight, ho, hi, hs]
  ring

/-- Full weighted compromise and existence of a fair certificate are equivalent.
This implication now includes the minimax existence proof. -/
theorem compromise_iff_fair [Nonempty V] :
    (∀ w : V → ℝ, (∀ v, 0 ≤ w v) → ∃ v, 0 ≤ surplus adj w v) ↔
      ∃ p, Fair adj p := by
  constructor
  · intro good
    have hno : ¬ ∃ w ∈ simplex, ∀ v, row (coefficient adj) w v < 0 := by
      rintro ⟨w, hw, bad⟩
      obtain ⟨v, hv⟩ := good w hw.1
      have hb := bad v
      rw [row_coefficient] at hb
      linarith
    obtain ⟨p, hp, cols⟩ := (fair_iff_no_bad (coefficient adj)).mpr hno
    refine ⟨p, hp.1, simplex_has_positive hp, ?_⟩
    intro u
    have hc := cols u
    rw [col_coefficient] at hc
    dsimp [slack] at hc
    linarith
  · rintro ⟨p, hp⟩ w hw
    obtain ⟨v, _, hv⟩ := compromise_of_fair adj p w hp hw
    refine ⟨v, ?_⟩
    dsimp [surplus]
    linarith

@[expose] def DeletedFair : Prop := ∀ x : V, ∃ p, FairOn adj (univ.erase x) p

theorem deleted_fair_full_support (deleted : DeletedFair adj)
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) (bad : ∀ v, surplus adj w v < 0) :
    ∀ x, 0 < w x := by
  intro x
  obtain ⟨p, hp⟩ := deleted x
  exact (singleton_fair_budget adj w hw bad x p hp).1

/-- Fair certificates after every one-vertex deletion force a counterexample
to have a reverse counterweight, with constant negative reverse surplus. -/
theorem reverse_counterweight [Nonempty V] (deleted : DeletedFair adj)
    (w0 : V → ℝ) (hw0 : ∀ v, 0 ≤ w0 v) (bad0 : ∀ v, surplus adj w0 v < 0) :
    ∃ p ∈ simplex, ∃ c : ℝ, c < 0 ∧ ∀ u, surplus (fun a b => adj b a) p u = c := by
  obtain ⟨w1, hw1, hb1⟩ := normalize_bad (coefficient adj) w0 hw0
    (fun v => by rw [row_coefficient]; exact bad0 v)
  have full : ∀ w ∈ simplex, (∀ v, row (coefficient adj) w v < 0) → ∀ v, 0 < w v := by
    intro w hw hb
    exact deleted_fair_full_support adj deleted w hw.1
      (fun v => by simpa [row_coefficient] using hb v)
  obtain ⟨_, _, p, hp, c, hc, _, _, cols⟩ :=
    critical_reversal (coefficient adj) w1 hw1 hb1 full
  refine ⟨p, hp, c, hc, ?_⟩
  intro u
  rw [← slack_reverse adj p u, ← col_coefficient adj p u]
  exact cols u

/-- The strengthened two-weight target: positive probability weights with the
same strictly negative surplus at every vertex, in the two orientations. -/
theorem two_sided_constant [Nonempty V]
    (deleted : DeletedFair adj) (deletedRev : DeletedFair (fun a b => adj b a))
    (w0 : V → ℝ) (hw0 : ∀ v, 0 ≤ w0 v) (bad0 : ∀ v, surplus adj w0 v < 0) :
    ∃ w ∈ simplex, ∃ p ∈ simplex, ∃ c : ℝ, c < 0 ∧
      (∀ v, 0 < w v) ∧ (∀ v, 0 < p v) ∧
        (∀ v, surplus adj w v = c) ∧ (∀ v, surplus (fun a b => adj b a) p v = c) := by
  obtain ⟨w1, hw1, hb1⟩ := normalize_bad (coefficient adj) w0 hw0
    (fun v => by rw [row_coefficient]; exact bad0 v)
  have full : ∀ w ∈ simplex, (∀ v, row (coefficient adj) w v < 0) → ∀ v, 0 < w v := by
    intro w hw hb
    exact deleted_fair_full_support adj deleted w hw.1
      (fun v => by simpa [row_coefficient] using hb v)
  have fullRev : ∀ p ∈ simplex, (∀ u, col (coefficient adj) p u < 0) → ∀ u, 0 < p u := by
    intro p hp hb
    apply deleted_fair_full_support (fun a b => adj b a) deletedRev p hp.1
    intro u
    rw [← slack_reverse adj p u, ← col_coefficient adj p u]
    exact hb u
  obtain ⟨w, hw, p, hp, c, hc, wp, pp, rows, cols⟩ :=
    critical_two_sided (coefficient adj) w1 hw1 hb1 full fullRev
  refine ⟨w, hw, p, hp, c, hc, wp, pp, ?_, ?_⟩
  · intro v
    rw [← row_coefficient adj w v]
    exact rows v
  · intro v
    rw [← slack_reverse adj p v, ← col_coefficient adj p v]
    exact cols v

/-- Every atom of a constant-deficit counterweight is at least half the
deficit. The omitted row of a fair certificate can lose at most twice its mass. -/
theorem equalized_atom_bound (deleted : DeletedFair adj)
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) (c : ℝ)
    (constant : ∀ v, surplus adj w v = c) : ∀ x, -c ≤ 2 * w x := by
  intro x
  obtain ⟨p, hp⟩ := deleted x
  let t := ∑ v, p v
  have tp : 0 < t := by
    obtain ⟨a, _, ha⟩ := hp.2.2.1
    have ht : p a ≤ t := single_le_sum (fun v _ => hp.1 v) (mem_univ a)
    exact ha.trans_le ht
  have pairing := surplus_slack_pairing adj p w
  simp_rw [constant] at pairing
  rw [← sum_mul] at pairing
  change t * c = ∑ u, w u * slack adj p u at pairing
  have split := sum_erase_add (univ : Finset V) (fun u => w u * slack adj p u) (mem_univ x)
  have retained : 0 ≤ ∑ u ∈ univ.erase x, w u * slack adj p u := by
    apply sum_nonneg
    intro u hu
    have hs := retained_row adj (univ.erase x) p hp u hu
    apply mul_nonneg (hw u)
    dsimp [slack]
    linarith
  have hin : mass p (inN adj x) ≤ t := by
    exact sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun v _ _ => hp.1 v)
  have hout : 0 ≤ mass p (outN adj x) := weight_nonneg p hp.1 _
  have hsecond : 0 ≤ mass p (secondIn adj x) := weight_nonneg p hp.1 _
  have lower : -2 * t ≤ slack adj p x := by
    dsimp [slack]
    linarith
  have hm := mul_le_mul_of_nonneg_left lower (hw x)
  have hc : t * (-2 * w x) ≤ t * c := by nlinarith
  have he := (mul_le_mul_iff_right₀ tp).mp hc
  linarith

theorem equalized_order_bound (deleted : DeletedFair adj)
    (w : V → ℝ) (hw : w ∈ simplex) (c : ℝ)
    (constant : ∀ v, surplus adj w v = c) :
    (Fintype.card V : ℝ) * (-c) ≤ 2 := by
  have h := sum_le_sum (s := (univ : Finset V))
    (fun x _ => equalized_atom_bound adj deleted w hw.1 c constant x)
  simpa [sum_const, nsmul_eq_mul, ← mul_sum, hw.2] using h

end CH.CompromiseCritical

#print axioms CH.CompromiseCritical.compromise_iff_fair
#print axioms CH.CompromiseCritical.deleted_fair_full_support
#print axioms CH.CompromiseCritical.reverse_counterweight
#print axioms CH.CompromiseCritical.two_sided_constant
#print axioms CH.CompromiseCritical.equalized_atom_bound
#print axioms CH.CompromiseCritical.equalized_order_bound
