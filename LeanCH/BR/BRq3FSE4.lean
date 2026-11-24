import LeanCH.BR.BRq3Base

/-!
# FSE(4): the three single-exit profiles, as one abstract count, Lean 4.35.0

Paper: `checkpoints/boundary_20261111/TOP4_attempt_subagent.md`, §3 (Lemmas 3, 4a, 4b), reorganised as one head count.

`fse4` is purely local: layers `N_1, N_2, N_3` (`|N_1| = 3`, `|N_2| + |N_3| = 7`, `3 ≤ |N_2| ≤ 5`), out-arcs as in a
single exit (`O(N_1) ⊆ N_1 ∪ N_2`, `O(N_2) ⊆ E`, each `p ∈ N_3` has at least two arcs into `E = N_1 ∪ N_2 ∪ N_3`), a
4-free digraph, and a relation `R` ("non-funnel arc") that contains every arc out of `N_3`, every arc `N_1 → N_1` and
every arc `N_2 → N_1 ∪ N_2`, with the cap: every `z ∈ E` has at most one `R`-in-neighbour in `E`.

Proof. Put `H = N_1 ∪ N_2`, `Q = {a ∈ N_1 : a has an arc into N_1}`, `m_p = |{b ∈ N_2 : b ↛ p}|`, `M = Σ_p m_p`.
* (cap) `Σ_{y ∈ E} |R-arcs y → H| ≤ |H| = 3 + n_2`; split into `C_1 + C_2 + C_3` over `N_1, N_2, N_3`.
* `C_1 ≥ |Q|`.
* `C_2 + n_2 n_3 ≥ 3 n_2 + M`: `b ∈ N_2` sends `3 - |O(b) ∩ N_3| = |N_3 ∖ O(b)| + 3 - n_3` arcs into `H`, and
  `Σ_b |N_3 ∖ O(b)| = M` (double counting).
* `C_3 ≥ X := |arcs N_3 → H|`, and `X ≥ n_3 + 1`: `N_3` sends `≥ 2n_3` arcs into `E`, at most `n_3 - 1` inside `N_3`
  (cap, plus a source of the acyclic `D[N_3]`).
* `X ≤ M + |Q|`: per `p`, `|O(p) ∩ H| ≤ m_p + |O(p) ∩ Q|`. If `m_p ≥ 3` this is `|O(p)| = 3`. Otherwise `p → b ∈ N_2`
  needs `b ↛ p` (digon), and `p → a ∈ N_1 ∖ Q` is impossible: `O(a) ⊆ N_2` has three vertices, none heading `p`
  (triangle), so `m_p ≥ 3`. And `Σ_p |O(p) ∩ Q| ≤ |Q|` by the cap.
* Hence `3 + n_2 ≥ 2X + 3n_2 - n_2 n_3 ≥ 2n_3 + 2 + 3n_2 - n_2 n_3`, false for `(n_2, n_3) = (3,4), (4,3), (5,2)`
  (`6 ≥ 7`, `7 ≥ 8`, `8 ≥ 11`).

This replaces the paper's three separate arguments (Lemma 3: heads of `N_3` and the DAG on `N_1`; Lemma 4a: `t = 3`
then the `dB ≤ 2` / `dB = 3` split with `β`; Lemma 4b: `t = 2`, `dB = 5`). The ingredients are the paper's (cap,
digons, triangles, acyclic `D[N_3]`), but the corollary `A + B + t ≥ 20` and `t` itself are not needed.

Also: `exists_source`, `double_count`, `head_count`, `card_filter_le_of_imp`.
-/

set_option linter.style.longLine false

namespace LeanCH.BR.BRq3

open LeanCH.BR.BRq2

variable {D : CH.Digraph} {W : Finset ℕ}

/-- A nonempty `T` with no closed walk of length `1..|T|` inside `T` has a vertex with no in-neighbour in `T`. -/
theorem exists_source {T : Finset ℕ} {q : ℕ} (hfree : QFree D T q) (hne : T.Nonempty) (hq : T.card ≤ q) :
    ∃ t ∈ T, ∀ z ∈ T, ¬ D z t = true := by
  classical
  by_contra hcon
  push Not at hcon
  let pr : ℕ → ℕ := fun t => if h : ∃ z ∈ T, D z t = true then h.choose else t
  have hpr : ∀ t ∈ T, pr t ∈ T ∧ D (pr t) t = true := by
    intro t ht
    have h := hcon t ht
    simp only [pr]
    split
    · next h' => exact h'.choose_spec
    · next h' => exact absurd h h'
  obtain ⟨t0, ht0⟩ := hne
  have hg : ∀ i, pr^[i] t0 ∈ T := by
    intro i
    induction i with
    | zero => exact ht0
    | succ i ih => rw [Function.iterate_succ_apply']; exact (hpr _ ih).1
  have hw : ∀ i l, Walk D T (pr^[i + l] t0) (pr^[i] t0) l := by
    intro i l
    induction l with
    | zero => exact .refl _
    | succ l ih =>
      have e : pr^[i + (l + 1)] t0 = pr (pr^[i + l] t0) := by
        rw [← Nat.add_assoc, Function.iterate_succ_apply']
      rw [e]
      exact .step (hg (i + l)) (hpr _ (hg (i + l))).2 ih
  obtain ⟨i, hi, j, hj, hij, heq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (s := Finset.range (T.card + 1)) (t := T) (f := fun i => pr^[i] t0) (by simp)
    (by intro i _; exact hg i)
  have heq' : pr^[i] t0 = pr^[j] t0 := heq
  simp only [Finset.mem_range] at hi hj
  rcases Nat.lt_or_gt_of_ne hij with h | h
  · have w := hw i (j - i)
    rw [Nat.add_sub_cancel' h.le, ← heq'] at w
    exact hfree _ (j - i) (by omega) (by omega) w
  · have w := hw j (i - j)
    rw [Nat.add_sub_cancel' h.le, heq'] at w
    exact hfree _ (i - j) (by omega) (by omega) w

/-- Double counting of a relation between two finite sets. -/
theorem double_count {S H : Finset ℕ} (R : ℕ → ℕ → Prop) [DecidableRel R] :
    ∑ y ∈ S, (H.filter (fun z => R y z)).card = ∑ z ∈ H, (S.filter (fun y => R y z)).card := by
  simp only [Finset.card_filter]
  exact Finset.sum_comm

/-- Distinct heads: if every `z ∈ H` has at most one `R`-in-neighbour in `S`, the `R`-arcs from `S` into `H` number
at most `|H|`. -/
theorem head_count {S H : Finset ℕ} (R : ℕ → ℕ → Prop) [DecidableRel R]
    (hcap : ∀ z ∈ H, (S.filter (fun y => R y z)).card ≤ 1) :
    ∑ y ∈ S, (H.filter (fun z => R y z)).card ≤ H.card := by
  rw [double_count R]
  calc ∑ z ∈ H, (S.filter (fun y => R y z)).card ≤ ∑ _z ∈ H, 1 := Finset.sum_le_sum hcap
    _ = H.card := by simp

theorem card_filter_le_of_imp {s : Finset ℕ} {p r : ℕ → Prop} [DecidablePred p] [DecidablePred r]
    (h : ∀ z ∈ s, p z → r z) : (s.filter p).card ≤ (s.filter r).card :=
  Finset.card_le_card (fun z hz => by
    obtain ⟨hzs, hpz⟩ := Finset.mem_filter.mp hz
    exact Finset.mem_filter.mpr ⟨hzs, h z hzs hpz⟩)

/-- **FSE(4)**, the local statement behind Lemmas 3, 4a and 4b: no single-exit configuration with profile
`(3, n_2, n_3, 1)`, `n_2 + n_3 = 7`, `3 ≤ n_2 ≤ 5`, satisfies the cap. -/
theorem fse4 {N1 N2 N3 : Finset ℕ} (R : ℕ → ℕ → Prop) [DecidableRel R] (hfree : QFree D W 4)
    (hW1 : N1 ⊆ W) (hW2 : N2 ⊆ W) (hW3 : N3 ⊆ W)
    (d12 : Disjoint N1 N2) (d13 : Disjoint N1 N3) (d23 : Disjoint N2 N3)
    (c1 : N1.card = 3) (c23 : N2.card + N3.card = 7) (c2 : 3 ≤ N2.card) (c2' : N2.card ≤ 5)
    (o1 : ∀ a ∈ N1, 3 ≤ (N1.filter (fun z => D a z = true)).card + (N2.filter (fun z => D a z = true)).card)
    (o2 : ∀ b ∈ N2, 3 ≤ ((N1 ∪ N2).filter (fun z => D b z = true)).card + (N3.filter (fun z => D b z = true)).card)
    (o3 : ∀ p ∈ N3, 2 ≤ ((N1 ∪ N2).filter (fun z => D p z = true)).card + (N3.filter (fun z => D p z = true)).card)
    (o3' : ∀ p ∈ N3, ((N1 ∪ N2).filter (fun z => D p z = true)).card ≤ 3)
    (cap : ∀ z ∈ N1 ∪ N2 ∪ N3, ((N1 ∪ N2 ∪ N3).filter (fun y => R y z)).card ≤ 1)
    (r1 : ∀ y ∈ N1, ∀ z ∈ N1, D y z = true → R y z)
    (r2 : ∀ y ∈ N2, ∀ z ∈ N1 ∪ N2, D y z = true → R y z)
    (r3 : ∀ y ∈ N3, ∀ z ∈ N1 ∪ N2 ∪ N3, D y z = true → R y z) : False := by
  classical
  have hS1 : N1 ⊆ N1 ∪ N2 ∪ N3 := fun z hz => Finset.mem_union_left _ (Finset.mem_union_left _ hz)
  have hS3 : N3 ⊆ N1 ∪ N2 ∪ N3 := fun z hz => Finset.mem_union_right _ hz
  have hHS : N1 ∪ N2 ⊆ N1 ∪ N2 ∪ N3 := Finset.subset_union_left
  have capS : ∀ T ⊆ N1 ∪ N2 ∪ N3, ∀ z ∈ N1 ∪ N2 ∪ N3, (T.filter (fun y => R y z)).card ≤ 1 :=
    fun T hT z hz => (Finset.card_le_card (Finset.filter_subset_filter _ hT)).trans (cap z hz)
  have hH : (N1 ∪ N2).card = 3 + N2.card := by rw [Finset.card_union_of_disjoint d12, c1]
  -- (1) the cap on `H = N_1 ∪ N_2`, split over the three layers
  have hC : ∑ y ∈ N1 ∪ N2 ∪ N3, ((N1 ∪ N2).filter (fun z => R y z)).card ≤ (N1 ∪ N2).card :=
    head_count R (fun z hz => cap z (hHS hz))
  rw [Finset.sum_union (Finset.disjoint_union_left.mpr ⟨d13, d23⟩), Finset.sum_union d12] at hC
  -- (2) a source `s` of `D[N_3]`; arcs inside `N_3` number at most `n_3 - 1`
  obtain ⟨s, hs, hsrc⟩ := exists_source (hfree.mono_set hW3) (Finset.card_pos.mp (by omega)) (by omega)
  have hY : ∑ p ∈ N3, (N3.filter (fun z => D p z = true)).card ≤ N3.card - 1 := by
    calc ∑ p ∈ N3, (N3.filter (fun z => D p z = true)).card
        ≤ ∑ p ∈ N3, ((N3.erase s).filter (fun z => R p z)).card := by
          apply Finset.sum_le_sum
          intro p hp
          apply Finset.card_le_card
          intro z hz
          obtain ⟨hz3, hpz⟩ := Finset.mem_filter.mp hz
          refine Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨?_, hz3⟩, r3 p hp z (hS3 hz3) hpz⟩
          intro h
          rw [h] at hpz
          exact hsrc p hp hpz
      _ ≤ (N3.erase s).card := head_count R (fun z hz => capS N3 hS3 z (hS3 (Finset.mem_of_mem_erase hz)))
      _ = N3.card - 1 := Finset.card_erase_of_mem hs
  -- (3) `Q`: vertices of `N_1` with an arc into `N_1`
  obtain ⟨Q, hQ⟩ : ∃ Q : Finset ℕ, Q = N1.filter (fun a => ∃ a' ∈ N1, D a a' = true) := ⟨_, rfl⟩
  have hQ1 : Q ⊆ N1 := by rw [hQ]; exact Finset.filter_subset _ _
  have hC1 : Q.card ≤ ∑ a ∈ N1, ((N1 ∪ N2).filter (fun z => R a z)).card := by
    calc Q.card = ∑ _a ∈ Q, 1 := by simp
      _ ≤ ∑ a ∈ Q, ((N1 ∪ N2).filter (fun z => R a z)).card := by
          apply Finset.sum_le_sum
          intro a ha
          rw [hQ, Finset.mem_filter] at ha
          obtain ⟨ha1, a', ha', haa'⟩ := ha
          exact Finset.card_pos.mpr
            ⟨a', Finset.mem_filter.mpr ⟨Finset.mem_union_left _ ha', r1 a ha1 a' ha' haa'⟩⟩
      _ ≤ ∑ a ∈ N1, ((N1 ∪ N2).filter (fun z => R a z)).card := Finset.sum_le_sum_of_subset hQ1
  -- (4) `N_2`: `C_2 + n_2 n_3 ≥ 3 n_2 + M`
  have hb : ∀ b ∈ N2, 3 + (N3.filter (fun p => ¬ D b p = true)).card ≤
      ((N1 ∪ N2).filter (fun z => R b z)).card + N3.card := by
    intro b hb
    have h1 := o2 b hb
    have h2 := Finset.card_filter_add_card_filter_not (s := N3) (fun p => D b p = true)
    have h3 : ((N1 ∪ N2).filter (fun z => D b z = true)).card ≤ ((N1 ∪ N2).filter (fun z => R b z)).card :=
      card_filter_le_of_imp (fun z hz h => r2 b hb z hz h)
    omega
  have hC2 := Finset.sum_le_sum hb
  have e3 : ∑ _b ∈ N2, 3 = N2.card * 3 := Finset.sum_const_nat (fun _ _ => rfl)
  have en : ∑ _b ∈ N2, N3.card = N2.card * N3.card := Finset.sum_const_nat (fun _ _ => rfl)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, e3, en] at hC2
  have hdc : ∑ b ∈ N2, (N3.filter (fun p => ¬ D b p = true)).card =
      ∑ p ∈ N3, (N2.filter (fun b => ¬ D b p = true)).card :=
    double_count (fun b p => ¬ D b p = true)
  -- (5) `N_3`: `X ≥ 2 n_3 - (n_3 - 1)`, `C_3 ≥ X`
  have hX : ∑ p ∈ N3, 2 ≤ ∑ p ∈ N3, (((N1 ∪ N2).filter (fun z => D p z = true)).card +
      (N3.filter (fun z => D p z = true)).card) := Finset.sum_le_sum o3
  have e2 : ∑ _p ∈ N3, 2 = N3.card * 2 := Finset.sum_const_nat (fun _ _ => rfl)
  rw [Finset.sum_add_distrib, e2] at hX
  have hC3 : ∑ p ∈ N3, ((N1 ∪ N2).filter (fun z => D p z = true)).card ≤
      ∑ p ∈ N3, ((N1 ∪ N2).filter (fun z => R p z)).card :=
    Finset.sum_le_sum (fun p hp => card_filter_le_of_imp (fun z hz h => r3 p hp z (hHS hz) h))
  -- (6) per `p`: `|O(p) ∩ H| ≤ m_p + |O(p) ∩ Q|`
  have hp : ∀ p ∈ N3, ((N1 ∪ N2).filter (fun z => D p z = true)).card ≤
      (N2.filter (fun b => ¬ D b p = true)).card + (Q.filter (fun z => D p z = true)).card := by
    intro p hp
    by_cases hm : 3 ≤ (N2.filter (fun b => ¬ D b p = true)).card
    · have := o3' p hp
      omega
    · have hsub : (N1 ∪ N2).filter (fun z => D p z = true) ⊆
          N2.filter (fun b => ¬ D b p = true) ∪ Q.filter (fun z => D p z = true) := by
        intro z hz
        obtain ⟨hzH, hpz⟩ := Finset.mem_filter.mp hz
        rcases Finset.mem_union.mp hzH with hz1 | hz2
        · by_cases hzQ : z ∈ Q
          · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hzQ, hpz⟩)
          · exfalso
            have h0 : (N1.filter (fun w => D z w = true)).card = 0 := by
              rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
              intro w hw hzw
              exact hzQ (by rw [hQ, Finset.mem_filter]; exact ⟨hz1, w, hw, hzw⟩)
            have h3 := o1 z hz1
            -- the three out-neighbours of `z` lie in `N_2` and none heads `p` (triangle)
            have h4 : (N2.filter (fun w => D z w = true)).card ≤ (N2.filter (fun b => ¬ D b p = true)).card := by
              apply Finset.card_le_card
              intro w hw
              obtain ⟨hw2, hzw⟩ := Finset.mem_filter.mp hw
              refine Finset.mem_filter.mpr ⟨hw2, fun hwp => ?_⟩
              exact hfree z 3 (by omega) (by omega)
                (.step (hW2 hw2) hzw (.step (hW3 hp) hwp (.step (hW1 hz1) hpz (.refl z))))
            omega
        · refine Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hz2, fun hzp => ?_⟩)
          exact digonfree hfree (by omega) (hW2 hz2) (hW3 hp) hzp hpz
      exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hXup := Finset.sum_le_sum hp
  rw [Finset.sum_add_distrib] at hXup
  -- (7) `Σ_p |O(p) ∩ Q| ≤ |Q|` by the cap
  have hQs : ∑ p ∈ N3, (Q.filter (fun z => D p z = true)).card ≤ Q.card := by
    calc ∑ p ∈ N3, (Q.filter (fun z => D p z = true)).card ≤ ∑ p ∈ N3, (Q.filter (fun z => R p z)).card :=
          Finset.sum_le_sum (fun p hp => card_filter_le_of_imp (fun z hz h => r3 p hp z (hS1 (hQ1 hz)) h))
      _ ≤ Q.card := head_count R (fun z hz => capS N3 hS3 z (hS1 (hQ1 hz)))
  -- (8) arithmetic, profile by profile
  have hprod : N2.card * N3.card = 12 ∧ N2.card = 3 ∨ N2.card * N3.card = 12 ∧ N2.card = 4 ∨
      N2.card * N3.card = 10 ∧ N2.card = 5 := by
    rcases (show N2.card = 3 ∨ N2.card = 4 ∨ N2.card = 5 by omega) with h | h | h
    · rw [h, show N3.card = 4 by omega]; simp
    · rw [h, show N3.card = 3 by omega]; simp
    · rw [h, show N3.card = 2 by omega]; simp
  omega

end LeanCH.BR.BRq3
