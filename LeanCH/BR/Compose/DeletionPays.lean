import LeanCH.BR.CH.Side.ScTwoHitFreeSetDescends
import LeanCH.BR.CH.Research.FixedDegreeCH

/-!
Composition test (2026-11-11): the August "k-set deletion engine"
(`CH.Side.sc_two_hit_free_set_descends`, fable, Aug 2026) proves the November
paper lemma `DeficitOneEveryPairHasActualCommonParent.md` (Nov 4, audited, paper only)
and its principal-order triple analogue.

General form: if `n = |S| + q (R-1)` and degree-`(R-1)` CH holds, a graph of minimum
outdegree `R` with no cycle of length at most `q` has, for every such `S`, an outside
vertex hitting two members of `S` (a common parent of some pair of `S`).
-/

namespace Compose.DeletionPays

open CH

theorem ceilDiv_mul_le (q m : Nat) (hm : 0 < m) : CH.ceilDiv (q * m) m ≤ q := by
  unfold CH.ceilDiv
  have h : q * m + m - 1 < (q + 1) * m := by
    rw [Nat.add_mul, Nat.one_mul]; omega
  have := (Nat.div_lt_iff_lt_mul hm).mpr h
  omega

/-- Deletion pays: some outside vertex double-hits `S`. -/
theorem outside_double_hit
    {G : CH.Digraph} {n R q : Nat} {S : Finset Nat}
    (hR : 2 ≤ R) (ih : CH.Research.FixedDegreeCH (R - 1)) (hq : 0 < q)
    (hsub : S ⊆ Finset.range n) (order : n = S.card + q * (R - 1))
    (loopless : CH.Loopless G n) (deg : CH.MinOutdegreeAtLeast G n R)
    (noShort : ¬ CH.HasDirectedCycleAtMost G n q) :
    ∃ v, v < n ∧ v ∉ S ∧ ∃ s₁ ∈ S, ∃ s₂ ∈ S, s₁ ≠ s₂ ∧ G v s₁ = true ∧ G v s₂ = true := by
  by_contra none
  push Not at none
  have hit : ∀ v, v < n → v ∉ S →
      ∀ s₁, s₁ ∈ S → ∀ s₂, s₂ ∈ S → s₁ ≠ s₂ → ¬(G v s₁ = true ∧ G v s₂ = true) := by
    intro v hv hvS s₁ h₁ s₂ h₂ hne both
    exact none v hv hvS s₁ h₁ s₂ h₂ hne both.1 |> fun h => by simp_all
  obtain ⟨H, hl, hd, lift⟩ := CH.Side.sc_two_hit_free_set_descends hsub loopless deg hit
  have hcard : n - S.card = q * (R - 1) := by omega
  rw [hcard] at hl hd lift
  obtain ⟨vs, cyc, len⟩ := ih (q * (R - 1)) H (Nat.mul_pos hq (by omega)) (by omega) hl hd
  exact noShort (lift q ⟨vs, cyc, len.trans (ceilDiv_mul_le q (R - 1) (by omega))⟩)

/-- Nov 4 paper lemma, now in Lean: at deficit-one triangle order every pair of distinct
vertices has a common parent (distinct from both). -/
theorem deficit_one_pair_common_parent
    {G : CH.Digraph} {R i j : Nat}
    (hR : 2 ≤ R) (ih : CH.Research.FixedDegreeCH (R - 1))
    (loopless : CH.Loopless G (3 * R - 1)) (deg : CH.MinOutdegreeAtLeast G (3 * R - 1) R)
    (noShort : ¬ CH.HasDirectedCycleAtMost G (3 * R - 1) 3)
    (hi : i < 3 * R - 1) (hj : j < 3 * R - 1) (hij : i ≠ j) :
    ∃ w, w < 3 * R - 1 ∧ w ≠ i ∧ w ≠ j ∧ G w i = true ∧ G w j = true := by
  have hsub : ({i, j} : Finset Nat) ⊆ Finset.range (3 * R - 1) := by
    intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> simpa
  have hcard : ({i, j} : Finset Nat).card = 2 := Finset.card_pair hij
  obtain ⟨v, hv, hvS, s₁, h₁, s₂, h₂, hne, e₁, e₂⟩ :=
    outside_double_hit (q := 3) hR ih (by omega) hsub (by rw [hcard]; omega) loopless deg noShort
  simp only [Finset.mem_insert, Finset.mem_singleton] at h₁ h₂ hvS
  push Not at hvS
  refine ⟨v, hv, hvS.1, hvS.2, ?_⟩
  rcases h₁ with rfl | rfl <;> rcases h₂ with rfl | rfl
  · exact absurd rfl hne
  · exact ⟨e₁, e₂⟩
  · exact ⟨e₂, e₁⟩
  · exact absurd rfl hne

/-- Principal-order analogue: at `n = 3R`, every three distinct vertices contain a pair
with a common parent outside the triple. -/
theorem principal_triple_has_common_parent_pair
    {G : CH.Digraph} {R x y z : Nat}
    (hR : 2 ≤ R) (ih : CH.Research.FixedDegreeCH (R - 1))
    (loopless : CH.Loopless G (3 * R)) (deg : CH.MinOutdegreeAtLeast G (3 * R) R)
    (noShort : ¬ CH.HasDirectedCycleAtMost G (3 * R) 3)
    (hx : x < 3 * R) (hy : y < 3 * R) (hz : z < 3 * R)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ∃ v, v < 3 * R ∧ v ≠ x ∧ v ≠ y ∧ v ≠ z ∧
      ((G v x = true ∧ G v y = true) ∨ (G v x = true ∧ G v z = true) ∨
       (G v y = true ∧ G v z = true)) := by
  have hsub : ({x, y, z} : Finset Nat) ⊆ Finset.range (3 * R) := by
    intro a ha; simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl <;> simpa
  have hcard : ({x, y, z} : Finset Nat).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hxy, hxz]), Finset.card_pair hyz]
  obtain ⟨v, hv, hvS, s₁, h₁, s₂, h₂, hne, e₁, e₂⟩ :=
    outside_double_hit (q := 3) hR ih (by omega) hsub (by rw [hcard]; omega) loopless deg noShort
  simp only [Finset.mem_insert, Finset.mem_singleton] at h₁ h₂ hvS
  push Not at hvS
  refine ⟨v, hv, hvS.1, hvS.2.1, hvS.2.2, ?_⟩
  rcases h₁ with rfl | rfl | rfl <;> rcases h₂ with rfl | rfl | rfl <;>
    first | exact absurd rfl hne | simp_all

end Compose.DeletionPays
