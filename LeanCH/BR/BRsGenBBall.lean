import LeanCH.BR.BRq3Base

/-!
# Boundary Ball suffices for BR (Lean 4.35.0)

`br_of_ball` only ever applies its ball hypothesis to the out-exactly-`s` trimming of a boundary graph. That graph lives
on `range (q*s+1)` and is `q`-free, so it is itself a boundary graph. This file states that interface explicitly.

`BBall q s`: every `q`-free digraph with out-degree exactly `s` **on the boundary vertex set `range (q*s+1)`** has
`|B_{q-1}(u)| ≥ s(q-1)+1`. It is strictly weaker than `Ball q s`: `Ball 3 4` is false (`BRq4.not_ball34`), and its
counterexample has 21 vertices, not 13.

`br_of_bball : BBall q s → BoundaryRegular q s`.
-/

namespace LeanCH.BR.BRsGen

open LeanCH.BR.BRq2 LeanCH.BR.BRq3 CH Compose.Boundary Compose.FloorSix

/-- Boundary Ball: the ball bound on boundary vertex sets only. -/
def BBall (q s : ℕ) : Prop :=
  ∀ (D : CH.Digraph), QFree D (Finset.range (q * s + 1)) q → OutEq s D (Finset.range (q * s + 1)) →
    ∀ u ∈ Finset.range (q * s + 1), s * (q - 1) + 1 ≤ (ball D (Finset.range (q * s + 1)) u (q - 1)).card

/-- `Ball q s` implies `BBall q s`. -/
theorem bball_of_ball {q s : ℕ}
    (hball : ∀ (D : CH.Digraph) (W : Finset ℕ), QFree D W q → OutEq s D W →
      ∀ u ∈ W, s * (q - 1) + 1 ≤ (ball D W u (q - 1)).card) : BBall q s :=
  fun D hf ho u hu => hball D _ hf ho u hu

/-- **Boundary Ball gives boundary regularity.** The proof is `br_of_ball`'s, with the ball hypothesis used only on
`range (q*s+1)`. -/
theorem br_of_bball {q s : ℕ} (hq : 1 ≤ q) (hball : BBall q s) : BoundaryRegular q s := by
  intro G loopless deg noShort
  classical
  have hfree : QFree G (Finset.range (q * s + 1)) q := qfree_of_noShort loopless noShort
  obtain ⟨G', hsub, hout⟩ := exists_outEq (G := G) (V := Finset.range (q * s + 1)) (s := s)
    (fun v hv => out_card deg (Finset.mem_range.mp hv))
  have e : s * (q - 1) + s = q * s := by
    obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    rw [Nat.add_sub_cancel, Nat.succ_mul, Nat.mul_comm]
  have hle : ∀ u ∈ Finset.range (q * s + 1), (par G (q * s + 1) u).card ≤ s := by
    intro u hu
    have hA := hball G' (qfree_sub hsub hfree) hout u hu
    have hsub2 : par G (q * s + 1) u ⊆ Finset.range (q * s + 1) \ ball G (Finset.range (q * s + 1)) u (q - 1) := by
      intro y hy
      obtain ⟨hyV, hyu⟩ := Finset.mem_filter.mp hy
      exact Finset.mem_sdiff.mpr ⟨hyV, fun hyb => no_back_arc hfree hu hyb (by omega) hyu⟩
    have h1 := Finset.card_le_card hsub2
    have h2 := Finset.card_le_card (ball_sub (W := Finset.range (q * s + 1)) (u := u) (k := q - 1) hsub)
    rw [Finset.card_sdiff_of_subset ball_subset, Finset.card_range] at h1
    omega
  have hge : ∑ _u ∈ Finset.range (q * s + 1), s ≤
      ∑ u ∈ Finset.range (q * s + 1), (par G (q * s + 1) u).card :=
    calc ∑ _u ∈ Finset.range (q * s + 1), s
        ≤ ∑ x ∈ Finset.range (q * s + 1),
            ((Finset.range (q * s + 1)).filter (fun w => G x w = true)).card :=
          Finset.sum_le_sum (fun x hx => out_card deg (Finset.mem_range.mp hx))
      _ = ∑ v ∈ Finset.range (q * s + 1),
            ((Finset.range (q * s + 1)).filter (fun u => G u v = true)).card :=
          Compose.ThinRigid.sum_out_eq_sum_in G _
      _ = ∑ u ∈ Finset.range (q * s + 1), (par G (q * s + 1) u).card := rfl
  have heq := le_antisymm (Finset.sum_le_sum hle) hge
  have each := (Finset.sum_eq_sum_iff_of_le hle).mp heq
  intro v hv
  exact each v (Finset.mem_range.mpr hv)

end LeanCH.BR.BRsGen
