import LeanCH.BR.BRq2Walk
import Mathlib.Data.Nat.ModEq

/-! Acyclic component order and cyclic phases certify directed girth. -/

namespace LeanCH.BR.BRq2

theorem qfree_of_rank_phase {D : CH.Digraph} {V : Finset ℕ} {q : ℕ}
    (rank phase : ℕ → ℕ)
    (hstep : ∀ a b, b ∈ V → D a b = true →
      rank a ≤ rank b ∧ (rank a = rank b → Nat.ModEq (q + 1) (phase a + 1) (phase b))) :
    QFree D V q := by
  have hwalk : ∀ {a b m}, Walk D V a b m → rank a ≤ rank b ∧
      (rank a = rank b → Nat.ModEq (q + 1) (phase a + m) (phase b)) := by
    intro a b m w
    induction w with
    | refl a => exact ⟨le_rfl, fun _ => by simp only [Nat.add_zero]; rfl⟩
    | @step a b c m hb hab _ ih =>
      obtain ⟨hr, hp⟩ := hstep a b hb hab
      refine ⟨hr.trans ih.1, ?_⟩
      intro heq
      have habr : rank a = rank b := by omega
      have hbcr : rank b = rank c := by omega
      have hs := (hp habr).add_right m
      have ht := hs.trans (ih.2 hbcr)
      convert ht using 1 <;> omega
  intro a m hm hmq w
  have hmod := (hwalk w).2 rfl
  have hd : q + 1 ∣ m := by
    have hh := hmod.symm.dvd'
    simpa using hh
  have hh := Nat.le_of_dvd hm hd
  omega

end LeanCH.BR.BRq2
