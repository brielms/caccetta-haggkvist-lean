import LeanCH.BR.BRCyclicBlocks

/-! Quotient projection and variable forward steps certify substitution girth. -/
namespace LeanCH.BR.BRq2

theorem Walk.project_blocks {D E : CH.Digraph} {V U : Finset ℕ} {a b l : ℕ}
    (block : ℕ → ℕ) (hmem : ∀ v ∈ V, block v ∈ U)
    (hstep : ∀ x y, y ∈ V → D x y = true →
      block x = block y ∨ E (block x) (block y) = true)
    (w : Walk D V a b l) :
    ∃ c, c ≤ l ∧ Walk E U (block a) (block b) c ∧
      (c = 0 → Walk D (V.filter (fun v => block v = block a)) a b l) := by
  classical
  induction w with
  | refl a => exact ⟨0, le_rfl, .refl _, fun _ => .refl a⟩
  | @step a b z l hb hab w ih =>
    obtain ⟨c, hc, hw, hz⟩ := ih
    rcases hstep a b hb hab with he | he
    · refine ⟨c, by omega, he ▸ hw, ?_⟩
      intro hc0
      apply Walk.step (Finset.mem_filter.mpr ⟨hb, he.symm⟩) hab
      apply (hz hc0).mono
      intro v hv
      obtain ⟨hvV, hvb⟩ := Finset.mem_filter.mp hv
      exact Finset.mem_filter.mpr ⟨hvV, hvb.trans he.symm⟩
    · exact ⟨c + 1, by omega, .step (hmem b hb) he hw, fun hh => (by omega : False).elim⟩

/-- Both quotient and every induced block being q-free suffices, for all q. -/
theorem qfree_of_quotient_blocks {D E : CH.Digraph} {V U : Finset ℕ} {q : ℕ}
    (block : ℕ → ℕ) (hmem : ∀ v ∈ V, block v ∈ U)
    (hstep : ∀ x y, y ∈ V → D x y = true →
      block x = block y ∨ E (block x) (block y) = true)
    (hquot : QFree E U q)
    (hinside : ∀ i, QFree D (V.filter (fun v => block v = i)) q) : QFree D V q := by
  intro a l hl hlq w
  obtain ⟨c, hc, hw, hz⟩ := w.project_blocks block hmem hstep
  have hc0 : c = 0 := by
    by_contra hn
    exact hquot _ c (by omega) (by omega) hw
  exact hinside (block a) a l hl hlq (hz hc0)

/-- A walk whose forward modular steps lie in [1,d] has total advance
between its length and d times its length. -/
theorem Walk.bounded_modular_steps {D : CH.Digraph} {V : Finset ℕ} {a b l N d : ℕ}
    (phase : ℕ → ℕ)
    (hstep : ∀ x ∈ V, ∀ y ∈ V, D x y = true →
      ∃ k, 1 ≤ k ∧ k ≤ d ∧ Nat.ModEq N (phase x + k) (phase y))
    (w : Walk D V a b l) : a ∈ V →
    ∃ t, l ≤ t ∧ t ≤ l * d ∧ Nat.ModEq N (phase a + t) (phase b) := by
  induction w with
  | refl a => exact fun _ => ⟨0, le_rfl, by simp, by simp only [Nat.add_zero]; rfl⟩
  | @step a b z l hb hab w ih =>
    intro ha
    obtain ⟨k, hk, hkd, hm⟩ := hstep a ha b hb hab
    obtain ⟨t, hlt, htd, ht⟩ := ih hb
    refine ⟨k + t, by omega, ?_, ?_⟩
    · rw [Nat.add_mul, Nat.one_mul]; omega
    simpa only [Nat.add_assoc] using (hm.add_right t).trans ht

theorem qfree_of_bounded_modular_steps {D : CH.Digraph} {V : Finset ℕ} {q N d : ℕ}
    (hsize : q * d < N) (phase : ℕ → ℕ)
    (hstep : ∀ x ∈ V, ∀ y ∈ V, D x y = true →
      ∃ k, 1 ≤ k ∧ k ≤ d ∧ Nat.ModEq N (phase x + k) (phase y)) : QFree D V q := by
  intro a l hl hlq w
  have ha : a ∈ V := by
    cases w with
    | refl => omega
    | step hb _ tail =>
      rcases tail.end_mem_or with h | h
      · exact h ▸ hb
      · exact h
  obtain ⟨t, hlt, htd, ht⟩ := w.bounded_modular_steps phase hstep ha
  have hd : N ∣ t := by simpa using ht.symm.dvd'
  have hNt := Nat.le_of_dvd (by omega : 0 < t) hd
  have hle := Nat.mul_le_mul_right d hlq
  omega

end LeanCH.BR.BRq2
