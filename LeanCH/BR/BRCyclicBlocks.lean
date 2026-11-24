import LeanCH.BR.BRRankPhase

/-! Cyclic substitution preserves a cutoff when each block does. -/

namespace LeanCH.BR.BRq2

/-- The phase certificate only needs to hold for vertices in the host. -/
theorem qfree_of_rank_phase_on {D : CH.Digraph} {V : Finset ℕ} {q : ℕ}
    (rank phase : ℕ → ℕ)
    (hstep : ∀ a ∈ V, ∀ b ∈ V, D a b = true →
      rank a ≤ rank b ∧ (rank a = rank b → Nat.ModEq (q + 1) (phase a + 1) (phase b))) :
    QFree D V q := by
  have hw : ∀ {a b l}, Walk D V a b l → a ∈ V → rank a ≤ rank b ∧
      (rank a = rank b → Nat.ModEq (q + 1) (phase a + l) (phase b)) := by
    intro a b l w
    induction w with
    | refl a => exact fun _ => ⟨le_rfl, fun _ => by simp only [Nat.add_zero]; rfl⟩
    | @step a b z l hb hab w ih =>
      intro ha
      obtain ⟨hr, hp⟩ := hstep a ha b hb hab
      have hh := ih hb
      refine ⟨hr.trans hh.1, ?_⟩
      intro heq
      have ht := ((hp (by omega)).add_right l).trans (hh.2 (by omega))
      convert ht using 1 <;> omega
  intro a l hl hlq w
  have ha : a ∈ V := by
    cases w with
    | refl => omega
    | step hb _ tail =>
      rcases tail.end_mem_or with h | h
      · exact h ▸ hb
      · exact h
  have hmod := (hw w ha).2 rfl
  have hd : q + 1 ∣ l := by simpa using hmod.symm.dvd'
  have hh := Nat.le_of_dvd (by omega : 0 < l) hd
  omega

/-- Count the steps that advance between cyclic blocks. Zero advancing steps
means that the whole walk stays in its starting block. -/
theorem Walk.cyclic_block_count {D : CH.Digraph} {V : Finset ℕ} {N a b l : ℕ}
    (block : ℕ → ℕ)
    (hstep : ∀ x y, y ∈ V → D x y = true →
      block x = block y ∨ Nat.ModEq N (block x + 1) (block y))
    (w : Walk D V a b l) :
    ∃ c, c ≤ l ∧ Nat.ModEq N (block a + c) (block b) ∧
      (c = 0 → Walk D (V.filter (fun v => block v = block a)) a b l) := by
  classical
  induction w with
  | refl a => exact ⟨0, le_rfl, by simp only [Nat.add_zero]; rfl, fun _ => .refl a⟩
  | @step a b z l hb hab w ih =>
    obtain ⟨c, hc, heq, hzero⟩ := ih
    rcases hstep a b hb hab with hsame | hnext
    · refine ⟨c, by omega, ?_, ?_⟩
      · simpa only [hsame] using heq
      · intro hc0
        apply Walk.step (Finset.mem_filter.mpr ⟨hb, hsame.symm⟩) hab
        apply (hzero hc0).mono
        intro v hv
        obtain ⟨hvV, hvb⟩ := Finset.mem_filter.mp hv
        exact Finset.mem_filter.mpr ⟨hvV, hvb.trans hsame.symm⟩
    · refine ⟨c + 1, by omega, ?_, fun hc0 => (by omega : False).elim⟩
      have hh := (hnext.add_right c).trans heq
      convert hh using 1 <;> omega

/-- A cyclic quotient longer than the forbidden cutoff and cutoff-free
induced blocks give a cutoff-free substitution. Internal graphs may vary. -/
theorem qfree_of_cyclic_blocks {D : CH.Digraph} {V : Finset ℕ} {q N : ℕ}
    (hN : q < N) (block : ℕ → ℕ)
    (hstep : ∀ a b, b ∈ V → D a b = true →
      block a = block b ∨ Nat.ModEq N (block a + 1) (block b))
    (hinside : ∀ i, QFree D (V.filter (fun v => block v = i)) q) : QFree D V q := by
  intro a l hl hlq w
  obtain ⟨c, hc, hmod, hzero⟩ := w.cyclic_block_count block hstep
  have hd : N ∣ c := by simpa using hmod.symm.dvd'
  have hc0 : c = 0 := by
    by_contra hn
    have hh := Nat.le_of_dvd (by omega : 0 < c) hd
    omega
  exact hinside (block a) a l hl hlq (hzero hc0)

end LeanCH.BR.BRq2
