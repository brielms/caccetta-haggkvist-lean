import LeanCH.BR.BRWeightedCritical

/-! Necessary conditions for repairs by edge addition on retained vertices.
An old short return path blocks every proposed new arc, even in a joint repair. -/
namespace LeanCH.BR.WeightedSD
open BRq2 BRq3 BR45 BRsub

theorem walk_mono_graph_on {D E : CH.Digraph} {K : Finset ℕ}
    (hDE : ∀ a ∈ K, ∀ b ∈ K, D a b = true → E a b = true)
    {a b l : ℕ} (w : Walk D K a b l) (ha : a ∈ K) : Walk E K a b l := by
  induction w with
  | refl a => exact .refl a
  | @step a b c l hb hab w ih => exact .step hb (hDE a ha b hb hab) (ih hb)

theorem repair_arc_blocks_old_return {q : ℕ} (hq : 1 ≤ q)
    {D E : CH.Digraph} {K : Finset ℕ} (hf : QFree E K q)
    (hDE : ∀ a ∈ K, ∀ b ∈ K, D a b = true → E a b = true)
    {a b : ℕ} (ha : a ∈ K) (hb : b ∈ K) (hab : E a b = true) :
    a ∉ ball D K b (q - 1) := by
  intro hreturn
  obtain ⟨_, k, hk, hw⟩ := mem_ball.mp hreturn
  exact hf a (k + 1) (by omega) (by omega)
    (.step hb hab (walk_mono_graph_on hDE hw hb))

/-- If every retained vertex already reaches t within q-1 steps, no q-free
extension retaining the old edges can give t an outgoing edge. -/
theorem persistent_sink {q : ℕ} (hq : 1 ≤ q)
    {D E : CH.Digraph} {K : Finset ℕ} {t : ℕ} (ht : t ∈ K)
    (hreach : ∀ v ∈ K, t ∈ ball D K v (q - 1)) (hf : QFree E K q)
    (hDE : ∀ a ∈ K, ∀ b ∈ K, D a b = true → E a b = true) :
    ∀ v ∈ K, E t v = false := by
  intro v hv
  apply Bool.eq_false_iff.mpr
  intro htv
  exact repair_arc_blocks_old_return hq hf hDE ht hv htv (hreach v hv)

theorem positive_feasibility_impossible_at_sink {q : ℕ}
    {E : CH.Digraph} {K : Finset ℕ} {t v : ℕ} (ht : t ∈ K) (hv : v ∈ K) (hne : v ≠ t)
    (hsink : ∀ u ∈ K, E t u = false) (w : ℕ → ℚ) (hw : ∀ u ∈ K, 0 < w u)
    (hr : ∀ u ∈ K, mass K w ≤ row q E K w u) : False := by
  have hout : outW E K w t = 0 := by
    apply Finset.sum_eq_zero
    intro u hu
    simp [hsink u hu]
  have hpos : 0 < mass (K.erase t) w := by
    apply Finset.sum_pos'
    · exact fun u hu => (hw u (Finset.mem_erase.mp hu).2).le
    · exact ⟨v, Finset.mem_erase.mpr ⟨hne, hv⟩, hw v hv⟩
  have hsum := Finset.sum_erase_add K w ht
  change mass (K.erase t) w + w t = mass K w at hsum
  have hh := hr t ht
  rw [row, hout, mul_zero, add_zero] at hh
  linarith

theorem no_positive_addition_repair {q : ℕ} (hq : 1 ≤ q)
    {D : CH.Digraph} {K : Finset ℕ} {t v : ℕ} (ht : t ∈ K) (hv : v ∈ K) (hne : v ≠ t)
    (hreach : ∀ u ∈ K, t ∈ ball D K u (q - 1)) :
    ¬ ∃ E : CH.Digraph,
      (∀ a ∈ K, ∀ b ∈ K, D a b = true → E a b = true) ∧ QFree E K q ∧
      ∃ w : ℕ → ℚ, (∀ u ∈ K, 0 < w u) ∧ ∀ u ∈ K, mass K w ≤ row q E K w u := by
  rintro ⟨E, hDE, hf, w, hw, hr⟩
  exact positive_feasibility_impossible_at_sink ht hv hne
    (persistent_sink hq ht hreach hf hDE) w hw hr

/-- The same obstruction survives substitution of the terminal vertex by
any internally self-dual block: a proper closed block has insufficient mass. -/
theorem positive_feasibility_impossible_at_closed_set {q : ℕ}
    {E : CH.Digraph} {K T : Finset ℕ} (hTK : T ⊆ K) (hT : T.Nonempty) (hne : T ≠ K)
    (hSD : SelfDual q E T)
    (hclosed : ∀ t ∈ T, ∀ v ∈ K, v ∉ T → E t v = false)
    (w : ℕ → ℚ) (hw : ∀ u ∈ K, 0 < w u)
    (hr : ∀ u ∈ K, mass K w ≤ row q E K w u) : False := by
  have hmass : mass T w < mass K w := by
    apply lt_of_le_of_ne (mass_mono hTK (fun u hu => (hw u hu).le))
    intro heq
    exact hne (positive_mass_eq_subset hTK hw heq)
  obtain ⟨t, ht, hsmall⟩ := exists_small_row hSD hT w (fun u hu => (hw u (hTK hu)).le)
  have hout : outW E (K \ T) w t = 0 := by
    apply Finset.sum_eq_zero
    intro v hv
    obtain ⟨hvK, hvT⟩ := Finset.mem_sdiff.mp hv
    simp [hclosed t ht v hvK hvT]
  have hh := hr t (hTK ht)
  rw [row, outW_split hTK w t, hout, add_zero] at hh
  exact (not_lt_of_ge (hh.trans hsmall)) hmass

theorem repair_preserves_terminal_set {q : ℕ} (hq : 1 ≤ q)
    {D E : CH.Digraph} {K T : Finset ℕ} (hTK : T ⊆ K)
    (hreach : ∀ t ∈ T, ∀ v ∈ K, v ∉ T → t ∈ ball D K v (q - 1))
    (hf : QFree E K q)
    (hDE : ∀ a ∈ K, ∀ b ∈ K, D a b = true → E a b = true) :
    ∀ t ∈ T, ∀ v ∈ K, v ∉ T → E t v = false := by
  intro t ht v hv hvT
  apply Bool.eq_false_iff.mpr
  intro htv
  exact repair_arc_blocks_old_return hq hf hDE (hTK ht) hv htv (hreach t ht v hv hvT)

end LeanCH.BR.WeightedSD
