import LeanCH.BR.BR45Base

/-! Local degree descent supplied by a global ball bound. -/

namespace LeanCH.BR.BRsGen

open BRq2 BRq3 BR45

variable {D : CH.Digraph} {V X : Finset ℕ} {q d a : ℕ}

/-- Inside a small set, every vertex quickly reaches a row below the ambient degree floor.
Rows already meeting the floor internally are restricted to the set; other rows retain
their ambient heads. The global ball theorem then forces an exit. -/
theorem local_degree_drop_reachable (hq : 2 ≤ q) (hb : Ball q d)
    (hf : QFree D V q) (hmin : ∀ v ∈ V, d ≤ (outN D V v).card)
    (hXV : X ⊆ V) (hX : X.card ≤ d * (q - 1)) (ha : a ∈ X) :
    ∃ b ∈ X, (outN D X b).card < d ∧
      ∃ m, m ≤ q - 2 ∧ Walk D X a b m := by
  classical
  let F : CH.Digraph := fun v w =>
    if v ∈ X ∧ d ≤ (outN D X v).card then D v w && decide (w ∈ X) else D v w
  have hsub : ∀ v w, F v w = true → D v w = true := by
    intro v w h
    dsimp only [F] at h
    split_ifs at h with hv
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      exact h.1
    · exact h
  have hminF : ∀ v ∈ V, d ≤ (outN F V v).card := by
    intro v hv
    by_cases hg : v ∈ X ∧ d ≤ (outN D X v).card
    · apply hg.2.trans
      apply Finset.card_le_card
      intro w hw
      obtain ⟨hwX, hvw⟩ := mem_outN.mp hw
      exact mem_outN.mpr ⟨hXV hwX, by simp [F, hg, hvw, hwX]⟩
    · apply (hmin v hv).trans
      apply Finset.card_le_card
      intro w hw
      exact mem_outN.mpr ⟨(mem_outN.mp hw).1, by simpa [F, hg] using (mem_outN.mp hw).2⟩
  by_contra hn
  have hwalk : ∀ m, m ≤ q - 1 → ∀ v, Walk F V a v m → v ∈ X ∧ Walk D X a v m := by
    intro m
    induction m with
    | zero =>
      intro _ v w
      cases w
      exact ⟨ha, .refl a⟩
    | succ m ih =>
      intro hm v w
      obtain ⟨b, wab, hvV, hbv⟩ := w.unsnoc
      obtain ⟨hbX, wabD⟩ := ih (by omega) b wab
      have hg : b ∈ X ∧ d ≤ (outN D X b).card := by
        refine ⟨hbX, ?_⟩
        by_contra hsmall
        exact hn ⟨b, hbX, by omega, m, by omega, wabD⟩
      have hedges : D b v = true ∧ v ∈ X := by simpa [F, hg] using hbv
      exact ⟨hedges.2, wabD.snoc hedges.2 hedges.1⟩
  have hball : ball F V a (q - 1) ⊆ X := by
    intro v hv
    obtain ⟨_, m, hm, w⟩ := mem_ball.mp hv
    exact (hwalk m hm v w).1
  have hbound := ball_of_min hb (qfree_sub hsub hf) hminF a (hXV ha)
  have hcap := Finset.card_le_card hball
  omega

/-- A small first set reaches every exterior label when a low internal row must head them all. -/
theorem small_first_funnel_of_ball {Y : Finset ℕ} {s : ℕ}
    (hq : 2 ≤ q) (hb : Ball q d) (hf : QFree D V q)
    (hmin : ∀ v ∈ V, d ≤ (outN D V v).card)
    (hXV : X ⊆ V) (hYV : Y ⊆ V) (hXY : Disjoint X Y)
    (hX : X.card ≤ d * (q - 1)) (hbudget : d + Y.card ≤ s + 1)
    (hhigh : ∀ x ∈ X, s ≤ (outN D (X ∪ Y) x).card) :
    ∀ x ∈ X, ∀ y ∈ Y, ∃ m, 1 ≤ m ∧ m ≤ q - 1 ∧ Walk D V x y m := by
  intro x hx y hy
  obtain ⟨b, hbX, hlow, m, hm, w⟩ := local_degree_drop_reachable hq hb hf hmin hXV hX hx
  have hh := hhigh b hbX
  rw [card_outN_union hXY] at hh
  have heq : outN D Y b = Y := Finset.eq_of_subset_of_card_le outN_subset (by omega)
  have hby := (mem_outN.mp (heq.symm ▸ hy)).2
  exact ⟨m + 1, by omega, by omega, (w.mono hXV).snoc (hYV hy) hby⟩

theorem small_first_no_back_of_ball {Y : Finset ℕ} {s : ℕ}
    (hq : 2 ≤ q) (hb : Ball q d) (hf : QFree D V q)
    (hmin : ∀ v ∈ V, d ≤ (outN D V v).card)
    (hXV : X ⊆ V) (hYV : Y ⊆ V) (hXY : Disjoint X Y)
    (hX : X.card ≤ d * (q - 1)) (hbudget : d + Y.card ≤ s + 1)
    (hhigh : ∀ x ∈ X, s ≤ (outN D (X ∪ Y) x).card) :
    ∀ y ∈ Y, ∀ x ∈ X, ¬ D y x = true := by
  intro y hy x hx hyx
  obtain ⟨m, hm, hmq, w⟩ := small_first_funnel_of_ball hq hb hf hmin
    hXV hYV hXY hX hbudget hhigh x hx y hy
  exact hf x (m + 1) (by omega) (by omega) (w.snoc (hXV hx) hyx)

/-- A small acyclic middle layer must expand by a full degree after this funnel. -/
theorem small_first_next_layer_card {Y Z : Finset ℕ} {s : ℕ}
    (hq : 2 ≤ q) (hb : Ball q d) (hf : QFree D V q)
    (hmin : ∀ v ∈ V, d ≤ (outN D V v).card)
    (hXV : X ⊆ V) (hYV : Y ⊆ V) (hXY : Disjoint X Y)
    (hX : X.card ≤ d * (q - 1)) (hbudget : d + Y.card ≤ s + 1)
    (hYne : Y.Nonempty) (hYsmall : Y.card ≤ q)
    (hhighX : ∀ x ∈ X, s ≤ (outN D (X ∪ Y) x).card)
    (hhighY : ∀ y ∈ Y, s ≤ (outN D (X ∪ Y ∪ Z) y).card) : s ≤ Z.card := by
  have hn := small_first_no_back_of_ball hq hb hf hmin hXV hYV hXY hX hbudget hhighX
  obtain ⟨y, hy, hsink⟩ := exists_sink (hf.mono_set hYV) hYne hYsmall
  have hsub : outN D (X ∪ Y ∪ Z) y ⊆ Z := by
    intro v hv
    obtain ⟨hvU, hyv⟩ := mem_outN.mp hv
    rcases Finset.mem_union.mp hvU with hvXY | hvZ
    · rcases Finset.mem_union.mp hvXY with hvX | hvY
      · exact (hn y hy v hvX hyv).elim
      · exact (hsink v hvY hyv).elim
    · exact hvZ
  exact (hhighY y hy).trans (Finset.card_le_card hsub)

end LeanCH.BR.BRsGen
