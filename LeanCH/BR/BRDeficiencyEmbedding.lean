import LeanCH.BR.BRDeficiencyCompletion

/-! The completion construction with an explicit copy of every old vertex and arc. -/

namespace LeanCH.BR.BRsGen
open BRq2 BRq3 BR45

theorem exists_deficiency_completion_embedding {D : CH.Digraph} {V : Finset ℕ} {q d : ℕ}
    (hf : QFree D V q) (hmin : ∀ v ∈ V, 1 ≤ (outN D V v).card) :
    ∃ (F : CH.Digraph) (U : Finset ℕ) (e : ℕ → ℕ), QFree F U q ∧
      (∀ v ∈ U, d ≤ (outN F U v).card) ∧
      U.card = V.card + ∑ v ∈ V, (d - (outN D V v).card) ∧
      Function.Injective e ∧ (∀ v ∈ V, e v ∈ U) ∧
      (∀ v w, F (e v) (e w) = D v w) := by
  classical
  have hchoose : ∀ v, ∃ w, v ∈ V → w ∈ V ∧ D v w = true := by
    intro v
    by_cases hv : v ∈ V
    · obtain ⟨w, hw⟩ := Finset.card_pos.mp (hmin v hv)
      exact ⟨w, fun _ => mem_outN.mp hw⟩
    · exact ⟨v, fun h => (hv h).elim⟩
  choose f hfspec using hchoose
  let gap := fun v => d - (outN D V v).card
  let S : Finset (Σ _ : ℕ, ℕ) := V.sigma (fun v => Finset.range (gap v + 1))
  let enc : (Σ _ : ℕ, ℕ) → ℕ := fun p => Nat.pair p.1 p.2
  let U := S.image enc
  let p : ℕ → ℕ := fun x =>
    if (Nat.unpair x).2 = 0 then (Nat.unpair x).1 else f (Nat.unpair x).1
  let F : CH.Digraph := fun x y => D (p x) (p y)
  have henc : Function.Injective enc := by
    rintro ⟨v, i⟩ ⟨w, j⟩ heq
    have hh := Nat.pair_eq_pair.mp heq
    rcases hh with ⟨rfl, rfl⟩
    rfl
  have hmem (v i : ℕ) (hv : v ∈ V) (hi : i ≤ gap v) : Nat.pair v i ∈ U := by
    apply Finset.mem_image.mpr
    exact ⟨⟨v, i⟩, Finset.mem_sigma.mpr
      ⟨hv, Finset.mem_range.mpr (by change i < gap v + 1; omega)⟩, rfl⟩
  have hp0 (v : ℕ) : p (Nat.pair v 0) = v := by simp [p]
  have hpi (v i : ℕ) (hi : i ≠ 0) : p (Nat.pair v i) = f v := by simp [p, hi]
  have hpV : ∀ x ∈ U, p x ∈ V := by
    intro x hx
    obtain ⟨⟨v, i⟩, hvi, rfl⟩ := Finset.mem_image.mp hx
    have hv := (Finset.mem_sigma.mp hvi).1
    change p (Nat.pair v i) ∈ V
    by_cases hi : i = 0
    · subst i
      rw [hp0]
      exact hv
    · rw [hpi v i hi]
      exact (hfspec v hv).1
  have hwalk : ∀ {a b m}, Walk F U a b m → Walk D V (p a) (p b) m := by
    intro a b m w
    induction w with
    | refl a => exact .refl (p a)
    | step hb hab _ ih => exact .step (hpV _ hb) hab ih
  refine ⟨F, U, (fun v => Nat.pair v 0),
    (fun a m hm hmq w => hf (p a) m hm hmq (hwalk w)), ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    have hv := hpV x hx
    let A := (outN D V (p x)).image (fun w => Nat.pair w 0)
    let B := (Finset.range (gap (p x))).image (fun i => Nat.pair (p x) (i + 1))
    have hAc : A.card = (outN D V (p x)).card := by
      apply Finset.card_image_of_injective
      intro a b h
      exact (Nat.pair_eq_pair.mp h).1
    have hBc : B.card = gap (p x) := by
      rw [Finset.card_image_of_injective]
      · exact Finset.card_range _
      · intro i j h
        have := (Nat.pair_eq_pair.mp h).2
        omega
    have hAB : Disjoint A B := by
      apply Finset.disjoint_left.mpr
      intro y hyA hyB
      obtain ⟨w, _, hw⟩ := Finset.mem_image.mp hyA
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hyB
      have := (Nat.pair_eq_pair.mp (hw.trans hi.symm)).2
      omega
    have hsub : A ∪ B ⊆ outN F U x := by
      intro y hy
      rcases Finset.mem_union.mp hy with hyA | hyB
      · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hyA
        refine mem_outN.mpr ⟨hmem w 0 (outN_subset hw) (by omega), ?_⟩
        change D (p x) (p (Nat.pair w 0)) = true
        rw [hp0]
        exact (mem_outN.mp hw).2
      · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hyB
        have hi' := Finset.mem_range.mp hi
        refine mem_outN.mpr ⟨hmem (p x) (i + 1) hv (by omega), ?_⟩
        change D (p x) (p (Nat.pair (p x) (i + 1))) = true
        rw [hpi _ _ (by omega)]
        exact (hfspec (p x) hv).2
    have hc := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hAB, hAc, hBc] at hc
    dsimp only [gap] at hc
    omega
  · change (S.image enc).card = _
    rw [Finset.card_image_of_injective _ henc]
    change (V.sigma (fun v => Finset.range (gap v + 1))).card = _
    rw [Finset.card_sigma]
    simp only [Finset.card_range, Finset.sum_add_distrib, gap]
    rw [Finset.sum_const_nat (fun _ _ => rfl)]
    omega
  · intro v w heq
    exact (Nat.pair_eq_pair.mp heq).1
  · intro v hv
    exact hmem v 0 hv (by omega)
  · intro v w
    change D (p (Nat.pair v 0)) (p (Nat.pair w 0)) = D v w
    rw [hp0, hp0]

theorem outN_card_le_embedding {D F : CH.Digraph} {V U : Finset ℕ} {e : ℕ → ℕ}
    (hinj : Function.Injective e) (hmem : ∀ v ∈ V, e v ∈ U)
    (hedge : ∀ v w, F (e v) (e w) = D v w) (v : ℕ) :
    (outN D V v).card ≤ (outN F U (e v)).card := by
  classical
  rw [← Finset.card_image_of_injective (outN D V v) hinj]
  apply Finset.card_le_card
  intro x hx
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hx
  exact mem_outN.mpr ⟨hmem w (mem_outN.mp hw).1, by rw [hedge]; exact (mem_outN.mp hw).2⟩

theorem inN_card_le_embedding {D F : CH.Digraph} {V U : Finset ℕ} {e : ℕ → ℕ}
    (hinj : Function.Injective e) (hmem : ∀ v ∈ V, e v ∈ U)
    (hedge : ∀ v w, F (e v) (e w) = D v w) (v : ℕ) :
    (inN D V v).card ≤ (inN F U (e v)).card := by
  classical
  rw [← Finset.card_image_of_injective (inN D V v) hinj]
  apply Finset.card_le_card
  intro x hx
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hx
  exact mem_inN.mpr ⟨hmem w (mem_inN.mp hw).1, by rw [hedge]; exact (mem_inN.mp hw).2⟩

end LeanCH.BR.BRsGen
