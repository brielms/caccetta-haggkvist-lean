import LeanCH.BR.BR45Base
import LeanCH.BR.BRPrefixRetention
import Mathlib.Data.Nat.Pairing
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-! Fill degree shortages by duplicating neighbours, preserving a graph projection.
The minimum-one hypothesis ensures that every deficient row has a neighbour to copy. -/

namespace LeanCH.BR.BRsGen

open BRq2 BRq3 BR45

/-- A finite graph of positive minimum degree admits a q-free degree-d completion
on exactly its original order plus its total degree-d deficiency. -/
theorem exists_deficiency_completion_marked {D : CH.Digraph} {V : Finset ℕ} {q d : ℕ}
    (hf : QFree D V q) (hmin : ∀ v ∈ V, 1 ≤ (outN D V v).card) :
    ∃ (F : CH.Digraph) (U : Finset ℕ), QFree F U q ∧
      (∀ v ∈ U, d ≤ (outN F U v).card) ∧
      U.card = V.card + ∑ v ∈ V, (d - (outN D V v).card) ∧
      (V.Nonempty → U.Nonempty) ∧
      (∀ v ∈ V, ∃ w ∈ U, (outN D V v).card ≤ (outN F U w).card) ∧
      ((∃ v ∈ V, (outN D V v).card < d) →
        ∃ a ∈ U, ∃ b ∈ U, a ≠ b ∧ ∀ z, F a z = F b z) ∧
      (∀ (H : Finset ℕ) (r : ℕ), H ⊆ V →
        (∀ v ∈ H, r ≤ (outN D V v).card) →
        ∃ J ⊆ U, H.card ≤ J.card ∧ (∀ w ∈ J, r ≤ (outN F U w).card) ∧
          ((∃ v ∈ V, (outN D V v).card < d ∧ outN D V v ⊆ H) →
            H.card + 1 ≤ J.card)) := by
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
  refine ⟨F, U, (fun a m hm hmq w => hf (p a) m hm hmq (hwalk w)), ?_, ?_, ?_, ?_, ?_, ?_⟩
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
  · rintro ⟨v, hv⟩
    exact ⟨Nat.pair v 0, hmem v 0 hv (by omega)⟩
  · intro v hv
    refine ⟨Nat.pair v 0, hmem v 0 hv (by omega), ?_⟩
    have hinj : Function.Injective (fun w => Nat.pair w 0) :=
      fun _ _ heq => (Nat.pair_eq_pair.mp heq).1
    have hc := Finset.card_image_of_injective (outN D V v) hinj
    rw [← hc]
    apply Finset.card_le_card
    intro w hw
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
    refine mem_outN.mpr ⟨hmem z 0 (outN_subset hz) (by omega), ?_⟩
    change D (p (Nat.pair v 0)) (p (Nat.pair z 0)) = true
    rw [hp0, hp0]
    exact (mem_outN.mp hz).2
  · rintro ⟨v, hv, hlow⟩
    refine ⟨Nat.pair v 1, hmem v 1 hv (by dsimp only [gap]; omega),
      Nat.pair (f v) 0, hmem (f v) 0 (hfspec v hv).1 (by omega), ?_, ?_⟩
    · intro heq
      have := (Nat.pair_eq_pair.mp heq).2
      omega
    · intro z
      change D (p (Nat.pair v 1)) (p z) = D (p (Nat.pair (f v) 0)) (p z)
      rw [hpi _ _ (by decide), hp0]
  -- Count all labels projecting to marked rows, including any forced extra copy.
  · intro H r hHV hhigh
    let J := U.filter (fun x => p x ∈ H)
    let A := H.image (fun v => Nat.pair v 0)
    have hAc : A.card = H.card := by
      apply Finset.card_image_of_injective
      intro v w heq
      exact (Nat.pair_eq_pair.mp heq).1
    have hAJ : A ⊆ J := by
      intro x hx
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_filter.mpr ⟨hmem v 0 (hHV hv) (by omega), by rwa [hp0]⟩
    have hrow : ∀ x ∈ U, (outN D V (p x)).card ≤ (outN F U x).card := by
      intro x hx
      have hinj : Function.Injective (fun w => Nat.pair w 0) :=
        fun _ _ heq => (Nat.pair_eq_pair.mp heq).1
      rw [← Finset.card_image_of_injective (outN D V (p x)) hinj]
      apply Finset.card_le_card
      intro w hw
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
      refine mem_outN.mpr ⟨hmem z 0 (outN_subset hz) (by omega), ?_⟩
      change D (p x) (p (Nat.pair z 0)) = true
      rw [hp0]
      exact (mem_outN.mp hz).2
    refine ⟨J, Finset.filter_subset _ _, by rw [← hAc]; exact Finset.card_le_card hAJ, ?_, ?_⟩
    · intro x hx
      exact (hhigh (p x) (Finset.mem_filter.mp hx).2).trans
        (hrow x (Finset.mem_filter.mp hx).1)
    · rintro ⟨v, hv, hlow, hheads⟩
      have hcJ : Nat.pair v 1 ∈ J := by
        refine Finset.mem_filter.mpr ⟨hmem v 1 hv (by dsimp only [gap]; omega), ?_⟩
        rw [hpi _ _ (by decide)]
        exact hheads (mem_outN.mpr (hfspec v hv))
      have hcA : Nat.pair v 1 ∉ A := by
        intro hc
        obtain ⟨w, _, heq⟩ := Finset.mem_image.mp hc
        have hh := (Nat.pair_eq_pair.mp heq).2
        omega
      have hh := Finset.card_le_card (Finset.insert_subset hcJ hAJ)
      rw [Finset.card_insert_of_notMem hcA, hAc] at hh
      exact hh

/-- The previous row-and-twin interface, retained for its existing callers. -/
theorem exists_deficiency_completion_rows {D : CH.Digraph} {V : Finset ℕ} {q d : ℕ}
    (hf : QFree D V q) (hmin : ∀ v ∈ V, 1 ≤ (outN D V v).card) :
    ∃ (F : CH.Digraph) (U : Finset ℕ), QFree F U q ∧
      (∀ v ∈ U, d ≤ (outN F U v).card) ∧
      U.card = V.card + ∑ v ∈ V, (d - (outN D V v).card) ∧
      (V.Nonempty → U.Nonempty) ∧
      (∀ v ∈ V, ∃ w ∈ U, (outN D V v).card ≤ (outN F U w).card) ∧
      ((∃ v ∈ V, (outN D V v).card < d) →
        ∃ a ∈ U, ∃ b ∈ U, a ≠ b ∧ ∀ z, F a z = F b z) := by
  obtain ⟨F, U, hF, hm, hc, hn, hr, ht, _⟩ := exists_deficiency_completion_marked (d := d) hf hmin
  exact ⟨F, U, hF, hm, hc, hn, hr, ht⟩

/-- The original scalar interface, retained for the existing size-bound applications. -/
theorem exists_deficiency_completion {D : CH.Digraph} {V : Finset ℕ} {q d : ℕ}
    (hf : QFree D V q) (hmin : ∀ v ∈ V, 1 ≤ (outN D V v).card) :
    ∃ (F : CH.Digraph) (U : Finset ℕ), QFree F U q ∧
      (∀ v ∈ U, d ≤ (outN F U v).card) ∧
      U.card = V.card + ∑ v ∈ V, (d - (outN D V v).card) ∧
      (V.Nonempty → U.Nonempty) := by
  obtain ⟨F, U, hF, hminF, hc, hne, _, _⟩ := exists_deficiency_completion_rows (d := d) hf hmin
  exact ⟨F, U, hF, hminF, hc, hne⟩

/-- Any proved order bound at minimum degree d transfers to a deficiency bound. -/
theorem deficiency_bound_of_size {q d n : ℕ}
    (hsize : ∀ (F : CH.Digraph) (U : Finset ℕ), QFree F U q →
      (∀ v ∈ U, d ≤ (outN F U v).card) → U.Nonempty → n ≤ U.card)
    {D : CH.Digraph} {V : Finset ℕ} (hf : QFree D V q)
    (hmin : ∀ v ∈ V, 1 ≤ (outN D V v).card) (hne : V.Nonempty) :
    n ≤ V.card + ∑ v ∈ V, (d - (outN D V v).card) := by
  obtain ⟨F, U, hF, hminF, hc, hneF⟩ := exists_deficiency_completion (d := d) hf hmin
  have hh := hsize F U hF hminF (hneF hne)
  rwa [hc] at hh

/-- The uniform degree-two deficiency inequality, with no unproved input. -/
theorem degree_two_deficiency {D : CH.Digraph} {V : Finset ℕ} {q : ℕ}
    (hq : 1 ≤ q) (hf : QFree D V q)
    (hmin : ∀ v ∈ V, 1 ≤ (outN D V v).card) (hne : V.Nonempty) :
    2 * q + 1 ≤ V.card + ∑ v ∈ V, (2 - (outN D V v).card) :=
  deficiency_bound_of_size (fun _ _ hf hmin hne => corB hq hf hmin hne) hf hmin hne

/-- All previously proved ball theorems also give their degree-deficiency bounds. -/
theorem deficiency_bound_of_ball {D : CH.Digraph} {V : Finset ℕ} {q d : ℕ}
    (hq : 1 ≤ q) (hb : Ball q d) (hf : QFree D V q)
    (hmin : ∀ v ∈ V, 1 ≤ (outN D V v).card) (hne : V.Nonempty) :
    q * d + 1 ≤ V.card + ∑ v ∈ V, (d - (outN D V v).card) :=
  deficiency_bound_of_size (fun _ _ hf hmin hne => dt_size hq hb hf hmin hne) hf hmin hne

/-- In a punctured prefix, only its last layer can lose heads to the next layer.
Any proved minimum-degree size bound therefore gives this local deficiency budget. -/
theorem prefix_deficiency_of_size {q d n s k u : ℕ}
    (hsize : ∀ (F : CH.Digraph) (U : Finset ℕ), QFree F U q →
      (∀ v ∈ U, d ≤ (outN F U v).card) → U.Nonempty → n ≤ U.card)
    {D : CH.Digraph} {V : Finset ℕ} (hf : QFree D V q) (hu : u ∈ V)
    (hk : k + 2 ≤ q) (hmin : ∀ v ∈ V, s ≤ (outN D V v).card) (hds : d ≤ s)
    (hnext : (ball D V u (k + 2) \ ball D V u (k + 1)).card < s) :
    n ≤ (ball D V u (k + 1)).card - 1 +
      (ball D V u (k + 1) \ ball D V u k).card *
        (d + (ball D V u (k + 2) \ ball D V u (k + 1)).card - s) := by
  classical
  let U := (ball D V u (k + 1)).erase u
  let S := ball D V u (k + 1) \ ball D V u k
  let T := ball D V u (k + 2) \ ball D V u (k + 1)
  let loss := d + T.card - s
  have hUV : U ⊆ V := (Finset.erase_subset _ _).trans ball_subset
  have hSU : S ⊆ U := by
    intro v hv
    refine Finset.mem_erase.mpr ⟨?_, (Finset.mem_sdiff.mp hv).1⟩
    intro heq
    subst v
    exact (Finset.mem_sdiff.mp hv).2 (self_mem_ball hu)
  have hminU : ∀ v ∈ U, 1 ≤ (outN D U v).card :=
    minOut_prefix_erase hf hu (by omega : (k + 1) + 1 ≤ q) hmin (by
      change 1 + (ball D V u (k + 2) \ ball D V u (k + 1)).card ≤ s
      omega)
  have hne : U.Nonempty := by
    obtain ⟨x, hx⟩ := Finset.card_pos.mp (by have := hmin u hu; omega : 0 < (outN D V u).card)
    refine ⟨x, Finset.mem_erase.mpr ⟨?_, ?_⟩⟩
    · intro heq
      exact loopfree hf (by omega) hu (heq ▸ (mem_outN.mp hx).2)
    · exact ball_mono_radius (by omega : 1 ≤ k + 1) ((mem_ball_one hu).mpr (Or.inr hx))
  have hlow : ∀ v ∈ S, d - (outN D U v).card ≤ loss := by
    intro v hv
    have hc := (Finset.card_le_card (outN_prefix_loss hf hu
      (by omega : (k + 1) + 1 ≤ q) (hSU hv))).trans (Finset.card_union_le _ _)
    have hh := hmin v (hUV (hSU hv))
    change (outN D V v).card ≤ (outN D U v).card + T.card at hc
    dsimp only [loss]
    omega
  have hzero : ∀ v ∈ U \ S, d - (outN D U v).card = 0 := by
    intro v hv
    obtain ⟨hvU, hvS⟩ := Finset.mem_sdiff.mp hv
    have hvk : v ∈ ball D V u k := by
      by_contra hn
      exact hvS (Finset.mem_sdiff.mpr ⟨Finset.mem_of_mem_erase hvU, hn⟩)
    have hh := (hmin v (hUV hvU)).trans
      (Finset.card_le_card (outN_prefix_erase_root hf hu (by omega : k + 1 ≤ q) hvk))
    change s ≤ (outN D U v).card at hh
    omega
  have hsum := Finset.sum_le_sum hlow
  rw [Finset.sum_const_nat (fun _ _ => rfl)] at hsum
  have hz := Finset.sum_eq_zero hzero
  have he := Finset.sum_sdiff hSU (f := fun v => d - (outN D U v).card)
  have hbound := deficiency_bound_of_size hsize (hf.mono_set hUV) hminU hne
  have hUc : U.card = (ball D V u (k + 1)).card - 1 :=
    Finset.card_erase_of_mem (self_mem_ball hu)
  change n ≤ (ball D V u (k + 1)).card - 1 + S.card * loss
  omega

theorem prefix_deficiency_of_ball {D : CH.Digraph} {V : Finset ℕ} {q d s k u : ℕ}
    (hq : 1 ≤ q) (hb : Ball q d) (hf : QFree D V q) (hu : u ∈ V)
    (hk : k + 2 ≤ q) (hmin : ∀ v ∈ V, s ≤ (outN D V v).card) (hds : d ≤ s)
    (hnext : (ball D V u (k + 2) \ ball D V u (k + 1)).card < s) :
    q * d + 1 ≤ (ball D V u (k + 1)).card - 1 +
      (ball D V u (k + 1) \ ball D V u k).card *
        (d + (ball D V u (k + 2) \ ball D V u (k + 1)).card - s) :=
  prefix_deficiency_of_size (fun _ _ hf hmin hne => dt_size hq hb hf hmin hne)
    hf hu hk hmin hds hnext

end LeanCH.BR.BRsGen
