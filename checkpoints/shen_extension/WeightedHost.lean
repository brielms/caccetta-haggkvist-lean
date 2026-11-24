import LeanCH.BR.BRDeficiencyCompletion

/-!
# Weighted hosts

Any blow-up of a q-free digraph is q-free.  So for a q-free digraph on W and integer
weights μ, if every vertex of positive weight has weighted out-degree at least s, the
total weight is at least the order of the smallest q-free host of minimum out-degree s.

The deficiency completion used so far is the special case in which each deficient row
gets its own private clones.  Here clones may be shared: one hub can serve every row
that points to it.  No radius, cutoff or degree guard appears anywhere.
-/
namespace LeanCH.BR.WeightedHost
open BRq2 BRq3 BR45 BRsGen
open Classical

/-- The blow-up of a q-free digraph by integer multiplicities. -/
theorem exists_blowup {D : CH.Digraph} {W : Finset ℕ} {q : ℕ} (μ : ℕ → ℕ)
    (hf : QFree D W q) :
    ∃ (F : CH.Digraph) (U : Finset ℕ), QFree F U q ∧
      U.card = ∑ v ∈ W, μ v ∧
      (∀ x ∈ U, ∃ v ∈ W, 0 < μ v ∧ (outN F U x).card = ∑ w ∈ outN D W v, μ w) := by
  let S : Finset (Σ _ : ℕ, ℕ) := W.sigma (fun v => Finset.range (μ v))
  let enc : (Σ _ : ℕ, ℕ) → ℕ := fun p => Nat.pair p.1 p.2
  let U := S.image enc
  let p : ℕ → ℕ := fun x => (Nat.unpair x).1
  let F : CH.Digraph := fun x y => D (p x) (p y)
  have henc : Function.Injective enc := by
    rintro ⟨v, i⟩ ⟨w, j⟩ heq
    have hh := Nat.pair_eq_pair.mp heq
    rcases hh with ⟨rfl, rfl⟩
    rfl
  have hp (v i : ℕ) : p (Nat.pair v i) = v := by simp [p]
  have hmem (v i : ℕ) (hv : v ∈ W) (hi : i < μ v) : Nat.pair v i ∈ U :=
    Finset.mem_image.mpr ⟨⟨v, i⟩, Finset.mem_sigma.mpr ⟨hv, Finset.mem_range.mpr hi⟩, rfl⟩
  have hU : ∀ x ∈ U, ∃ v i, v ∈ W ∧ i < μ v ∧ x = Nat.pair v i := by
    intro x hx
    obtain ⟨⟨v, i⟩, hvi, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hv, hi⟩ := Finset.mem_sigma.mp hvi
    exact ⟨v, i, hv, Finset.mem_range.mp hi, rfl⟩
  have hpW : ∀ x ∈ U, p x ∈ W := by
    intro x hx
    obtain ⟨v, i, hv, _, rfl⟩ := hU x hx
    rw [hp]
    exact hv
  have hwalk : ∀ {a b m}, Walk F U a b m → Walk D W (p a) (p b) m := by
    intro a b m w
    induction w with
    | refl a => exact .refl (p a)
    | step hb hab _ ih => exact .step (hpW _ hb) hab ih
  refine ⟨F, U, fun a m hm hmq w => hf (p a) m hm hmq (hwalk w), ?_, ?_⟩
  · change (S.image enc).card = _
    rw [Finset.card_image_of_injective _ henc]
    change (W.sigma (fun v => Finset.range (μ v))).card = _
    rw [Finset.card_sigma]
    simp only [Finset.card_range]
  · intro x hx
    obtain ⟨v, i, hv, hi, rfl⟩ := hU x hx
    refine ⟨v, hv, by omega, ?_⟩
    have hrow : outN F U (Nat.pair v i) =
        ((outN D W v).sigma (fun w => Finset.range (μ w))).image enc := by
      ext y
      constructor
      · intro hy
        obtain ⟨hyU, hvy⟩ := mem_outN.mp hy
        obtain ⟨w, j, hw, hj, rfl⟩ := hU y hyU
        change D (p (Nat.pair v i)) (p (Nat.pair w j)) = true at hvy
        rw [hp, hp] at hvy
        exact Finset.mem_image.mpr ⟨⟨w, j⟩, Finset.mem_sigma.mpr
          ⟨mem_outN.mpr ⟨hw, hvy⟩, Finset.mem_range.mpr hj⟩, rfl⟩
      · intro hy
        obtain ⟨⟨w, j⟩, hwj, rfl⟩ := Finset.mem_image.mp hy
        obtain ⟨hw, hj⟩ := Finset.mem_sigma.mp hwj
        obtain ⟨hwW, hvw⟩ := mem_outN.mp hw
        refine mem_outN.mpr ⟨hmem w j hwW (Finset.mem_range.mp hj), ?_⟩
        change D (p (Nat.pair v i)) (p (Nat.pair w j)) = true
        rw [hp, hp]
        exact hvw
    rw [hrow, Finset.card_image_of_injective _ henc, Finset.card_sigma]
    simp only [Finset.card_range]

/-- Weighted host bound: total weight is at least the least host order. -/
theorem weighted_bound {q s L : ℕ}
    (order : ∀ (F : CH.Digraph) (U : Finset ℕ), QFree F U q →
      (∀ v ∈ U, s ≤ (outN F U v).card) → U.Nonempty → L ≤ U.card)
    {D : CH.Digraph} {W : Finset ℕ} (μ : ℕ → ℕ) (hf : QFree D W q)
    (hpos : ∃ v ∈ W, 0 < μ v)
    (hdeg : ∀ v ∈ W, 0 < μ v → s ≤ ∑ w ∈ outN D W v, μ w) :
    L ≤ ∑ v ∈ W, μ v := by
  obtain ⟨F, U, hF, hc, hrow⟩ := exists_blowup μ hf
  have hne : U.Nonempty := by
    obtain ⟨v, hv, hμ⟩ := hpos
    have hle := Finset.single_le_sum (f := μ) (fun _ _ => Nat.zero_le _) hv
    exact Finset.card_pos.mp (by omega)
  have hmin : ∀ x ∈ U, s ≤ (outN F U x).card := by
    intro x hx
    obtain ⟨v, hv, hμ, he⟩ := hrow x hx
    rw [he]
    exact hdeg v hv hμ
  have h := order F U hF hmin hne
  omega

/-- Cover form: keep every vertex once and add x(w) clones of w. -/
theorem cover_bound {q s L : ℕ}
    (order : ∀ (F : CH.Digraph) (U : Finset ℕ), QFree F U q →
      (∀ v ∈ U, s ≤ (outN F U v).card) → U.Nonempty → L ≤ U.card)
    {D : CH.Digraph} {W : Finset ℕ} (x : ℕ → ℕ) (hf : QFree D W q) (hne : W.Nonempty)
    (hcover : ∀ v ∈ W, s ≤ (outN D W v).card + ∑ w ∈ outN D W v, x w) :
    L ≤ W.card + ∑ v ∈ W, x v := by
  have h := weighted_bound order (fun v => 1 + x v) hf
    (by obtain ⟨v, hv⟩ := hne; exact ⟨v, hv, by omega⟩)
    (by
      intro v hv _
      rw [Finset.sum_add_distrib, Finset.sum_const_nat (fun _ _ => rfl), Nat.mul_one]
      exact hcover v hv)
  rw [Finset.sum_add_distrib, Finset.sum_const_nat (fun _ _ => rfl), Nat.mul_one] at h
  exact h

/-- Shared clones: choose one retained out-neighbour f(z) for every vertex.  A hub pays
only for the largest shortage among the vertices that chose it, not for their sum. -/
theorem sup_cover_bound {q s L : ℕ}
    (order : ∀ (F : CH.Digraph) (U : Finset ℕ), QFree F U q →
      (∀ v ∈ U, s ≤ (outN F U v).card) → U.Nonempty → L ≤ U.card)
    {D : CH.Digraph} {W : Finset ℕ} (f : ℕ → ℕ) (hf : QFree D W q) (hne : W.Nonempty)
    (hchoice : ∀ z ∈ W, f z ∈ outN D W z) :
    L ≤ W.card + ∑ v ∈ W,
      (W.filter (fun z => f z = v)).sup (fun z => s - (outN D W z).card) := by
  apply cover_bound order
    (fun v => (W.filter (fun z => f z = v)).sup (fun z => s - (outN D W z).card)) hf hne
  intro z hz
  have hsup : s - (outN D W z).card ≤
      (W.filter (fun y => f y = f z)).sup (fun y => s - (outN D W y).card) :=
    Finset.le_sup (f := fun y => s - (outN D W y).card)
      (Finset.mem_filter.mpr ⟨hz, rfl⟩)
  have hsingle := Finset.single_le_sum
    (f := fun v => (W.filter (fun y => f y = v)).sup (fun y => s - (outN D W y).card))
    (fun _ _ => Nat.zero_le _) (hchoice z hz)
  omega

#print axioms exists_blowup
#print axioms weighted_bound
#print axioms cover_bound
#print axioms sup_cover_bound
end LeanCH.BR.WeightedHost
