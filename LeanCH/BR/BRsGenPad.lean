import LeanCH.BR.BRsGenDiam

/-!
# Route 1 for general out-degree `s`: padding with `r` fresh vertices and the exit lemma (Lean 4.35.0)

Paper: `checkpoints/boundary_20261111/Route1_GeneralS_subagent.md`, §1 (Lemma 3_s, Lemma 4_{s,r}); the `s = 3`,
`r = 1` case is `BRq3Pad.lean`. No existing file is changed.

`G` is `k`-free with out-degree `s` on `W`, `z ∈ W`, `B = B_k(z)`, and `X` is any finite set of fresh vertices
(`X ∩ W = ∅`, `|X| = r`). `exitN G W B z y` is the set of out-neighbours of `y` that equal `z` or leave `B`, so its size is
the paper's `t(y) + [y → z]`. The paper's hypothesis is

  (†_r)  `|exitN y| ≤ r + 1` for every `y ∈ B`.

The padded digraph `padS G B X z sel` lives on `B ∪ X`:
* every `x ∈ X` copies `O(z)` (the paper's `x → z, a₁, …, a_{s-1}` is replaced by `x → O(z)`; both drop from depth
  `k+1` to `≤ 1`);
* `a ∈ B` keeps its arcs inside `B` and adds arcs to `sel a ⊆ ({z} ∪ X) ∖ O(a)`, with `|sel a| = s - |O(a) ∩ B|`.
  `(†_r)` is exactly what makes such a `sel a` exist (`exists_sel`).

* `pad_walk_s` (the potential): a padded walk of length `m` from level `i` ends at level `i + m`; `X` sits at level `k+1`.
* `pad_outEq_s`, `pad_qfree_s`, `pad_ball_s` (**Lemma 3_s**, all `r`): out-`s`, `k`-free, and `B^H_k(z) = B`.
* `exists_pad_s`: Lemma 3_s packaged for `r` fresh vertices (covers `r = 0, 1, 2, …`).
* `exit_lemma_s` (**Lemma 4_{s,r}**): with `Ball(k,s)`, `r ≥ 1` and `|B_k(z)| ≤ sk+1-r`, some `y ∈ B_k(z)` has
  `|exitN y| ≥ r + 2`.
-/

set_option linter.style.longLine false

namespace LeanCH.BR.BRsGen

open LeanCH.BR.BRq2 LeanCH.BR.BRq3

variable {G : CH.Digraph} {W : Finset ℕ}

/-- The out-neighbours of `y` that equal `z` or leave `B` (size `t(y) + [y → z]`). -/
def exitN (G : CH.Digraph) (W B : Finset ℕ) (z y : ℕ) : Finset ℕ :=
  (outN G W y).filter (fun b => b = z ∨ b ∉ B)

/-- The padded digraph of Lemma 3_s on `B ∪ X`. -/
def padS (G : CH.Digraph) (B X : Finset ℕ) (z : ℕ) (sel : ℕ → Finset ℕ) : CH.Digraph :=
  fun a b => if a ∈ X then decide (b ∈ outN G B z) else
    (G a b && decide (b ∈ B)) || (decide (a ∈ B) && decide (b ∈ sel a))

/-- The redirect sets: `sel a ⊆ ({z} ∪ X) ∖ O(a)` with `|sel a| + |O(a) ∩ B| = s`. -/
def SelOK (G : CH.Digraph) (B X : Finset ℕ) (z s : ℕ) (sel : ℕ → Finset ℕ) : Prop :=
  ∀ a ∈ B, sel a ⊆ insert z X ∧ Disjoint (sel a) (outN G B a) ∧ (sel a).card + (outN G B a).card = s

theorem walk_uncons_s {D : CH.Digraph} {U : Finset ℕ} {a c m : ℕ} (w : Walk D U a c (m + 1)) :
    ∃ b, b ∈ U ∧ D a b = true ∧ Walk D U b c m := by
  cases w with
  | step hb hab w' => exact ⟨_, hb, hab, w'⟩

/-- A walk either avoids `X` (after its start), or passes through some `x ∈ X`. -/
theorem walk_visit {D : CH.Digraph} {U X : Finset ℕ} {a c m : ℕ} (w : Walk D U a c m) :
    Walk D (U \ X) a c m ∨ ∃ x ∈ X, ∃ m1 m2, m1 + m2 = m ∧ Walk D U a x m1 ∧ Walk D U x c m2 := by
  induction w with
  | refl a => exact Or.inl (.refl a)
  | @step a b c k hb hab w ih =>
    by_cases hbX : b ∈ X
    · exact Or.inr ⟨b, hbX, 1, k, by omega, .step hb hab (.refl b), w⟩
    · rcases ih with h | ⟨x, hx, m1, m2, hs, w1, w2⟩
      · exact Or.inl (.step (Finset.mem_sdiff.mpr ⟨hb, hbX⟩) hab h)
      · exact Or.inr ⟨x, hx, m1 + 1, m2, by omega, .step hb hab w1, w2⟩

theorem outN_mono_set_s {B : Finset ℕ} (hB : B ⊆ W) (a : ℕ) : outN G B a ⊆ outN G W a :=
  fun _ hc => mem_outN.mpr ⟨hB (mem_outN.mp hc).1, (mem_outN.mp hc).2⟩

/-- A vertex of `B_i(z)`, `i + 1 ≤ k`, keeps all its arcs inside `B_k(z)`. -/
theorem outN_inner {z i k a : ℕ} (ha : a ∈ ball G W z i) (hik : i + 1 ≤ k) :
    outN G (ball G W z k) a = outN G W a := by
  ext c
  rw [mem_outN, mem_outN]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨ball_subset h1, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨ball_mono_radius hik (ball_step ha h1 h2), h2⟩

/-- `|exitN a| + |O(a) ∩ B| = s + [a → z]`. -/
theorem exitN_card {s z a : ℕ} {B : Finset ℕ} (hout : OutEq s G W) (ha : a ∈ W) (hBW : B ⊆ W) (hzB : z ∈ B) :
    (exitN G W B z a).card + (outN G B a).card = s + (if G a z = true then 1 else 0) := by
  classical
  have e1 : (outN G W a).filter (fun b => b ∈ B) = outN G B a := by
    ext b
    simp only [Finset.mem_filter, mem_outN]
    constructor
    · rintro ⟨⟨_, h⟩, hb⟩; exact ⟨hb, h⟩
    · rintro ⟨hb, h⟩; exact ⟨⟨hBW hb, h⟩, hb⟩
  have e2 := Finset.card_filter_add_card_filter_not (s := outN G W a) (fun b => b ∈ B)
  rw [e1, hout a ha] at e2
  have e3 : exitN G W B z a =
      (outN G W a).filter (fun b => b = z) ∪ (outN G W a).filter (fun b => b ∉ B) := by
    unfold exitN
    rw [Finset.filter_or]
  have hdisj : Disjoint ((outN G W a).filter (fun b => b = z)) ((outN G W a).filter (fun b => b ∉ B)) := by
    rw [Finset.disjoint_filter]
    rintro b _ rfl h
    exact h hzB
  rw [e3, Finset.card_union_of_disjoint hdisj, Finset.filter_eq']
  by_cases h : G a z = true
  · have hz : z ∈ outN G W a := mem_outN.mpr ⟨hBW hzB, h⟩
    rw [if_pos hz, if_pos h, Finset.card_singleton]
    omega
  · have hz : z ∉ outN G W a := fun h' => h (mem_outN.mp h').2
    rw [if_neg hz, if_neg h, Finset.card_empty]
    omega

/-- `(†_r)` gives the redirect sets. -/
theorem exists_sel {s z : ℕ} {B X : Finset ℕ} (hout : OutEq s G W) (hBW : B ⊆ W) (hzB : z ∈ B)
    (hXW : ∀ x ∈ X, x ∉ W) (hdag : ∀ y ∈ B, (exitN G W B z y).card ≤ X.card + 1) :
    ∃ sel : ℕ → Finset ℕ, SelOK G B X z s sel := by
  classical
  have hex : ∀ a, ∃ t ⊆ insert z X \ outN G B a,
      t.card = min (s - (outN G B a).card) (insert z X \ outN G B a).card :=
    fun a => Finset.exists_subset_card_eq (min_le_right _ _)
  choose sel hsel hcard using hex
  refine ⟨sel, fun a ha => ⟨fun b hb => (Finset.mem_sdiff.mp (hsel a hb)).1, ?_, ?_⟩⟩
  · rw [Finset.disjoint_left]
    intro b hb hb'
    exact (Finset.mem_sdiff.mp (hsel a hb)).2 hb'
  · have hc := exitN_card hout (hBW ha) hBW hzB (a := a) (z := z)
    have hd := hdag a ha
    have hle : (outN G B a).card ≤ s := by
      have := Finset.card_le_card (outN_mono_set_s (G := G) hBW a)
      rwa [hout a (hBW ha)] at this
    have hzX : z ∉ X := fun h' => hXW z h' (hBW hzB)
    rw [hcard a]
    by_cases h : G a z = true
    · rw [if_pos h] at hc
      have hsub : X ⊆ insert z X \ outN G B a := fun x hx =>
        Finset.mem_sdiff.mpr ⟨Finset.mem_insert_of_mem hx, fun h' => hXW x hx (hBW (mem_outN.mp h').1)⟩
      have := Finset.card_le_card hsub
      omega
    · rw [if_neg h] at hc
      have hsub : insert z X ⊆ insert z X \ outN G B a := by
        intro x hx
        refine Finset.mem_sdiff.mpr ⟨hx, fun h' => ?_⟩
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact h (mem_outN.mp h').2
        · exact hXW x hx (hBW (mem_outN.mp h').1)
      have := Finset.card_le_card hsub
      rw [Finset.card_insert_of_notMem hzX] at this
      omega

section Pad

variable {s k z : ℕ} {X : Finset ℕ} {sel : ℕ → Finset ℕ}

/-- A vertex of `B_i(z)`, `i + 1 ≤ k`, has no redirected arc. -/
theorem sel_empty (hout : OutEq s G W) (hsel : SelOK G (ball G W z k) X z s sel) {a i : ℕ}
    (ha : a ∈ ball G W z i) (hik : i + 1 ≤ k) (b : ℕ) : b ∉ sel a := by
  intro hb
  have haB : a ∈ ball G W z k := ball_mono_radius (by omega) ha
  have h1 := (hsel a haB).2.2
  rw [outN_inner ha hik, hout a (ball_subset ha)] at h1
  have : (sel a).card = 0 := by omega
  rw [Finset.card_eq_zero] at this
  rw [this] at hb
  exact Finset.notMem_empty b hb

/-- One padded arc raises the level by at most one. -/
theorem pad_step_s (hz : z ∈ W) (hout : OutEq s G W) (hsel : SelOK G (ball G W z k) X z s sel) {a b i : ℕ}
    (ha : a ∈ ball G W z i ∨ (a ∈ X ∧ k + 1 ≤ i)) (hab : padS G (ball G W z k) X z sel a b = true) :
    b ∈ ball G W z (i + 1) ∨ (b ∈ X ∧ k + 1 ≤ i + 1) := by
  by_cases haX : a ∈ X
  · have hb : b ∈ outN G (ball G W z k) z := by simpa [padS, haX] using hab
    obtain ⟨hbB, hzb⟩ := mem_outN.mp hb
    exact Or.inl (ball_mono_radius (by omega) (ball_of_adj (ball_subset hbB) hzb))
  · have ha' : a ∈ ball G W z i := ha.resolve_right (fun h => haX h.1)
    simp only [padS, haX, ite_false, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hab
    rcases hab with ⟨hG, hbB⟩ | ⟨haB, hbs⟩
    · exact Or.inl (ball_step ha' (ball_subset hbB) hG)
    · rcases Finset.mem_insert.mp ((hsel a haB).1 hbs) with rfl | hbX
      · exact Or.inl (self_mem_ball hz)
      · refine Or.inr ⟨hbX, ?_⟩
        by_contra hi
        exact sel_empty hout hsel ha' (by omega) b hbs

/-- **The potential.** A padded walk of length `m` from level `i` ends at level `i + m`. -/
theorem pad_walk_s (hz : z ∈ W) (hout : OutEq s G W) (hsel : SelOK G (ball G W z k) X z s sel)
    {U : Finset ℕ} {a c m : ℕ} (w : Walk (padS G (ball G W z k) X z sel) U a c m) :
    ∀ i, (a ∈ ball G W z i ∨ (a ∈ X ∧ k + 1 ≤ i)) → (c ∈ ball G W z (i + m) ∨ (c ∈ X ∧ k + 1 ≤ i + m)) := by
  induction w with
  | refl a => intro i h; simpa using h
  | @step a b c m _ hab _ ih =>
    intro i h
    have := ih (i + 1) (pad_step_s hz hout hsel h hab)
    rwa [show i + 1 + m = i + (m + 1) by omega] at this

/-- A padded walk through vertices of `B ∖ ({z} ∪ X)`, not starting in `X`, is a `G`-walk. -/
theorem pad_toG_s (hsel : SelOK G (ball G W z k) X z s sel) {U : Finset ℕ}
    (hU : ∀ b ∈ U, b ∈ ball G W z k ∧ b ≠ z ∧ b ∉ X) {a c m : ℕ}
    (w : Walk (padS G (ball G W z k) X z sel) U a c m) : a ∉ X → Walk G W a c m := by
  induction w with
  | refl a => intro _; exact .refl a
  | @step a b c m hb hab _ ih =>
    intro haX
    obtain ⟨hbB, hbz, hbX⟩ := hU b hb
    refine .step (ball_subset hbB) ?_ (ih hbX)
    simp only [padS, haX, ite_false, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hab
    rcases hab with ⟨hG, _⟩ | ⟨haB, hbs⟩
    · exact hG
    · rcases Finset.mem_insert.mp ((hsel a haB).1 hbs) with h | h
      · exact absurd h hbz
      · exact absurd h hbX

/-- **Lemma 3_s, out-degree.** -/
theorem pad_outEq_s (hk : 1 ≤ k) (hout : OutEq s G W) (hz : z ∈ W)
    (hsel : SelOK G (ball G W z k) X z s sel) :
    OutEq s (padS G (ball G W z k) X z sel) (ball G W z k ∪ X) := by
  classical
  have hzB : z ∈ ball G W z k := self_mem_ball hz
  intro a ha
  by_cases haX : a ∈ X
  · have e : outN (padS G (ball G W z k) X z sel) (ball G W z k ∪ X) a = outN G (ball G W z k) z := by
      ext b
      rw [mem_outN]
      simp only [padS, haX, ite_true, decide_eq_true_eq]
      exact ⟨fun h => h.2, fun h => ⟨Finset.mem_union_left _ (mem_outN.mp h).1, h⟩⟩
    rw [e, outN_inner (self_mem_ball (D := G) (k := 0) hz) hk, hout z hz]
  · have haB : a ∈ ball G W z k := by
      rcases Finset.mem_union.mp ha with h | h
      · exact h
      · exact absurd h haX
    have e : outN (padS G (ball G W z k) X z sel) (ball G W z k ∪ X) a =
        outN G (ball G W z k) a ∪ sel a := by
      ext b
      rw [mem_outN, Finset.mem_union, Finset.mem_union, mem_outN]
      simp only [padS, haX, haB, ite_false, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, true_and]
      constructor
      · rintro ⟨_, ⟨hG, hbB⟩ | hbs⟩
        · exact Or.inl ⟨hbB, hG⟩
        · exact Or.inr hbs
      · rintro (⟨hbB, hG⟩ | hbs)
        · exact ⟨Or.inl hbB, Or.inl ⟨hG, hbB⟩⟩
        · refine ⟨?_, Or.inr hbs⟩
          rcases Finset.mem_insert.mp ((hsel a haB).1 hbs) with rfl | h
          · exact Or.inl hzB
          · exact Or.inr h
    rw [e, Finset.card_union_of_disjoint (hsel a haB).2.1.symm]
    have := (hsel a haB).2.2
    omega

/-- **Lemma 3_s, `k`-freeness.** -/
theorem pad_qfree_s (hfree : QFree G W k) (hout : OutEq s G W) (hz : z ∈ W) (hXW : ∀ x ∈ X, x ∉ W)
    (hsel : SelOK G (ball G W z k) X z s sel) :
    QFree (padS G (ball G W z k) X z sel) (ball G W z k ∪ X) k := by
  intro a ℓ h1 hℓ w
  have hzX : z ∉ X := fun h => hXW z h hz
  rcases walk_visit (X := X) w with h | ⟨x, hx, m1, m2, hs, w1, w2⟩
  · -- the closed walk avoids `X`
    have hUB : ∀ b ∈ (ball G W z k ∪ X) \ X, b ∈ ball G W z k ∧ b ∉ X := by
      intro b hb
      obtain ⟨hb1, hb2⟩ := Finset.mem_sdiff.mp hb
      rcases Finset.mem_union.mp hb1 with h' | h'
      · exact ⟨h', hb2⟩
      · exact absurd h' hb2
    have hUz : ∀ b ∈ ((ball G W z k ∪ X) \ X).erase z, b ∈ ball G W z k ∧ b ≠ z ∧ b ∉ X := by
      intro b hb
      obtain ⟨hbz, hb'⟩ := Finset.mem_erase.mp hb
      exact ⟨(hUB b hb').1, hbz, (hUB b hb').2⟩
    rcases h.lastVisit z with h' | ⟨n1, n2, _, hsum', v1, v2⟩
    · -- it also avoids `z`: a closed `G`-walk
      obtain ⟨ℓ', rfl⟩ : ∃ ℓ', ℓ = ℓ' + 1 := ⟨ℓ - 1, by omega⟩
      obtain ⟨_, _, haE, _⟩ := h'.unsnoc
      exact hfree a (ℓ' + 1) h1 hℓ (pad_toG_s hsel hUz h' (hUz a haE).2.2)
    · -- rotate to a closed walk at `z`; its last arc `t → z` comes from `t ∈ B_{ℓ-1}(z)`
      have wz := (v2.mono (Finset.erase_subset _ _)).append v1
      obtain ⟨n, hn⟩ : ∃ n, n2 + n1 = n + 1 := ⟨n2 + n1 - 1, by omega⟩
      rw [hn] at wz
      obtain ⟨t, wt, _, htz⟩ := wz.unsnoc
      obtain ⟨m', hm', wt'⟩ := wt.fromStart
      have g := pad_toG_s hsel hUz wt' hzX
      have htW : t ∈ W := by
        rcases wt'.end_mem_or with e | e
        · rw [e]; exact hz
        · exact ball_subset (hUz t e).1
      have htb : t ∈ ball G W z m' := mem_ball_of_walk g le_rfl htW
      have htX : t ∉ X := fun e => hXW t e htW
      simp only [padS, htX, ite_false, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at htz
      rcases htz with ⟨hG, _⟩ | ⟨_, hzs⟩
      · exact hfree z (m' + 1) (by omega) (by omega) (g.snoc hz hG)
      · exact sel_empty hout hsel htb (by omega) z hzs
  · -- the closed walk visits `x ∈ X`: rotate to `x`, step to `O(z) ⊆ B_1(z)`, climb back to level `k + 1`
    have wx := w2.append w1
    obtain ⟨n, hn⟩ : ∃ n, m2 + m1 = n + 1 := ⟨m2 + m1 - 1, by omega⟩
    rw [hn] at wx
    obtain ⟨b, _, hxb, w'⟩ := walk_uncons_s wx
    have hb : b ∈ outN G (ball G W z k) z := by simpa [padS, hx] using hxb
    obtain ⟨hbB, hzb⟩ := mem_outN.mp hb
    rcases pad_walk_s hz hout hsel w' 1 (Or.inl (ball_of_adj (ball_subset hbB) hzb)) with h | ⟨_, h⟩
    · exact hXW x hx (ball_subset h)
    · omega

/-- `G`-walks of length `≤ k - i` from `B_i(z)` survive in the padded digraph. -/
theorem pad_lift (hXW : ∀ x ∈ X, x ∉ W) {a c m : ℕ} (w : Walk G W a c m) :
    ∀ i, a ∈ ball G W z i → i + m ≤ k → Walk (padS G (ball G W z k) X z sel) (ball G W z k ∪ X) a c m := by
  induction w with
  | refl a => intro _ _ _; exact .refl a
  | @step a b c m hb hab _ ih =>
    intro i ha him
    have hb' : b ∈ ball G W z (i + 1) := ball_step ha hb hab
    have hbB : b ∈ ball G W z k := ball_mono_radius (by omega) hb'
    have haX : a ∉ X := fun h => hXW a h (ball_subset ha)
    refine .step (Finset.mem_union_left _ hbB) ?_ (ih (i + 1) hb' (by omega))
    simp [padS, haX, hab, hbB]

/-- **Lemma 3_s, the ball.** `B^H_k(z) = B`. -/
theorem pad_ball_s (hout : OutEq s G W) (hz : z ∈ W) (hXW : ∀ x ∈ X, x ∉ W)
    (hsel : SelOK G (ball G W z k) X z s sel) :
    ball (padS G (ball G W z k) X z sel) (ball G W z k ∪ X) z k = ball G W z k := by
  ext v
  constructor
  · intro hv
    obtain ⟨_, m, hm, w⟩ := mem_ball.mp hv
    rcases pad_walk_s hz hout hsel w 0 (Or.inl (self_mem_ball hz)) with h | ⟨_, h⟩
    · exact ball_mono_radius (by omega) h
    · omega
  · intro hv
    obtain ⟨hvW, m, hm, w⟩ := mem_ball.mp hv
    exact mem_ball.mpr ⟨Finset.mem_union_left _ hv, m, hm,
      pad_lift hXW w 0 (self_mem_ball hz) (by omega)⟩

end Pad

/-- **Lemma 3_s (padding), packaged.** If `G` is `k`-free and out-`s`, `k ≥ 1`, `z ∈ W`, and `(†_r)` holds on
`B = B_k(z)` for a set `X` of fresh vertices, then some `H` on `B ∪ X` is out-`s`, `k`-free, has `B^H_k(z) = B`, keeps
every `G`-arc inside `B`, and adds only arcs into `{z} ∪ X` from `B`. -/
theorem exists_pad_s {s k z : ℕ} {X : Finset ℕ} (hk : 1 ≤ k) (hfree : QFree G W k) (hout : OutEq s G W)
    (hz : z ∈ W) (hXW : ∀ x ∈ X, x ∉ W)
    (hdag : ∀ y ∈ ball G W z k, (exitN G W (ball G W z k) z y).card ≤ X.card + 1) :
    ∃ H : CH.Digraph, OutEq s H (ball G W z k ∪ X) ∧ QFree H (ball G W z k ∪ X) k ∧
      ball H (ball G W z k ∪ X) z k = ball G W z k ∧
      (∀ a ∈ ball G W z k, ∀ b ∈ ball G W z k, G a b = true → H a b = true) ∧
      (∀ a ∈ ball G W z k, ∀ b, H a b = true → (G a b = true ∧ b ∈ ball G W z k) ∨ b = z ∨ b ∈ X) := by
  obtain ⟨sel, hsel⟩ := exists_sel hout ball_subset (self_mem_ball hz) hXW hdag
  refine ⟨padS G (ball G W z k) X z sel, pad_outEq_s hk hout hz hsel, pad_qfree_s hfree hout hz hXW hsel,
    pad_ball_s hout hz hXW hsel, ?_, ?_⟩
  · intro a ha b hb hab
    have haX : a ∉ X := fun h => hXW a h (ball_subset ha)
    simp [padS, haX, hab, hb]
  · intro a ha b hab
    have haX : a ∉ X := fun h => hXW a h (ball_subset ha)
    simp only [padS, haX, ite_false, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hab
    rcases hab with h | ⟨_, hbs⟩
    · exact Or.inl h
    · rcases Finset.mem_insert.mp ((hsel a ha).1 hbs) with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)

/-- `r` fresh vertices above `W`. -/
theorem exists_fresh (W : Finset ℕ) (r : ℕ) : ∃ X : Finset ℕ, X.card = r ∧ ∀ x ∈ X, x ∉ W := by
  refine ⟨(Finset.range r).map ⟨fun i => W.sup id + 1 + i, add_right_injective _⟩, by simp,
    fun x hx hxW => ?_⟩
  obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hx
  have h2 := Finset.le_sup (f := id) hxW
  simp only [id, Function.Embedding.coeFn_mk] at h2
  omega

/-- **Lemma 3_s with `r` fresh vertices** (`r = 0, 1, 2, …`): under `(†_r)` there is a `k`-free out-`s` host on
`|B_k(z)| + r` vertices whose radius-`k` ball at `z` is `B_k(z)`. -/
theorem exists_pad_r {s k z r : ℕ} (hk : 1 ≤ k) (hfree : QFree G W k) (hout : OutEq s G W) (hz : z ∈ W)
    (hdag : ∀ y ∈ ball G W z k, (exitN G W (ball G W z k) z y).card ≤ r + 1) :
    ∃ X : Finset ℕ, X.card = r ∧ (∀ x ∈ X, x ∉ W) ∧ ∃ H : CH.Digraph,
      OutEq s H (ball G W z k ∪ X) ∧ QFree H (ball G W z k ∪ X) k ∧
      ball H (ball G W z k ∪ X) z k = ball G W z k := by
  obtain ⟨X, hX, hXW⟩ := exists_fresh W r
  obtain ⟨H, h1, h2, h3, _⟩ := exists_pad_s hk hfree hout hz hXW (by rw [hX]; exact hdag)
  exact ⟨X, hX, hXW, H, h1, h2, h3⟩

/-- **Lemma 4_{s,r} (exit lemma).** With `Ball(k,s)`, `k ≥ 1`, `r ≥ 1`, in a `k`-free out-`s` digraph with
`|B_k(z)| ≤ sk+1-r`, some `y ∈ B_k(z)` has at least `r + 2` out-neighbours equal to `z` or outside `B_k(z)`. -/
theorem exit_lemma_s {s k z r : ℕ} (hk : 1 ≤ k) (hbk : Ball k s) (hfree : QFree G W k) (hout : OutEq s G W)
    (hz : z ∈ W) (hr : 1 ≤ r) (hcard : (ball G W z k).card + r ≤ s * k + 1) :
    ∃ y ∈ ball G W z k, r + 2 ≤ (exitN G W (ball G W z k) z y).card := by
  by_contra hcon
  push Not at hcon
  obtain ⟨X, hX, hXW, H, hHout, hHfree, hHball⟩ :=
    exists_pad_r (r := r) hk hfree hout hz (fun y hy => by have := hcon y hy; omega)
  have hdisj : Disjoint (ball G W z k) X := by
    rw [Finset.disjoint_left]
    intro a ha haX
    exact hXW a haX (ball_subset ha)
  have hU : (ball G W z k ∪ X).card ≤ s * k + 1 := by
    rw [Finset.card_union_of_disjoint hdisj, hX]; exact hcard
  have hdiam := diam_small_s hk hbk hHfree hHout hU z (Finset.mem_union_left _ (self_mem_ball hz))
  rw [hHball] at hdiam
  obtain ⟨x, hx⟩ : X.Nonempty := by rw [← Finset.card_pos, hX]; omega
  have : x ∈ ball G W z k := by rw [hdiam]; exact Finset.mem_union_right _ hx
  exact hXW x hx (ball_subset this)

end LeanCH.BR.BRsGen
