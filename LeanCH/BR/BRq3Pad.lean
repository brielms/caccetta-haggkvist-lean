import LeanCH.BR.BRq3Diam

/-!
# Route 1, Lemmas 3 and 4: padding and the exit lemma (Lean 4.35.0)

Paper: `checkpoints/boundary_20261111/Route1_PiIteration_subagent.md`, §3 (Lemma 3 with `r = 1`, Lemma 4).

`G` is `k`-free with out-degree three on `W`, `z ∈ W`, `B = B_k(z)`, and `x ∉ W` is a fresh vertex. The padded digraph
`padD G B z x` lives on `insert x B`:
* `x` copies `O(z)` (the paper's `x → z, a₁, a₂` is replaced by `x → O(z)`; both drop from depth `k+1` to `≤ 1`);
* `a ≠ x` keeps its arcs inside `B`, adds `a → z` if it has `r(a) := |O(a) ∩ B| ≤ 2`, and adds `a → x` if
  `r(a) ≤ 1` or (`r(a) = 2` and `a → z`). This is the paper's construction with `t(a) = 3 - r(a)`.

* `pad_walk` (the potential): a padded walk of length `m` from level `i` ends at level `i + m`, where level `i` means
  `B_i(z)`, and `x` sits at level `k + 1`.
* `pad_outEq`, `pad_qfree`, `pad_not_mem` (Lemma 3): out-3, `k`-free, and `x ∉ B^H_k(z)`, assuming no exit vertex.
* `exit_lemma` (**Lemma 4**): with `Ball(k,3)` and `|B_k(z)| ≤ 3k`, some `y ∈ B_k(z)` has all its out-neighbours
  equal to `z` or outside `B_k(z)`.
-/

set_option linter.style.longLine false

namespace LeanCH.BR.BRq3

open LeanCH.BR.BRq2

variable {G : CH.Digraph} {W : Finset ℕ}

/-- The padded digraph of Lemma 3 (`r = 1`). -/
def padD (G : CH.Digraph) (B : Finset ℕ) (z x : ℕ) : CH.Digraph :=
  fun a b => if a = x then decide (b ∈ outN G B z) else
    (G a b && decide (b ∈ B)) || (decide (b = z) && decide ((outN G B a).card ≤ 2)) ||
      (decide (b = x) && decide ((outN G B a).card ≤ 1 ∨ ((outN G B a).card = 2 ∧ G a z = true)))

theorem walk_uncons {D : CH.Digraph} {a c m : ℕ} (w : Walk D W a c (m + 1)) :
    ∃ b, b ∈ W ∧ D a b = true ∧ Walk D W b c m := by
  cases w with
  | step hb hab w' => exact ⟨_, hb, hab, w'⟩

/-- A vertex of `B_i(z)`, `i + 1 ≤ k`, keeps all three arcs inside `B_k(z)`. -/
theorem three_le_inner (hout : OutEq 3 G W) {z i k a : ℕ} (ha : a ∈ ball G W z i) (hik : i + 1 ≤ k) :
    3 ≤ (outN G (ball G W z k) a).card := by
  have hsub : outN G W a ⊆ outN G (ball G W z k) a := by
    intro c hc
    obtain ⟨hcW, hac⟩ := mem_outN.mp hc
    exact mem_outN.mpr ⟨ball_mono_radius hik (ball_step ha hcW hac), hac⟩
  have := Finset.card_le_card hsub
  rwa [hout a (ball_subset ha)] at this

/-- One padded arc raises the level by at most one. -/
theorem pad_step {k z x a b i : ℕ} (hz : z ∈ W) (hout : OutEq 3 G W)
    (ha : a ∈ ball G W z i ∨ (a = x ∧ k + 1 ≤ i)) (hab : padD G (ball G W z k) z x a b = true) :
    b ∈ ball G W z (i + 1) ∨ (b = x ∧ k + 1 ≤ i + 1) := by
  by_cases hax : a = x
  · have hb : b ∈ outN G (ball G W z k) z := by simpa [padD, hax] using hab
    obtain ⟨hbB, hzb⟩ := mem_outN.mp hb
    exact Or.inl (ball_mono_radius (by omega) (ball_of_adj (ball_subset hbB) hzb))
  · have ha' : a ∈ ball G W z i := ha.resolve_right (fun h => hax h.1)
    simp only [padD, hax, ite_false, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hab
    rcases hab with ((⟨hG, hbB⟩ | ⟨hbz, _⟩) | ⟨hbx, hr⟩)
    · exact Or.inl (ball_step ha' (ball_subset hbB) hG)
    · rw [hbz]; exact Or.inl (self_mem_ball hz)
    · refine Or.inr ⟨hbx, ?_⟩
      have hr2 : (outN G (ball G W z k) a).card ≤ 2 := by
        rcases hr with h | ⟨h, _⟩ <;> omega
      by_contra hi
      have := three_le_inner hout ha' (k := k) (by omega)
      omega

/-- **The potential.** A padded walk of length `m` from level `i` ends at level `i + m`. -/
theorem pad_walk {k z x : ℕ} (hz : z ∈ W) (hout : OutEq 3 G W) {U : Finset ℕ} {a c m : ℕ}
    (w : Walk (padD G (ball G W z k) z x) U a c m) :
    ∀ i, (a ∈ ball G W z i ∨ (a = x ∧ k + 1 ≤ i)) → (c ∈ ball G W z (i + m) ∨ (c = x ∧ k + 1 ≤ i + m)) := by
  induction w with
  | refl a => intro i h; simpa using h
  | @step a b c m _ hab _ ih =>
    intro i h
    have := ih (i + 1) (pad_step hz hout h hab)
    rwa [show i + 1 + m = i + (m + 1) by omega] at this

/-- A padded walk inside `B ∖ {z}` not starting at `x` is a `G`-walk. -/
theorem pad_toG {B : Finset ℕ} {z x : ℕ} (hBW : B ⊆ W) (hx : x ∉ W) {a c m : ℕ}
    (w : Walk (padD G B z x) (B.erase z) a c m) : a ≠ x → Walk G W a c m := by
  induction w with
  | refl a => intro _; exact .refl a
  | @step a b c m hb hab _ ih =>
    intro ha
    have hbB := Finset.mem_of_mem_erase hb
    have hbz := Finset.ne_of_mem_erase hb
    have hbx : b ≠ x := fun h => hx (h ▸ hBW hbB)
    refine .step (hBW hbB) ?_ (ih hbx)
    simpa [padD, ha, hbz, hbx, hbB] using hab

theorem outN_mono_set {B : Finset ℕ} (hB : B ⊆ W) (a : ℕ) : outN G B a ⊆ outN G W a :=
  fun _ hc => mem_outN.mpr ⟨hB (mem_outN.mp hc).1, (mem_outN.mp hc).2⟩

/-- Finset bookkeeping for `pad_outEq`. -/
theorem card_three_aux {A S : Finset ℕ} {z x : ℕ} {g : Prop} (hzA : z ∈ A ↔ g) (hxA : x ∉ A) (hxz : x ≠ z)
    (hA3 : A.card ≤ 3) {b0 : ℕ} (hb0 : b0 ∈ A) (hb0z : b0 ≠ z)
    (hS : ∀ b, b ∈ S ↔ b ∈ A ∨ (b = z ∧ A.card ≤ 2) ∨ (b = x ∧ (A.card ≤ 1 ∨ (A.card = 2 ∧ g)))) :
    S.card = 3 := by
  have hA1 : 1 ≤ A.card := Finset.card_pos.mpr ⟨b0, hb0⟩
  rcases (by omega : A.card = 3 ∨ A.card = 2 ∨ A.card = 1) with h3 | h2 | h1
  · have e : S = A := by
      ext b
      rw [hS b]
      constructor
      · rintro (h | ⟨_, h⟩ | ⟨_, h | ⟨h, _⟩⟩)
        · exact h
        all_goals omega
      · exact fun h => Or.inl h
    rw [e, h3]
  · by_cases hg : g
    · have e : S = insert x A := by
        ext b
        rw [hS b, Finset.mem_insert]
        constructor
        · rintro (h | ⟨rfl, _⟩ | ⟨rfl, _⟩)
          · exact Or.inr h
          · exact Or.inr (hzA.mpr hg)
          · exact Or.inl rfl
        · rintro (rfl | h)
          · exact Or.inr (Or.inr ⟨rfl, Or.inr ⟨h2, hg⟩⟩)
          · exact Or.inl h
      rw [e, Finset.card_insert_of_notMem hxA, h2]
    · have hzA' : z ∉ A := fun h => hg (hzA.mp h)
      have e : S = insert z A := by
        ext b
        rw [hS b, Finset.mem_insert]
        constructor
        · rintro (h | ⟨rfl, _⟩ | ⟨_, h | ⟨_, h⟩⟩)
          · exact Or.inr h
          · exact Or.inl rfl
          · omega
          · exact absurd h hg
        · rintro (rfl | h)
          · exact Or.inr (Or.inl ⟨rfl, by omega⟩)
          · exact Or.inl h
      rw [e, Finset.card_insert_of_notMem hzA', h2]
  · have hzA' : z ∉ A := fun h => hb0z (Finset.card_le_one.mp h1.le b0 hb0 z h)
    have hxzA : x ∉ insert z A := by
      rw [Finset.mem_insert]; rintro (h | h)
      · exact hxz h
      · exact hxA h
    have e : S = insert x (insert z A) := by
      ext b
      rw [hS b, Finset.mem_insert, Finset.mem_insert]
      constructor
      · rintro (h | ⟨rfl, _⟩ | ⟨rfl, _⟩)
        · exact Or.inr (Or.inr h)
        · exact Or.inr (Or.inl rfl)
        · exact Or.inl rfl
      · rintro (rfl | rfl | h)
        · exact Or.inr (Or.inr ⟨rfl, Or.inl (by omega)⟩)
        · exact Or.inr (Or.inl ⟨rfl, by omega⟩)
        · exact Or.inl h
    rw [e, Finset.card_insert_of_notMem hxzA, Finset.card_insert_of_notMem hzA', h1]

/-- **Lemma 3, out-degree.** If every `y ∈ B_k(z)` has an out-neighbour in `B_k(z) ∖ {z}`, the padded digraph has
out-degree exactly three on `insert x B_k(z)`. -/
theorem pad_outEq {k z x : ℕ} (hk : 1 ≤ k) (hout : OutEq 3 G W) (hz : z ∈ W) (hx : x ∉ W)
    (hno : ∀ y ∈ ball G W z k, ∃ b ∈ outN G W y, b ≠ z ∧ b ∈ ball G W z k) :
    OutEq 3 (padD G (ball G W z k) z x) (insert x (ball G W z k)) := by
  have hBW : ball G W z k ⊆ W := ball_subset
  have hxB : x ∉ ball G W z k := fun h => hx (hBW h)
  have hzB : z ∈ ball G W z k := self_mem_ball hz
  have hxz : x ≠ z := fun h => hx (h ▸ hz)
  intro a ha
  rcases Finset.mem_insert.mp ha with hax | haB
  · -- `x` copies `O(z)`
    rw [hax]
    have hxrow : ∀ b, padD G (ball G W z k) z x x b = decide (b ∈ outN G (ball G W z k) z) :=
      fun b => by simp [padD]
    have e : outN (padD G (ball G W z k) z x) (insert x (ball G W z k)) x = outN G (ball G W z k) z := by
      ext b
      rw [mem_outN, hxrow, decide_eq_true_eq]
      exact ⟨fun h => h.2, fun h => ⟨Finset.mem_insert_of_mem (mem_outN.mp h).1, h⟩⟩
    rw [e]
    have h1 := Finset.card_le_card (outN_mono_set (G := G) hBW z)
    rw [hout z hz] at h1
    exact le_antisymm h1 (three_le_inner hout (self_mem_ball (D := G) (k := 0) hz) hk)
  · have hxa : a ≠ x := fun h => hxB (h ▸ haB)
    have hA3 : (outN G (ball G W z k) a).card ≤ 3 := by
      have := Finset.card_le_card (outN_mono_set (G := G) hBW a)
      rwa [hout a (hBW haB)] at this
    obtain ⟨b0, hb0, hb0z, hb0B⟩ := hno a haB
    have hb0A : b0 ∈ outN G (ball G W z k) a := mem_outN.mpr ⟨hb0B, (mem_outN.mp hb0).2⟩
    have hzA : z ∈ outN G (ball G W z k) a ↔ G a z = true :=
      ⟨fun h => (mem_outN.mp h).2, fun h => mem_outN.mpr ⟨hzB, h⟩⟩
    have hxA : x ∉ outN G (ball G W z k) a := fun h => hxB (mem_outN.mp h).1
    refine card_three_aux hzA hxA hxz hA3 hb0A hb0z (fun b => ?_)
    simp only [mem_outN, padD, hxa, ite_false, Finset.mem_insert, Bool.or_eq_true, Bool.and_eq_true,
      decide_eq_true_eq]
    constructor
    · rintro ⟨_, (⟨h1, h2⟩ | h) | h⟩
      · exact Or.inl ⟨h2, h1⟩
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    · rintro (⟨h1, h2⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩)
      · exact ⟨Or.inr h1, Or.inl (Or.inl ⟨h2, h1⟩)⟩
      · exact ⟨Or.inr hzB, Or.inl (Or.inr ⟨rfl, h⟩)⟩
      · exact ⟨Or.inl rfl, Or.inr ⟨rfl, h⟩⟩

/-- **Lemma 3, `k`-freeness.** The padded digraph is `k`-free on `insert x B_k(z)`. -/
theorem pad_qfree {k z x : ℕ} (hfree : QFree G W k) (hout : OutEq 3 G W) (hz : z ∈ W) (hx : x ∉ W) :
    QFree (padD G (ball G W z k) z x) (insert x (ball G W z k)) k := by
  intro a ℓ h1 hℓ w
  have hBW : ball G W z k ⊆ W := ball_subset
  have hxB : x ∉ ball G W z k := fun h => hx (hBW h)
  have hzB : z ∈ ball G W z k := self_mem_ball hz
  have hzx : z ≠ x := fun h => hx (h ▸ hz)
  rcases w.lastVisit x with h | ⟨m1, m2, _, hsum, w1, w2⟩
  · -- the closed walk avoids `x`, so it lies in `B`
    rw [Finset.erase_insert hxB] at h
    rcases h.lastVisit z with h' | ⟨n1, n2, _, hsum', v1, v2⟩
    · -- it also avoids `z`: a closed `G`-walk
      obtain ⟨ℓ', rfl⟩ : ∃ ℓ', ℓ = ℓ' + 1 := ⟨ℓ - 1, by omega⟩
      obtain ⟨_, _, haE, _⟩ := h'.unsnoc
      have hax : a ≠ x := fun e => hxB (e ▸ Finset.mem_of_mem_erase haE)
      exact hfree a (ℓ' + 1) h1 hℓ (pad_toG hBW hx h' hax)
    · -- rotate to a closed walk at `z`; its last arc `s → z` comes from `s ∈ B_{ℓ-1}(z)`
      have wz := (v2.mono (Finset.erase_subset _ _)).append v1
      obtain ⟨n, hn⟩ : ∃ n, n2 + n1 = n + 1 := ⟨n2 + n1 - 1, by omega⟩
      rw [hn] at wz
      obtain ⟨s, ws, _, hsz⟩ := wz.unsnoc
      obtain ⟨m', hm', ws'⟩ := ws.fromStart
      have g := pad_toG hBW hx ws' hzx
      have hsW : s ∈ W := by
        rcases ws'.end_mem_or with e | e
        · rw [e]; exact hz
        · exact hBW (Finset.mem_of_mem_erase e)
      have hsb : s ∈ ball G W z m' := mem_ball_of_walk g le_rfl hsW
      have hsx : s ≠ x := fun e => hx (e ▸ hsW)
      have hsz' : G s z = true ∨ (outN G (ball G W z k) s).card ≤ 2 := by
        simpa [padD, hsx, hzx, hzB] using hsz
      rcases hsz' with hsz | hsz
      · exact hfree z (m' + 1) (by omega) (by omega) (g.snoc hz hsz)
      · have := three_le_inner hout hsb (k := k) (by omega)
        omega
  · -- the closed walk visits `x`: rotate to `x`, step to `O(z) ⊆ B_1(z)`, and climb back to level `k + 1`
    have wx := (w2.mono (Finset.erase_subset _ _)).append w1
    obtain ⟨n, hn⟩ : ∃ n, m2 + m1 = n + 1 := ⟨m2 + m1 - 1, by omega⟩
    rw [hn] at wx
    obtain ⟨b, _, hxb, w'⟩ := walk_uncons wx
    have hb : b ∈ outN G (ball G W z k) z := by simpa [padD] using hxb
    obtain ⟨hbB, hzb⟩ := mem_outN.mp hb
    rcases pad_walk hz hout w' 1 (Or.inl (ball_of_adj (hBW hbB) hzb)) with h | ⟨_, h⟩
    · exact hx (ball_subset h)
    · omega

/-- **Lemma 3, the ball.** `x ∉ B^H_k(z)`. -/
theorem pad_not_mem {k z x : ℕ} (hout : OutEq 3 G W) (hz : z ∈ W) (hx : x ∉ W) :
    x ∉ ball (padD G (ball G W z k) z x) (insert x (ball G W z k)) z k := by
  intro hxb
  obtain ⟨_, m, hm, w⟩ := mem_ball.mp hxb
  rcases pad_walk hz hout w 0 (Or.inl (self_mem_ball hz)) with h | ⟨_, h⟩
  · exact hx (ball_subset h)
  · omega

/-- **Lemma 4 (exit lemma).** With `Ball(k,3)`, `k ≥ 1`, in a `k`-free out-3 digraph with `|B_k(z)| ≤ 3k`, some
`y ∈ B_k(z)` has every out-neighbour equal to `z` or outside `B_k(z)`. -/
theorem exit_lemma {k z : ℕ} (hk : 1 ≤ k) (hbk : Ball k 3) (hfree : QFree G W k) (hout : OutEq 3 G W)
    (hz : z ∈ W) (hcard : (ball G W z k).card ≤ 3 * k) :
    ∃ y ∈ ball G W z k, ∀ b ∈ outN G W y, b = z ∨ b ∉ ball G W z k := by
  by_contra hcon
  have hno : ∀ y ∈ ball G W z k, ∃ b ∈ outN G W y, b ≠ z ∧ b ∈ ball G W z k := by
    intro y hy
    by_contra h
    refine hcon ⟨y, hy, fun b hb => ?_⟩
    by_contra h'
    exact h ⟨b, hb, fun e => h' (Or.inl e), by by_contra h''; exact h' (Or.inr h'')⟩
  -- a fresh vertex
  have hx : W.sup id + 1 ∉ W := by
    intro h
    have := Finset.le_sup (f := id) h
    simp only [id] at this
    omega
  have hxB : W.sup id + 1 ∉ ball G W z k := fun h => hx (ball_subset h)
  have hU : (insert (W.sup id + 1) (ball G W z k)).card ≤ 3 * k + 1 := by
    rw [Finset.card_insert_of_notMem hxB]; omega
  have hdiam := diam_small hk hbk (pad_qfree hfree hout hz hx) (pad_outEq hk hout hz hx hno) hU z
    (Finset.mem_insert_of_mem (self_mem_ball hz))
  exact pad_not_mem hout hz hx (k := k) (by rw [hdiam]; exact Finset.mem_insert_self _ _)

end LeanCH.BR.BRq3
