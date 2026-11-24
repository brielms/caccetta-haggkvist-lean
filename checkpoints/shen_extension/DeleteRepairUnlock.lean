import LeanCH.BR.BRq3Base

/-!
# Deletion with repair: which arcs a deletion unlocks, and the free-recipient form of the debit rule

Lean 4.35.0. Paper: `checkpoints/shen_extension/DeleteRepair_FreeRecipients_20261118.md`.

The state is the original digraph `D`, a carrier `U` (the labels that survive a deletion), a set `P` of rows and,
for each row `u ∈ P`, a set `S u` of new heads.

* `split_or_avoid`: a walk avoids a deleted bank or splits at its first entry into it.
* `cutter_far`: a deleted label on a short return walk into `u` is far from `u` in out-distance.
* `near_deletion_avoided`, `head_avoided`: deleting labels within out-distance two of `u` (in particular heads of
  `u`) destroys no short return walk into `u`.
* `loser_stays_blocked`: so after deleting one vertex, a repair arc that was unsafe stays unsafe at every row that
  lost a head.
* `repair_qfree`: soundness of simultaneous repairs when no repair head returns quickly to a repaired row.
* `free_recipients`: if no `q`-free digraph on the carrier has minimum outdegree `d`, and no label of `F` returns
  within `q-1` steps to a short row, then one short row `u` has `|F ∪ N⁺(u)| ≤ d-1`.
* `common_recipient`: hence for every recipient `w` some row is short by two, or short by one with `w` in its
  closed zone (itself, a head, or a short return).
* `bank_free_recipients`, `refined_debit`: the same on a least-order source after deleting any bank `R` with
  `q*k ≤ |R|`.
* `tight_parents_cover`, `one_parent_heads_free`: the single-vertex case, with no saturation assumed.
-/

set_option linter.style.longLine false

namespace LeanCH.BR.DeleteRepair

open LeanCH.BR.BRq2 LeanCH.BR.BRq3

variable {D : CH.Digraph} {W : Finset ℕ}

/-- A walk in `W` either avoids `R` or splits at its first entry into `R`. -/
theorem split_or_avoid (R : Finset ℕ) {a b m : ℕ} (w : Walk D W a b m) :
    Walk D (W \ R) a b m ∨
      ∃ x ∈ R, ∃ i j, 1 ≤ i ∧ i + j = m ∧ Walk D W a x i ∧ Walk D W x b j := by
  induction w with
  | refl a => exact Or.inl (.refl a)
  | @step a b c k hb hab w' ih =>
    by_cases hbR : b ∈ R
    · exact Or.inr ⟨b, hbR, 1, k, le_rfl, by omega, .step hb hab (.refl _), w'⟩
    · rcases ih with h | ⟨x, hx, i, j, hi, hsum, w1, w2⟩
      · exact Or.inl (.step (Finset.mem_sdiff.mpr ⟨hb, hbR⟩) hab h)
      · exact Or.inr ⟨x, hx, i + 1, j, by omega, by omega, .step hb hab w1, w2⟩

/-- If `x` lies `a` steps into a return walk of total length at most `q-1` that ends at `u`, with `b` steps left,
then every walk from `u` to `x` has at least `a+2` arcs. -/
theorem cutter_far {V : Finset ℕ} {q x u a b c : ℕ} (hf : QFree D V q)
    (rest : Walk D V x u b) (back : Walk D V u x c) (hc : 1 ≤ c) (hab : a + b + 1 ≤ q) : a + 2 ≤ c := by
  by_contra h
  exact hf x (b + c) (by omega) (by omega) (rest.append back)

/-- Deleting labels that `u` reaches in one or two steps destroys no short return walk into `u`. -/
theorem near_deletion_avoided {V R : Finset ℕ} {q u w m : ℕ} (hf : QFree D V q)
    (near : ∀ x ∈ R, ∃ c, 1 ≤ c ∧ c ≤ 2 ∧ Walk D V u x c)
    (walk : Walk D V w u m) (hm : m + 1 ≤ q) : Walk D (V \ R) w u m := by
  rcases split_or_avoid R walk with h | ⟨x, hx, i, j, hi, hsum, _, w2⟩
  · exact h
  · obtain ⟨c, c1, c2, back⟩ := near x hx
    exact absurd (w2.append back) (hf x (j + c) (by omega) (by omega))

/-- A short return walk into `u` never enters a head of `u`. -/
theorem head_avoided {V : Finset ℕ} {q u v w m : ℕ} (hf : QFree D V q) (hv : v ∈ V)
    (arc : D u v = true) (walk : Walk D V w u m) (hm : m + 1 ≤ q) : Walk D (V \ {v}) w u m :=
  near_deletion_avoided (R := {v}) hf (by
    intro x hx
    rw [Finset.mem_singleton] at hx
    subst hx
    exact ⟨1, le_rfl, by omega, .step hv arc (.refl _)⟩) walk hm

/-- `D` together with new arcs `u → z` for each `u ∈ P` and each `z ∈ S u`. -/
def repair (D : CH.Digraph) (P : Finset ℕ) (S : ℕ → Finset ℕ) : CH.Digraph :=
  fun a b => D a b || (decide (a ∈ P) && decide (b ∈ S a))

theorem repair_old {P : Finset ℕ} {S : ℕ → Finset ℕ} {a b : ℕ} (h : D a b = true) :
    repair D P S a b = true := by
  simp [repair, h]

theorem repair_new {P : Finset ℕ} {S : ℕ → Finset ℕ} {a b : ℕ} (h : a ∈ P) (hb : b ∈ S a) :
    repair D P S a b = true := by
  simp [repair, h, hb]

theorem repair_cases {P : Finset ℕ} {S : ℕ → Finset ℕ} {a b : ℕ} (h : repair D P S a b = true) :
    D a b = true ∨ (a ∈ P ∧ b ∈ S a) := by
  simp only [repair, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h

/-- A walk in the repaired digraph is an old walk, or splits at its first new arc. -/
theorem first_new_arc {P : Finset ℕ} {S : ℕ → Finset ℕ} {a b m : ℕ} (w : Walk (repair D P S) W a b m) :
    Walk D W a b m ∨
      ∃ u ∈ P, ∃ z ∈ S u, ∃ i j, i + 1 + j = m ∧ Walk D W a u i ∧ Walk (repair D P S) W z b j := by
  induction w with
  | refl a => exact Or.inl (.refl a)
  | @step a b c k hb hab w' ih =>
    rcases repair_cases hab with old | ⟨aP, hbS⟩
    · rcases ih with h | ⟨u, hu, z, hz, i, j, hsum, w1, w2⟩
      · exact Or.inl (.step hb old h)
      · exact Or.inr ⟨u, hu, z, hz, i + 1, j, by omega, .step hb old w1, w2⟩
    · exact Or.inr ⟨a, aP, b, hbS, 0, k, by omega, .refl a, w'⟩

/-- Simultaneous repairs are safe when no repair head returns within `q-1` steps to any repaired row. -/
theorem repair_qfree {P : Finset ℕ} {S : ℕ → Finset ℕ} {q : ℕ} (hf : QFree D W q)
    (far : ∀ u ∈ P, ∀ z ∈ S u, ∀ u' ∈ P, ∀ m, m + 1 ≤ q → ¬ Walk D W z u' m) :
    QFree (repair D P S) W q := by
  intro a ℓ h1 hq w
  rcases first_new_arc w with h | ⟨u, hu, z, hz, i, j, hsum, w1, w2⟩
  · exact hf a ℓ h1 hq h
  · rcases first_new_arc w2 with h | ⟨u', hu', z', _, i', j', hsum', w1', _⟩
    · exact far u hu z hz u hu (j + i) (by omega) (h.append w1)
    · exact far u hu z hz u' hu' i' (by omega) w1'

/-- **Half-range safety.** A repair head must not return within `q-1` steps to its own row, but for the other
repaired rows it only has to stay out of half range: no walk of `m` arcs with `2(m+1) ≤ q`. A short closed walk
with two or more new arcs has two old segments, each longer than half range. -/
theorem repair_qfree_half {P : Finset ℕ} {S : ℕ → Finset ℕ} {q : ℕ} (hf : QFree D W q)
    (own : ∀ u ∈ P, ∀ z ∈ S u, ∀ m, m + 1 ≤ q → ¬ Walk D W z u m)
    (cross : ∀ u ∈ P, ∀ z ∈ S u, ∀ u' ∈ P, ∀ m, 2 * (m + 1) ≤ q → ¬ Walk D W z u' m) :
    QFree (repair D P S) W q := by
  intro a ℓ h1 hq w
  rcases first_new_arc w with h | ⟨u, hu, z, hz, i, j, hsum, w1, w2⟩
  · exact hf a ℓ h1 hq h
  · rcases first_new_arc w2 with h | ⟨u', hu', z', hz', i', j', hsum', w1', w2'⟩
    · exact own u hu z hz (j + i) (by omega) (h.append w1)
    · have c1 : ¬ 2 * (i' + 1) ≤ q := fun h => cross u hu z hz u' hu' i' h w1'
      have back : Walk (repair D P S) W z' u (j' + i) :=
        w2'.append (walk_sub (fun _ _ h => repair_old h) w1)
      rcases first_new_arc back with h | ⟨u'', hu'', z'', _, i'', j'', hsum'', w1'', _⟩
      · exact cross u' hu' z' hz' u hu (j' + i) (by omega) h
      · exact cross u' hu' z' hz' u'' hu'' i'' (by omega) w1''

/-- After deleting one vertex `v`, a row `u` that lost the head `v` cannot use a repair arc `u → w` that was
blocked by a short return walk before the deletion. -/
theorem loser_stays_blocked {V P : Finset ℕ} {S : ℕ → Finset ℕ} {q u v w m : ℕ} (hf : QFree D V q)
    (hv : v ∈ V) (hw : w ∈ V) (hwv : w ≠ v) (arc : D u v = true)
    (walk : Walk D V w u m) (hm : m + 1 ≤ q) (hu : u ∈ P) (hS : w ∈ S u) :
    ¬ QFree (repair D P S) (V \ {v}) q := by
  intro free
  have inner := head_avoided hf hv arc walk hm
  have lifted : Walk (repair D P S) (V \ {v}) w u m := walk_sub (fun _ _ h => repair_old h) inner
  exact free u (m + 1) (by omega) hm
    (.step (Finset.mem_sdiff.mpr ⟨hw, by simpa using hwv⟩) (repair_new hu hS) lifted)

/-- **Free recipients.** Suppose no `q`-free digraph on the carrier `U` has minimum outdegree `d`. Call a row
short when it keeps fewer than `d` heads in `U`. Let `F` be any set of labels of `U`, none of which returns
within `q-1` steps to a short row. Then some short row `u` has `|F ∪ N⁺_U(u)| ≤ d-1`. -/
theorem free_recipients {U F : Finset ℕ} {q d : ℕ} (hf : QFree D U q)
    (hF : ∀ w ∈ F, w ∈ U ∧ ∀ u ∈ U, (outN D U u).card + 1 ≤ d → ∀ m, m + 1 ≤ q → ¬ Walk D U w u m)
    (stuck : ∀ E : CH.Digraph, QFree E U q → ¬ ∀ x ∈ U, d ≤ (outN E U x).card) :
    ∃ u ∈ U, (outN D U u).card + 1 ≤ d ∧ (F ∪ outN D U u).card + 1 ≤ d := by
  by_contra bad
  push Not at bad
  have ex : ∀ u, ∃ T : Finset ℕ, (u ∈ U ∧ (outN D U u).card + 1 ≤ d) →
      T ⊆ F \ outN D U u ∧ T.card = d - (outN D U u).card := by
    intro u
    by_cases h : u ∈ U ∧ (outN D U u).card + 1 ≤ d
    · have big := bad u h.1 h.2
      have e := Finset.card_sdiff_add_card F (outN D U u)
      obtain ⟨T, hT, hc⟩ := Finset.exists_subset_card_eq (s := F \ outN D U u)
        (n := d - (outN D U u).card) (by omega)
      exact ⟨T, fun _ => ⟨hT, hc⟩⟩
    · exact ⟨∅, fun h' => absurd h' h⟩
  choose S hS using ex
  obtain ⟨P, hPdef⟩ : ∃ P, P = U.filter (fun u => (outN D U u).card + 1 ≤ d) := ⟨_, rfl⟩
  have memP : ∀ u, u ∈ P ↔ u ∈ U ∧ (outN D U u).card + 1 ≤ d := by
    intro u; rw [hPdef]; exact Finset.mem_filter
  have free : QFree (repair D P S) U q := by
    refine repair_qfree hf ?_
    intro u hu z hz u' hu' m hm
    have zF := (Finset.mem_sdiff.mp ((hS u ((memP u).mp hu)).1 hz)).1
    obtain ⟨uU', short'⟩ := (memP u').mp hu'
    exact (hF z zF).2 u' uU' short' m hm
  refine stuck _ free ?_
  intro x hx
  by_cases xP : x ∈ P
  · obtain ⟨sub, card⟩ := hS x ((memP x).mp xP)
    have dis : Disjoint (outN D U x) (S x) :=
      Finset.disjoint_left.mpr (fun z hz hs => (Finset.mem_sdiff.mp (sub hs)).2 hz)
    have inc : outN D U x ∪ S x ⊆ outN (repair D P S) U x := by
      intro z hz
      rcases Finset.mem_union.mp hz with old | new
      · exact mem_outN.mpr ⟨(mem_outN.mp old).1, repair_old (mem_outN.mp old).2⟩
      · exact mem_outN.mpr ⟨(hF z (Finset.mem_sdiff.mp (sub new)).1).1, repair_new xP new⟩
    have le := Finset.card_le_card inc
    rw [Finset.card_union_of_disjoint dis, card] at le
    have := ((memP x).mp xP).2
    omega
  · have inc : outN D U x ⊆ outN (repair D P S) U x := by
      intro z hz
      exact mem_outN.mpr ⟨(mem_outN.mp hz).1, repair_old (mem_outN.mp hz).2⟩
    have le := Finset.card_le_card inc
    have high : ¬ ((outN D U x).card + 1 ≤ d) := fun h => xP ((memP x).mpr ⟨hx, h⟩)
    omega

/-- **Half-range recipients.** Suppose no `q`-free digraph on the carrier `U` has minimum outdegree `d`. For each
short row `u` let `A u` be any set of labels of `U` that are not heads of `u`, do not return to `u` within `q-1`
steps, and do not reach any short row within half range. Then some short row `u` has
`|A u| + |N⁺_U(u)| ≤ d-1`: its allowed recipients cannot cover its shortage. -/
theorem half_recipients {U : Finset ℕ} {q d : ℕ} (A : ℕ → Finset ℕ) (hf : QFree D U q)
    (hA : ∀ u ∈ U, (outN D U u).card + 1 ≤ d → ∀ z ∈ A u, z ∈ U ∧ D u z ≠ true ∧
      (∀ m, m + 1 ≤ q → ¬ Walk D U z u m) ∧
      ∀ u' ∈ U, (outN D U u').card + 1 ≤ d → ∀ m, 2 * (m + 1) ≤ q → ¬ Walk D U z u' m)
    (stuck : ∀ E : CH.Digraph, QFree E U q → ¬ ∀ x ∈ U, d ≤ (outN E U x).card) :
    ∃ u ∈ U, (outN D U u).card + 1 ≤ d ∧ (A u).card + (outN D U u).card + 1 ≤ d := by
  by_contra bad
  push Not at bad
  have ex : ∀ u, ∃ T : Finset ℕ, (u ∈ U ∧ (outN D U u).card + 1 ≤ d) →
      T ⊆ A u ∧ T.card = d - (outN D U u).card := by
    intro u
    by_cases h : u ∈ U ∧ (outN D U u).card + 1 ≤ d
    · have big := bad u h.1 h.2
      obtain ⟨T, hT, hc⟩ := Finset.exists_subset_card_eq (s := A u)
        (n := d - (outN D U u).card) (by omega)
      exact ⟨T, fun _ => ⟨hT, hc⟩⟩
    · exact ⟨∅, fun h' => absurd h' h⟩
  choose S hS using ex
  obtain ⟨P, hPdef⟩ : ∃ P, P = U.filter (fun u => (outN D U u).card + 1 ≤ d) := ⟨_, rfl⟩
  have memP : ∀ u, u ∈ P ↔ u ∈ U ∧ (outN D U u).card + 1 ≤ d := by
    intro u; rw [hPdef]; exact Finset.mem_filter
  have free : QFree (repair D P S) U q := by
    refine repair_qfree_half hf ?_ ?_
    · intro u hu z hz m hm
      obtain ⟨uU, short⟩ := (memP u).mp hu
      exact (hA u uU short z ((hS u ⟨uU, short⟩).1 hz)).2.2.1 m hm
    · intro u hu z hz u' hu' m hm
      obtain ⟨uU, short⟩ := (memP u).mp hu
      obtain ⟨uU', short'⟩ := (memP u').mp hu'
      exact (hA u uU short z ((hS u ⟨uU, short⟩).1 hz)).2.2.2 u' uU' short' m hm
  refine stuck _ free ?_
  intro x hx
  by_cases xP : x ∈ P
  · obtain ⟨xU, short⟩ := (memP x).mp xP
    obtain ⟨sub, card⟩ := hS x ⟨xU, short⟩
    have dis : Disjoint (outN D U x) (S x) :=
      Finset.disjoint_left.mpr (fun z hz hs => (hA x xU short z (sub hs)).2.1 (mem_outN.mp hz).2)
    have inc : outN D U x ∪ S x ⊆ outN (repair D P S) U x := by
      intro z hz
      rcases Finset.mem_union.mp hz with old | new
      · exact mem_outN.mpr ⟨(mem_outN.mp old).1, repair_old (mem_outN.mp old).2⟩
      · exact mem_outN.mpr ⟨(hA x xU short z (sub new)).1, repair_new xP new⟩
    have le := Finset.card_le_card inc
    rw [Finset.card_union_of_disjoint dis, card] at le
    omega
  · have inc : outN D U x ⊆ outN (repair D P S) U x := by
      intro z hz
      exact mem_outN.mpr ⟨(mem_outN.mp hz).1, repair_old (mem_outN.mp hz).2⟩
    have le := Finset.card_le_card inc
    have high : ¬ ((outN D U x).card + 1 ≤ d) := fun h => xP ((memP x).mpr ⟨hx, h⟩)
    omega

/-- **Recipient rule.** If no `q`-free digraph on the carrier `U` has minimum outdegree `d`, then for every
label `w ∈ U` some row is short of `d` by at least two, or short by one with `w` in its closed zone. -/
theorem common_recipient {U : Finset ℕ} {q d w : ℕ} (hf : QFree D U q) (hw : w ∈ U)
    (stuck : ∀ E : CH.Digraph, QFree E U q → ¬ ∀ x ∈ U, d ≤ (outN E U x).card) :
    ∃ u ∈ U, (outN D U u).card + 1 ≤ d ∧
      ((outN D U u).card + 2 ≤ d ∨ u = w ∨ D u w = true ∨ ∃ m, m + 1 ≤ q ∧ Walk D U w u m) := by
  by_cases ret : ∃ u ∈ U, (outN D U u).card + 1 ≤ d ∧ ∃ m, m + 1 ≤ q ∧ Walk D U w u m
  · obtain ⟨u, hu, low, walk⟩ := ret
    exact ⟨u, hu, low, Or.inr (Or.inr (Or.inr walk))⟩
  · push Not at ret
    obtain ⟨u, hu, low, small⟩ := free_recipients (F := {w}) hf (by
      intro z hz
      rw [Finset.mem_singleton] at hz
      subst hz
      exact ⟨hw, fun u hu low m hm => ret u hu low m hm⟩) stuck
    refine ⟨u, hu, low, ?_⟩
    by_cases arc : D u w = true
    · exact Or.inr (Or.inr (Or.inl arc))
    · have notin : w ∉ outN D U u := fun h => arc (mem_outN.mp h).2
      rw [Finset.singleton_union, Finset.card_insert_of_notMem notin] at small
      exact Or.inl (by omega)

/-- Least-order hypothesis: Caccetta–Häggkvist holds on every strictly smaller host, for every degree. -/
def Below (q : ℕ) (V : Finset ℕ) : Prop :=
  ∀ (E : CH.Digraph) (U : Finset ℕ) (d : ℕ), U.card < V.card → U.Nonempty → 1 ≤ d → QFree E U q →
    (∀ x ∈ U, d ≤ (outN E U x).card) → q * d + 1 ≤ U.card

/-- In a least-order source of order at most `q*s`, after deleting a nonempty bank `R` with `q*k ≤ |R|` and
`k < s`, no `q`-free digraph on the surviving labels has minimum outdegree `s-k`. -/
theorem bank_stuck {V R : Finset ℕ} {q s k : ℕ} (below : Below q V) (order : V.card ≤ q * s)
    (hR : R ⊆ V) (hne : R.Nonempty) (hk : q * k ≤ R.card) (hks : k < s) (hU : (V \ R).Nonempty) :
    ∀ E : CH.Digraph, QFree E (V \ R) q → ¬ ∀ x ∈ V \ R, s - k ≤ (outN E (V \ R) x).card := by
  intro E free deg
  have cardU : (V \ R).card + R.card = V.card := Finset.card_sdiff_add_card_eq_card hR
  have small : (V \ R).card < V.card := by have := hne.card_pos; omega
  have key : q * (s - k) + q * k = q * s := by
    rw [← Nat.mul_add]; congr 1; omega
  have := below E (V \ R) (s - k) small hU (by omega) free deg
  omega

/-- **Free recipients after a bank deletion.** In a least-order source, delete a nonempty proper bank `R` with
`q*k ≤ |R|`, `k < s`. If no label of `F` returns within `q-1` surviving steps to a row keeping fewer than `s-k`
heads, then one such row `u` has `|F ∪ (N⁺(u) \ R)| ≤ s-k-1`. -/
theorem bank_free_recipients {V R F : Finset ℕ} {q s k : ℕ} (hf : QFree D V q)
    (below : Below q V) (order : V.card ≤ q * s)
    (hR : R ⊆ V) (hne : R.Nonempty) (hk : q * k ≤ R.card) (hks : k < s) (hU : (V \ R).Nonempty)
    (hF : ∀ w ∈ F, w ∈ V \ R ∧ ∀ u ∈ V \ R, (outN D (V \ R) u).card + k + 1 ≤ s →
      ∀ m, m + 1 ≤ q → ¬ Walk D (V \ R) w u m) :
    ∃ u ∈ V \ R, (outN D (V \ R) u).card + k + 1 ≤ s ∧ (F ∪ outN D (V \ R) u).card + k + 1 ≤ s := by
  obtain ⟨u, hu, low, small⟩ := free_recipients (d := s - k) (F := F)
    (hf.mono_set Finset.sdiff_subset)
    (fun w hw => ⟨(hF w hw).1, fun u hu low m hm => (hF w hw).2 u hu (by omega) m hm⟩)
    (bank_stuck below order hR hne hk hks hU)
  exact ⟨u, hu, by omega, by omega⟩

/-- **Debit rule with a free recipient.** In a least-order source of order at most `q*s`, delete any nonempty
bank `R` with `q*k ≤ |R|`, `k < s`. For every surviving label `w` there is a surviving row whose retained degree
is at most `s-k-2`, or exactly `s-k-1` with `w` in its closed zone computed after the deletion. -/
theorem refined_debit {V R : Finset ℕ} {q s k w : ℕ} (hf : QFree D V q)
    (below : Below q V) (order : V.card ≤ q * s)
    (hR : R ⊆ V) (hne : R.Nonempty) (hk : q * k ≤ R.card) (hks : k < s) (hw : w ∈ V \ R) :
    ∃ u ∈ V \ R, (outN D (V \ R) u).card + k + 1 ≤ s ∧
      ((outN D (V \ R) u).card + k + 2 ≤ s ∨ u = w ∨ D u w = true ∨
        ∃ m, m + 1 ≤ q ∧ Walk D (V \ R) w u m) := by
  obtain ⟨u, hu, low, alt⟩ := common_recipient (d := s - k) (hf.mono_set Finset.sdiff_subset) hw
    (bank_stuck below order hR hne hk hks ⟨w, hw⟩)
  refine ⟨u, hu, by omega, ?_⟩
  rcases alt with h | h | h | h
  · exact Or.inl (by omega)
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr h))

/-- A row that keeps fewer than `s` heads after deleting the single vertex `v` is a parent of `v` with exactly
`s` heads. -/
theorem short_is_tight_parent {V : Finset ℕ} {s u v : ℕ} (deg : ∀ x ∈ V, s ≤ (outN D V x).card)
    (uV : u ∈ V) (low : (outN D (V \ {v}) u).card + 1 ≤ s) :
    D u v = true ∧ (outN D V u).card = s ∧ (outN D (V \ {v}) u).card + 1 = s := by
  have sub : outN D V u ⊆ insert v (outN D (V \ {v}) u) := by
    intro z hz
    obtain ⟨zV, arc⟩ := mem_outN.mp hz
    by_cases zv : z = v
    · exact Finset.mem_insert.mpr (Or.inl zv)
    · exact Finset.mem_insert_of_mem (mem_outN.mpr ⟨Finset.mem_sdiff.mpr ⟨zV, by simpa using zv⟩, arc⟩)
  have le := (Finset.card_le_card sub).trans (Finset.card_insert_le _ _)
  have ge := deg u uV
  have arc : D u v = true := by
    by_contra no
    have sub' : outN D V u ⊆ outN D (V \ {v}) u := by
      intro z hz
      obtain ⟨zV, zarc⟩ := mem_outN.mp hz
      have zv : z ≠ v := fun h => no (h ▸ zarc)
      exact mem_outN.mpr ⟨Finset.mem_sdiff.mpr ⟨zV, by simpa using zv⟩, zarc⟩
    have := Finset.card_le_card sub'
    omega
  exact ⟨arc, by omega, by omega⟩

/-- Same-degree least-order hypothesis, in the shape of `ShenMinimumOrder.Source.least`. It needs neither the
order bound `|V| ≤ q*s` nor any lower-degree induction hypothesis. -/
def Least (q s : ℕ) (V : Finset ℕ) : Prop :=
  ∀ (E : CH.Digraph) (U : Finset ℕ), QFree E U q → (∀ x ∈ U, s ≤ (outN E U x).card) → U.Nonempty →
    V.card ≤ U.card

/-- After deleting any nonempty proper bank from a least-order source, no `q`-free digraph on the surviving
labels has minimum outdegree `s`. -/
theorem least_stuck {V R : Finset ℕ} {q s : ℕ} (least : Least q s V) (hR : R ⊆ V) (hne : R.Nonempty)
    (hU : (V \ R).Nonempty) :
    ∀ E : CH.Digraph, QFree E (V \ R) q → ¬ ∀ x ∈ V \ R, s ≤ (outN E (V \ R) x).card := by
  intro E free deg
  have cardU : (V \ R).card + R.card = V.card := Finset.card_sdiff_add_card_eq_card hR
  have := least E (V \ R) free deg hU
  have := hne.card_pos
  omega

/-- **Free recipients after any deletion, same degree.** In a least-order source delete a nonempty proper bank
`R`. If no label of `F` returns within `q-1` surviving steps to a row that lost more heads than its excess, then
one such row `u` has `|F ∪ (N⁺(u) \ R)| ≤ s-1`. -/
theorem source_free_recipients {V R F : Finset ℕ} {q s : ℕ} (hf : QFree D V q) (least : Least q s V)
    (hR : R ⊆ V) (hne : R.Nonempty) (hU : (V \ R).Nonempty)
    (hF : ∀ w ∈ F, w ∈ V \ R ∧ ∀ u ∈ V \ R, (outN D (V \ R) u).card + 1 ≤ s →
      ∀ m, m + 1 ≤ q → ¬ Walk D (V \ R) w u m) :
    ∃ u ∈ V \ R, (outN D (V \ R) u).card + 1 ≤ s ∧ (F ∪ outN D (V \ R) u).card + 1 ≤ s :=
  free_recipients (hf.mono_set Finset.sdiff_subset) hF (least_stuck least hR hne hU)

/-- **Tight parents cover.** In a least-order source, for every vertex `v` and every other label `w`, some
parent `u` of `v` with exactly `s` heads has `w` in its closed zone: `u = w`, or `u → w`, or `w` returns to `u`
within `q-1` steps without using `v`. No saturation is assumed. -/
theorem tight_parents_cover {V : Finset ℕ} {q s v w : ℕ} (hf : QFree D V q) (least : Least q s V)
    (deg : ∀ x ∈ V, s ≤ (outN D V x).card) (hv : v ∈ V) (hw : w ∈ V) (hwv : w ≠ v) :
    ∃ u ∈ V, u ≠ v ∧ D u v = true ∧ (outN D V u).card = s ∧
      (u = w ∨ D u w = true ∨ ∃ m, m + 1 ≤ q ∧ Walk D (V \ {v}) w u m) := by
  have wU : w ∈ V \ {v} := Finset.mem_sdiff.mpr ⟨hw, by simpa using hwv⟩
  obtain ⟨u, hu, low, alt⟩ := common_recipient (d := s) (hf.mono_set Finset.sdiff_subset) wU
    (least_stuck least (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v) ⟨w, wU⟩)
  obtain ⟨uV, unv⟩ := Finset.mem_sdiff.mp hu
  obtain ⟨arc, tight, exact⟩ := short_is_tight_parent deg uV low
  refine ⟨u, uV, by simpa using unv, arc, tight, ?_⟩
  rcases alt with h | h
  · omega
  · exact h

/-- **Unreached labels are siblings.** In a least-order source, if `w` does not reach `v` within `q` steps, then
`v` and `w` have a common parent with exactly `s` heads. No saturation is assumed. -/
theorem unreached_is_sibling {V : Finset ℕ} {q s v w : ℕ} (hf : QFree D V q) (least : Least q s V)
    (hq : 1 ≤ q) (deg : ∀ x ∈ V, s ≤ (outN D V x).card) (hv : v ∈ V) (hw : w ∈ V)
    (far : ∀ m, m ≤ q → ¬ Walk D V w v m) :
    ∃ u ∈ V, D u v = true ∧ D u w = true ∧ (outN D V u).card = s := by
  have hwv : w ≠ v := fun h => far 0 (by omega) (h ▸ .refl w)
  obtain ⟨u, uV, _, arc, tight, alt⟩ := tight_parents_cover hf least deg hv hw hwv
  rcases alt with h | h | ⟨m, hm, walk⟩
  · exact absurd (.step hv (h ▸ arc) (.refl v)) (far 1 hq)
  · exact ⟨u, uV, arc, h, tight⟩
  · exact absurd ((walk.mono Finset.sdiff_subset).snoc hv arc) (far (m + 1) hm)

/-- **One tight parent heads every free label.** In a least-order source fix `v`. Let `F` be any set of labels
other than `v`, none of which returns within `q-1` steps (avoiding `v`) to a parent of `v` with exactly `s` heads.
Then a single such parent has all of `F` among its heads. In particular `|F| ≤ s-1`. -/
theorem one_parent_heads_free {V F : Finset ℕ} {q s v : ℕ} (hf : QFree D V q) (least : Least q s V)
    (deg : ∀ x ∈ V, s ≤ (outN D V x).card) (hv : v ∈ V) (hU : (V \ {v}).Nonempty)
    (hF : ∀ w ∈ F, w ∈ V ∧ w ≠ v ∧ ∀ u ∈ V, D u v = true → (outN D V u).card = s →
      ∀ m, m + 1 ≤ q → ¬ Walk D (V \ {v}) w u m) :
    ∃ u ∈ V, D u v = true ∧ (outN D V u).card = s ∧ F ⊆ outN D V u ∧ F.card + 1 ≤ s := by
  obtain ⟨u, hu, low, small⟩ := source_free_recipients (R := {v}) (F := F) hf least
    (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v) hU
    (fun w hw => by
      obtain ⟨wV, wv, far⟩ := hF w hw
      refine ⟨Finset.mem_sdiff.mpr ⟨wV, by simpa using wv⟩, ?_⟩
      intro u hu low m hm
      obtain ⟨arc, tight, _⟩ := short_is_tight_parent deg (Finset.mem_sdiff.mp hu).1 low
      exact far u (Finset.mem_sdiff.mp hu).1 arc tight m hm)
  have uV := (Finset.mem_sdiff.mp hu).1
  obtain ⟨arc, tight, exact⟩ := short_is_tight_parent deg uV low
  have eq : outN D (V \ {v}) u = F ∪ outN D (V \ {v}) u :=
    Finset.eq_of_subset_of_card_le Finset.subset_union_right (by omega)
  have sub : F ⊆ outN D V u := by
    intro z hz
    have : z ∈ outN D (V \ {v}) u := by rw [eq]; exact Finset.mem_union_left _ hz
    exact mem_outN.mpr ⟨(Finset.mem_sdiff.mp (mem_outN.mp this).1).1, (mem_outN.mp this).2⟩
  have Fle : F.card ≤ (F ∪ outN D (V \ {v}) u).card := Finset.card_le_card Finset.subset_union_left
  exact ⟨u, uV, arc, tight, sub, by omega⟩

/-- **One tight parent is saturated away from the half ball.** In a least-order source, every vertex `v` has a
parent `u` with exactly `s` heads such that every other label `w` is a head of `u`, or returns to `u` within
`q-1` steps, or reaches a tight parent of `v` within half range (`m` arcs with `2(m+1) ≤ q`), all avoiding `v`.
No saturation, order bound or induction hypothesis is assumed. -/
theorem half_zone_parent {V : Finset ℕ} {q s v : ℕ} (hf : QFree D V q) (least : Least q s V)
    (deg : ∀ x ∈ V, s ≤ (outN D V x).card) (hv : v ∈ V) (hU : (V \ {v}).Nonempty) :
    ∃ u ∈ V, D u v = true ∧ (outN D V u).card = s ∧ ∀ w ∈ V, w ≠ v →
      (D u w = true ∨ (∃ m, m + 1 ≤ q ∧ Walk D (V \ {v}) w u m) ∨
        ∃ u' ∈ V, D u' v = true ∧ (outN D V u').card = s ∧
          ∃ m, 2 * (m + 1) ≤ q ∧ Walk D (V \ {v}) w u' m) := by
  classical
  obtain ⟨A, hAdef⟩ : ∃ A : ℕ → Finset ℕ, ∀ u z, z ∈ A u ↔ (z ∈ V \ {v} ∧ D u z ≠ true ∧
      (∀ m, m + 1 ≤ q → ¬ Walk D (V \ {v}) z u m) ∧
      ∀ u' ∈ V \ {v}, (outN D (V \ {v}) u').card + 1 ≤ s →
        ∀ m, 2 * (m + 1) ≤ q → ¬ Walk D (V \ {v}) z u' m) :=
    ⟨fun u => (V \ {v}).filter (fun z => D u z ≠ true ∧
      (∀ m, m + 1 ≤ q → ¬ Walk D (V \ {v}) z u m) ∧
      ∀ u' ∈ V \ {v}, (outN D (V \ {v}) u').card + 1 ≤ s →
        ∀ m, 2 * (m + 1) ≤ q → ¬ Walk D (V \ {v}) z u' m), fun _ _ => Finset.mem_filter⟩
  obtain ⟨u, hu, low, small⟩ := half_recipients (d := s) A (hf.mono_set Finset.sdiff_subset)
    (fun u _ _ z hz => (hAdef u z).mp hz)
    (least_stuck least (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v) hU)
  have uV := (Finset.mem_sdiff.mp hu).1
  obtain ⟨arc, tight, exact⟩ := short_is_tight_parent deg uV low
  have empty : A u = ∅ := Finset.card_eq_zero.mp (by omega)
  refine ⟨u, uV, arc, tight, ?_⟩
  intro w hw hwv
  have wU : w ∈ V \ {v} := Finset.mem_sdiff.mpr ⟨hw, by simpa using hwv⟩
  have notA : w ∉ A u := by rw [empty]; exact Finset.notMem_empty w
  by_cases h1 : D u w = true
  · exact Or.inl h1
  by_cases h2 : ∃ m, m + 1 ≤ q ∧ Walk D (V \ {v}) w u m
  · exact Or.inr (Or.inl h2)
  by_cases h3 : ∃ u' ∈ V, D u' v = true ∧ (outN D V u').card = s ∧
      ∃ m, 2 * (m + 1) ≤ q ∧ Walk D (V \ {v}) w u' m
  · exact Or.inr (Or.inr h3)
  exfalso
  refine notA ((hAdef u w).mpr ⟨wU, h1, fun m hm walk => h2 ⟨m, hm, walk⟩, ?_⟩)
  intro u' hu' low' m hm walk
  obtain ⟨arc', tight', _⟩ := short_is_tight_parent deg (Finset.mem_sdiff.mp hu').1 low'
  exact h3 ⟨u', (Finset.mem_sdiff.mp hu').1, arc', tight', m, hm, walk⟩

end LeanCH.BR.DeleteRepair

open LeanCH.BR.DeleteRepair in
#print axioms half_recipients
open LeanCH.BR.DeleteRepair in
#print axioms half_zone_parent
open LeanCH.BR.DeleteRepair in
#print axioms free_recipients
open LeanCH.BR.DeleteRepair in
#print axioms bank_free_recipients
open LeanCH.BR.DeleteRepair in
#print axioms one_parent_heads_free
open LeanCH.BR.DeleteRepair in
#print axioms loser_stays_blocked
open LeanCH.BR.DeleteRepair in
#print axioms unreached_is_sibling
