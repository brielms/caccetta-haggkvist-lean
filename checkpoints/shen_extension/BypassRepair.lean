import checkpoints.shen_extension.RemoteParentPacking
import checkpoints.shen_extension.NativeCascade

/-!
# Edit after deletion: one shortcut through an erased parent, paid by cuts

Lean 4.35.0.

State: a `q`-free digraph `D` on `V`, the survivors `U` of a deletion, and the lower quota `t`
(`t = r-1` in the degree descent). `spare D U t c` is the number of heads a surviving row `c` may
still lose, namely its surviving degree minus `t`.

* `descent_stuck`: the consumer with the size budget `|V| - q t ≤ |B|` (not `q ≤ |B|`).
* `via`: rows that can lie on a short return to `x` from a head of a parent-two-steps label `p`.
* `shortcut_iff`: for `x → p → z`, the shortcut `x → z` can be made safe by cuts inside the spare
  budgets exactly when `z` is off the active cascade of `x` computed on `via`.
* `shortcut_host`, `clean_parent_host`: the literal lower-degree host.
* `unpaid_return`: when the shortcut is blocked, an actual return `z ⇝ y → x` of exactly `q-1` arcs
  whose last tail `y` has no spare and does not point to `p`.
* `lone_row_law`, `forced_row`: what a graph with no lower-degree host must satisfy.
* `cut_budget`: the total spare in terms of the arcs lost to the bank.
* `native_first_attack`: the law on the labels of the marked chain of a native source.
-/

set_option linter.style.longLine false

namespace LeanCH.BR.BypassRepair
open Finset BRq2 BRq3 FundedCascade DeleteRepair

/-- The lower-degree hypothesis exactly as a degree descent consumes it. -/
def NoHost (q t : ℕ) : Prop :=
  ∀ (E : CH.Digraph) (U : Finset ℕ), U.Nonempty → U.card ≤ q * t → QFree E U q →
    ¬ ∀ x ∈ U, t ≤ (outN E U x).card

/-- Rows that can lie on a return of at most `q-1` arcs into `x` that starts at a head of `p`,
where `x → p`: they neither point to `p` nor are heads of `x`. -/
def via (D : CH.Digraph) (U : Finset ℕ) (x p : ℕ) : Finset ℕ :=
  U.filter (fun c => c = x ∨ (D c p ≠ true ∧ D x c ≠ true))

theorem mem_via {D : CH.Digraph} {U : Finset ℕ} {x p c : ℕ} :
    c ∈ via D U x p ↔ c ∈ U ∧ (c = x ∨ (D c p ≠ true ∧ D x c ≠ true)) := mem_filter

theorem via_subset {D : CH.Digraph} {U : Finset ℕ} {x p : ℕ} : via D U x p ⊆ U := filter_subset _ _

private theorem pos_of_ne {E : CH.Digraph} {W : Finset ℕ} {a b k : ℕ} (w : Walk E W a b k)
    (ne : a ≠ b) : 1 ≤ k := by
  cases w with
  | refl => exact absurd rfl ne
  | step _ _ _ => omega

private theorem end_mem {E : CH.Digraph} {W : Finset ℕ} {a b k : ℕ} (w : Walk E W a b k)
    (aw : a ∈ W) : b ∈ W := by
  rcases w.end_mem_or with rfl | h
  · exact aw
  · exact h

private theorem last_arc {E : CH.Digraph} {W : Finset ℕ} {a b m : ℕ} (w : Walk E W a b m)
    (pos : 1 ≤ m) : ∃ y k, k + 1 = m ∧ Walk E W a y k ∧ E y b = true := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  obtain ⟨y, wy, _, last⟩ := w.unsnoc
  exact ⟨y, k, rfl, wy, last⟩

/-- **Consumer with the size budget.** Delete any bank `B` with `|V| - q t ≤ |B|`, pass to any
subgraph `K` of the surviving arcs and add arcs that pass the own-return and half-range cross tests
in `K`. If no lower-degree host exists, some surviving row ends below `t`. -/
theorem descent_stuck {D K : CH.Digraph} {V B P : Finset ℕ} {S : ℕ → Finset ℕ} {q t : ℕ}
    (free : QFree D V q) (none : NoHost q t) (hB : B ⊆ V) (size : V.card - q * t ≤ B.card)
    (hU : (V \ B).Nonempty) (sub : ∀ a b, K a b = true → D a b = true)
    (own : ∀ u ∈ P, ∀ z ∈ S u, ∀ m, m + 1 ≤ q → ¬ Walk K (V \ B) z u m)
    (cross : ∀ u ∈ P, ∀ z ∈ S u, ∀ u' ∈ P, ∀ m, 2 * (m + 1) ≤ q → ¬ Walk K (V \ B) z u' m) :
    ∃ x ∈ V \ B, (outN (repair K P S) (V \ B) x).card < t := by
  by_contra bad
  push Not at bad
  have kfree : QFree K (V \ B) q :=
    fun a l h1 h2 w => free a l h1 h2 ((walk_sub sub w).mono sdiff_subset)
  have count := card_sdiff_add_card_eq_card hB
  exact none (repair K P S) (V \ B) hU (by omega) (repair_qfree_half kfree own cross) bad

/-- A short return from a head of `p` into `x` stays inside `via`. -/
theorem via_walk {D E : CH.Digraph} {V U : Finset ℕ} {q x p z a i m : ℕ}
    (free : QFree D V q) (uv : U ⊆ V) (sub : ∀ a b, E a b = true → D a b = true)
    (pv : p ∈ V) (zv : z ∈ V) (pz : D p z = true)
    (pre : Walk D V z a i) (path : Walk E U a x m) (lim : i + m + 1 ≤ q) :
    Walk E (via D U x p) a x m := by
  induction path generalizing i with
  | refl => exact .refl _
  | @step a b x k bu edge tail ih =>
    have bv := uv bu
    have ab := sub _ _ edge
    have grow : Walk D V z b (i + 1) := pre.snoc bv ab
    refine .step (mem_via.mpr ⟨bu, ?_⟩) edge (ih grow (by omega))
    by_cases bx : b = x
    · exact Or.inl bx
    · have kpos := pos_of_ne tail bx
      refine Or.inr ⟨fun bp => ?_, fun xb => ?_⟩
      · exact free p (i + 1 + 1 + 1) (by omega) (by omega) (.step zv pz (grow.snoc pv bp))
      · exact free x (k + 1) (by omega) (by omega)
          (.step bv xb ((walk_sub sub tail).mono uv))

section shortcut
variable {D : CH.Digraph} {V U : Finset ℕ} {q t x p z : ℕ}

theorem target_ne (free : QFree D V q) (hq : 2 ≤ q) (xv : x ∈ V) (pv : p ∈ V)
    (xp : D x p = true) (pz : D p z = true) : z ≠ x := by
  rintro rfl
  exact digonfree free hq xv pv xp pz

theorem target_mem_via (free : QFree D V q) (hq : 2 ≤ q) (uv : U ⊆ V) (zu : z ∈ U) (pv : p ∈ V)
    (pz : D p z = true) (xz : D x z ≠ true) : z ∈ via D U x p :=
  mem_via.mpr ⟨zu, Or.inr ⟨fun zp => digonfree free hq pv (uv zu) pz zp, xz⟩⟩

/-- The static cut read off the cascade on `via` makes the shortcut `x → z` safe. -/
theorem shortcut_free (free : QFree D V q) (hq : 2 ≤ q) (uv : U ⊆ V) (zu : z ∈ U) (pv : p ∈ V)
    (pz : D p z = true) (xz : D x z ≠ true)
    (off : z ∉ active D (via D U x p) {x} (spare D U t) (q - 1)) :
    QFree (repair (cut D (fun c => bill D (via D U x p) {x} (spare D U t) c (q - 1)))
      {x} (fun _ => {z})) U q := by
  have sub : ∀ a b, cut D (fun c => bill D (via D U x p) {x} (spare D U t) c (q - 1)) a b = true →
      D a b = true := fun _ _ h => (Bool.and_eq_true_iff.mp h).1
  have kfree : QFree (cut D (fun c => bill D (via D U x p) {x} (spare D U t) c (q - 1))) U q :=
    fun a l h1 h2 w => free a l h1 h2 ((walk_sub sub w).mono uv)
  apply repair_qfree kfree
  intro u hu z' hz' u' hu' m hm walk
  rw [mem_singleton] at hu hu' hz'
  subst hu hu' hz'
  have inside := via_walk free uv sub pv (uv zu) pz (.refl _) walk (by omega)
  exact off (active_mono D _ _ _ (by omega : m ≤ q - 1)
    (sound_cut D _ _ _ (target_mem_via free hq uv zu pv pz xz) (mem_singleton_self _)
      (by omega) inside))

/-- If `z` is on the cascade, every cut inside the spare budgets leaves a short cycle through the
shortcut. The carrier is any set of survivors containing `x`. -/
theorem shortcut_blocked {W : Finset ℕ} (hq : 1 ≤ q) (wu : W ⊆ U) (xw : x ∈ W) (zu : z ∈ U)
    (on : z ∈ active D W {x} (spare D U t) (q - 1))
    (C : ℕ → Finset ℕ) (budget : ∀ c ∈ U, (C c).card ≤ spare D U t c) :
    ¬ QFree (repair (cut D C) {x} (fun _ => {z})) U q := by
  intro safe
  obtain ⟨x', hx', l, lk, path⟩ := robust D W {x} (spare D U t) (singleton_subset_iff.mpr xw) on C
    (fun c cw => budget c (wu cw))
  rw [mem_singleton] at hx'
  subst hx'
  have lifted : Walk (repair (cut D C) {x'} (fun _ => {z})) U z x' l :=
    walk_sub (fun _ _ h => repair_old h) (path.mono wu)
  exact safe x' (l + 1) (by omega) (by omega)
    (.step zu (repair_new (mem_singleton_self _) (mem_singleton_self _)) lifted)

/-- **Exact test for the shortcut through `p`.** With `x → p → z` and `x ↛ z`, some cut inside
the spare budgets makes `x → z` safe on the survivors exactly when `z` is off the active cascade
of `x` on `via D U x p`. Rows pointing to `p` and heads of `x` never enter the bill. -/
theorem shortcut_iff (free : QFree D V q) (hq : 2 ≤ q) (uv : U ⊆ V) (xu : x ∈ U) (zu : z ∈ U)
    (pv : p ∈ V) (pz : D p z = true) (xz : D x z ≠ true) :
    (∃ C : ℕ → Finset ℕ, (∀ c ∈ U, (C c).card ≤ spare D U t c) ∧
      QFree (repair (cut D C) {x} (fun _ => {z})) U q) ↔
    z ∉ active D (via D U x p) {x} (spare D U t) (q - 1) := by
  constructor
  · rintro ⟨C, budget, safe⟩ on
    exact shortcut_blocked (by omega) via_subset (mem_via.mpr ⟨xu, Or.inl rfl⟩) zu on C budget safe
  · intro off
    exact ⟨_, fun c _ => affordable D _ _ _ c _, shortcut_free free hq uv zu pv pz xz off⟩

/-- **Literal host from one shortcut.** Every surviving row other than `x` keeps `t` heads, `x`
keeps `t-1`, and `z` is off the cascade: the cut graph plus `x → z` is `q`-free on the survivors
with minimum outdegree `t`. -/
theorem shortcut_host (free : QFree D V q) (hq : 2 ≤ q) (uv : U ⊆ V) (zu : z ∈ U) (pv : p ∈ V)
    (pz : D p z = true) (xz : D x z ≠ true)
    (rows : ∀ c ∈ U, c ≠ x → t ≤ (outN D U c).card) (row : t ≤ (outN D U x).card + 1)
    (off : z ∉ active D (via D U x p) {x} (spare D U t) (q - 1)) :
    ∃ E : CH.Digraph, QFree E U q ∧ ∀ c ∈ U, t ≤ (outN E U c).card := by
  classical
  refine ⟨_, shortcut_free free hq uv zu pv pz xz off, ?_⟩
  intro c cu
  have keep : outN D U c \ bill D (via D U x p) {x} (spare D U t) c (q - 1) ⊆
      outN (repair (cut D (fun c => bill D (via D U x p) {x} (spare D U t) c (q - 1)))
        {x} (fun _ => {z})) U c := by
    intro y hy
    obtain ⟨old, kept⟩ := mem_sdiff.mp hy
    obtain ⟨yu, cy⟩ := mem_outN.mp old
    exact mem_outN.mpr ⟨yu, repair_old (by simp [cut, cy, kept])⟩
  have paid : (bill D (via D U x p) {x} (spare D U t) c (q - 1)).card ≤ (outN D U c).card - t :=
    affordable D _ _ _ c _
  have left := le_card_sdiff (bill D (via D U x p) {x} (spare D U t) c (q - 1)) (outN D U c)
  by_cases cx : c = x
  · subst cx
    have fresh : z ∉ outN D U c \ bill D (via D U c p) {c} (spare D U t) c (q - 1) :=
      fun h => xz (mem_outN.mp (mem_sdiff.mp h).1).2
    have new : z ∈ outN (repair (cut D (fun y => bill D (via D U c p) {c} (spare D U t) y (q - 1)))
        {c} (fun _ => {z})) U c :=
      mem_outN.mpr ⟨zu, repair_new (mem_singleton_self _) (mem_singleton_self _)⟩
    have bound := card_le_card (insert_subset new keep)
    rw [card_insert_of_notMem fresh] at bound
    omega
  · have bound := card_le_card keep
    have deg := rows c cu cx
    omega

/-- With no unpaid parent, the cascade of `x` on `via` never leaves `x`. -/
theorem clean_active
    (clean : ∀ y ∈ U, D y x = true → D y p ≠ true → t < (outN D U y).card) (k : ℕ) :
    active D (via D U x p) {x} (spare D U t) k = {x} := by
  induction k with
  | zero => rfl
  | succ k ih =>
    unfold active
    rw [ih]
    refine union_eq_left.mpr (fun y hy => ?_)
    obtain ⟨yw, rich⟩ := mem_filter.mp hy
    rw [mem_singleton]
    by_contra yx
    obtain ⟨yu, shape⟩ := mem_via.mp yw
    have yp : D y p ≠ true := by
      rcases shape with h | h
      · exact absurd h yx
      · exact h.1
    have small : (outN D {x} y).card ≤ 1 := (card_le_card outN_subset).trans (by simp)
    have arc : D y x = true := by
      by_contra no
      have empty : outN D {x} y = ∅ := by
        ext w
        simp only [mem_outN, mem_singleton, notMem_empty, iff_false, not_and]
        rintro rfl
        exact no
      rw [empty] at rich
      simp at rich
    have pays := clean y yu arc yp
    unfold spare at rich
    omega

/-- **Host when every unpaid parent of `x` points to `p`.** Then any head `z` of `p` that `x`
misses is a safe shortcut: only parents of `x` with spare are cut, once each. -/
theorem clean_parent_host (free : QFree D V q) (hq : 2 ≤ q) (uv : U ⊆ V) (xu : x ∈ U) (zu : z ∈ U)
    (pv : p ∈ V) (xp : D x p = true) (pz : D p z = true) (xz : D x z ≠ true)
    (rows : ∀ c ∈ U, c ≠ x → t ≤ (outN D U c).card) (row : t ≤ (outN D U x).card + 1)
    (clean : ∀ y ∈ U, D y x = true → D y p ≠ true → t < (outN D U y).card) :
    ∃ E : CH.Digraph, QFree E U q ∧ ∀ c ∈ U, t ≤ (outN E U c).card := by
  apply shortcut_host free hq uv zu pv pz xz rows row
  rw [clean_active clean, mem_singleton]
  exact target_ne free hq (uv xu) pv xp pz

/-- A shortcut through `p` is never blocked before the last step of the cascade. -/
theorem early_inactive {W : Finset ℕ} {e : ℕ → ℕ} (free : QFree D V q) (wv : W ⊆ V) (xw : x ∈ W)
    (pv : p ∈ V) (zv : z ∈ V) (xp : D x p = true) (pz : D p z = true) {k : ℕ} (early : k + 2 ≤ q) :
    z ∉ active D W {x} e k := by
  intro act
  obtain ⟨x', hx', l, lk, path⟩ := robust D W {x} e (singleton_subset_iff.mpr xw) act (fun _ => ∅)
    (by simp)
  rw [mem_singleton] at hx'
  subst hx'
  have native : Walk D V z x' l :=
    (walk_sub (fun _ _ h => (Bool.and_eq_true_iff.mp h).1) path).mono wv
  exact free x' (l + 1 + 1) (by omega) (by omega) (.step pv xp (.step zv pz native))

/-- A blocked shortcut has more first hops on the cascade at horizon `q-2` than its spare. -/
theorem first_hops {W : Finset ℕ} {e : ℕ → ℕ} (free : QFree D V q) (hq : 2 ≤ q) (wv : W ⊆ V)
    (xw : x ∈ W) (pv : p ∈ V) (zv : z ∈ V) (xp : D x p = true) (pz : D p z = true)
    (on : z ∈ active D W {x} e (q - 1)) :
    e z < (outN D (active D W {x} e (q - 2)) z).card := by
  rw [show q - 1 = (q - 2) + 1 by omega] at on
  obtain old | new := mem_union.mp on
  · exact (early_inactive free wv xw pv zv xp pz (by omega) old).elim
  · exact (mem_filter.mp new).2

/-- **The surviving return.** If the shortcut `x → z` through `p` is blocked, there is an actual
return `z ⇝ y → x` of exactly `q-1` arcs inside `via` whose last tail `y` has no spare. It does not
point to `p`, so the head it lost is another erased label. -/
theorem unpaid_return (free : QFree D V q) (hq : 2 ≤ q) (uv : U ⊆ V) (xu : x ∈ U) (zu : z ∈ U)
    (pv : p ∈ V) (xp : D x p = true) (pz : D p z = true) (xz : D x z ≠ true)
    (on : z ∈ active D (via D U x p) {x} (spare D U t) (q - 1)) :
    ∃ y ∈ U, y ≠ x ∧ D y x = true ∧ D y p ≠ true ∧ (outN D U y).card ≤ t ∧
      Walk D (via D U x p) z y (q - 2) := by
  classical
  let C : ℕ → Finset ℕ := fun c => if D c x = true ∧ 0 < spare D U t c then {x} else ∅
  have budget : ∀ c ∈ via D U x p, (C c).card ≤ spare D U t c := by
    intro c _
    simp only [C]
    split_ifs with h
    · rw [card_singleton]
      exact h.2
    · simp
  have xw : x ∈ via D U x p := mem_via.mpr ⟨xu, Or.inl rfl⟩
  have zw := target_mem_via free hq uv zu pv pz xz
  have zx := target_ne free hq (uv xu) pv xp pz
  obtain ⟨x', hx', l, lk, path⟩ := robust D _ {x} (spare D U t) (singleton_subset_iff.mpr xw) on C
    budget
  rw [mem_singleton] at hx'
  subst hx'
  obtain ⟨y, k, len, wy, last⟩ := last_arc path (pos_of_ne path zx)
  obtain ⟨arc, kept⟩ := Bool.and_eq_true_iff.mp last
  have yw : y ∈ via D U x' p := end_mem wy zw
  have native : Walk D (via D U x' p) z y k :=
    walk_sub (fun _ _ h => (Bool.and_eq_true_iff.mp h).1) wy
  have yx : y ≠ x' := by
    rintro rfl
    exact loopfree free (by omega) (uv xu) arc
  obtain ⟨yu, shape⟩ := mem_via.mp yw
  have yp : D y p ≠ true := by
    rcases shape with h | h
    · exact absurd h yx
    · exact h.1
  have none : (outN D U y).card ≤ t := by
    by_contra big
    have h : D y x' = true ∧ 0 < spare D U t y := ⟨arc, by unfold spare; omega⟩
    have billed : x' ∈ C y := by
      simp only [C]
      split_ifs
      exact mem_singleton_self _
    exact (of_decide_eq_true kept) billed
  have long : q ≤ k + 2 := by
    by_contra short
    exact free x' (k + 1 + 1 + 1) (by omega) (by omega)
      (.step pv xp (.step (uv zu) pz ((native.mono (via_subset.trans uv)).snoc (uv xu) arc)))
  have exact : k = q - 2 := by omega
  exact ⟨y, yu, yx, arc, yp, none, exact ▸ native⟩

/-- A row that kept at most `t` heads, had more than `t`, and does not point to `p` lost a head
to an erased label other than `p`. -/
theorem lost_other_label {B : Finset ℕ} {y : ℕ} (low : (outN D (V \ B) y).card ≤ t)
    (high : t < (outN D V y).card) (yp : D y p ≠ true) : ∃ h ∈ B, h ≠ p ∧ D y h = true := by
  by_contra none
  push Not at none
  have sub : outN D V y ⊆ outN D (V \ B) y := by
    intro h hh
    obtain ⟨hv, yh⟩ := mem_outN.mp hh
    refine mem_outN.mpr ⟨mem_sdiff.mpr ⟨hv, fun hb => ?_⟩, yh⟩
    exact none h hb (fun eq => yp (eq ▸ yh)) yh
  have := card_le_card sub
  omega

/-- **A candidate exists.** If `x → p`, the row `x` has no more heads than `p`, and every erased
head of `p` is a head of `x`, then `p` has a surviving head that `x` misses. On the marked chain
both rows have exactly `r` heads. -/
theorem candidate_exists {B : Finset ℕ} (free : QFree D V q) (hq : 1 ≤ q) (pv : p ∈ V)
    (xp : D x p = true) (size : (outN D V x).card ≤ (outN D V p).card)
    (erased : ∀ h ∈ B, D p h = true → D x h = true) :
    ∃ z ∈ V \ B, D p z = true ∧ D x z ≠ true := by
  by_contra none
  push Not at none
  have sub : outN D V p ⊆ (outN D V x).erase p := by
    intro z hz
    obtain ⟨zv, pz⟩ := mem_outN.mp hz
    refine mem_erase.mpr ⟨fun eq => loopfree free hq pv (eq ▸ pz), mem_outN.mpr ⟨zv, ?_⟩⟩
    by_cases zb : z ∈ B
    · exact erased z zb pz
    · exact none z (mem_sdiff.mpr ⟨zv, zb⟩) pz
  have bound := card_le_card sub
  rw [card_erase_of_mem (mem_outN.mpr ⟨pv, xp⟩)] at bound
  have pos := card_pos.mpr (show (outN D V x).Nonempty from ⟨p, mem_outN.mpr ⟨pv, xp⟩⟩)
  omega

/-- **Lone short row, shortcut through an erased parent.** No lower-degree host exists; the bank
meets the size budget; `x` is the only surviving row below `t`, by one; `x → p → z` with `z`
surviving and `x ↛ z`. Then `z` enters the cascade of `x` exactly at step `q-1`, it has more
first hops on the cascade than its spare, and an actual return `z ⇝ y → x` of exactly `q-1` arcs
ends at a parent `y` of `x` with no spare that does not point to `p`. -/
theorem lone_row_law {B : Finset ℕ} (free : QFree D V q) (hq : 2 ≤ q) (none : NoHost q t)
    (hB : B ⊆ V) (size : V.card - q * t ≤ B.card) (xu : x ∈ V \ B) (zu : z ∈ V \ B)
    (pv : p ∈ V) (xp : D x p = true) (pz : D p z = true) (xz : D x z ≠ true)
    (rows : ∀ c ∈ V \ B, c ≠ x → t ≤ (outN D (V \ B) c).card)
    (row : t ≤ (outN D (V \ B) x).card + 1) :
    z ∈ active D (via D (V \ B) x p) {x} (spare D (V \ B) t) (q - 1) ∧
    z ∉ active D (via D (V \ B) x p) {x} (spare D (V \ B) t) (q - 2) ∧
    spare D (V \ B) t z <
      (outN D (active D (via D (V \ B) x p) {x} (spare D (V \ B) t) (q - 2)) z).card ∧
    ∃ y ∈ V \ B, y ≠ x ∧ D y x = true ∧ D y p ≠ true ∧ (outN D (V \ B) y).card = t ∧
      Walk D (via D (V \ B) x p) z y (q - 2) := by
  have uv : V \ B ⊆ V := sdiff_subset
  have xw : x ∈ via D (V \ B) x p := mem_via.mpr ⟨xu, Or.inl rfl⟩
  have wv : via D (V \ B) x p ⊆ V := via_subset.trans uv
  have on : z ∈ active D (via D (V \ B) x p) {x} (spare D (V \ B) t) (q - 1) := by
    by_contra off
    obtain ⟨E, efree, deg⟩ := shortcut_host free hq uv zu pv pz xz rows row off
    have count := card_sdiff_add_card_eq_card hB
    exact none E (V \ B) ⟨x, xu⟩ (by omega) efree deg
  obtain ⟨y, yu, yx, arc, yp, low, ret⟩ := unpaid_return free hq uv xu zu pv xp pz xz on
  exact ⟨on, early_inactive free wv xw pv (uv zu) xp pz (by omega),
    first_hops free hq wv xw pv (uv zu) xp pz on,
    y, yu, yx, arc, yp, le_antisymm low (rows y yu yx), ret⟩

end shortcut

/-- **Forced row for any bank.** No lower-degree host exists and the bank meets the size budget.
Let `P` be the surviving rows below `t` and `A` the active cascade of `P` at horizon `q-1` with the
spare budgets. Some row of `P` has fewer surviving non-heads outside `A` than it is short. -/
theorem forced_row {D : CH.Digraph} {V B : Finset ℕ} {q t : ℕ} (free : QFree D V q)
    (none : NoHost q t) (hB : B ⊆ V) (size : V.card - q * t ≤ B.card) (hU : (V \ B).Nonempty) :
    ∃ u ∈ V \ B, (outN D (V \ B) u).card < t ∧
      (((V \ B) \ active D (V \ B) ((V \ B).filter (fun c => (outN D (V \ B) c).card < t))
        (spare D (V \ B) t) (q - 1)).filter (fun z => D u z ≠ true)).card +
        (outN D (V \ B) u).card < t := by
  classical
  obtain ⟨U, hUdef⟩ : ∃ U, U = V \ B := ⟨_, rfl⟩
  rw [← hUdef] at hU ⊢
  obtain ⟨P, hP⟩ : ∃ P, P = U.filter (fun c => (outN D U c).card < t) := ⟨_, rfl⟩
  rw [← hP]
  have memP : ∀ c, c ∈ P ↔ c ∈ U ∧ (outN D U c).card < t := by
    intro c; rw [hP]; exact mem_filter
  obtain ⟨A, hA⟩ : ∃ A, A = active D U P (spare D U t) (q - 1) := ⟨_, rfl⟩
  rw [← hA]
  by_contra bad
  push Not at bad
  have ex : ∀ u, ∃ T : Finset ℕ, u ∈ P →
      T ⊆ (U \ A).filter (fun z => D u z ≠ true) ∧ T.card = t - (outN D U u).card := by
    intro u
    by_cases h : u ∈ P
    · obtain ⟨uu, low⟩ := (memP u).mp h
      have big := bad u uu low
      obtain ⟨T, hT, hc⟩ := exists_subset_card_eq
        (s := (U \ A).filter (fun z => D u z ≠ true)) (n := t - (outN D U u).card) (by omega)
      exact ⟨T, fun _ => ⟨hT, hc⟩⟩
    · exact ⟨∅, fun h' => absurd h' h⟩
  choose S hS using ex
  obtain ⟨C, hC⟩ : ∃ C : ℕ → Finset ℕ, C = fun c => bill D U P (spare D U t) c (q - 1) := ⟨_, rfl⟩
  have sub : ∀ a b, cut D C a b = true → D a b = true := fun _ _ h => (Bool.and_eq_true_iff.mp h).1
  have uv : U ⊆ V := hUdef ▸ sdiff_subset
  have kfree : QFree (cut D C) U q := fun a l h1 h2 w => free a l h1 h2 ((walk_sub sub w).mono uv)
  have safe : QFree (repair (cut D C) P S) U q := by
    apply repair_qfree kfree
    intro u hu z hz u' hu' m hm walk
    obtain ⟨zin, _⟩ := mem_filter.mp ((hS u hu).1 hz)
    obtain ⟨zu, zoff⟩ := mem_sdiff.mp zin
    rw [hC] at walk
    exact zoff (hA ▸ active_mono D U P _ (by omega : m ≤ q - 1)
      (sound_cut D U P _ zu hu' (by omega) walk))
  have count := card_sdiff_add_card_eq_card hB
  rw [← hUdef] at count
  refine none (repair (cut D C) P S) U hU (by omega) safe ?_
  intro c cu
  have paid : (C c).card ≤ (outN D U c).card - t := by
    rw [hC]; exact affordable D U P _ c _
  have keep : outN D U c \ C c ⊆ outN (repair (cut D C) P S) U c := by
    intro y hy
    obtain ⟨old, kept⟩ := mem_sdiff.mp hy
    obtain ⟨yu, cy⟩ := mem_outN.mp old
    exact mem_outN.mpr ⟨yu, repair_old (by simp [cut, cy, kept])⟩
  have left := le_card_sdiff (C c) (outN D U c)
  by_cases cp : c ∈ P
  · obtain ⟨into, size'⟩ := hS c cp
    have new : S c ⊆ outN (repair (cut D C) P S) U c := by
      intro z hz
      obtain ⟨zin, _⟩ := mem_filter.mp (into hz)
      exact mem_outN.mpr ⟨(mem_sdiff.mp zin).1, repair_new cp hz⟩
    have apart : Disjoint (outN D U c \ C c) (S c) := by
      refine disjoint_left.mpr (fun z old fresh => ?_)
      exact (mem_filter.mp (into fresh)).2 (mem_outN.mp (mem_sdiff.mp old).1).2
    have bound := card_le_card (union_subset keep new)
    rw [card_union_of_disjoint apart, size'] at bound
    have low := ((memP c).mp cp).2
    omega
  · have high : ¬ (outN D U c).card < t := fun h => cp ((memP c).mpr ⟨cu, h⟩)
    have bound := card_le_card keep
    omega

/-- **Cut budget.** Over the survivors `U`, total spare plus arcs lost to the erased labels plus
`|U| t` equals the total native degree plus the total shortage. -/
theorem cut_budget {D : CH.Digraph} {V U : Finset ℕ} {t : ℕ} (uv : U ⊆ V) :
    (∑ c ∈ U, spare D U t c) + (∑ c ∈ U, (outN D (V \ U) c).card) + U.card * t =
      (∑ c ∈ U, (outN D V c).card) + ∑ c ∈ U, (t - (outN D U c).card) := by
  classical
  have key : ∀ c ∈ U, spare D U t c + (outN D (V \ U) c).card + t =
      (outN D V c).card + (t - (outN D U c).card) := by
    intro c _
    have inner : outN D U c ⊆ outN D V c :=
      fun y hy => mem_outN.mpr ⟨uv (outN_subset hy), (mem_outN.mp hy).2⟩
    have outside : outN D V c \ outN D U c = outN D (V \ U) c := by
      ext y
      simp only [mem_sdiff, mem_outN]
      tauto
    have split := card_sdiff_add_card_eq_card inner
    rw [outside] at split
    unfold spare
    omega
  have total := sum_congr rfl key
  simp only [sum_add_distrib, sum_const, smul_eq_mul] at total
  exact total

/-- **The law on the marked chain of a native source.** Take the chain and its bypass supply from
the packing theorem. For every bank meeting the size budget in which the grandparent
`x = v (i+2)` is the only surviving row below `r-1`, by one, and for every surviving head `z` of
the chain parent `p = v (i+1)` that `x` misses, an actual return `z ⇝ y → x` of exactly `q-1` arcs
ends at a parent `y` of `x` that kept exactly `r-1` heads, does not point to `p`, and lost a head
to another erased label. -/
theorem native_first_attack {q r : ℕ} (X : ShenMinimumOrder.Source q r) (hq : 2 ≤ q) (hr : 2 ≤ r)
    (order : X.V.card ≤ q * r) (none : NoHost q (r - 1)) {u : ℕ} (uv : u ∈ X.V) :
    ∃ v : ℕ → ℕ, v 0 = u ∧ (∀ i, v i ∈ X.V) ∧
      (∀ i, X.D (v (i + 1)) (v i) = true ∧ (outN X.D X.V (v (i + 1))).card = r ∧
        RemoteParentPacking.missed X.D X.V q (v i) ⊆ outN X.D X.V (v (i + 1))) ∧
      (∀ a, r ≤ ∑ i ∈ range (q + 1),
        (outN X.D X.V (v (a + i + 1)) \ RemoteParentPacking.missed X.D X.V q (v (a + i))).card) ∧
      ∀ (B : Finset ℕ) (i z : ℕ), B ⊆ X.V → X.V.card - q * (r - 1) ≤ B.card →
        v (i + 2) ∈ X.V \ B → z ∈ X.V \ B →
        (∀ c ∈ X.V \ B, c ≠ v (i + 2) → r - 1 ≤ (outN X.D (X.V \ B) c).card) →
        r - 1 ≤ (outN X.D (X.V \ B) (v (i + 2))).card + 1 →
        X.D (v (i + 1)) z = true → X.D (v (i + 2)) z ≠ true →
        ∃ y ∈ X.V \ B, y ≠ v (i + 2) ∧ X.D y (v (i + 2)) = true ∧ X.D y (v (i + 1)) ≠ true ∧
          (outN X.D (X.V \ B) y).card = r - 1 ∧
          (∃ h ∈ B, h ≠ v (i + 1) ∧ X.D y h = true) ∧
          Walk X.D (via X.D (X.V \ B) (v (i + 2)) (v (i + 1))) z y (q - 2) := by
  obtain ⟨v, first, live, steps, supply⟩ := RemoteParentPacking.every_window X hq (by omega) order uv
  refine ⟨v, first, live, steps, supply, ?_⟩
  intro B i z hB size xu zu rows row pz xz
  obtain ⟨_, _, _, y, yu, yx, arc, yp, exact, ret⟩ :=
    lone_row_law X.free hq none hB size xu zu (live (i + 1)) (steps (i + 1)).1 pz xz rows row
  have high : r - 1 < (outN X.D X.V y).card := by
    have := X.degree y (mem_sdiff.mp yu).1
    omega
  exact ⟨y, yu, yx, arc, yp, exact, lost_other_label exact.le high yp, ret⟩

#print axioms descent_stuck
#print axioms shortcut_iff
#print axioms shortcut_host
#print axioms clean_parent_host
#print axioms unpaid_return
#print axioms candidate_exists
#print axioms lone_row_law
#print axioms forced_row
#print axioms cut_budget
#print axioms native_first_attack
end LeanCH.BR.BypassRepair
