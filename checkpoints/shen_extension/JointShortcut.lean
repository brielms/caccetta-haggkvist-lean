import checkpoints.shen_extension.BypassBankReplay

/-!
# Several short rows paying together: the exact test on arc labels

Lean 4.35.0. Standalone; nothing shared is edited.

State: a retained graph `K` on the survivors `U` (in the descent `K = cut D C` for one fixed cut)
and a finite family `F` of new arcs, each kept as the ordered pair of its own tail and head.

* `Trail K U F i k c`: a walk in the transition graph on arc labels. One transition `i → j` is an
  old walk in `K[U]` from the head of `i` to the tail of `j`, of `d ≥ 0` arcs, and costs `d + 1`.
* `install_iff`: installing `F` is safe exactly when `K` is safe and no label has a nonempty
  closed trail of total cost at most `q`. `Trail.cyclic` turns a trail into an indexed list.
* `pair_iff`, `one_way`: the two-label test. Own returns need `q` arcs; the two cross returns only
  need `q - 1` arcs together. A short cross return in one direction alone forbids nothing.
* `ranked_safe`: for any ranking of the labels, a new head has to avoid its own tail (`q-1` arcs)
  and the tails ranked at or below it (`q-2` arcs). Walks to higher tails are free.
* `kin_iff`: if every tail points to the parent of every label ranked at or above it, the family
  is safe exactly when no label has an own return of exactly `q-1` arcs.
* `joint_host`, `bank_exit`: a paid family on a bank gives the lower-quota host.
* `joint_cycle`, `joint_cycle_list`, `ranked_row`, `common_parent_row`: what `NoHost` forces for
  every cut and every paying family.
* `last_step_row`: the joint cascade of `forced_row` guards one step too far; the law with the
  larger set of usable heads.
* `residual_debt`: after a safe partial repair the rows still unpaid obey the forced-row law in
  the repaired graph.
* `joint_blocked`: the same on a marked cell with a second short row.
* `band_all`, `band_row`, `band_unpaid`: at order `q (r-1) + 2` every short row points to both
  erased labels, so short rows never block each other; the obstruction is an own return of exactly
  `q-1` arcs, and its last tail is a surviving parent with fewer spare heads than short heads.
-/

set_option linter.style.longLine false

namespace LeanCH.BR.JointShortcut
open Finset BRq2 BRq3 FundedCascade BypassRepair BypassBankReplay

/-- A new arc, kept as the ordered pair of its own tail and head. -/
abbrev Arc := ℕ × ℕ

/-- `K` together with the arcs of `F`. -/
def install (K : CH.Digraph) (F : Finset Arc) : CH.Digraph :=
  fun a b => K a b || decide ((a, b) ∈ F)

/-- The heads that `F` adds at the row `u`. -/
def newHeads (F : Finset Arc) (u : ℕ) : Finset ℕ := (F.filter (fun j => j.1 = u)).image Prod.snd

/-- A walk in the transition graph on the labels of `F`, with its total cost. -/
inductive Trail (K : CH.Digraph) (U : Finset ℕ) (F : Finset Arc) : Arc → Arc → ℕ → Prop
  | refl (i : Arc) : Trail K U F i i 0
  | step {i j k : Arc} {d c : ℕ} : j ∈ F → Walk K U i.2 j.1 d → Trail K U F j k c →
      Trail K U F i k (d + 1 + c)

section basic
variable {K : CH.Digraph} {U : Finset ℕ} {F : Finset Arc}

theorem install_old {a b : ℕ} (h : K a b = true) : install K F a b = true := by
  simp [install, h]

theorem install_new {a b : ℕ} (h : (a, b) ∈ F) : install K F a b = true := by
  simp [install, h]

theorem install_cases {a b : ℕ} (h : install K F a b = true) : K a b = true ∨ (a, b) ∈ F := by
  simp only [install, Bool.or_eq_true, decide_eq_true_eq] at h
  exact h

theorem mem_newHeads {u z : ℕ} : z ∈ newHeads F u ↔ (u, z) ∈ F := by
  simp only [newHeads, mem_image, mem_filter]
  constructor
  · rintro ⟨j, ⟨jF, rfl⟩, rfl⟩
    exact jF
  · intro h
    exact ⟨(u, z), ⟨h, rfl⟩, rfl⟩

/-- The row-indexed repair of `DeleteRepairUnlock` is the installation of its labelled arcs. -/
theorem repair_eq_install (K : CH.Digraph) (P : Finset ℕ) (S : ℕ → Finset ℕ) :
    DeleteRepair.repair K P S = install K (P.biUnion (fun u => (S u).image (Prod.mk u))) := by
  funext a b
  have mem : (a, b) ∈ P.biUnion (fun u => (S u).image (Prod.mk u)) ↔ a ∈ P ∧ b ∈ S a := by
    simp only [mem_biUnion, mem_image, Prod.mk.injEq]
    constructor
    · rintro ⟨u, uP, z, zS, rfl, rfl⟩
      exact ⟨uP, zS⟩
    · rintro ⟨aP, bS⟩
      exact ⟨a, aP, b, bS, rfl, rfl⟩
  simp only [DeleteRepair.repair, install, mem, Bool.decide_and]

theorem cut_sub {D : CH.Digraph} {C : ℕ → Finset ℕ} (a b : ℕ) (h : cut D C a b = true) :
    D a b = true := (Bool.and_eq_true_iff.mp h).1

namespace Trail

theorem eq_of_zero {i k : Arc} {c : ℕ} (tr : Trail K U F i k c) (zero : c = 0) : i = k := by
  cases tr with
  | refl => rfl
  | step _ _ _ => omega

theorem last_mem {i k : Arc} {c : ℕ} (tr : Trail K U F i k c) (iF : i ∈ F) : k ∈ F := by
  induction tr with
  | refl => exact iF
  | step jF _ _ ih => exact ih jF

/-- A trail is a walk of the installed graph from the first head to the last head. -/
theorem walk (inU : ∀ j ∈ F, j.2 ∈ U) {i k : Arc} {c : ℕ} (tr : Trail K U F i k c) :
    Walk (install K F) U i.2 k.2 c := by
  induction tr with
  | refl => exact .refl _
  | @step i j k d c jF w _ ih =>
    have lifted : Walk (install K F) U i.2 j.1 d := walk_sub (fun _ _ h => install_old h) w
    have go := lifted.append (Walk.step (inU j jF) (install_new (show (j.1, j.2) ∈ F from jF)) ih)
    rwa [show d + (c + 1) = d + 1 + c by omega] at go

/-- A trail as an indexed list of labels with the old walks between them. -/
theorem cyclic {i k : Arc} {c : ℕ} (tr : Trail K U F i k c) :
    ∃ (n : ℕ) (lab : ℕ → Arc) (len : ℕ → ℕ), lab 0 = i ∧ lab n = k ∧
      (∀ l < n, lab (l + 1) ∈ F ∧ Walk K U (lab l).2 (lab (l + 1)).1 (len l)) ∧
      ∑ l ∈ range n, (len l + 1) = c := by
  induction tr with
  | refl i =>
    exact ⟨0, fun _ => i, fun _ => 0, rfl, rfl, fun l hl => absurd hl (Nat.not_lt_zero _), by simp⟩
  | @step i j k d c jF w _ ih =>
    obtain ⟨n, lab, len, l0, ln, steps, sum⟩ := ih
    refine ⟨n + 1, fun l => if l = 0 then i else lab (l - 1),
      fun l => if l = 0 then d else len (l - 1), by simp, by simp [ln], ?_, ?_⟩
    · intro l hl
      rcases Nat.eq_zero_or_pos l with rfl | pos
      · simpa [l0] using And.intro jF w
      · obtain ⟨m, rfl⟩ : ∃ m, l = m + 1 := ⟨l - 1, by omega⟩
        simpa using steps m (by omega)
    · have e : ∀ l ∈ range n, ((if l + 1 = 0 then d else len (l + 1 - 1)) + 1) = len l + 1 := by
        intro l _
        simp
      rw [Finset.sum_range_succ', Finset.sum_congr rfl e, sum]
      simp
      omega

/-- **A closed trail has a step that does not go up.** For any ranking, a nonempty trail whose
last label is ranked at or below its first contains a transition `j → j'` with `j'` ranked at or
below `j`. That transition is the whole trail or leaves at least one more unit of cost. -/
theorem descent (ρ : Arc → ℕ) {i k : Arc} {c : ℕ} (tr : Trail K U F i k c) :
    i ∈ F → ρ k ≤ ρ i → 0 < c →
    ∃ j ∈ F, ∃ j' ∈ F, ∃ d, Walk K U j.2 j'.1 d ∧ ρ j' ≤ ρ j ∧
      (d + 2 ≤ c ∨ (j = i ∧ j' = k ∧ d + 1 = c)) := by
  induction tr with
  | refl => intro _ _ pos; omega
  | @step i j k d c jF w tr ih =>
    intro iF down _
    by_cases level : ρ j ≤ ρ i
    · refine ⟨i, iF, j, jF, d, w, level, ?_⟩
      rcases Nat.eq_zero_or_pos c with zero | pos
      · exact Or.inr ⟨rfl, tr.eq_of_zero zero, by omega⟩
      · exact Or.inl (by omega)
    · have pos : 0 < c := by
        rcases Nat.eq_zero_or_pos c with zero | pos
        · have same := tr.eq_of_zero zero
          rw [same] at level
          exact absurd down level
        · exact pos
      obtain ⟨a, aF, a', aF', e, path, order, far⟩ := ih jF (by omega) pos
      refine ⟨a, aF, a', aF', e, path, order, Or.inl ?_⟩
      rcases far with h | ⟨_, _, h⟩ <;> omega

end Trail

/-- A walk of the installed graph is old, or splits at its first and last new arcs. -/
theorem split {a b ℓ : ℕ} (w : Walk (install K F) U a b ℓ) :
    Walk K U a b ℓ ∨ ∃ j ∈ F, ∃ k d c e, Walk K U a j.1 d ∧ Trail K U F j k c ∧
      Walk K U k.2 b e ∧ d + 1 + c + e = ℓ := by
  induction w with
  | refl a => exact Or.inl (.refl a)
  | @step a b c n hb hab _ ih =>
    rcases install_cases hab with old | new
    · rcases ih with h | ⟨j, jF, k, d, c', e, w1, tr, w2, sum⟩
      · exact Or.inl (.step hb old h)
      · exact Or.inr ⟨j, jF, k, d + 1, c', e, .step hb old w1, tr, w2, by omega⟩
    · rcases ih with h | ⟨j, jF, k, d, c', e, w1, tr, w2, sum⟩
      · exact Or.inr ⟨(a, b), new, (a, b), 0, 0, n, .refl a, .refl _, h, by omega⟩
      · exact Or.inr ⟨(a, b), new, k, 0, d + 1 + c', e, .refl a, .step jF w1 tr, w2, by omega⟩

/-- **Exact test for a family on one retained graph.** With every new head on the carrier,
installing `F` is `q`-free exactly when `K` is `q`-free and no label of `F` has a nonempty closed
trail of total cost at most `q`. Both directions keep the labels of the arcs. -/
theorem install_iff {q : ℕ} (inU : ∀ j ∈ F, j.2 ∈ U) :
    QFree (install K F) U q ↔
      QFree K U q ∧ ∀ i ∈ F, ∀ c, 0 < c → c ≤ q → ¬ Trail K U F i i c := by
  constructor
  · intro safe
    exact ⟨fun a l h1 h2 w => safe a l h1 h2 (walk_sub (fun _ _ h => install_old h) w),
      fun i _ c pos le tr => safe i.2 c pos le (tr.walk inU)⟩
  · rintro ⟨old, none⟩ a l h1 h2 w
    rcases split w with h | ⟨j, jF, k, d, c, e, w1, tr, w2, sum⟩
    · exact old a l h1 h2 h
    · exact none k (tr.last_mem jF) (e + d + 1 + c) (by omega) (by omega)
        (.step jF (w2.append w1) tr)

private theorem pair_other {α : Type} [DecidableEq α] {a b x y : α} (hx : x ∈ ({a, b} : Finset α))
    (hy : y ∈ ({a, b} : Finset α)) (ne : y ≠ x) : (x = a ∧ y = b) ∨ (x = b ∧ y = a) := by
  simp only [mem_insert, mem_singleton] at hx hy
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · exact absurd (hy.trans hx.symm) ne
  · exact Or.inl ⟨hx, hy⟩
  · exact Or.inr ⟨hx, hy⟩
  · exact absurd (hy.trans hx.symm) ne

/-- **Two labels.** The pair is safe exactly when `K` is safe, neither head returns to its own
tail within `q-1` arcs, and the two cross returns have at least `q-1` arcs together. -/
theorem pair_iff {q : ℕ} {e₁ e₂ : Arc} (h₁ : e₁.2 ∈ U) (h₂ : e₂.2 ∈ U) :
    QFree (install K {e₁, e₂}) U q ↔ QFree K U q ∧
      (∀ d, d + 1 ≤ q → ¬ Walk K U e₁.2 e₁.1 d) ∧ (∀ d, d + 1 ≤ q → ¬ Walk K U e₂.2 e₂.1 d) ∧
      ∀ a b, a + b + 2 ≤ q → Walk K U e₁.2 e₂.1 a → ¬ Walk K U e₂.2 e₁.1 b := by
  have inU : ∀ j ∈ ({e₁, e₂} : Finset Arc), j.2 ∈ U := by
    intro j hj
    rcases mem_insert.mp hj with rfl | hj
    · exact h₁
    · rw [mem_singleton.mp hj]; exact h₂
  have m₁ : e₁ ∈ ({e₁, e₂} : Finset Arc) := mem_insert_self _ _
  have m₂ : e₂ ∈ ({e₁, e₂} : Finset Arc) := mem_insert_of_mem (mem_singleton_self _)
  rw [install_iff inU]
  constructor
  · rintro ⟨old, none⟩
    refine ⟨old, fun d le w => ?_, fun d le w => ?_, fun a b le w w' => ?_⟩
    · exact none e₁ m₁ (d + 1 + 0) (by omega) (by omega) (.step m₁ w (.refl _))
    · exact none e₂ m₂ (d + 1 + 0) (by omega) (by omega) (.step m₂ w (.refl _))
    · exact none e₁ m₁ (a + 1 + (b + 1 + 0)) (by omega) (by omega)
        (.step m₂ w (.step m₁ w' (.refl _)))
  · rintro ⟨old, own₁, own₂, cross⟩
    have own : ∀ j ∈ ({e₁, e₂} : Finset Arc), ∀ d, d + 1 ≤ q → ¬ Walk K U j.2 j.1 d := by
      intro j hj
      rcases mem_insert.mp hj with rfl | hj
      · exact own₁
      · rw [mem_singleton.mp hj]; exact own₂
    refine ⟨old, ?_⟩
    intro i iF c pos le tr
    cases tr with
    | refl => omega
    | @step _ j _ d c' jF w tr' =>
      by_cases same : j = i
      · subst same
        exact own j jF d (by omega) w
      · cases tr' with
        | refl => exact same rfl
        | @step _ j' _ d' c'' jF' w' tr'' =>
          by_cases back : j' = j
          · subst back
            exact own j' jF d' (by omega) w'
          · rcases pair_other iF jF same with ⟨ia, jb⟩ | ⟨ib, ja⟩
            · have third : j' = e₁ := by
                rcases pair_other jF jF' back with ⟨_, h⟩ | ⟨_, h⟩
                · exact absurd (h.trans jb.symm) back
                · exact h
              subst ia jb
              rw [third] at w'
              exact cross d d' (by omega) w w'
            · have third : j' = e₂ := by
                rcases pair_other jF jF' back with ⟨_, h⟩ | ⟨_, h⟩
                · exact h
                · exact absurd (h.trans ja.symm) back
              subst ib ja
              rw [third] at w'
              exact cross d' d (by omega) w' w

/-- **One direction alone forbids nothing.** If both own tests pass and the second head has no
walk of at most `q-2` arcs to the first tail, the pair is safe, whatever leads from the first head
to the second tail. -/
theorem one_way {q : ℕ} {e₁ e₂ : Arc} (h₁ : e₁.2 ∈ U) (h₂ : e₂.2 ∈ U) (old : QFree K U q)
    (own₁ : ∀ d, d + 1 ≤ q → ¬ Walk K U e₁.2 e₁.1 d)
    (own₂ : ∀ d, d + 1 ≤ q → ¬ Walk K U e₂.2 e₂.1 d)
    (back : ∀ b, b + 2 ≤ q → ¬ Walk K U e₂.2 e₁.1 b) : QFree (install K {e₁, e₂}) U q :=
  (pair_iff h₁ h₂).mpr ⟨old, own₁, own₂, fun _ b le _ w => back b (by omega) w⟩

/-- **Ranked test.** Rank the labels in any way. A family is safe if each new head has no return
of at most `q-1` arcs to its own tail and no walk of at most `q-2` arcs to a different tail ranked
at or below it. Walks to tails ranked above it are never tested. -/
theorem ranked_safe {q : ℕ} (ρ : Arc → ℕ) (inU : ∀ j ∈ F, j.2 ∈ U) (old : QFree K U q)
    (own : ∀ j ∈ F, ∀ d, d + 1 ≤ q → ¬ Walk K U j.2 j.1 d)
    (down : ∀ j ∈ F, ∀ j' ∈ F, j'.1 ≠ j.1 → ρ j' ≤ ρ j → ∀ d, d + 2 ≤ q → ¬ Walk K U j.2 j'.1 d) :
    QFree (install K F) U q := by
  refine (install_iff inU).mpr ⟨old, fun i iF c pos le tr => ?_⟩
  obtain ⟨j, jF, j', jF', d, w, order, far⟩ := tr.descent ρ iF le_rfl pos
  by_cases same : j'.1 = j.1
  · rw [same] at w
    refine own j jF d ?_ w
    rcases far with h | ⟨_, _, h⟩ <;> omega
  · rcases far with h | ⟨rfl, rfl, _⟩
    · exact down j jF j' jF' same order d (by omega) w
    · exact same rfl

/-- An old walk from a head of `p` to a parent of `p` has at least `q-1` arcs. -/
theorem parent_long {D : CH.Digraph} {V : Finset ℕ} {q p z u d : ℕ} (free : QFree D V q)
    (uv : U ⊆ V) (sub : ∀ a b, K a b = true → D a b = true) (pv : p ∈ V) (zu : z ∈ U)
    (pz : D p z = true) (up : D u p = true) (w : Walk K U z u d) : q ≤ d + 1 := by
  by_contra short
  exact free p (d + 1 + 1) (by omega) (by omega)
    (.step (uv zu) pz (((walk_sub sub w).mono uv).snoc pv up))

/-- **Kin labels never block each other.** `K` is a subgraph of a `q`-free `D` on `V ⊇ U`. Each
label `j` has a parent `par j` in `V` feeding its head, and the tail of every label ranked at or
below `j` points to `par j` (one common erased parent is the case of a constant ranking). Then the
family is safe exactly when no head returns to its own tail in exactly `q-1` arcs of `K`. -/
theorem kin_iff {D : CH.Digraph} {V : Finset ℕ} {q : ℕ} (free : QFree D V q) (hq : 1 ≤ q)
    (uv : U ⊆ V) (sub : ∀ a b, K a b = true → D a b = true) (inU : ∀ j ∈ F, j.2 ∈ U)
    (par : Arc → ℕ) (ρ : Arc → ℕ) (pv : ∀ j ∈ F, par j ∈ V)
    (feeds : ∀ j ∈ F, D (par j) j.2 = true)
    (kin : ∀ j ∈ F, ∀ j' ∈ F, ρ j' ≤ ρ j → D j'.1 (par j) = true) :
    QFree (install K F) U q ↔ ∀ j ∈ F, ¬ Walk K U j.2 j.1 (q - 1) := by
  constructor
  · intro safe j jF w
    have closed : Walk (install K F) U j.2 j.2 (q - 1 + 1) :=
      (walk_sub (fun _ _ h => install_old h) w).snoc (inU j jF)
        (install_new (show (j.1, j.2) ∈ F from jF))
    exact safe j.2 (q - 1 + 1) (by omega) (by omega) closed
  · intro own
    have old : QFree K U q := fun a l h1 h2 w => free a l h1 h2 ((walk_sub sub w).mono uv)
    refine (install_iff inU).mpr ⟨old, fun i iF c pos le tr => ?_⟩
    obtain ⟨j, jF, j', jF', d, w, order, far⟩ := tr.descent ρ iF le_rfl pos
    have long := parent_long free uv sub (pv j jF) (inU j jF) (feeds j jF) (kin j jF j' jF' order) w
    rcases far with h | ⟨rfl, rfl, h⟩
    · omega
    · have exact : d = q - 1 := by omega
      subst exact
      exact own _ jF w

end basic

section host
variable {D : CH.Digraph} {V B U : Finset ℕ} {q t : ℕ} {C : ℕ → Finset ℕ} {F : Finset Arc}

/-- A cut inside the spare budgets together with enough new heads at every short row pays every
row: quota plus actual loss is at most old degree plus new heads. -/
theorem pays_of_spare (budget : ∀ c ∈ U, (C c).card ≤ spare D U t c)
    (cover : ∀ u ∈ U, (outN D U u).card < t → t ≤ (outN D U u).card + (newHeads F u).card) :
    ∀ u ∈ U, t + (outN D U u ∩ C u).card ≤ (outN D U u).card + (newHeads F u).card := by
  intro u uu
  have loss := card_le_card (inter_subset_right : outN D U u ∩ C u ⊆ C u)
  have paid : (C u).card ≤ (outN D U u).card - t := budget u uu
  by_cases low : (outN D U u).card < t
  · have := cover u uu low
    omega
  · omega

/-- **Host from a paid family.** For any cut `C` and any family `F` of arcs absent from `D` with
heads on `U`: if every row satisfies quota + actual loss ≤ old degree + new heads and the installed
graph is `q`-free, it is a `q`-free graph on `U` with minimum outdegree `t`. -/
theorem joint_host (inU : ∀ j ∈ F, j.2 ∈ U) (fresh : ∀ j ∈ F, D j.1 j.2 ≠ true)
    (pays : ∀ u ∈ U, t + (outN D U u ∩ C u).card ≤ (outN D U u).card + (newHeads F u).card)
    (safe : QFree (install (cut D C) F) U q) :
    ∃ E : CH.Digraph, QFree E U q ∧ ∀ c ∈ U, t ≤ (outN E U c).card := by
  classical
  refine ⟨_, safe, fun c cu => ?_⟩
  have keep : (outN D U c \ C c) ∪ newHeads F c ⊆ outN (install (cut D C) F) U c := by
    intro y hy
    rcases mem_union.mp hy with old | new
    · obtain ⟨old, kept⟩ := mem_sdiff.mp old
      obtain ⟨yu, cy⟩ := mem_outN.mp old
      exact mem_outN.mpr ⟨yu, install_old (by simp [cut, cy, kept])⟩
    · have arc := mem_newHeads.mp new
      exact mem_outN.mpr ⟨inU _ arc, install_new arc⟩
  have dis : Disjoint (outN D U c \ C c) (newHeads F c) := disjoint_left.mpr (fun y old new =>
    fresh _ (mem_newHeads.mp new) (mem_outN.mp (mem_sdiff.mp old).1).2)
  have bound := card_le_card keep
  rw [card_union_of_disjoint dis] at bound
  have exact := card_sdiff_add_card_inter (outN D U c) (C c)
  have := pays c cu
  omega

/-- A paid safe family on an eligible bank contradicts `NoHost`. -/
theorem bank_exit (none : NoHost q t) (bank : Eligible V B q t)
    (inU : ∀ j ∈ F, j.2 ∈ V \ B) (fresh : ∀ j ∈ F, D j.1 j.2 ≠ true)
    (pays : ∀ u ∈ V \ B, t + (outN D (V \ B) u ∩ C u).card ≤
      (outN D (V \ B) u).card + (newHeads F u).card)
    (safe : QFree (install (cut D C) F) (V \ B) q) : False := by
  obtain ⟨E, free, deg⟩ := joint_host inU fresh pays safe
  have card := card_sdiff_add_card_eq_card bank.sub
  have size := bank.size
  exact none E _ bank.live (by omega) free deg

/-- **The obstruction for that very cut.** No lower-quota host, an eligible bank, any cut, any
paying family of missing arcs: some label has a nonempty closed trail of cost at most `q` in the
cut graph on the survivors. -/
theorem joint_cycle (free : QFree D V q) (none : NoHost q t) (bank : Eligible V B q t)
    (inU : ∀ j ∈ F, j.2 ∈ V \ B) (fresh : ∀ j ∈ F, D j.1 j.2 ≠ true)
    (pays : ∀ u ∈ V \ B, t + (outN D (V \ B) u ∩ C u).card ≤
      (outN D (V \ B) u).card + (newHeads F u).card) :
    ∃ i ∈ F, ∃ c, 0 < c ∧ c ≤ q ∧ Trail (cut D C) (V \ B) F i i c := by
  by_contra clear
  push Not at clear
  have old : QFree (cut D C) (V \ B) q :=
    fun a l h1 h2 w => free a l h1 h2 ((walk_sub cut_sub w).mono sdiff_subset)
  exact bank_exit none bank inU fresh pays
    ((install_iff inU).mpr ⟨old, fun i iF c pos le tr => clear i iF c pos le tr⟩)

/-- The same obstruction as a cyclic list: labels `lab 0, …, lab n = lab 0` of `F`, an old walk of
`len l` arcs of the cut graph from the head of `lab l` to the tail of `lab (l+1)`, and the common
budget `Σ (len l + 1) ≤ q`. -/
theorem joint_cycle_list (free : QFree D V q) (none : NoHost q t) (bank : Eligible V B q t)
    (inU : ∀ j ∈ F, j.2 ∈ V \ B) (fresh : ∀ j ∈ F, D j.1 j.2 ≠ true)
    (pays : ∀ u ∈ V \ B, t + (outN D (V \ B) u ∩ C u).card ≤
      (outN D (V \ B) u).card + (newHeads F u).card) :
    ∃ (n : ℕ) (lab : ℕ → Arc) (len : ℕ → ℕ), 0 < n ∧ lab n = lab 0 ∧ (∀ l ≤ n, lab l ∈ F) ∧
      (∀ l < n, Walk (cut D C) (V \ B) (lab l).2 (lab (l + 1)).1 (len l)) ∧
      ∑ l ∈ range n, (len l + 1) ≤ q := by
  obtain ⟨i, iF, c, pos, le, tr⟩ := joint_cycle free none bank inU fresh pays
  obtain ⟨n, lab, len, l0, ln, steps, sum⟩ := tr.cyclic
  have npos : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · simp at sum
      omega
    · exact h
  refine ⟨n, lab, len, npos, ln.trans l0.symm, ?_, fun l hl => (steps l hl).2, by omega⟩
  intro l hl
  rcases Nat.eq_zero_or_pos l with rfl | h
  · rw [l0]; exact iF
  · obtain ⟨m, rfl⟩ : ∃ m, l = m + 1 := ⟨l - 1, by omega⟩
    exact (steps m (by omega)).1

/-- **Ranked obstruction.** For every ranking of the labels there are labels `j`, `j'` with `j'`
ranked at or below `j` and an old walk in the cut graph from the head of `j` to the tail of `j'`:
of at most `q-1` arcs if the tails agree, of at most `q-2` arcs if they differ. -/
theorem ranked_row (free : QFree D V q) (none : NoHost q t) (bank : Eligible V B q t)
    (inU : ∀ j ∈ F, j.2 ∈ V \ B) (fresh : ∀ j ∈ F, D j.1 j.2 ≠ true)
    (pays : ∀ u ∈ V \ B, t + (outN D (V \ B) u ∩ C u).card ≤
      (outN D (V \ B) u).card + (newHeads F u).card) (ρ : Arc → ℕ) :
    ∃ j ∈ F, ∃ j' ∈ F, ∃ d, Walk (cut D C) (V \ B) j.2 j'.1 d ∧ ρ j' ≤ ρ j ∧
      ((j'.1 = j.1 ∧ d + 1 ≤ q) ∨ (j'.1 ≠ j.1 ∧ d + 2 ≤ q)) := by
  obtain ⟨i, iF, c, pos, le, tr⟩ := joint_cycle free none bank inU fresh pays
  obtain ⟨j, jF, j', jF', d, w, order, far⟩ := tr.descent ρ iF le_rfl pos
  refine ⟨j, jF, j', jF', d, w, order, ?_⟩
  by_cases same : j'.1 = j.1
  · refine Or.inl ⟨same, ?_⟩
    rcases far with h | ⟨_, _, h⟩ <;> omega
  · rcases far with h | ⟨rfl, rfl, _⟩
    · exact Or.inr ⟨same, by omega⟩
    · exact absurd rfl same

open Classical in
/-- Surviving heads of `p` that the row `u` misses and that do not return to `u` in exactly `q-1`
arcs of `K`. -/
noncomputable def clear (D K : CH.Digraph) (U : Finset ℕ) (q p u : ℕ) : Finset ℕ :=
  U.filter (fun z => D p z = true ∧ D u z ≠ true ∧ ¬ Walk K U z u (q - 1))

/-- **Common erased parent.** Suppose every short row points to one label `p`. Then for every cut
inside the spare budgets some short row has fewer clear heads of `p` than it is short. No cross
condition between different short rows occurs. -/
theorem common_parent_row {p : ℕ} (free : QFree D V q) (hq : 1 ≤ q) (none : NoHost q t)
    (bank : Eligible V B q t) (pv : p ∈ V)
    (common : ∀ u ∈ V \ B, (outN D (V \ B) u).card < t → D u p = true)
    (budget : ∀ c ∈ V \ B, (C c).card ≤ spare D (V \ B) t c) :
    ∃ u ∈ V \ B, (outN D (V \ B) u).card < t ∧
      (clear D (cut D C) (V \ B) q p u).card + (outN D (V \ B) u).card < t := by
  classical
  by_contra bad
  push Not at bad
  let P := (V \ B).filter (fun u => (outN D (V \ B) u).card < t)
  let F : Finset Arc := (P ×ˢ (V \ B)).filter (fun j => j.2 ∈ clear D (cut D C) (V \ B) q p j.1)
  have memF : ∀ j, j ∈ F ↔ (j.1 ∈ V \ B ∧ (outN D (V \ B) j.1).card < t) ∧ j.2 ∈ V \ B ∧
      j.2 ∈ clear D (cut D C) (V \ B) q p j.1 := by
    intro j
    simp only [F, P, mem_filter, mem_product, and_assoc]
  have inU : ∀ j ∈ F, j.2 ∈ V \ B := fun j jF => ((memF j).mp jF).2.1
  have props : ∀ j ∈ F, D p j.2 = true ∧ D j.1 j.2 ≠ true ∧
      ¬ Walk (cut D C) (V \ B) j.2 j.1 (q - 1) :=
    fun j jF => (mem_filter.mp ((memF j).mp jF).2.2).2
  have safe : QFree (install (cut D C) F) (V \ B) q := by
    refine (kin_iff free hq sdiff_subset cut_sub inU (fun _ => p) (fun _ => 0) (fun _ _ => pv)
      (fun j jF => (props j jF).1) ?_).mpr (fun j jF => (props j jF).2.2)
    intro _ _ j' jF' _
    obtain ⟨⟨ju, short⟩, _⟩ := (memF j').mp jF'
    exact common _ ju short
  refine bank_exit none bank inU (fun j jF => (props j jF).2.1) (pays_of_spare budget ?_) safe
  intro u uu low
  have enough := bad u uu low
  have sub : clear D (cut D C) (V \ B) q p u ⊆ newHeads F u := by
    intro z hz
    exact mem_newHeads.mpr ((memF (u, z)).mpr ⟨⟨uu, low⟩, (mem_filter.mp hz).1, hz⟩)
  have := card_le_card sub
  omega

open Classical in
/-- **The joint cascade guards one step too far.** Take the joint cascade of the short rows and
its own static cut. A missing head is usable at the short row `u` as soon as it is off the cascade
at step `q-2` and has no return of exactly `q-1` arcs to `u` itself in the cut graph. A return of
`q-1` arcs to a different short row does not count. Even so, some short row has fewer usable heads
than it is short. -/
theorem last_step_row (free : QFree D V q) (none : NoHost q t) (bank : Eligible V B q t) :
    ∃ u ∈ V \ B, (outN D (V \ B) u).card < t ∧
      ((V \ B).filter (fun z =>
        z ∉ active D (V \ B) ((V \ B).filter (fun c => (outN D (V \ B) c).card < t))
          (spare D (V \ B) t) (q - 2) ∧ D u z ≠ true ∧
        ¬ Walk (cut D (fun c => bill D (V \ B)
            ((V \ B).filter (fun c => (outN D (V \ B) c).card < t)) (spare D (V \ B) t) c (q - 1)))
          (V \ B) z u (q - 1))).card + (outN D (V \ B) u).card < t := by
  classical
  by_contra bad
  push Not at bad
  let P := (V \ B).filter (fun c => (outN D (V \ B) c).card < t)
  let A := active D (V \ B) P (spare D (V \ B) t)
  let C : ℕ → Finset ℕ := fun c => bill D (V \ B) P (spare D (V \ B) t) c (q - 1)
  let G : ℕ → Finset ℕ := fun u => (V \ B).filter (fun z =>
    z ∉ A (q - 2) ∧ D u z ≠ true ∧ ¬ Walk (cut D C) (V \ B) z u (q - 1))
  let F : Finset Arc := (P ×ˢ (V \ B)).filter (fun j => j.2 ∈ G j.1)
  have memF : ∀ j, j ∈ F ↔ (j.1 ∈ V \ B ∧ (outN D (V \ B) j.1).card < t) ∧ j.2 ∈ V \ B ∧
      j.2 ∈ G j.1 := by
    intro j
    simp only [F, P, mem_filter, mem_product, and_assoc]
  have inU : ∀ j ∈ F, j.2 ∈ V \ B := fun j jF => ((memF j).mp jF).2.1
  have props : ∀ j ∈ F, j.2 ∉ A (q - 2) ∧ D j.1 j.2 ≠ true ∧
      ¬ Walk (cut D C) (V \ B) j.2 j.1 (q - 1) :=
    fun j jF => (mem_filter.mp ((memF j).mp jF).2.2).2
  have near : ∀ j ∈ F, ∀ j' ∈ F, ∀ d, d + 2 ≤ q → ¬ Walk (cut D C) (V \ B) j.2 j'.1 d := by
    intro j jF j' jF' d le w
    have tail : j'.1 ∈ P := mem_filter.mpr ((memF j').mp jF').1
    exact (props j jF).1 (active_mono D _ _ _ (by omega : d ≤ q - 2)
      (sound_cut D _ _ _ (inU j jF) tail (by omega) w))
  have old : QFree (cut D C) (V \ B) q :=
    fun a l h1 h2 w => free a l h1 h2 ((walk_sub cut_sub w).mono sdiff_subset)
  have safe : QFree (install (cut D C) F) (V \ B) q := by
    refine ranked_safe (fun _ => 0) inU old ?_ (fun j jF j' jF' _ _ d le => near j jF j' jF' d le)
    intro j jF d le w
    rcases Nat.lt_or_ge (d + 1) q with lt | ge
    · exact near j jF j jF d (by omega) w
    · have exact : d = q - 1 := by omega
      subst exact
      exact (props j jF).2.2 w
  refine bank_exit none bank inU (fun j jF => (props j jF).2.1)
    (pays_of_spare (fun c _ => affordable D _ _ _ c _) ?_) safe
  intro u uu low
  have enough : t ≤ (G u).card + (outN D (V \ B) u).card := bad u uu low
  have sub : G u ⊆ newHeads F u := by
    intro z hz
    exact mem_newHeads.mpr ((memF (u, z)).mpr ⟨⟨uu, low⟩, (mem_filter.mp hz).1, hz⟩)
  have := card_le_card sub
  omega

/-- **What stays unpaid.** After any safe edit `E` of the survivors, the rows still below quota
obey the forced-row law in `E` itself: some short row has fewer targets off the joint cascade of
`E` than it is short. -/
theorem residual_debt {E : CH.Digraph} (none : NoHost q t) (live : U.Nonempty)
    (size : U.card ≤ q * t) (safe : QFree E U q) : BankDebt E U q t := by
  have debt := any_bank (B := ∅) safe none
    ⟨empty_subset _, by rw [card_empty]; omega, by rw [sdiff_empty]; exact live⟩
  rwa [sdiff_empty] at debt

end host

section cell
variable {q r : ℕ} {X : ShenMinimumOrder.Source q r} {m : Cell}

/-- What a marked cell with a second short row must satisfy: for every cut and every paying family
of missing arcs on the survivors, a cyclic list of labels with old walks of the cut graph between
them inside the common budget `q`. -/
structure JointBlocked (X : ShenMinimumOrder.Source q r) (m : Cell) : Prop where
  second : ∃ j ∈ X.V \ m.bank, j ≠ m.x ∧ (outN X.D (X.V \ m.bank) j).card < r - 1
  cycle : ∀ (C : ℕ → Finset ℕ) (F : Finset Arc), (∀ j ∈ F, j.2 ∈ X.V \ m.bank) →
    (∀ j ∈ F, X.D j.1 j.2 ≠ true) →
    (∀ u ∈ X.V \ m.bank, (r - 1) + (outN X.D (X.V \ m.bank) u ∩ C u).card ≤
      (outN X.D (X.V \ m.bank) u).card + (newHeads F u).card) →
    ∃ (n : ℕ) (lab : ℕ → Arc) (len : ℕ → ℕ), 0 < n ∧ lab n = lab 0 ∧ (∀ l ≤ n, lab l ∈ F) ∧
      (∀ l < n, Walk (cut X.D C) (X.V \ m.bank) (lab l).2 (lab (l + 1)).1 (len l)) ∧
      ∑ l ∈ range n, (len l + 1) ≤ q

/-- **Capstone-facing statement on a `JointShort` child.** -/
theorem joint_blocked (none : NoHost q (r - 1)) (cell : Marked X m) (joint : JointShort X m) :
    JointBlocked X m :=
  ⟨joint, fun _ _ inU fresh pays =>
    joint_cycle_list X.free none (marked_bank cell) inU fresh pays⟩

/-- A paid safe family on the marked cell closes it. -/
theorem joint_exit (none : NoHost q (r - 1)) (cell : Marked X m) {C : ℕ → Finset ℕ}
    {F : Finset Arc} (inU : ∀ j ∈ F, j.2 ∈ X.V \ m.bank) (fresh : ∀ j ∈ F, X.D j.1 j.2 ≠ true)
    (pays : ∀ u ∈ X.V \ m.bank, (r - 1) + (outN X.D (X.V \ m.bank) u ∩ C u).card ≤
      (outN X.D (X.V \ m.bank) u).card + (newHeads F u).card)
    (safe : QFree (install (cut X.D C) F) (X.V \ m.bank) q) : False :=
  bank_exit none (marked_bank cell) inU fresh pays safe

/-- **The band `N = q (r-1) + 2`.** The bank has two labels, so every short row points to both and
is short by exactly one. -/
theorem band_all (cell : Marked X m) (band : X.V.card = q * (r - 1) + 2) :
    ∀ u ∈ X.V \ m.bank, (outN X.D (X.V \ m.bank) u).card < r - 1 →
      (outN X.D (X.V \ m.bank) u).card + 2 = r ∧ (outN X.D X.V u).card = r ∧
        ∀ h ∈ m.bank, X.D u h = true := by
  intro u uu low
  have two : m.bank.card = 2 := by
    have := cell.size
    omega
  have deg := X.degree u (mem_sdiff.mp uu).1
  have all : outN X.D X.V u ⊆ outN X.D (X.V \ m.bank) u ∪ m.bank := by
    intro y hy
    obtain ⟨yv, uy⟩ := mem_outN.mp hy
    by_cases yb : y ∈ m.bank
    · exact mem_union_right _ yb
    · exact mem_union_left _ (mem_outN.mpr ⟨mem_sdiff.mpr ⟨yv, yb⟩, uy⟩)
  have a1 := card_le_card all
  have a2 := card_union_le (outN X.D (X.V \ m.bank) u) m.bank
  refine ⟨by omega, by omega, ?_⟩
  intro h hb
  by_contra miss
  have part : outN X.D X.V u ⊆ outN X.D (X.V \ m.bank) u ∪ m.bank.erase h := by
    intro y hy
    obtain ⟨yv, uy⟩ := mem_outN.mp hy
    by_cases yb : y ∈ m.bank
    · exact mem_union_right _ (mem_erase.mpr ⟨fun e => miss (e ▸ uy), yb⟩)
    · exact mem_union_left _ (mem_outN.mpr ⟨mem_sdiff.mpr ⟨yv, yb⟩, uy⟩)
  have b1 := card_le_card part
  have b2 := card_union_le (outN X.D (X.V \ m.bank) u) (m.bank.erase h)
  have b3 := card_erase_of_mem hb
  omega

/-- **Band law.** At order `q (r-1) + 2`, for every cut inside the spare budgets there is a short
row `u` (short by one, pointing to the erased parent `p`) with a surviving head of `p` that it
misses, such that every such head returns to `u` in exactly `q-1` arcs of the cut graph. Short
rows impose nothing on each other. -/
theorem band_row (hq : 2 ≤ q) (none : NoHost q (r - 1)) (cell : Marked X m)
    (band : X.V.card = q * (r - 1) + 2) {C : ℕ → Finset ℕ}
    (budget : ∀ c ∈ X.V \ m.bank, (C c).card ≤ spare X.D (X.V \ m.bank) (r - 1) c) :
    ∃ u ∈ X.V \ m.bank, (outN X.D (X.V \ m.bank) u).card + 2 = r ∧ X.D u m.parent = true ∧
      (∃ z ∈ X.V \ m.bank, X.D m.parent z = true ∧ X.D u z ≠ true) ∧
      ∀ z ∈ X.V \ m.bank, X.D m.parent z = true → X.D u z ≠ true →
        Walk (cut X.D C) (X.V \ m.bank) z u (q - 1) := by
  classical
  have pv := cell.sub cell.erased
  have rows := band_all cell band
  obtain ⟨u, uu, low, few⟩ := common_parent_row X.free (by omega) none (marked_bank cell) pv
    (fun u uu low => (rows u uu low).2.2 _ cell.erased) budget
  obtain ⟨two, native, points⟩ := rows u uu low
  refine ⟨u, uu, two, points _ cell.erased, ?_, ?_⟩
  · exact candidate_exists X.free (by omega) pv (points _ cell.erased)
      (native.le.trans (X.degree _ pv)) (fun h hb _ => points h hb)
  · intro z zu pz uz
    by_contra no
    have inClear : z ∈ clear X.D (cut X.D C) (X.V \ m.bank) q m.parent u :=
      mem_filter.mpr ⟨zu, pz, uz, no⟩
    have := card_pos.mpr ⟨z, inClear⟩
    omega

/-- **The unpaid row of the band.** At order `q (r-1) + 2` there is a short row `u` such that
every surviving head `z` of the erased parent `p` that `u` misses reaches, in `q-2` old arcs on
the survivors, a surviving parent `y` of `u` that does not point to `p`, meets quota, and points
to more short rows than it has spare heads. -/
theorem band_unpaid (hq : 2 ≤ q) (none : NoHost q (r - 1)) (cell : Marked X m)
    (band : X.V.card = q * (r - 1) + 2) :
    ∃ u ∈ X.V \ m.bank, (outN X.D (X.V \ m.bank) u).card + 2 = r ∧ X.D u m.parent = true ∧
      (∃ z ∈ X.V \ m.bank, X.D m.parent z = true ∧ X.D u z ≠ true) ∧
      ∀ z ∈ X.V \ m.bank, X.D m.parent z = true → X.D u z ≠ true →
        ∃ y ∈ X.V \ m.bank, X.D y u = true ∧ X.D y m.parent ≠ true ∧
          r - 1 ≤ (outN X.D (X.V \ m.bank) y).card ∧
          spare X.D (X.V \ m.bank) (r - 1) y <
            (outN X.D ((X.V \ m.bank).filter
              (fun c => (outN X.D (X.V \ m.bank) c).card < r - 1)) y).card ∧
          Walk X.D (X.V \ m.bank) z y (q - 2) := by
  classical
  let C : ℕ → Finset ℕ := fun y =>
    if (outN X.D ((X.V \ m.bank).filter
        (fun c => (outN X.D (X.V \ m.bank) c).card < r - 1)) y).card ≤
        spare X.D (X.V \ m.bank) (r - 1) y
    then outN X.D ((X.V \ m.bank).filter
        (fun c => (outN X.D (X.V \ m.bank) c).card < r - 1)) y else ∅
  have budget : ∀ c ∈ X.V \ m.bank, (C c).card ≤ spare X.D (X.V \ m.bank) (r - 1) c := by
    intro c _
    dsimp only [C]
    split_ifs with h
    · exact h
    · simp
  have pv := cell.sub cell.erased
  obtain ⟨u, uu, two, up, cand, returns⟩ := band_row hq none cell band budget
  refine ⟨u, uu, two, up, cand, ?_⟩
  intro z zu pz uz
  have w := returns z zu pz uz
  obtain ⟨k, hk⟩ : ∃ k, q - 1 = k + 1 := ⟨q - 2, by omega⟩
  rw [hk] at w
  obtain ⟨y, wy, _, last⟩ := w.unsnoc
  have yu : y ∈ X.V \ m.bank := by
    rcases wy.end_mem_or with rfl | h
    · exact zu
    · exact h
  obtain ⟨arc, kept⟩ := Bool.and_eq_true_iff.mp last
  have kept : u ∉ C y := of_decide_eq_true kept
  have old : Walk X.D (X.V \ m.bank) z y k := walk_sub cut_sub wy
  have offp : X.D y m.parent ≠ true := by
    intro yp
    exact X.free m.parent (k + 1 + 1) (by omega) (by omega)
      (.step (sdiff_subset zu) pz ((old.mono sdiff_subset).snoc pv yp))
  have short : u ∈ (X.V \ m.bank).filter
      (fun c => (outN X.D (X.V \ m.bank) c).card < r - 1) := mem_filter.mpr ⟨uu, by omega⟩
  have quota : r - 1 ≤ (outN X.D (X.V \ m.bank) y).card := by
    by_contra low
    exact offp ((band_all cell band y yu (by omega)).2.2 _ cell.erased)
  refine ⟨y, yu, arc, offp, quota, ?_, by rw [show q - 2 = k by omega]; exact old⟩
  by_contra fits
  apply kept
  dsimp only [C]
  split_ifs with h
  · exact mem_outN.mpr ⟨short, arc⟩
  · exact absurd (by omega) h

end cell

#print axioms repair_eq_install
#print axioms install_iff
#print axioms Trail.cyclic
#print axioms pair_iff
#print axioms one_way
#print axioms ranked_safe
#print axioms kin_iff
#print axioms joint_host
#print axioms joint_cycle_list
#print axioms ranked_row
#print axioms common_parent_row
#print axioms last_step_row
#print axioms residual_debt
#print axioms joint_blocked
#print axioms joint_exit
#print axioms band_all
#print axioms band_row
#print axioms band_unpaid
end LeanCH.BR.JointShortcut
