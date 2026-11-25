import checkpoints.shen_extension.CollarTwo

/-!
# Thin suppliers: complete heads of thin roots pay for tight roots

Every out-degree is exactly `r` and there is no closed walk of length at most `q`. A root `u`
has heads `X` (`r` labels), second layer `Y`, third layer `Z`. It is *thin* (`Thin`) when
`|Y| = r - 1` and *tight* (`TightR`) when moreover `|Z| ≤ r - 1` (the pattern
`ShapeClimbAvoid.tightA r`). A head of `u` is *complete* when it has at most one head in `X`
(`complete`); then it points to all of `Y`.

Paper source: degree-nine dossier, Appendix 30 (44 vertices), Appendix 17 item 2, Appendix 31.
Everything is generic in `q` and `r`; the range is stated with each result. The single-loop
range is `q + 1 ≤ r ≤ 2q - 1` (for `r ≤ q` there is no thin root at all).

* `lone_count` (generic, `1 ≤ q`): on `n ≤ 2q` labels, `q`-free, minimum out-degree one,
  at least `2q + 2 - n` rows have exactly one head. Proof by the private-head completion: give
  every such row `p` a new private head, a copy of its sole head `h p` with that row extended in
  the same way; the completion is `q`-free with minimum out-degree two (`clone_free`,
  `clone_out2`), so it has at least `2q + 1` labels (`BRq2.ball_growth`), and at exactly
  `2q + 1` every in-degree is two, which a private copy without a lone parent breaks.
* `lone_near` (`2 ≤ q`, `n ≤ 2q - 1`): every row reaches a lone row within `q - 2` steps:
  otherwise the completion's `(q-2)`-ball stays among the other rows.
* Thin roots (`3 ≤ q`, `r ≤ 2q - 1`): `complete_count` (at least `2q + 2 - r` complete heads),
  `complete_full`, `no_return_r` (no arc from `Y` back to `X` or the root), `third_wide`
  (`|Z| ≥ r - 1`, so a tight root has `|Z| = r - 1`).
* `complete_ball` (`2 ≤ q`): for a complete head `x` with `X`-head `b`, `1 ≤ j ≤ q`:
  `|B (j+1) u| + |B_X (j-1) b| ≤ |B j x| + r`.
* `supplier_gain` (`3 ≤ q`, `r ≤ 2q - 1`): if `x` is a complete head of `s` thin roots with
  pairwise different second layers, its `X`-head in each has at least `s` heads in that `X`.
* `same_far_r`, `twins_gap_r`: `CollarTwo.same_far` at any regular degree.
* `no_tight_thin`: the count through `BankCount.bank_count`.
* `no_tight_44`, `profile_44`: the instance at `r = 9`, `q = 5`, `n = 44`, floors as hypotheses.
-/

set_option linter.style.longLine false
namespace LeanCH.BR.ThinSuppliers
open Finset BRq2 BRq3 FifthStripAll RigidHost LoopCollar
open DotTwoPassShellTransport (layer layer_subset)
open ShapeClimbRoot (mem_layer)
open ReachLedger (gap mem_gap)

variable {D : CH.Digraph} {q : ℕ}

/-! ### The private-head completion -/

section clone
variable {S : Finset ℕ}

/-- Rows with at most one head inside `S`. -/
def lone (D : CH.Digraph) (S : Finset ℕ) : Finset ℕ := S.filter (fun v => (outN D S v).card ≤ 1)

/-- The sole head of a lone row. -/
noncomputable def hd (D : CH.Digraph) (S : Finset ℕ) (p : ℕ) : ℕ := (outN D S p).sup id

/-- A label above all of `S`; the private copy of `p` is `top S + p`. -/
def top (S : Finset ℕ) : ℕ := S.sup id + 1

/-- `S` with one private copy per lone row. -/
def cloneSet (D : CH.Digraph) (S : Finset ℕ) : Finset ℕ :=
  S ∪ (lone D S).image (fun p => top S + p)

/-- The completion: a lone row also heads its copy; the copy of `p` has the row of `h p`,
extended in the same way. -/
noncomputable def cloneG (D : CH.Digraph) (S : Finset ℕ) : CH.Digraph := fun a b =>
  if a < top S then (if b < top S then D a b else decide (b = top S + a))
  else (if b < top S then D (hd D S (a - top S)) b else decide (b - top S = hd D S (a - top S)))

/-- The projection of the completion back to `S`. -/
noncomputable def proj (D : CH.Digraph) (S : Finset ℕ) (a : ℕ) : ℕ :=
  if a < top S then a else hd D S (a - top S)

theorem lt_top {v : ℕ} (hv : v ∈ S) : v < top S :=
  Nat.lt_succ_of_le (le_sup (f := id) hv)

theorem mem_lone {v : ℕ} : v ∈ lone D S ↔ v ∈ S ∧ (outN D S v).card ≤ 1 := mem_filter

theorem lone_subset : lone D S ⊆ S := filter_subset _ _

theorem hd_spec (deg : ∀ v ∈ S, 1 ≤ (outN D S v).card) {p : ℕ} (hp : p ∈ lone D S) :
    outN D S p = {hd D S p} := by
  obtain ⟨pS, one⟩ := mem_lone.mp hp
  obtain ⟨a, ha⟩ := card_eq_one.mp (le_antisymm one (deg p pS))
  rw [ha]
  simp [hd, ha]

theorem hd_mem (deg : ∀ v ∈ S, 1 ≤ (outN D S v).card) {p : ℕ} (hp : p ∈ lone D S) :
    hd D S p ∈ S ∧ D p (hd D S p) = true := by
  have h : hd D S p ∈ outN D S p := by rw [hd_spec deg hp]; exact mem_singleton_self _
  exact mem_outN.mp h

theorem mem_cloneSet {a : ℕ} :
    a ∈ cloneSet D S ↔ a ∈ S ∨ (top S ≤ a ∧ a - top S ∈ lone D S) := by
  simp only [cloneSet, mem_union, mem_image]
  constructor
  · rintro (h | ⟨p, hp, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨by omega, by simpa using hp⟩
  · rintro (h | ⟨h1, h2⟩)
    · exact Or.inl h
    · exact Or.inr ⟨a - top S, h2, by omega⟩

theorem mem_of_lt {a : ℕ} (ha : a ∈ cloneSet D S) (lt : a < top S) : a ∈ S := by
  rcases mem_cloneSet.mp ha with h | ⟨h, -⟩
  · exact h
  · omega

theorem lone_of_ge {a : ℕ} (ha : a ∈ cloneSet D S) (ge : ¬ a < top S) : a - top S ∈ lone D S := by
  rcases mem_cloneSet.mp ha with h | ⟨-, h⟩
  · exact absurd (lt_top h) ge
  · exact h

theorem copy_mem {p : ℕ} (hp : p ∈ lone D S) : top S + p ∈ cloneSet D S :=
  mem_cloneSet.mpr (Or.inr ⟨by omega, by simpa using hp⟩)

theorem proj_mem (deg : ∀ v ∈ S, 1 ≤ (outN D S v).card) {a : ℕ} (ha : a ∈ cloneSet D S) :
    proj D S a ∈ S := by
  unfold proj
  split_ifs with h
  · exact mem_of_lt ha h
  · exact (hd_mem deg (lone_of_ge ha h)).1

theorem arc_proj (deg : ∀ v ∈ S, 1 ≤ (outN D S v).card) {a b : ℕ}
    (hb : b ∈ cloneSet D S) (ab : cloneG D S a b = true) :
    D (proj D S a) (proj D S b) = true := by
  unfold cloneG at ab
  unfold proj
  by_cases a1 : a < top S <;> by_cases b1 : b < top S <;>
    simp only [a1, b1, ↓reduceIte] at ab ⊢
  · exact ab
  · have e : b = top S + a := by simpa using ab
    have bl := lone_of_ge hb b1
    rw [e, show top S + a - top S = a by omega] at bl ⊢
    exact (hd_mem deg bl).2
  · exact ab
  · have e : b - top S = hd D S (a - top S) := by simpa using ab
    have bl := lone_of_ge hb b1
    rw [e] at bl ⊢
    exact (hd_mem deg bl).2

theorem walk_proj (deg : ∀ v ∈ S, 1 ≤ (outN D S v).card) {a b m : ℕ}
    (w : Walk (cloneG D S) (cloneSet D S) a b m) :
    a ∈ cloneSet D S → Walk D S (proj D S a) (proj D S b) m := by
  induction w with
  | refl a => exact fun _ => .refl _
  | step hb hab _ ih =>
    intro _
    exact .step (proj_mem deg hb) (arc_proj deg hb hab) (ih hb)

/-- The completion is `q`-free. -/
theorem clone_free (deg : ∀ v ∈ S, 1 ≤ (outN D S v).card) (free : QFree D S q) :
    QFree (cloneG D S) (cloneSet D S) q := by
  intro a ℓ h1 h2 w
  obtain ⟨k, rfl⟩ : ∃ k, ℓ = k + 1 := ⟨ℓ - 1, by omega⟩
  obtain ⟨_, _, ha, _⟩ := w.unsnoc
  exact free (proj D S a) (k + 1) h1 h2 (walk_proj deg w ha)

theorem two_le_card {T : Finset ℕ} {a b : ℕ} (ne : a ≠ b) (ha : a ∈ T) (hb : b ∈ T) :
    2 ≤ T.card := Finset.one_lt_card.mpr ⟨a, ha, b, hb, ne⟩

/-- The completion has minimum out-degree two. -/
theorem clone_out2 (deg : ∀ v ∈ S, 1 ≤ (outN D S v).card) :
    MinOut2 (cloneG D S) (cloneSet D S) := by
  intro v hv
  change 2 ≤ (outN (cloneG D S) (cloneSet D S) v).card
  -- a row whose extended row contains that of the label `h ∈ S`
  have extend : ∀ a h, h ∈ S →
      (∀ c ∈ S, D h c = true → c ∈ outN (cloneG D S) (cloneSet D S) a) →
      (h ∈ lone D S → top S + h ∈ outN (cloneG D S) (cloneSet D S) a) →
      2 ≤ (outN (cloneG D S) (cloneSet D S) a).card := by
    intro a h hS rowS rowC
    by_cases hl : h ∈ lone D S
    · obtain ⟨cS, hc⟩ := hd_mem deg hl
      refine two_le_card ?_ (rowS _ cS hc) (rowC hl)
      have := lt_top cS
      omega
    · have big : 2 ≤ (outN D S h).card := by
        by_contra small
        exact hl (mem_lone.mpr ⟨hS, by omega⟩)
      refine big.trans (card_le_card fun c hc => ?_)
      exact rowS c (mem_outN.mp hc).1 (mem_outN.mp hc).2
  by_cases v1 : v < top S
  · have vS := mem_of_lt hv v1
    refine extend v v vS (fun c hc vc => ?_) (fun hl => ?_)
    · refine mem_outN.mpr ⟨mem_union_left _ hc, ?_⟩
      simp only [cloneG, v1, lt_top hc, ↓reduceIte, vc]
    · refine mem_outN.mpr ⟨copy_mem hl, ?_⟩
      simp [cloneG, v1]
  · have pl := lone_of_ge hv v1
    obtain ⟨hS, -⟩ := hd_mem deg pl
    refine extend v (hd D S (v - top S)) hS (fun c hc vc => ?_) (fun hl => ?_)
    · refine mem_outN.mpr ⟨mem_union_left _ hc, ?_⟩
      simp only [cloneG, v1, lt_top hc, ↓reduceIte, vc]
    · refine mem_outN.mpr ⟨copy_mem hl, ?_⟩
      simp [cloneG, v1]

theorem clone_card : (cloneSet D S).card = S.card + (lone D S).card := by
  rw [cloneSet, card_union_of_disjoint, card_image_of_injective _ (add_right_injective (top S))]
  rw [disjoint_left]
  intro a ha hi
  obtain ⟨p, -, rfl⟩ := mem_image.mp hi
  have := lt_top ha
  omega

/-- The parents of a private copy: its lone row, and copies of lone rows heading that row. -/
theorem copy_parents {p : ℕ} :
    (cloneSet D S).filter (fun a => cloneG D S a (top S + p) = true) ⊆
      insert p (((lone D S).filter (fun p' => hd D S p' = p)).image (fun p' => top S + p')) := by
  intro a ha
  obtain ⟨aW, arc⟩ := mem_filter.mp ha
  unfold cloneG at arc
  by_cases a1 : a < top S
  · simp only [a1, show ¬ top S + p < top S by omega, ↓reduceIte, decide_eq_true_eq] at arc
    rw [show a = p by omega]
    exact mem_insert_self _ _
  · simp only [a1, show ¬ top S + p < top S by omega, ↓reduceIte, decide_eq_true_eq] at arc
    refine mem_insert_of_mem (mem_image.mpr ⟨a - top S, mem_filter.mpr ⟨lone_of_ge aW a1, ?_⟩, by omega⟩)
    rw [← arc]
    omega

/-- **Lone count.** A nonempty `q`-free set of at most `2q` labels with minimum out-degree one
has at least `2q + 2 - |S|` rows with exactly one head (`1 ≤ q`). -/
theorem lone_count (free : QFree D S q) (hq : 1 ≤ q) (deg : ∀ v ∈ S, 1 ≤ (outN D S v).card)
    (ne : S.Nonempty) (small : S.card ≤ 2 * q) : 2 * q + 2 ≤ S.card + (lone D S).card := by
  classical
  have fr := clone_free deg free
  have m2 := clone_out2 deg (D := D) (S := S)
  have cc := clone_card (D := D) (S := S)
  by_contra lt
  push Not at lt
  obtain ⟨x, hx⟩ := ne
  have xW : x ∈ cloneSet D S := mem_union_left _ hx
  have big := ball_growth q hq _ _ fr m2 x xW q le_rfl
  have Wle := card_le_card (ball_subset (D := cloneG D S) (W := cloneSet D S) (u := x) (k := q))
  have par_le : ∀ v ∈ (cloneSet D S), ((cloneSet D S).filter (fun a => (cloneG D S) a v = true)).card ≤ 2 := by
    intro v hv
    have hA := ball_growth q hq (cloneG D S) (cloneSet D S) fr m2 v hv (q - 1) (by omega)
    have hsub : (cloneSet D S).filter (fun a => (cloneG D S) a v = true) ⊆ (cloneSet D S) \ ball (cloneG D S) (cloneSet D S) v (q - 1) := by
      intro y hy
      obtain ⟨hyW, hyv⟩ := mem_filter.mp hy
      exact mem_sdiff.mpr ⟨hyW, fun hyb => no_back_arc fr hv hyb (by omega) hyv⟩
    have := card_le_card hsub
    rw [card_sdiff_of_subset ball_subset] at this
    omega
  have sumeq := Compose.ThinRigid.sum_out_eq_sum_in (cloneG D S) (cloneSet D S)
  have outge : ∑ _v ∈ (cloneSet D S), 2 ≤ ∑ v ∈ (cloneSet D S), ((cloneSet D S).filter (fun w => (cloneG D S) v w = true)).card :=
    sum_le_sum m2
  have heq : ∑ v ∈ (cloneSet D S), ((cloneSet D S).filter (fun a => (cloneG D S) a v = true)).card = ∑ _v ∈ (cloneSet D S), 2 :=
    le_antisymm (sum_le_sum par_le) (by rw [← sumeq]; exact outge)
  have each := (sum_eq_sum_iff_of_le par_le).mp heq
  -- the lone rows: nonempty, and closed under the sole head
  have Lne : (lone D S).Nonempty := by
    by_contra e
    rw [not_nonempty_iff_eq_empty] at e
    rw [e, card_empty] at cc
    omega
  have copies : ∀ p ∈ (lone D S), 2 ≤ 1 + ((lone D S).filter (fun p' => hd D S p' = p)).card := by
    intro p hp
    have e := each (top S + p) (copy_mem hp)
    have c := (card_le_card (copy_parents (D := D) (S := S) (p := p))).trans
      ((card_insert_le _ _).trans (Nat.add_le_add_right card_image_le 1))
    omega
  have key : ∑ p ∈ (lone D S), ((lone D S).filter (fun p' => hd D S p' = p)).card =
      ((lone D S).filter (fun p' => hd D S p' ∈ (lone D S))).card := by
    simp only [card_filter]
    rw [sum_comm]
    refine sum_congr rfl (fun p' _ => ?_)
    rw [sum_ite_eq]
  have s1 := sum_le_sum copies
  rw [sum_const, smul_eq_mul, sum_add_distrib, sum_const, smul_eq_mul, key] at s1
  have all : (lone D S).filter (fun p' => hd D S p' ∈ (lone D S)) = (lone D S) :=
    eq_of_subset_of_card_le (filter_subset _ _) (by omega)
  have closed : ∀ p ∈ (lone D S), ∃ y ∈ (lone D S), D p y = true := by
    intro p hp
    have : p ∈ (lone D S).filter (fun p' => hd D S p' ∈ (lone D S)) := by rw [all]; exact hp
    exact ⟨hd D S p, (mem_filter.mp this).2, (hd_mem deg hp).2⟩
  have many := ReachLedger.closed_chain free lone_subset Lne closed
  have := card_le_card (lone_subset (D := D) (S := S))
  omega

/-- Walks of the completion that stay among non-lone rows (but the last label) are walks of `S`. -/
theorem walk_lift {a c m : ℕ}
    (w : Walk (cloneG D S) (cloneSet D S) a c m) :
    a ∈ S → (∀ j < m, ∀ z ∈ ball D S a j, z ∉ lone D S) → Walk D S a c m := by
  induction w with
  | refl a => exact fun _ _ => .refl _
  | @step a b c k hb hab _ ih =>
    intro ha avoid
    have aL : a ∉ lone D S := avoid 0 (by omega) a (self_mem_ball ha)
    have a1 := lt_top ha
    have b1 : b < top S := by
      by_contra b1
      have bl := lone_of_ge hb b1
      simp only [cloneG, a1, b1, ↓reduceIte, decide_eq_true_eq] at hab
      rw [hab, show top S + a - top S = a by omega] at bl
      exact aL bl
    have bS := mem_of_lt hb b1
    have ab : D a b = true := by simpa only [cloneG, a1, b1, ↓reduceIte] using hab
    refine .step bS ab (ih bS (fun j hj z hz => avoid (j + 1) (by omega) z ?_))
    exact ReachLedger.ball_succ bS ab hz

theorem ball_lift {x k : ℕ} (hx : x ∈ S)
    (avoid : ∀ z ∈ ball D S x k, z ∉ lone D S) :
    ball (cloneG D S) (cloneSet D S) x k ⊆ ball D S x k := by
  intro z hz
  obtain ⟨-, j, hj, w⟩ := mem_ball.mp hz
  have w' := walk_lift w hx (fun j' hj' y hy => avoid y (ball_mono_radius (by omega) hy))
  have zS : z ∈ S := by
    rcases w'.end_mem_or with rfl | h
    · exact hx
    · exact h
  exact mem_ball.mpr ⟨zS, j, hj, w'⟩

/-- **A lone row nearby.** On at most `2q - 1` labels, `q`-free, minimum out-degree one,
`2 ≤ q`: every row reaches a lone row within `q - 2` steps. -/
theorem lone_near (free : QFree D S q) (hq : 2 ≤ q) (deg : ∀ v ∈ S, 1 ≤ (outN D S v).card)
    (small : S.card + 1 ≤ 2 * q) {x : ℕ} (hx : x ∈ S) :
    ∃ c ∈ ball D S x (q - 2), c ∈ lone D S := by
  by_contra none
  push Not at none
  have sub := ball_lift hx none
  have big := ball_growth q (by omega) _ _ (clone_free deg free) (clone_out2 deg) x
    (mem_union_left _ hx) (q - 2) (by omega)
  have inS : ball D S x (q - 2) ⊆ S \ lone D S :=
    fun c hc => mem_sdiff.mpr ⟨ball_subset hc, none c hc⟩
  have c1 := card_le_card sub
  have c2 := card_le_card inS
  rw [card_sdiff_of_subset lone_subset] at c2
  have count := lone_count free (by omega) deg ⟨x, hx⟩ (by omega)
  have := card_le_card (lone_subset (D := D) (S := S))
  omega

end clone

/-! ### Thin roots -/

section root
variable {V : Finset ℕ} {u r : ℕ}

/-- The second layer has `r - 1` labels. -/
def Thin (D : CH.Digraph) (V : Finset ℕ) (r u : ℕ) : Prop := (layer D V 2 u).card + 1 = r

/-- Second layer `r - 1`, third layer at most `r - 1` (`ShapeClimbAvoid.tightA r`). -/
def TightR (D : CH.Digraph) (V : Finset ℕ) (r u : ℕ) : Prop :=
  (layer D V 2 u).card + 1 = r ∧ (layer D V 3 u).card + 1 ≤ r

/-- The complete heads of `u`: heads with at most one head among the heads of `u`. -/
def complete (D : CH.Digraph) (V : Finset ℕ) (u : ℕ) : Finset ℕ := lone D (outN D V u)

theorem complete_subset : complete D V u ⊆ outN D V u := lone_subset

/-- At a thin root every head has a head among the heads. -/
theorem x_heads_r (free : QFree D V q) (hq : 2 ≤ q) (reg : ∀ v ∈ V, (outN D V v).card = r)
    (hu : u ∈ V) (thin : Thin D V r u) :
    ∀ x ∈ outN D V u, 1 ≤ (outN D (outN D V u) x).card :=
  DipCost.layer_host (fun x hx => (reg x (outN_subset hx)).ge) (head_keep free hq hu)
    (by unfold Thin at thin; omega)

/-- **Complete-row count.** A thin root, `r ≤ 2q`, has at least `2q + 2 - r` complete heads. -/
theorem complete_count (free : QFree D V q) (hq : 2 ≤ q) (reg : ∀ v ∈ V, (outN D V v).card = r)
    (hu : u ∈ V) (thin : Thin D V r u) (hr : r ≤ 2 * q) :
    2 * q + 2 ≤ r + (complete D V u).card := by
  have ne : (outN D V u).Nonempty := card_pos.mp (by rw [reg u hu]; unfold Thin at thin; omega)
  have := lone_count (free.mono_set outN_subset) (by omega) (x_heads_r free hq reg hu thin) ne
    (by rw [reg u hu]; exact hr)
  rw [reg u hu] at this
  exact this

/-- A complete head of a thin root heads all of its second layer. -/
theorem complete_full (free : QFree D V q) (hq : 2 ≤ q) (reg : ∀ v ∈ V, (outN D V v).card = r)
    (hu : u ∈ V) (thin : Thin D V r u) {x : ℕ} (hx : x ∈ complete D V u) :
    layer D V 2 u ⊆ outN D V x := by
  classical
  obtain ⟨xX, one⟩ := mem_lone.mp hx
  have keep := head_keep free hq hu
  have cover : outN D V x ⊆ outN D (outN D V u) x ∪ (layer D V 2 u ∩ outN D V x) := by
    intro w hw
    rcases mem_union.mp (keep x xX hw) with h | h
    · exact mem_union_left _ (mem_outN.mpr ⟨h, (mem_outN.mp hw).2⟩)
    · exact mem_union_right _ (mem_inter.mpr ⟨h, hw⟩)
  have c := (card_le_card cover).trans (card_union_le _ _)
  rw [reg x (outN_subset xX)] at c
  unfold Thin at thin
  have full : layer D V 2 u ∩ outN D V x = layer D V 2 u :=
    eq_of_subset_of_card_le inter_subset_left (by omega)
  intro w hw
  rw [← full] at hw
  exact (mem_inter.mp hw).2

/-- **A complete head nearby.** At a thin root, `r ≤ 2q - 1`, every head reaches a complete
head within `q - 2` steps among the heads. -/
theorem complete_near_r (free : QFree D V q) (hq : 2 ≤ q) (reg : ∀ v ∈ V, (outN D V v).card = r)
    (hu : u ∈ V) (thin : Thin D V r u) (hr : r + 1 ≤ 2 * q) {x : ℕ} (hx : x ∈ outN D V u) :
    ∃ c ∈ ball D (outN D V u) x (q - 2), c ∈ complete D V u :=
  lone_near (free.mono_set outN_subset) hq (x_heads_r free hq reg hu thin)
    (by rw [reg u hu]; exact hr) hx

/-- **No arcs back.** At a thin root, `3 ≤ q`, `r ≤ 2q - 1`, no label of the second layer
points to the root or to a head of the root. -/
theorem no_return_r (free : QFree D V q) (hq : 3 ≤ q) (reg : ∀ v ∈ V, (outN D V v).card = r)
    (hu : u ∈ V) (thin : Thin D V r u) (hr : r + 1 ≤ 2 * q) {y : ℕ} (hy : y ∈ layer D V 2 u)
    {w : ℕ} (hw : w ∈ insert u (outN D V u)) : ¬ D y w = true := by
  intro yw
  have yb : y ∈ ball D V u 2 := (mem_layer.mp hy).1
  have yV : y ∈ V := ball_subset yb
  rcases mem_insert.mp hw with rfl | wX
  · exact no_back_arc free hu yb (by omega) yw
  · have XV : outN D V u ⊆ V := outN_subset
    obtain ⟨c, cb, cc⟩ := complete_near_r free (by omega) reg hu thin hr wX
    have cy : D c y = true :=
      (mem_outN.mp (complete_full free (by omega) reg hu thin cc hy)).2
    obtain ⟨-, k, hk, walk⟩ := mem_ball.mp cb
    exact free w (k + 1 + 1) (by omega) (by omega)
      (((walk.mono XV).snoc yV cy).snoc (XV wX) yw)

/-- Rows of the second layer of a thin root stay in the second and third layers. -/
theorem y_keep_r (free : QFree D V q) (hq : 3 ≤ q) (reg : ∀ v ∈ V, (outN D V v).card = r)
    (hu : u ∈ V) (thin : Thin D V r u) (hr : r + 1 ≤ 2 * q) :
    ∀ y ∈ layer D V 2 u, outN D V y ⊆ layer D V 2 u ∪ layer D V 3 u := by
  intro y hy w hw
  obtain ⟨wV, yw⟩ := mem_outN.mp hw
  have yb : y ∈ ball D V u 2 := (mem_layer.mp hy).1
  have wb : w ∈ ball D V u 3 := ball_step yb wV yw
  have n1 : w ∉ ball D V u 1 := by
    intro h
    rcases (mem_ball_one hu).mp h with e | h
    · exact no_return_r free hq reg hu thin hr hy (e ▸ mem_insert_self u (outN D V u)) yw
    · exact no_return_r free hq reg hu thin hr hy (mem_insert_of_mem h) yw
  by_cases n2 : w ∈ ball D V u 2
  · exact mem_union_left _ (mem_layer.mpr ⟨n2, n1⟩)
  · exact mem_union_right _ (mem_layer.mpr ⟨wb, n2⟩)

/-- **The third layer is wide.** A thin root, `3 ≤ q`, `r ≤ 2q - 1`, has at least `r - 1`
labels in its third layer: otherwise its second layer keeps minimum out-degree two on
`r - 1 < 2q + 1` labels. So a tight root has exactly `r - 1`. -/
theorem third_wide (free : QFree D V q) (hq : 3 ≤ q) (reg : ∀ v ∈ V, (outN D V v).card = r)
    (hu : u ∈ V) (thin : Thin D V r u) (hr : r + 1 ≤ 2 * q) :
    r ≤ (layer D V 3 u).card + 1 := by
  by_contra h
  push Not at h
  have keep := y_keep_r free hq reg hu thin hr
  have inner := DipCost.layer_host (X := layer D V 2 u) (Y := layer D V 3 u) (c := 2)
    (fun y hy => (reg y (layer_subset hy)).ge) keep (by omega)
  unfold Thin at thin
  obtain ⟨y, hy⟩ : (layer D V 2 u).Nonempty := card_pos.mp (by omega)
  have big := ball_growth q (by omega) D (layer D V 2 u) (free.mono_set layer_subset)
    (fun v hv => inner v hv) y hy q le_rfl
  have := card_le_card (ball_subset (D := D) (W := layer D V 2 u) (u := y) (k := q))
  omega

theorem tight_third (free : QFree D V q) (hq : 3 ≤ q) (reg : ∀ v ∈ V, (outN D V v).card = r)
    (hu : u ∈ V) (tight : TightR D V r u) (hr : r + 1 ≤ 2 * q) :
    (layer D V 3 u).card + 1 = r := by
  have := third_wide free hq reg hu tight.1 hr
  have := tight.2
  omega

/-- The first three ball sizes of a root, by layers. -/
theorem balls_by_layers (free : QFree D V q) (hq : 1 ≤ q) (reg : ∀ v ∈ V, (outN D V v).card = r)
    (hu : u ∈ V) :
    (ball D V u 1).card = r + 1 ∧
      (ball D V u 2).card = (layer D V 2 u).card + r + 1 ∧
      (ball D V u 3).card = (layer D V 3 u).card + (layer D V 2 u).card + r + 1 := by
  have b1 := ReachLedger.ball_one free hq hu
  rw [reg u hu] at b1
  have b2 : (ball D V u 2).card = (layer D V 2 u).card + (ball D V u 1).card :=
    ShapeClimbRoot.card_ball_succ 1
  have b3 : (ball D V u 3).card = (layer D V 3 u).card + (ball D V u 2).card :=
    ShapeClimbRoot.card_ball_succ 2
  refine ⟨b1, ?_, ?_⟩ <;> omega

/-! ### Complete heads are fat -/

/-- **A complete head is fat.** For a complete head `x` of a thin root `u` with head `b` among
the heads of `u`, and `1 ≤ j ≤ q` (`2 ≤ q`): everything within `j + 1` of `u` beyond its
first ball is within `j` of `x`, and so is the `(j-1)`-ball of `b` among the heads, which
misses `x`. Hence `|B (j+1) u| + |B_X (j-1) b| ≤ |B j x| + r`. -/
theorem complete_ball (free : QFree D V q) (hq : 2 ≤ q) (reg : ∀ v ∈ V, (outN D V v).card = r)
    (hu : u ∈ V) (thin : Thin D V r u) {x : ℕ} (hx : x ∈ complete D V u) {b : ℕ}
    (hb : b ∈ outN D (outN D V u) x) {j : ℕ} (hj : 1 ≤ j) (hjq : j ≤ q) :
    (ball D V u (j + 1)).card + (ball D (outN D V u) b (j - 1)).card ≤
      (ball D V x j).card + r := by
  classical
  have XV : outN D V u ⊆ V := outN_subset
  have xX : x ∈ outN D V u := complete_subset hx
  have xV : x ∈ V := XV xX
  obtain ⟨bX, xb⟩ := mem_outN.mp hb
  have bV : b ∈ V := XV bX
  have full := complete_full free hq reg hu thin hx
  have far : ball D V u (j + 1) \ ball D V u 1 ⊆ ball D V x j := by
    intro z hz
    obtain ⟨zb, z1⟩ := mem_sdiff.mp hz
    by_cases z2 : z ∈ ball D V u 2
    · have zY : z ∈ layer D V 2 u := mem_layer.mpr ⟨z2, z1⟩
      exact ball_mono_radius hj ((mem_ball_one xV).mpr (Or.inr (full zY)))
    · have zb' : z ∈ ball D V u ((j - 1) + 2) := by rwa [show j - 1 + 2 = j + 1 by omega]
      obtain ⟨y, hy, zy⟩ := CollarTwo.through_second hu (j - 1) z zb' z2
      have := ReachLedger.ball_succ (layer_subset hy) (mem_outN.mp (full hy)).2 zy
      rwa [show j - 1 + 1 = j by omega] at this
  have near : ball D (outN D V u) b (j - 1) ⊆ ball D V x j := by
    intro z hz
    obtain ⟨zX, m, hm, w⟩ := mem_ball.mp hz
    exact mem_ball.mpr ⟨XV zX, m + 1, by omega, .step bV xb (w.mono XV)⟩
  have off : x ∉ ball D (outN D V u) b (j - 1) := by
    intro h
    obtain ⟨-, m, hm, w⟩ := mem_ball.mp h
    exact free x (m + 1) (by omega) (by omega) (.step bV xb (w.mono XV))
  have inner : insert x (ball D (outN D V u) b (j - 1)) ⊆ ball D V u 1 := by
    intro z hz
    rcases mem_insert.mp hz with rfl | h
    · exact (mem_ball_one hu).mpr (Or.inr xX)
    · exact (mem_ball_one hu).mpr (Or.inr (ball_subset h))
  have disj : Disjoint (insert x (ball D (outN D V u) b (j - 1)))
      (ball D V u (j + 1) \ ball D V u 1) := by
    rw [disjoint_left]
    intro z hz hz'
    exact (mem_sdiff.mp hz').2 (inner hz)
  have sub : insert x (ball D (outN D V u) b (j - 1)) ∪ (ball D V u (j + 1) \ ball D V u 1) ⊆
      ball D V x j :=
    union_subset (insert_subset (self_mem_ball xV) near) far
  have c := card_le_card sub
  rw [card_union_of_disjoint disj, card_insert_of_notMem off,
    card_sdiff_of_subset (ball_mono_radius (by omega))] at c
  have b1 := ReachLedger.ball_one free (by omega) hu
  rw [reg u hu] at b1
  have := card_le_card (ball_mono_radius (D := D) (W := V) (u := u) (show 1 ≤ j + 1 by omega))
  omega

/-! ### A supplier used by several classes -/

/-- **Supplier gain.** `3 ≤ q`, `r ≤ 2q - 1`. Let `x` be a complete head of every root in `R`,
all thin, with pairwise different second layers. Then for `w ∈ R` the head `b` of `x` among
the heads of `w` has at least `|R|` heads among the heads of `w`. (For `w' ≠ w` in `R` the
private head `b'` of `x` at `w'` lies in the second layer of `w`, and `b` lies in the second
layer of `w'`, which has no arc back into the heads of `w'`; so `b` misses `|R| - 1` labels of
the second layer of `w`.) -/
theorem supplier_gain (free : QFree D V q) (hq : 3 ≤ q) (reg : ∀ v ∈ V, (outN D V v).card = r)
    (hr : r + 1 ≤ 2 * q) {R : Finset ℕ} (RV : R ⊆ V) (thin : ∀ w ∈ R, Thin D V r w) {x : ℕ}
    (hx : ∀ w ∈ R, x ∈ complete D V w)
    (inj : ∀ w ∈ R, ∀ w' ∈ R, layer D V 2 w = layer D V 2 w' → w = w')
    {w : ℕ} (hw : w ∈ R) {b : ℕ} (hb : b ∈ outN D (outN D V w) x) :
    R.card ≤ (outN D (outN D V w) b).card := by
  classical
  set O := outN D V x with hO
  have xV : x ∈ V := outN_subset (complete_subset (hx w hw))
  have Ocard : O.card = r := reg x xV
  have full : ∀ w' ∈ R, layer D V 2 w' ⊆ O := fun w' hw' =>
    complete_full free (by omega) reg (RV hw') (thin w' hw') (hx w' hw')
  have keep : ∀ w' ∈ R, O ⊆ outN D V w' ∪ layer D V 2 w' := fun w' hw' =>
    head_keep free (by omega) (RV hw') x (complete_subset (hx w' hw'))
  have erase : ∀ w' ∈ R, ∀ c ∈ O, c ∉ layer D V 2 w' → layer D V 2 w' = O.erase c := by
    intro w' hw' c hc nc
    refine eq_of_subset_of_card_le
      (fun y hy => mem_erase.mpr ⟨fun e => nc (e ▸ hy), full w' hw' hy⟩) ?_
    rw [card_erase_of_mem hc, Ocard]
    have := thin w' hw'
    unfold Thin at this
    omega
  -- the private head of `x` at each root
  set β : ℕ → ℕ := fun w' => (O \ layer D V 2 w').sup id with hβ
  have βspec : ∀ w' ∈ R, β w' ∈ O ∧ β w' ∉ layer D V 2 w' := by
    intro w' hw'
    have c1 : (O \ layer D V 2 w').card = 1 := by
      rw [card_sdiff_of_subset (full w' hw'), Ocard]
      have := thin w' hw'
      unfold Thin at this
      omega
    obtain ⟨a, ha⟩ := card_eq_one.mp c1
    have : β w' = a := by simp [hβ, ha]
    rw [this]
    exact mem_sdiff.mp (ha ▸ mem_singleton_self a)
  have βX : ∀ w' ∈ R, β w' ∈ outN D V w' := by
    intro w' hw'
    obtain ⟨bo, bn⟩ := βspec w' hw'
    exact (mem_union.mp (keep w' hw' bo)).resolve_right bn
  have βinj : ∀ w1 ∈ R, ∀ w2 ∈ R, β w1 = β w2 → w1 = w2 := by
    intro w1 h1 w2 h2 e
    refine inj w1 h1 w2 h2 ?_
    rw [erase w1 h1 (β w1) (βspec w1 h1).1 (βspec w1 h1).2,
      erase w2 h2 (β w2) (βspec w2 h2).1 (βspec w2 h2).2, e]
  obtain ⟨bX, xb⟩ := mem_outN.mp hb
  have bO : b ∈ O := mem_outN.mpr ⟨outN_subset bX, xb⟩
  have bY : b ∉ layer D V 2 w := fun h =>
    (mem_layer.mp h).2 ((mem_ball_one (RV hw)).mpr (Or.inr bX))
  have βw : β w = b := by
    by_contra ne
    have := βspec w hw
    rw [erase w hw b bO bY] at this
    exact this.2 (mem_erase.mpr ⟨ne, this.1⟩)
  set B := R.image β with hB
  have Bcard : B.card = R.card := card_image_of_injOn (fun a ha c hc e => βinj a ha c hc e)
  have bB : b ∈ B := mem_image.mpr ⟨w, hw, βw⟩
  -- the other private heads lie in the second layer of `w`, and `b` does not head them
  have other : ∀ w' ∈ R, w' ≠ w → β w' ∈ layer D V 2 w ∧ ¬ D b (β w') = true := by
    intro w' hw' ne
    have bne : β w' ≠ b := fun e => ne (βinj w' hw' w hw (e.trans βw.symm))
    refine ⟨?_, fun arc => ?_⟩
    · rw [erase w hw b bO bY]
      exact mem_erase.mpr ⟨bne, (βspec w' hw').1⟩
    · have bY' : b ∈ layer D V 2 w' := by
        rw [erase w' hw' (β w') (βspec w' hw').1 (βspec w' hw').2]
        exact mem_erase.mpr ⟨bne.symm, bO⟩
      exact no_return_r free hq reg (RV hw') (thin w' hw') hr bY'
        (mem_insert_of_mem (βX w' hw')) arc
  have Bsub : B.erase b ⊆ layer D V 2 w ∩ B := by
    intro c hc
    obtain ⟨cne, cB⟩ := mem_erase.mp hc
    obtain ⟨w', hw', rfl⟩ := mem_image.mp cB
    have ne : w' ≠ w := fun e => cne (e ▸ βw)
    exact mem_inter.mpr ⟨(other w' hw' ne).1, cB⟩
  have cover : outN D V b ⊆ outN D (outN D V w) b ∪ (layer D V 2 w \ B) := by
    intro z hz
    obtain ⟨zV, bz⟩ := mem_outN.mp hz
    rcases mem_union.mp (head_keep free (by omega) (RV hw) b bX hz) with h | h
    · exact mem_union_left _ (mem_outN.mpr ⟨h, bz⟩)
    · refine mem_union_right _ (mem_sdiff.mpr ⟨h, fun zB => ?_⟩)
      obtain ⟨w', hw', e⟩ := mem_image.mp zB
      by_cases ew : w' = w
      · subst ew
        exact bY (by rw [← βw, e]; exact h)
      · exact (other w' hw' ew).2 (e ▸ bz)
  have c := (card_le_card cover).trans (card_union_le _ _)
  rw [reg b (outN_subset bX)] at c
  have split := card_sdiff_add_card_inter (layer D V 2 w) B
  have e1 := card_le_card Bsub
  rw [card_erase_of_mem bB, Bcard] at e1
  have th := thin w hw
  unfold Thin at th
  have pos : 0 < R.card := card_pos.mpr ⟨w, hw⟩
  omega

/-! ### Same second layer, far apart (any regular degree) -/

/-- `CollarTwo.same_far` at out-degree `r`: two distinct roots with the same second layer are
not within `q` of each other (`2 ≤ q`). The proof uses only that the two out-degrees agree. -/
theorem same_far_r (free : QFree D V q) (hq : 2 ≤ q) (reg : ∀ v ∈ V, (outN D V v).card = r)
    {u' : ℕ} (hu : u ∈ V) (hu' : u' ∈ V) (ne : u ≠ u')
    (same : layer D V 2 u = layer D V 2 u') : u' ∉ ball D V u q := by
  classical
  intro h
  by_cases n1 : u' ∈ ball D V u 1
  · rcases (mem_ball_one hu).mp n1 with e | h1
    · exact ne e.symm
    · have sub : outN D V u' ⊆ outN D V u := by
        intro w hw
        rcases mem_union.mp (head_keep free hq hu u' h1 hw) with a | a
        · exact a
        · rw [same] at a
          exact ((mem_layer.mp a).2 ((mem_ball_one hu').mpr (Or.inr hw))).elim
      have eq : outN D V u' = outN D V u :=
        eq_of_subset_of_card_le sub (by rw [reg u hu, reg u' hu'])
      rw [← eq] at h1
      exact loopfree free (by omega) hu' (mem_outN.mp h1).2
  by_cases n2 : u' ∈ ball D V u 2
  · have : u' ∈ layer D V 2 u' := same ▸ mem_layer.mpr ⟨n2, n1⟩
    exact (mem_layer.mp this).2 (self_mem_ball hu')
  · have h' : u' ∈ ball D V u ((q - 2) + 2) := by rwa [show q - 2 + 2 = q by omega]
    obtain ⟨y, hy, back⟩ := CollarTwo.through_second hu (q - 2) u' h' n2
    rw [same] at hy
    obtain ⟨yb, ny⟩ := mem_layer.mp hy
    obtain ⟨-, a, ha, wa⟩ := mem_ball.mp back
    obtain ⟨-, b, hb, wb⟩ := mem_ball.mp yb
    rcases Nat.eq_zero_or_pos b with rfl | bpos
    · exact (ny (FlatAtCutoff.walk_zero wb ▸ self_mem_ball hu')).elim
    · exact free y (a + b) (by omega) (by omega) (wa.append wb)

theorem twins_gap_r (free : QFree D V q) (hq : 2 ≤ q) (reg : ∀ v ∈ V, (outN D V v).card = r)
    {u' : ℕ} (hu : u ∈ V) (hu' : u' ∈ V) (ne : u ≠ u')
    (same : layer D V 2 u = layer D V 2 u') {i j : ℕ} (hi : i ≤ q) (hj : j ≤ q) :
    u' ∈ gap D V i j u :=
  mem_gap.mpr ⟨hu', fun h => same_far_r free hq reg hu hu' ne same (ball_mono_radius hi h),
    fun h => same_far_r free hq reg hu' hu (Ne.symm ne) same.symm (ball_mono_radius hj h)⟩

/-! ### Every second layer is wide; one layer deeper at a tight root -/

/-- **The second layer is wide.** `2 ≤ q`, `r ≤ 2q`: every root has at least `r - 1` labels in
its second layer, else its heads keep minimum out-degree two on `r < 2q + 1` labels. So
`|B 2 u| ≥ 2r` for every root. -/
theorem second_wide (free : QFree D V q) (hq : 2 ≤ q) (reg : ∀ v ∈ V, (outN D V v).card = r)
    (hu : u ∈ V) (hr : r ≤ 2 * q) : r ≤ (layer D V 2 u).card + 1 := by
  by_contra h
  push Not at h
  have inner := DipCost.layer_host (X := outN D V u) (Y := layer D V 2 u) (c := 2)
    (fun x hx => (reg x (outN_subset hx)).ge) (head_keep free hq hu) (by omega)
  obtain ⟨x, hx⟩ : (outN D V u).Nonempty := card_pos.mp (by rw [reg u hu]; omega)
  have big := ball_growth q (by omega) D (outN D V u) (free.mono_set outN_subset)
    (fun v hv => inner v hv) x hx q le_rfl
  have := card_le_card (ball_subset (D := D) (W := outN D V u) (u := x) (k := q))
  rw [reg u hu] at this
  omega

/-- A lone row of a fragment whose heads stay in it or in `B`, `|B| + 1 ≤ r ≤` out-degree,
heads all of `B`. -/
theorem lone_full {A B : Finset ℕ} {y : ℕ} (keep : outN D V y ⊆ A ∪ B)
    (deg : r ≤ (outN D V y).card) (one : (outN D A y).card ≤ 1) (hB : B.card + 1 ≤ r) :
    B ⊆ outN D V y := by
  classical
  have cover : outN D V y ⊆ outN D A y ∪ (B ∩ outN D V y) := by
    intro w hw
    rcases mem_union.mp (keep hw) with h | h
    · exact mem_union_left _ (mem_outN.mpr ⟨h, (mem_outN.mp hw).2⟩)
    · exact mem_union_right _ (mem_inter.mpr ⟨h, hw⟩)
  have c := (card_le_card cover).trans (card_union_le _ _)
  have le := card_le_card (inter_subset_left : B ∩ outN D V y ⊆ B)
  have full : B ∩ outN D V y = B := eq_of_subset_of_card_le inter_subset_left (by omega)
  intro w hw
  rw [← full] at hw
  exact (mem_inter.mp hw).2

/-- At a tight root every row of the second layer has a head in it. -/
theorem y_heads (free : QFree D V q) (hq : 3 ≤ q) (reg : ∀ v ∈ V, (outN D V v).card = r)
    (hu : u ∈ V) (tight : TightR D V r u) (hr : r + 1 ≤ 2 * q) :
    ∀ y ∈ layer D V 2 u, 1 ≤ (outN D (layer D V 2 u) y).card :=
  DipCost.layer_host (fun y hy => (reg y (layer_subset hy)).ge) (y_keep_r free hq reg hu tight.1 hr)
    tight.2

/-- At a tight root a lone row of the second layer heads all of the third layer. -/
theorem y_full (free : QFree D V q) (hq : 3 ≤ q) (reg : ∀ v ∈ V, (outN D V v).card = r)
    (hu : u ∈ V) (tight : TightR D V r u) (hr : r + 1 ≤ 2 * q) {y : ℕ}
    (hy : y ∈ lone D (layer D V 2 u)) : layer D V 3 u ⊆ outN D V y := by
  obtain ⟨yY, one⟩ := mem_lone.mp hy
  exact lone_full (y_keep_r free hq reg hu tight.1 hr y yY) (reg y (layer_subset yY)).ge one
    tight.2

/-- At a tight root, `r ≤ 2q - 1`: at least `2q + 3 - r` lone rows in the second layer. -/
theorem y_lone_count (free : QFree D V q) (hq : 3 ≤ q) (reg : ∀ v ∈ V, (outN D V v).card = r)
    (hu : u ∈ V) (tight : TightR D V r u) (hr : r + 1 ≤ 2 * q) :
    2 * q + 3 ≤ r + (lone D (layer D V 2 u)).card := by
  have cX := complete_count free (by omega) reg hu tight.1 (by omega)
  have cs := card_le_card (complete_subset (D := D) (V := V) (u := u))
  rw [reg u hu] at cs
  have y := tight.1
  obtain ⟨y0, hy0⟩ : (layer D V 2 u).Nonempty := card_pos.mp (by omega)
  have := lone_count (free.mono_set layer_subset) (by omega) (y_heads free hq reg hu tight hr)
    ⟨y0, hy0⟩ (by omega)
  omega

/-- At a tight root no row of the third layer points into the second (`3 ≤ q`, `r ≤ 2q - 1`). -/
theorem z_no_y (free : QFree D V q) (hq : 3 ≤ q) (reg : ∀ v ∈ V, (outN D V v).card = r)
    (hu : u ∈ V) (tight : TightR D V r u) (hr : r + 1 ≤ 2 * q) {z : ℕ}
    (hz : z ∈ layer D V 3 u) {y : ℕ} (hy : y ∈ layer D V 2 u) : ¬ D z y = true := by
  intro zy
  have YV : layer D V 2 u ⊆ V := layer_subset
  have yc := tight.1
  obtain ⟨c, cb, cl⟩ := lone_near (free.mono_set YV) (by omega) (y_heads free hq reg hu tight hr)
    (by omega) hy
  have cz := (mem_outN.mp (y_full free hq reg hu tight hr cl hz)).2
  obtain ⟨-, k, hk, w⟩ := mem_ball.mp cb
  exact free y (k + 1 + 1) (by omega) (by omega)
    (((w.mono YV).snoc (layer_subset hz) cz).snoc (YV hy) zy)

/-- **No return from the third layer to the heads.** At a tight root, `4 ≤ q`, `r ≤ 2q - 1`,
`3r ≤ 5q + 2` (at `q = 5`: `r ≤ 9`): no row of the third layer points to a head of the root.
A head `x` with such a parent has no complete head within `q - 3` among the heads, heads no lone
row of the second layer (each heads the whole third layer), so it has at least `2q + 4 - r`
heads among the heads, and its `(q-3)`-ball there, at least `3q + 1 - r` labels, would fit
among the at most `2r - 2q - 2` heads that are not complete. (Appendix 31, paragraph 3,
generalised.) -/
theorem z_no_x (free : QFree D V q) (hq : 4 ≤ q) (reg : ∀ v ∈ V, (outN D V v).card = r)
    (hu : u ∈ V) (tight : TightR D V r u) (hr : r + 1 ≤ 2 * q) (hr3 : 3 * r ≤ 5 * q + 2)
    {z : ℕ} (hz : z ∈ layer D V 3 u) {x : ℕ} (hx : x ∈ outN D V u) : ¬ D z x = true := by
  classical
  intro zx
  have thin := tight.1
  have XV : outN D V u ⊆ V := outN_subset
  have xV := XV hx
  obtain ⟨y0, hy0, y0z⟩ := ShapeClimbRoot.parent_mem hu (i := 2) (by norm_num) hz
  have zV : z ∈ V := layer_subset hz
  have y0V : y0 ∈ V := layer_subset hy0
  -- no complete head within `q - 3` of `x`
  have farC : ∀ c ∈ ball D (outN D V u) x (q - 3), c ∉ complete D V u := by
    intro c hc cc
    obtain ⟨-, k, hk, w⟩ := mem_ball.mp hc
    have cy := (mem_outN.mp (complete_full free (by omega) reg hu thin cc hy0)).2
    exact free x (k + 1 + 1 + 1) (by omega) (by omega)
      ((((w.mono XV).snoc y0V cy).snoc zV y0z).snoc xV zx)
  -- `x` heads no lone row of the second layer
  have xY : outN D V x ∩ layer D V 2 u ⊆ layer D V 2 u \ lone D (layer D V 2 u) := by
    intro y hy
    obtain ⟨hy1, hy2⟩ := mem_inter.mp hy
    refine mem_sdiff.mpr ⟨hy2, fun yl => ?_⟩
    have yz := (mem_outN.mp (y_full free (by omega) reg hu tight hr yl hz)).2
    exact free x (0 + 1 + 1 + 1) (by omega) (by omega)
      ((((Walk.refl x).snoc (layer_subset hy2) (mem_outN.mp hy1).2).snoc zV yz).snoc xV zx)
  have cY := y_lone_count free (by omega) reg hu tight hr
  have cover : outN D V x ⊆ outN D (outN D V u) x ∪ (outN D V x ∩ layer D V 2 u) := by
    intro t ht
    rcases mem_union.mp (head_keep free (by omega) hu x hx ht) with h | h
    · exact mem_union_left _ (mem_outN.mpr ⟨h, (mem_outN.mp ht).2⟩)
    · exact mem_union_right _ (mem_inter.mpr ⟨ht, h⟩)
  have c1 := (card_le_card cover).trans (card_union_le _ _)
  rw [reg x xV] at c1
  have c2 := card_le_card xY
  rw [card_sdiff_of_subset lone_subset] at c2
  have cX := complete_count free (by omega) reg hu thin (by omega)
  have inN : ball D (outN D V u) x (q - 3) ⊆ outN D V u \ complete D V u :=
    fun c hc => mem_sdiff.mpr ⟨ball_subset hc, farC c hc⟩
  have cN := card_le_card inN
  rw [card_sdiff_of_subset complete_subset, reg u hu] at cN
  have b1 := ReachLedger.ball_one (free.mono_set XV) (by omega) hx
  rcases TubeAtCutoff.closed_or_grow (D := D) (S := outN D V u) (v := x) (a := 1) (M := q - 4)
    with ⟨k, hk1, hkq, cl⟩ | g
  · -- a closed ball of heads that are not complete has minimum out-degree two
    have KX : ball D (outN D V u) x k ⊆ outN D V u := ball_subset
    have Kin : ball D (outN D V u) x k ⊆ ball D (outN D V u) x (q - 3) :=
      ball_mono_radius (by omega)
    have m2 : MinOut2 D (ball D (outN D V u) x k) := by
      intro v hv
      change 2 ≤ (outN D (ball D (outN D V u) x k) v).card
      have vX := KX hv
      have two : 2 ≤ (outN D (outN D V u) v).card := by
        by_contra h
        exact farC v (Kin hv) (mem_lone.mpr ⟨vX, by omega⟩)
      refine two.trans (card_le_card fun t ht => ?_)
      obtain ⟨tX, vt⟩ := mem_outN.mp ht
      exact mem_outN.mpr ⟨cl v hv t tX vt, vt⟩
    have big := ball_growth q (by omega) D _ (free.mono_set (KX.trans XV)) m2 x
      (self_mem_ball hx) q le_rfl
    have := card_le_card (ball_subset (D := D) (W := ball D (outN D V u) x k) (u := x) (k := q))
    have := card_le_card KX
    rw [reg u hu] at this
    omega
  · rw [show 1 + (q - 4) = q - 3 by omega] at g
    omega

/-- At a tight root, `4 ≤ q`, `r ≤ 2q - 1`, `3r ≤ 5q + 2`, rows of the third layer stay in the
third and fourth layers. -/
theorem z_keep (free : QFree D V q) (hq : 4 ≤ q) (reg : ∀ v ∈ V, (outN D V v).card = r)
    (hu : u ∈ V) (tight : TightR D V r u) (hr : r + 1 ≤ 2 * q) (hr3 : 3 * r ≤ 5 * q + 2) :
    ∀ z ∈ layer D V 3 u, outN D V z ⊆ layer D V 3 u ∪ layer D V 4 u := by
  intro z hz t ht
  obtain ⟨tV, zt⟩ := mem_outN.mp ht
  have zb : z ∈ ball D V u 3 := (mem_layer.mp hz).1
  have tb : t ∈ ball D V u 4 := ball_step zb tV zt
  have n2 : t ∉ ball D V u 2 := by
    intro h2
    by_cases h1 : t ∈ ball D V u 1
    · rcases (mem_ball_one hu).mp h1 with rfl | hX
      · exact no_back_arc free hu zb (by omega) zt
      · exact z_no_x free hq reg hu tight hr hr3 hz hX zt
    · exact z_no_y free (by omega) reg hu tight hr hz (mem_layer.mpr ⟨h2, h1⟩) zt
  by_cases n3 : t ∈ ball D V u 3
  · exact mem_union_left _ (mem_layer.mpr ⟨n3, n2⟩)
  · exact mem_union_right _ (mem_layer.mpr ⟨tb, n3⟩)

/-- **The fourth layer is wide.** At a tight root, `4 ≤ q`, `r ≤ 2q - 1`, `3r ≤ 5q + 2`: at
least `r - 1` labels in the fourth layer, so `|B 4 u| ≥ 4r - 2` (`34` at `r = 9`). -/
theorem tight_ball_four (free : QFree D V q) (hq : 4 ≤ q) (reg : ∀ v ∈ V, (outN D V v).card = r)
    (hu : u ∈ V) (tight : TightR D V r u) (hr : r + 1 ≤ 2 * q) (hr3 : 3 * r ≤ 5 * q + 2) :
    r ≤ (layer D V 4 u).card + 1 ∧ 4 * r ≤ (ball D V u 4).card + 2 := by
  have wide : r ≤ (layer D V 4 u).card + 1 := by
    by_contra h
    push Not at h
    have inner := DipCost.layer_host (X := layer D V 3 u) (Y := layer D V 4 u) (c := 2)
      (fun z hz => (reg z (layer_subset hz)).ge) (z_keep free hq reg hu tight hr hr3) (by omega)
    have z3 := tight_third free (by omega) reg hu tight hr
    obtain ⟨z, hz⟩ : (layer D V 3 u).Nonempty := card_pos.mp (by omega)
    have big := ball_growth q (by omega) D (layer D V 3 u) (free.mono_set layer_subset)
      (fun v hv => inner v hv) z hz q le_rfl
    have := card_le_card (ball_subset (D := D) (W := layer D V 3 u) (u := z) (k := q))
    omega
  refine ⟨wide, ?_⟩
  have L := balls_by_layers free (by omega) reg hu
  have b4 : (ball D V u 4).card = (layer D V 4 u).card + (ball D V u 3).card :=
    ShapeClimbRoot.card_ball_succ 3
  have z3 := tight_third free (by omega) reg hu tight hr
  have y := tight.1
  omega

end root

/-! ### The count -/

/-- **No tight root.** `3 ≤ q`, `r ≤ 2q - 1`, radii `i + j ≤ q` with `2 ≤ i`, `1 ≤ j`. Floors
`a`, `b` at radii `i`, `j` and `a'`, `b'` at radii `i + 1`, `j + 1` for tight rows; `A` for the
two balls of a row that is not tight. If loose rows reach the level `|V| + 1`, tight rows fall
short by at most `δ`, `|V| + 1 + 2r ≤ a' + b' + 1 + j` (a complete head serving `s` classes is
`s` above the level: `complete_ball` and `supplier_gain`), and `m (δ + 1) < m² + (2q + 2 - r)`
for every `m`, then no root is tight. Proved through `BankCount.bank_count` with `π = 1`:
savers are the tight roots, the class of a tight root is the largest tight root with the same
second layer, and the bank of a class is the set of complete heads of that root (at least
`2q + 2 - r` of them, `complete_count`). -/
theorem no_tight_thin {V : Finset ℕ} {r i j a b a' b' A δ : ℕ} (free : QFree D V q)
    (hq : 3 ≤ q) (hr : r + 1 ≤ 2 * q) (reg : ∀ v ∈ V, (outN D V v).card = r) (hij : i + j ≤ q)
    (hi : 2 ≤ i) (hj : 1 ≤ j)
    (fa : ∀ v ∈ V, TightR D V r v → a ≤ (ball D V v i).card)
    (fb : ∀ v ∈ V, TightR D V r v → b ≤ (ball D V v j).card)
    (fa' : ∀ v ∈ V, TightR D V r v → a' ≤ (ball D V v (i + 1)).card)
    (fb' : ∀ v ∈ V, TightR D V r v → b' ≤ (ball D V v (j + 1)).card)
    (loose : ∀ v ∈ V, ¬ TightR D V r v → A ≤ (ball D V v i).card + (ball D V v j).card)
    (loosepay : V.card + 1 ≤ A)
    (bankrow : V.card + 1 + 2 * r ≤ a' + b' + 1 + j)
    (tightpay : V.card + 1 ≤ a + b + δ)
    (pay : ∀ m, m * (δ + 1) < m * m + (2 * q + 2 - r)) :
    ∀ v ∈ V, ¬ TightR D V r v := by
  classical
  set S := V.filter (fun v => TightR D V r v) with hS
  set cls : ℕ → ℕ := fun u => (S.filter (fun w => layer D V 2 w = layer D V 2 u)).sup id
    with hcls
  have rep : ∀ u ∈ S, cls u ∈ S ∧ layer D V 2 (cls u) = layer D V 2 u := by
    intro u hu
    obtain ⟨w, hw, he⟩ := exists_mem_eq_sup (S.filter (fun w => layer D V 2 w = layer D V 2 u))
      ⟨u, mem_filter.mpr ⟨hu, rfl⟩⟩ id
    have : cls u = w := he
    rw [this]
    exact mem_filter.mp hw
  have cong : ∀ u u', layer D V 2 u = layer D V 2 u' → cls u = cls u' := by
    intro u u' h
    simp only [hcls, h]
  have sv : S ⊆ V := filter_subset _ _
  have tightOf : ∀ u ∈ S, u ∈ V ∧ TightR D V r u := fun u hu => mem_filter.mp hu
  have empty : S = ∅ := by
    refine BankCount.bank_count (b := 2 * q + 2 - r) (cls := cls) (bank := fun c => complete D V c)
      (π := 1) (δ := δ) free hij sv
      (fun u _ => complete_subset.trans outN_subset)
      (fun u hu => ?_) (fun u hu => ?_) (fun v hv vS => ?_) (fun x hx hp => ?_)
      (fun u hu u' hu' hc ne => ?_) (fun m => by rw [mul_one]; exact pay m)
    · obtain ⟨wV, wt⟩ := tightOf _ (rep u hu).1
      have := complete_count free (by omega) reg wV wt.1 (by omega)
      omega
    · obtain ⟨uV, ut⟩ := tightOf u hu
      have := fa u uV ut
      have := fb u uV ut
      omega
    · have vt : ¬ TightR D V r v := fun h => vS (mem_filter.mpr ⟨hv, h⟩)
      have := loose v hv vt
      omega
    · -- a complete head serving `R.card` classes pays `R.card`
      set R := (S.image cls).filter (fun c => x ∈ complete D V c) with hR
      change 0 < R.card at hp
      change V.card + 1 + 1 * R.card ≤ _
      have Rrep : ∀ c ∈ R, c ∈ S ∧ x ∈ complete D V c := by
        intro c hc
        obtain ⟨cI, xc⟩ := mem_filter.mp hc
        obtain ⟨u, hu, rfl⟩ := mem_image.mp cI
        exact ⟨(rep u hu).1, xc⟩
      have RV : R ⊆ V := fun c hc => sv (Rrep c hc).1
      have inj : ∀ c ∈ R, ∀ c' ∈ R, layer D V 2 c = layer D V 2 c' → c = c' := by
        intro c hc c' hc' e
        obtain ⟨u, hu, rfl⟩ := mem_image.mp (mem_filter.mp hc).1
        obtain ⟨u', hu', rfl⟩ := mem_image.mp (mem_filter.mp hc').1
        rw [(rep u hu).2, (rep u' hu').2] at e
        exact cong u u' e
      obtain ⟨c, hc⟩ := card_pos.mp hp
      obtain ⟨cS, xc⟩ := Rrep c hc
      obtain ⟨cV, ct⟩ := tightOf c cS
      have xX := complete_subset xc
      obtain ⟨b0, hb0⟩ := card_pos.mp (x_heads_r free (by omega) reg cV ct.1 x xX)
      have gain := supplier_gain free hq reg hr RV (fun w hw => (tightOf w (Rrep w hw).1).2.1)
        (fun w hw => (Rrep w hw).2) inj hc hb0
      have bi := complete_ball free (by omega) reg cV ct.1 xc hb0 (j := i) (by omega) (by omega)
      have bj := complete_ball free (by omega) reg cV ct.1 xc hb0 (j := j) hj (by omega)
      have XV : outN D V c ⊆ V := outN_subset
      have b0X := (mem_outN.mp hb0).1
      have one := ReachLedger.ball_one (free.mono_set XV) (by omega) b0X
      have mono := card_le_card
        (ball_mono_radius (D := D) (W := outN D V c) (u := b0) (show 1 ≤ i - 1 by omega))
      have grow := ball_grow (free.mono_set XV) (x_heads_r free (by omega) reg cV ct.1) b0X
        (j - 1) (by omega)
      have := fa' c cV ct
      have := fb' c cV ct
      omega
    · have same : layer D V 2 u = layer D V 2 u' := by
        rw [← (rep u hu).2, ← (rep u' hu').2, hc]
      exact twins_gap_r free (by omega) reg (sv hu) (sv hu') (Ne.symm ne) same
        (by omega) (by omega)
  intro v hv h
  have : v ∈ S := mem_filter.mpr ⟨hv, h⟩
  rw [empty] at this
  simp at this

/-! ### Short thin roots: the count with per-root bank floors -/

/-- **No short thin root.** `3 ≤ q`, `r ≤ 2q - 1`, radii `i + j ≤ q`, `2 ≤ i`, `1 ≤ j`. Rows
that are not thin reach the level `|V| + 1` at radii `(i, j)`; thin rows fall short by at most
`δ`; every thin row below the level has `|V| + 1 + 2r ≤ |B (i+1)| + |B (j+1)| + 1 + j`; and
`m (δ + 1) < m² + (2q + 2 - r)` for every `m`. Then every thin row reaches the level. Same
count as `no_tight_thin` (`BankCount.bank_count`, `π = 1`), with savers the thin roots below
the level, classes by second layer, banks the complete heads. -/
theorem no_short_thin {V : Finset ℕ} {r i j δ : ℕ} (free : QFree D V q)
    (hq : 3 ≤ q) (hr : r + 1 ≤ 2 * q) (reg : ∀ v ∈ V, (outN D V v).card = r) (hij : i + j ≤ q)
    (hi : 2 ≤ i) (hj : 1 ≤ j)
    (fat : ∀ v ∈ V, ¬ Thin D V r v → V.card + 1 ≤ (ball D V v i).card + (ball D V v j).card)
    (short : ∀ v ∈ V, Thin D V r v →
      V.card + 1 ≤ (ball D V v i).card + (ball D V v j).card + δ)
    (bankrow : ∀ v ∈ V, Thin D V r v →
      (ball D V v i).card + (ball D V v j).card < V.card + 1 →
      V.card + 1 + 2 * r ≤ (ball D V v (i + 1)).card + (ball D V v (j + 1)).card + 1 + j)
    (pay : ∀ m, m * (δ + 1) < m * m + (2 * q + 2 - r)) :
    ∀ v ∈ V, Thin D V r v → V.card + 1 ≤ (ball D V v i).card + (ball D V v j).card := by
  classical
  set S := V.filter (fun v => Thin D V r v ∧
    (ball D V v i).card + (ball D V v j).card < V.card + 1) with hS
  set cls : ℕ → ℕ := fun u => (S.filter (fun w => layer D V 2 w = layer D V 2 u)).sup id
    with hcls
  have rep : ∀ u ∈ S, cls u ∈ S ∧ layer D V 2 (cls u) = layer D V 2 u := by
    intro u hu
    obtain ⟨w, hw, he⟩ := exists_mem_eq_sup (S.filter (fun w => layer D V 2 w = layer D V 2 u))
      ⟨u, mem_filter.mpr ⟨hu, rfl⟩⟩ id
    have : cls u = w := he
    rw [this]
    exact mem_filter.mp hw
  have cong : ∀ u u', layer D V 2 u = layer D V 2 u' → cls u = cls u' := by
    intro u u' h
    simp only [hcls, h]
  have sv : S ⊆ V := filter_subset _ _
  have ofS : ∀ u ∈ S, u ∈ V ∧ Thin D V r u ∧
      (ball D V u i).card + (ball D V u j).card < V.card + 1 := fun u hu => mem_filter.mp hu
  have empty : S = ∅ := by
    refine BankCount.bank_count (b := 2 * q + 2 - r) (cls := cls)
      (bank := fun c => complete D V c) (π := 1) (δ := δ) free hij sv
      (fun u _ => complete_subset.trans outN_subset)
      (fun u hu => ?_) (fun u hu => ?_) (fun v hv vS => ?_) (fun x hx hp => ?_)
      (fun u hu u' hu' hc ne => ?_) (fun m => by rw [mul_one]; exact pay m)
    · obtain ⟨wV, wt, -⟩ := ofS _ (rep u hu).1
      have := complete_count free (by omega) reg wV wt (by omega)
      omega
    · obtain ⟨uV, ut, -⟩ := ofS u hu
      exact short u uV ut
    · by_cases vt : Thin D V r v
      · by_contra low
        exact vS (mem_filter.mpr ⟨hv, vt, by omega⟩)
      · exact fat v hv vt
    · set R := (S.image cls).filter (fun c => x ∈ complete D V c) with hR
      change 0 < R.card at hp
      change V.card + 1 + 1 * R.card ≤ _
      have Rrep : ∀ c ∈ R, c ∈ S ∧ x ∈ complete D V c := by
        intro c hc
        obtain ⟨cI, xc⟩ := mem_filter.mp hc
        obtain ⟨u, hu, rfl⟩ := mem_image.mp cI
        exact ⟨(rep u hu).1, xc⟩
      have RV : R ⊆ V := fun c hc => sv (Rrep c hc).1
      have inj : ∀ c ∈ R, ∀ c' ∈ R, layer D V 2 c = layer D V 2 c' → c = c' := by
        intro c hc c' hc' e
        obtain ⟨u, hu, rfl⟩ := mem_image.mp (mem_filter.mp hc).1
        obtain ⟨u', hu', rfl⟩ := mem_image.mp (mem_filter.mp hc').1
        rw [(rep u hu).2, (rep u' hu').2] at e
        exact cong u u' e
      obtain ⟨c, hc⟩ := card_pos.mp hp
      obtain ⟨cS, xc⟩ := Rrep c hc
      obtain ⟨cV, ct, clow⟩ := ofS c cS
      have xX := complete_subset xc
      obtain ⟨b0, hb0⟩ := card_pos.mp (x_heads_r free (by omega) reg cV ct x xX)
      have gain := supplier_gain free hq reg hr RV (fun w hw => (ofS w (Rrep w hw).1).2.1)
        (fun w hw => (Rrep w hw).2) inj hc hb0
      have bi := complete_ball free (by omega) reg cV ct xc hb0 (j := i) (by omega) (by omega)
      have bj := complete_ball free (by omega) reg cV ct xc hb0 (j := j) hj (by omega)
      have XV : outN D V c ⊆ V := outN_subset
      have b0X := (mem_outN.mp hb0).1
      have one := ReachLedger.ball_one (free.mono_set XV) (by omega) b0X
      have mono := card_le_card
        (ball_mono_radius (D := D) (W := outN D V c) (u := b0) (show 1 ≤ i - 1 by omega))
      have grow := ball_grow (free.mono_set XV) (x_heads_r free (by omega) reg cV ct) b0X
        (j - 1) (by omega)
      have := bankrow c cV ct clow
      omega
    · have same : layer D V 2 u = layer D V 2 u' := by
        rw [← (rep u hu).2, ← (rep u' hu').2, hc]
      exact twins_gap_r free (by omega) reg (sv hu) (sv hu') (Ne.symm ne) same
        (by omega) (by omega)
  intro v hv vt
  by_contra low
  have : v ∈ S := mem_filter.mpr ⟨hv, vt, by omega⟩
  rw [empty] at this
  simp at this

/-! ### The instances at `r = 9`, `q = 5` (inclusive ball floors) -/

section nine
variable {V : Finset ℕ}

/-- The ball cards of a root at `r = 9`, `q = 5`: `|B 2| = |Y| + 10 ≥ 18`, `|B 3| = |Z| + |B 2|`;
a thin root has `|Z| ≥ 8`, a tight one `|Z| = 8` and `|B 4| ≥ 34`. -/
theorem nine_facts (free : QFree D V 5) (reg : ∀ v ∈ V, (outN D V v).card = 9) {v : ℕ}
    (hv : v ∈ V) :
    (ball D V v 2).card = (layer D V 2 v).card + 10 ∧
      (ball D V v 3).card = (layer D V 3 v).card + (ball D V v 2).card ∧
      8 ≤ (layer D V 2 v).card ∧
      (Thin D V 9 v → 8 ≤ (layer D V 3 v).card) ∧
      (TightR D V 9 v → (layer D V 3 v).card = 8 ∧ 34 ≤ (ball D V v 4).card) := by
  have L := balls_by_layers free (by norm_num) reg hv
  have sw := second_wide free (by norm_num) reg hv (by norm_num)
  refine ⟨by omega, by omega, by omega, fun t => ?_, fun t => ?_⟩
  · have := third_wide free (by norm_num) reg hv t (by norm_num)
    omega
  · have := tight_third free (by norm_num) reg hv t (by norm_num)
    have := (tight_ball_four free (by norm_num) reg hv t (by norm_num) (by norm_num)).2
    omega

/-- At `r = 9`, `q = 5`, a root that is not tight, with three-ball floor `26`, scores at least
`45` at radii `(2, 3)`. -/
theorem loose_45 (free : QFree D V 5) (reg : ∀ v ∈ V, (outN D V v).card = 9)
    {v : ℕ} (hv : v ∈ V) (t : ¬ TightR D V 9 v) (f3 : 26 ≤ (ball D V v 3).card) :
    45 ≤ (ball D V v 2).card + (ball D V v 3).card := by
  obtain ⟨b2, b3, y8, -, -⟩ := nine_facts free reg hv
  unfold TightR at t
  by_cases y : (layer D V 2 v).card + 1 = 9
  · have z : ¬ (layer D V 3 v).card + 1 ≤ 9 := fun h => t ⟨y, h⟩
    omega
  · omega

/-- **No tight root at 44.** `r = 9`, `q = 5`, `44` labels, and the floor `26` at radius three
for rows that are not tight (the value of the `ShapeClimbAvoid.tightA 9` climb). Tight rows have
balls `18, 26, 34` (`nine_facts`), one short of `45` at radii `(2, 3)`; other rows reach `45`
(`loose_45`); a complete head serving `s` classes has `|B 2| ≥ 26 + 1 + s - 9` and
`|B 3| ≥ 34 + 3 - 9`, so `45 + s`; at least `3` complete heads per class; `2m < m² + 3`. -/
theorem no_tight_44 (free : QFree D V 5) (reg : ∀ v ∈ V, (outN D V v).card = 9)
    (n : V.card = 44) (f3 : ∀ v ∈ V, ¬ TightR D V 9 v → 26 ≤ (ball D V v 3).card) :
    ∀ v ∈ V, ¬ TightR D V 9 v := by
  have tb : ∀ v ∈ V, TightR D V 9 v → (ball D V v 2).card = 18 ∧
      (ball D V v 3).card = 26 ∧ 34 ≤ (ball D V v 4).card := by
    intro v hv t
    obtain ⟨b2, b3, -, -, ht⟩ := nine_facts free reg hv
    have := ht t
    have := t.1
    omega
  refine no_tight_thin (i := 2) (j := 3) (a := 18) (b := 26) (a' := 26) (b' := 34) (A := 45)
    (δ := 1) free (by norm_num) (by norm_num) reg (by norm_num) le_rfl (by norm_num)
    (fun v hv t => (tb v hv t).1.ge) (fun v hv t => (tb v hv t).2.1.ge)
    (fun v hv t => (tb v hv t).2.1.ge) (fun v hv t => (tb v hv t).2.2)
    (fun v hv t => loose_45 free reg hv t (f3 v hv t)) (by omega) (by omega)
    (by omega) (fun m => ?_)
  show m * 2 < m * m + 3
  rcases Nat.lt_or_ge m 2 with h | h
  · interval_cases m <;> omega
  · have := Nat.mul_le_mul_right m h
    omega

/-- Every score at least the level and the ledger: every score is exactly the level. -/
theorem exact_level {i j : ℕ} (free : QFree D V q) (hij : i + j ≤ q)
    (low : ∀ v ∈ V, V.card + 1 ≤ (ball D V v i).card + (ball D V v j).card) :
    ∀ v ∈ V, (ball D V v i).card + (ball D V v j).card = V.card + 1 := by
  have led := ReachLedger.ledger free hij
  intro v hv
  by_contra ne
  have lt : ∑ _w ∈ V, (V.card + 1) < ∑ w ∈ V, ((ball D V w i).card + (ball D V w j).card) :=
    sum_lt_sum low ⟨v, hv, by have := low v hv; omega⟩
  rw [sum_const, smul_eq_mul, sum_add_distrib] at lt
  omega

/-- **No thin root at an exact level.** `r = 9`, `q = 5`, every score at radii `(2, 3)` exactly
`L ≥ 45`, and rows with `|B 2| ≥ L - 25` have `|B 3| ≥ L - 19`. Then no root is thin: a thin
root has `|B 3| = L - 18`, so a complete head `x` of it has `|B 2 x| ≥ L - 18 + 2 - 9`
(`complete_ball`), and `x` would score `2L - 44 > L`. -/
theorem thin_exact (free : QFree D V 5) (reg : ∀ v ∈ V, (outN D V v).card = 9) {L : ℕ}
    (hL : 45 ≤ L) (exact : ∀ v ∈ V, (ball D V v 2).card + (ball D V v 3).card = L)
    (fatfloor : ∀ v ∈ V, L ≤ (ball D V v 2).card + 25 → L ≤ (ball D V v 3).card + 19)
    {v : ℕ} (hv : v ∈ V) (thin : Thin D V 9 v) : False := by
  obtain ⟨x, hx⟩ : (complete D V v).Nonempty := card_pos.mp (by
    have := complete_count free (by norm_num) reg hv thin (by norm_num)
    omega)
  have xV := outN_subset (complete_subset hx)
  obtain ⟨b0, hb0⟩ := card_pos.mp
    (x_heads_r free (by norm_num) reg hv thin x (complete_subset hx))
  have b0X := (mem_outN.mp hb0).1
  have bx : (ball D V v 3).card + (ball D (outN D V v) b0 1).card ≤ (ball D V x 2).card + 9 :=
    complete_ball free (by norm_num) reg hv thin hx hb0 (j := 2) (by norm_num) (by norm_num)
  have one := ReachLedger.ball_one (free.mono_set (outN_subset (D := D) (W := V) (y := v)))
    (by norm_num) b0X
  have pos := x_heads_r free (by norm_num) reg hv thin b0 b0X
  have ex := exact x xV
  have ev := exact v hv
  obtain ⟨b2, -, -, -, -⟩ := nine_facts free reg hv
  have th := thin
  unfold Thin at th
  have := fatfloor x xV (by omega)
  omega

/-- **What remains at 44.** `r = 9`, `q = 5`, `44` labels, floor `26` at radius three for rows
that are not tight: every root has second layer `9` and third layer `7` (balls `19, 26`). No
root is tight (`no_tight_44`); every score at radii `(2, 3)` is at least `45`, so every score is
exactly `45` (`exact_level`); a thin root that is not tight has `|B 3| ≥ 27`, and its complete
heads would score above `45` (`thin_exact`). -/
theorem profile_44 (free : QFree D V 5) (reg : ∀ v ∈ V, (outN D V v).card = 9)
    (n : V.card = 44) (f3 : ∀ v ∈ V, ¬ TightR D V 9 v → 26 ≤ (ball D V v 3).card) :
    ∀ v ∈ V, (layer D V 2 v).card = 9 ∧ (layer D V 3 v).card = 7 := by
  have none := no_tight_44 free reg n f3
  have low : ∀ v ∈ V, V.card + 1 ≤ (ball D V v 2).card + (ball D V v 3).card := fun v hv => by
    have := loose_45 free reg hv (none v hv) (f3 v hv (none v hv))
    omega
  have exact := exact_level free (by norm_num) low
  rw [n] at exact
  intro v hv
  obtain ⟨b2, b3, y8, -, -⟩ := nine_facts free reg hv
  have e := exact v hv
  have := f3 v hv (none v hv)
  have notthin : ¬ Thin D V 9 v := by
    intro thin
    have z : ¬ (layer D V 3 v).card + 1 ≤ 9 := fun h => none v hv ⟨thin, h⟩
    refine thin_exact free reg le_rfl exact (fun x xV _ => ?_) hv thin
    have := f3 x xV (none x xV)
    omega
  unfold Thin at notthin
  omega

/-- **44 vertices, modulo one pattern.** If moreover every root whose second layer has at least
`9` labels has three-ball at least `27` (the unproved exclusion of the widths `[9, y, z]`,
`y ≥ 9`, `y + z ≤ 16`: dossier Appendix 30, "f3 = 25 forces f2 = 17"), there is no `q`-free
`9`-regular digraph on `44` labels at `q = 5`. No other floor is assumed: a root that is not
tight is thin with third layer at least `9`, or has second layer at least `9` (`second_wide`). -/
theorem no_44_of_fatShort (free : QFree D V 5) (reg : ∀ v ∈ V, (outN D V v).card = 9)
    (n : V.card = 44)
    (fatShort : ∀ v ∈ V, 9 ≤ (layer D V 2 v).card → 27 ≤ (ball D V v 3).card) : False := by
  have f3 : ∀ v ∈ V, ¬ TightR D V 9 v → 26 ≤ (ball D V v 3).card := by
    intro v hv t
    obtain ⟨b2, b3, y8, -, -⟩ := nine_facts free reg hv
    unfold TightR at t
    by_cases y : (layer D V 2 v).card + 1 = 9
    · have z : ¬ (layer D V 3 v).card + 1 ≤ 9 := fun h => t ⟨y, h⟩
      omega
    · have := fatShort v hv (by omega)
      omega
  obtain ⟨v, hv⟩ : V.Nonempty := card_pos.mp (by omega)
  obtain ⟨y, z⟩ := profile_44 free reg n f3 v hv
  obtain ⟨b2, b3, -, -, -⟩ := nine_facts free reg hv
  have := fatShort v hv (by omega)
  omega

/-- **What remains at 45.** `r = 9`, `q = 5`, `45` labels. Hypotheses: the floor `33` at radius
four for thin roots that are not tight (the `tightA 9` climb gives `33` for every root that is
not tight), and the unproved pattern `fatShort` as in `no_44_of_fatShort`. Then every root has
second layer `9` and third layer `8` (balls `19, 27`): the uniform profile of dossier
Appendix 31, "The uniform profile is impossible". Proof: rows that are not thin reach `46`
(`fatShort`); thin rows are at most `2` short; a short thin root `w` is tight (`|B 3| = 26`,
`|B 4| ≥ 34`, `tight_ball_four`) or has `|B 3| = 27`, `|B 4| ≥ 33`, and either way
`46 + 18 ≤ |B 3 w| + |B 4 w| + 4`; `3m < m² + 3`. So `no_short_thin` puts every row at `46` or
more, the ledger makes every score `46`, `thin_exact` removes thin roots, and `46 = 19 + 27`. -/
theorem profile_45 (free : QFree D V 5) (reg : ∀ v ∈ V, (outN D V v).card = 9)
    (n : V.card = 45)
    (f4 : ∀ v ∈ V, Thin D V 9 v → ¬ TightR D V 9 v → 33 ≤ (ball D V v 4).card)
    (fatShort : ∀ v ∈ V, 9 ≤ (layer D V 2 v).card → 27 ≤ (ball D V v 3).card) :
    ∀ v ∈ V, (layer D V 2 v).card = 9 ∧ (layer D V 3 v).card = 8 := by
  have fat : ∀ v ∈ V, ¬ Thin D V 9 v →
      V.card + 1 ≤ (ball D V v 2).card + (ball D V v 3).card := by
    intro v hv nt
    obtain ⟨b2, b3, y8, -, -⟩ := nine_facts free reg hv
    unfold Thin at nt
    have := fatShort v hv (by omega)
    omega
  have thinOK := no_short_thin (i := 2) (j := 3) (δ := 2) free (by norm_num) (by norm_num) reg
    (by norm_num) le_rfl (by norm_num) fat
    (fun v hv t => by
      obtain ⟨b2, b3, -, z8, -⟩ := nine_facts free reg hv
      have := z8 t
      unfold Thin at t
      omega)
    (fun v hv t low => by
      show V.card + 1 + 2 * 9 ≤ (ball D V v 3).card + (ball D V v 4).card + 1 + 3
      obtain ⟨b2, b3, -, z8, ht⟩ := nine_facts free reg hv
      have := z8 t
      have th : (layer D V 2 v).card + 1 = 9 := t
      by_cases tt : TightR D V 9 v
      · have := ht tt
        omega
      · have := f4 v hv t tt
        have zz : ¬ (layer D V 3 v).card + 1 ≤ 9 := fun h => tt ⟨t, h⟩
        omega)
    (fun m => by
      show m * 3 < m * m + 3
      rcases Nat.lt_or_ge m 3 with h | h
      · interval_cases m <;> omega
      · have := Nat.mul_le_mul_right m h
        omega)
  have low : ∀ v ∈ V, V.card + 1 ≤ (ball D V v 2).card + (ball D V v 3).card := by
    intro v hv
    by_cases t : Thin D V 9 v
    · exact thinOK v hv t
    · exact fat v hv t
  have exact := exact_level free (by norm_num) low
  rw [n] at exact
  intro v hv
  obtain ⟨b2, b3, y8, -, -⟩ := nine_facts free reg hv
  have e := exact v hv
  have notthin : ¬ Thin D V 9 v := by
    intro thin
    refine thin_exact free reg (by norm_num) exact (fun x xV h => ?_) hv thin
    obtain ⟨c2, -, -, -, -⟩ := nine_facts free reg xV
    have := fatShort x xV (by omega)
    omega
  unfold Thin at notthin
  have := fatShort v hv (by omega)
  omega

end nine

#print axioms lone_count
#print axioms lone_near
#print axioms complete_count
#print axioms complete_full
#print axioms no_return_r
#print axioms third_wide
#print axioms second_wide
#print axioms complete_ball
#print axioms supplier_gain
#print axioms same_far_r
#print axioms twins_gap_r
#print axioms y_lone_count
#print axioms z_no_x
#print axioms tight_ball_four
#print axioms no_tight_thin
#print axioms no_short_thin
#print axioms no_tight_44
#print axioms profile_44
#print axioms no_44_of_fatShort
#print axioms profile_45
end LeanCH.BR.ThinSuppliers
