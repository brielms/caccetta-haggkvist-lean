import checkpoints.shen_extension.JointShortcutReplay

/-!
# The lone deficient row: exact columns, the erased head, and the swapped bank

Setting. `D` is `q`-free on `V`, `U ⊆ V` are the survivors, the quota is `t`, the row `x ∈ U` has
`t-1` surviving heads and every other surviving row has at least `t`. `NoHost q t` and `|U| ≤ q t`.
A *tight parent* of `x` is a surviving `y → x` with exactly `t` surviving heads. A *candidate
column* is a surviving `k ≠ x` with `x ↛ k`.

* `column`, `row_iff_far`: the exact table. Column `k` is blocked by a tight parent `y` together
  with a walk `k ⇝ y` of at most `q-2` arcs that stays inside the candidate columns. The two-step
  table of `BypassTwoStepRow` is the shadow of this one (`far_of_routes`).
* `head_split`, `head_bill`: for any label `h`, either all surviving heads of `h` other than `x`
  lie in the row of `x` (and `h` owes the bill), or a named candidate head `k` of `h` is blocked by
  a tight parent that misses `h`; if `x → h` the blocking walk has exactly `q-2` arcs.
* `slots_floor`: on a marked bank the bill forces `q(r-1)+3 ≤ |V|`.
* `swap_return`: exchange `x` with an erased `h` that keeps `t` heads. The short rows of the new
  survivor set are exactly the tight parents of `x` that miss `h`, they share the erased parent
  `x`, and for every affordable cut one of them has an exact `(q-1)`-return from every head of `x`
  it misses.
* `lost_head_deep`: the capstone-facing fork on the same `x, y, h`.
* `pair_parent`: at order `q(r-1)+2` every two labels have a common parent of native degree `r`.
* `parent_bypass`: remove every arc into `x`. Then `x` is on no closed walk, and each tight parent
  may take a head of `x` it misses. For every affordable cut some tight parent has an exact
  `(q-1)`-return from every such head.
* `near_exit`: the lone child closes from `NoNearHost q (r-1)`, a statement about the survivors
  alone.
-/

namespace LeanCH.BR.LoneRow
open Finset BRq2 BRq3 FundedCascade BypassRepair BypassBankReplay BypassTwoStepRow JointShortcut
  JointShortcutReplay

variable {D : CH.Digraph} {V U B : Finset ℕ} {q t x : ℕ}

/-- The hypotheses of the lone-row child, on the actual labels. -/
structure Lone (D : CH.Digraph) (V U : Finset ℕ) (q t x : ℕ) : Prop where
  none : NoHost q t
  small : U.card ≤ q*t
  free : QFree D V q
  uv : U ⊆ V
  xu : x ∈ U
  row : (outN D U x).card + 1 = t
  other : ∀ a ∈ U, a ≠ x → t ≤ (outN D U a).card

theorem on_cell {q r} {X : ShenMinimumOrder.Source q r} {m : Cell}
    (none : NoHost q (r-1)) (cell : Marked X m) (lone : LoneBlocked X m) :
    Lone X.D X.V (X.V \ m.bank) q (r-1) m.x := by
  have size := cell.size
  have card := card_sdiff_add_card_eq_card cell.sub
  exact ⟨none, by omega, X.free, sdiff_subset, cell.xu, cell.deficit, lone.paid_elsewhere⟩

/-- Candidate columns: surviving labels other than `x` that `x` misses. -/
def cols (D : CH.Digraph) (U : Finset ℕ) (x : ℕ) : Finset ℕ :=
  U.filter (fun k => k ≠ x ∧ D x k ≠ true)

theorem mem_cols {k : ℕ} : k ∈ cols D U x ↔ k ∈ U ∧ k ≠ x ∧ D x k ≠ true := mem_filter

theorem cols_subset : cols D U x ⊆ U := filter_subset _ _

/-- A walk of at most `q-2` arcs on the survivors that ends at a parent of `x` never leaves the
candidate columns. -/
theorem walk_cols (free : QFree D V q) (uv : U ⊆ V) (xu : x ∈ U) {a y l : ℕ}
    (w : Walk D U a y l) (yx : D y x = true) (cap : l + 2 ≤ q) : Walk D (cols D U x) a y l := by
  induction w with
  | refl => exact .refl _
  | @step a b c k bu ab rest ih =>
    have bx : b ≠ x := by
      rintro rfl
      exact free c (k+1) (by omega) (by omega) (.step (uv xu) yx (rest.mono uv))
    have fresh : D x b ≠ true := fun xb =>
      free c (k+1+1) (by omega) (by omega)
        (.step (uv xu) yx (.step (uv bu) xb (rest.mono uv)))
    exact .step (mem_cols.mpr ⟨bu, bx, fresh⟩) ab (ih yx (by omega))

/-- One entry of the exact table: the tight parent `y` blocks the column `k` at depth `l`. -/
structure Blocks (D : CH.Digraph) (V U : Finset ℕ) (q t x y k l : ℕ) : Prop where
  column : k ∈ cols D U x
  parent : TightParent D U t x y
  short : l + 2 ≤ q
  walk : Walk D (cols D U x) k y l
  returns : ∀ i, 0 < i → i + l ≤ q → ¬ Walk D V y k i

/-- **Every candidate column is blocked, with its depth.** -/
theorem column (L : Lone D V U q t x) {k : ℕ} (kc : k ∈ cols D U x) :
    ∃ y l, Blocks D V U q t x y k l := by
  obtain ⟨ku, kx, fresh⟩ := mem_cols.mp kc
  obtain ⟨y, tight, l, cap, w, back⟩ :=
    blocked_return L.none L.small L.free L.uv L.xu L.row L.other ku kx fresh
  exact ⟨y, l, kc, tight, cap, walk_cols L.free L.uv L.xu w tight.2.2.1 cap, back⟩

/-- **The exact row.** `x → k` precisely when no tight parent is within `q-2` arcs of `k` on the
survivors. -/
theorem row_iff_far (L : Lone D V U q t x) {k : ℕ} (ku : k ∈ U) (kx : k ≠ x) :
    D x k = true ↔ ∀ y, TightParent D U t x y → ∀ l, l + 2 ≤ q → ¬ Walk D U k y l := by
  constructor
  · intro xk y tight l cap w
    exact L.free y (l+1+1) (by omega) (by omega)
      (.step (L.uv L.xu) tight.2.2.1 (.step (L.uv ku) xk (w.mono L.uv)))
  · intro far
    by_contra fresh
    obtain ⟨y, l, blk⟩ := column L (mem_cols.mpr ⟨ku, kx, fresh⟩)
    exact far y blk.parent l blk.short (blk.walk.mono cols_subset)

/-- The closing premise in its exact form: one candidate column far from every tight parent. -/
theorem far_exit (L : Lone D V U q t x) {k : ℕ} (kc : k ∈ cols D U x)
    (far : ∀ y, TightParent D U t x y → ∀ l, l + 2 ≤ q → ¬ Walk D U k y l) : False := by
  obtain ⟨ku, kx, fresh⟩ := mem_cols.mp kc
  exact fresh ((row_iff_far L ku kx).mpr far)

/-- A common two-step target is far, so `far_exit` contains the two-step exit. -/
theorem far_of_routes (free : QFree D V q) (uv : U ⊆ V) {k : ℕ}
    (routes : ∀ y, TightParent D U t x y → Walk D V y k 2) :
    ∀ y, TightParent D U t x y → ∀ l, l + 2 ≤ q → ¬ Walk D U k y l :=
  fun y tight l cap w =>
    free y (2+l) (by omega) (by omega) ((routes y tight).append (w.mono uv))

namespace Blocks

variable {y k l : ℕ}

theorem kv (b : Blocks D V U q t x y k l) (uv : U ⊆ V) : k ∈ V := uv (cols_subset b.column)

/-- The blocking parent has no intermediary to its column, erased or not. -/
theorem no_route (b : Blocks D V U q t x y k l) (uv : U ⊆ V) {h : ℕ} (hv : h ∈ V)
    (yh : D y h = true) : D h k ≠ true := fun hk =>
  b.returns 2 (by decide) (by have := b.short; omega) (.step hv yh (.step (b.kv uv) hk (.refl k)))

/-- A column two native steps after `x` is blocked at depth exactly `q-2`. -/
theorem deep (b : Blocks D V U q t x y k l) (uv : U ⊆ V) (xu : x ∈ U) {h : ℕ} (hv : h ∈ V)
    (xh : D x h = true) (hk : D h k = true) : l + 2 = q := by
  by_contra ne
  have cap := b.short
  exact b.returns 3 (by decide) (by omega)
    (.step (uv xu) b.parent.2.2.1 (.step hv xh (.step (b.kv uv) hk (.refl k))))

/-- The blocking parent has an erased head, and that head misses the column. -/
theorem erased_head (b : Blocks D V U q t x y k l) (uv : U ⊆ V)
    (high : t < (outN D V y).card) : ∃ h ∈ V \ U, D y h = true ∧ D h k ≠ true := by
  have lost : ∃ h ∈ V \ U, D y h = true := by
    by_contra no
    push Not at no
    have sub : outN D V y ⊆ outN D U y := by
      intro j hj
      obtain ⟨jv, arc⟩ := mem_outN.mp hj
      refine mem_outN.mpr ⟨?_, arc⟩
      by_contra ju
      exact no j (mem_sdiff.mpr ⟨jv, ju⟩) arc
    have le := card_le_card sub
    have eq := b.parent.2.2.2
    omega
  obtain ⟨h, hw, arc⟩ := lost
  exact ⟨h, hw, arc, b.no_route uv (mem_sdiff.mp hw).1 arc⟩

end Blocks

/-- **The erased head, with its column.** For any label `h`: either every surviving head of `h`
other than `x` lies in the row of `x`, or some candidate head `k` of `h` is blocked by a tight
parent `v` that misses `h`. If `x → h`, the blocking walk has exactly `q-2` arcs. -/
theorem head_split (L : Lone D V U q t x) {h : ℕ} (hv : h ∈ V) :
    (outN D U h).erase x ⊆ outN D U x ∨
    ∃ k ∈ cols D U x, D h k = true ∧ ∃ v l, Blocks D V U q t x v k l ∧ D v h ≠ true ∧
      (D x h = true → l + 2 = q) := by
  by_cases sub : (outN D U h).erase x ⊆ outN D U x
  · exact Or.inl sub
  · obtain ⟨k, hk, off⟩ := not_subset.mp sub
    obtain ⟨kx, head⟩ := mem_erase.mp hk
    obtain ⟨ku, arc⟩ := mem_outN.mp head
    have kc : k ∈ cols D U x := mem_cols.mpr ⟨ku, kx, fun xk => off (mem_outN.mpr ⟨ku, xk⟩)⟩
    obtain ⟨v, l, blk⟩ := column L kc
    exact Or.inr ⟨k, kc, arc, v, l, blk, fun vh => blk.no_route L.uv hv vh arc,
      fun xh => blk.deep L.uv L.xu hv xh arc⟩

/-- The bill of the first alternative needs no assumption on which tight parents feed `h`. -/
theorem head_bill (uv : U ⊆ V) (xu : x ∈ U) {h : ℕ}
    (sub : (outN D U h).erase x ⊆ outN D U x) :
    (outN D V h).card ≤ (outN D (V \ U) h).card +
      (if D h x = true then 1 else 0) + (outN D U x).card := by
  have row : outN D V h = outN D (V \ U) h ∪ outN D U h := by
    ext k
    simp only [mem_outN, mem_union, mem_sdiff]
    grind
  have le := card_le_card sub
  have parts := card_union_le (outN D (V \ U) h) (outN D U h)
  rw [row]
  by_cases hx : D h x = true
  · have := card_erase_add_one (mem_outN.mpr ⟨xu, hx⟩)
    simp only [hx, ↓reduceIte]
    omega
  · simp only [hx]
    rw [erase_eq_of_notMem (show x ∉ outN D U h from fun hit => hx (mem_outN.mp hit).2)] at le
    omega

/-! ### The bill raises the order floor -/

/-- On a marked bank, an erased head that owes two slots inside the bank and the marked row needs
a bank of at least three labels. -/
theorem slots_floor {q r} {X : ShenMinimumOrder.Source q r} {m : Cell} (hq : 2 ≤ q)
    (cell : Marked X m) {h : ℕ} (hb : h ∈ m.bank)
    (bill : 2 ≤ (outN X.D m.bank h).card + (if X.D h m.x = true then 1 else 0)) :
    q*(r-1)+3 ≤ X.V.card := by
  by_contra! small
  have size := cell.size
  have eq := missed_slots (D := X.D) m.x cell.sub
  have deg := X.degree m.x (mem_sdiff.mp cell.xu).1
  have row := cell.deficit
  have empty : m.bank \ outN X.D m.bank m.x = ∅ := card_eq_zero.mp (by omega)
  have xh : X.D m.x h = true := by
    by_contra off
    have hit : h ∈ m.bank \ outN X.D m.bank m.x :=
      mem_sdiff.mpr ⟨hb, fun inRow => off (mem_outN.mp inRow).2⟩
    rw [empty] at hit
    exact absurd hit (notMem_empty h)
  have hx : X.D h m.x ≠ true := fun back =>
    digonfree X.free hq (cell.sub hb) (mem_sdiff.mp cell.xu).1 back xh
  have inner : outN X.D m.bank h ⊆ m.bank.erase h := by
    intro k hk
    obtain ⟨kb, arc⟩ := mem_outN.mp hk
    refine mem_erase.mpr ⟨?_, kb⟩
    rintro rfl
    exact loopfree X.free (by omega) (cell.sub kb) arc
  have le := card_le_card inner
  have one := card_erase_add_one hb
  split_ifs at bill with back
  · exact hx back
  · omega

theorem descendant_slots_floor {q r n} {X : ShenMinimumOrder.Source q r} {m : Cell} (hq : 2 ≤ q)
    (cell : Marked X m) {h : ℕ} (hb : h ∈ m.bank)
    (bill : 2 ≤ (outN X.D m.bank h).card + (if X.D h m.x = true then 1 else 0))
    (order : X.V.card ≤ n) : q*(r-1)+3 ≤ n := (slots_floor hq cell hb bill).trans order

/-! ### Exchanging `x` with an erased head -/

/-- The bank after `x` and the erased `h` change places. -/
abbrev swap (B : Finset ℕ) (x h : ℕ) : Finset ℕ := insert x (B.erase h)

variable {h : ℕ}

theorem swap_eligible (bank : Eligible V B q t) (xu : x ∈ V \ B) (hb : h ∈ B) :
    Eligible V (swap B x h) q t := by
  obtain ⟨xv, xb⟩ := mem_sdiff.mp xu
  refine ⟨insert_subset xv ((erase_subset _ _).trans bank.sub), ?_, ⟨h, mem_sdiff.mpr ⟨bank.sub hb, ?_⟩⟩⟩
  · have one := card_erase_add_one hb
    rw [card_insert_of_notMem (fun hit => xb (mem_of_mem_erase hit))]
    have := bank.size
    omega
  · intro hit
    rcases mem_insert.mp hit with e | e
    · exact xb (e ▸ hb)
    · exact (mem_erase.mp e).1 rfl

theorem old_row_sub (a : ℕ) : (outN D (V \ B) a).erase x ⊆ outN D (V \ swap B x h) a := by
  intro k hk
  obtain ⟨kx, head⟩ := mem_erase.mp hk
  obtain ⟨ku, arc⟩ := mem_outN.mp head
  obtain ⟨kv, kb⟩ := mem_sdiff.mp ku
  refine mem_outN.mpr ⟨mem_sdiff.mpr ⟨kv, fun hit => ?_⟩, arc⟩
  rcases mem_insert.mp hit with e | e
  · exact kx e
  · exact kb (mem_of_mem_erase e)

/-- **Who is short after the exchange.** Apart from `h` itself, exactly the tight parents of `x`
that miss `h`. -/
theorem swap_short (sub : B ⊆ V) (xu : x ∈ V \ B) (hb : h ∈ B)
    (other : ∀ a ∈ V \ B, a ≠ x → t ≤ (outN D (V \ B) a).card)
    {a : ℕ} (au : a ∈ V \ swap B x h) (ah : a ≠ h)
    (low : (outN D (V \ swap B x h) a).card < t) :
    TightParent D (V \ B) t x a ∧ D a h ≠ true := by
  obtain ⟨av, off⟩ := mem_sdiff.mp au
  have ax : a ≠ x := fun e => off (mem_insert.mpr (Or.inl e))
  have ab : a ∉ B := fun hit => off (mem_insert.mpr (Or.inr (mem_erase.mpr ⟨ah, hit⟩)))
  have aU : a ∈ V \ B := mem_sdiff.mpr ⟨av, ab⟩
  have ge := other a aU ax
  have keep := card_le_card (old_row_sub (D := D) (V := V) (B := B) (x := x) (h := h) a)
  have hit : x ∈ outN D (V \ B) a := by
    by_contra miss
    rw [erase_eq_of_notMem miss] at keep
    omega
  have one := card_erase_add_one hit
  refine ⟨⟨aU, ax, (mem_outN.mp hit).2, by omega⟩, fun arc => ?_⟩
  have fresh : h ∉ (outN D (V \ B) a).erase x := fun inRow =>
    (mem_sdiff.mp (outN_subset (mem_of_mem_erase inRow))).2 hb
  have hU : h ∈ V \ swap B x h := by
    refine mem_sdiff.mpr ⟨sub hb, fun hit' => ?_⟩
    rcases mem_insert.mp hit' with e | e
    · exact (mem_sdiff.mp xu).2 (e ▸ hb)
    · exact (mem_erase.mp e).1 rfl
  have more : insert h ((outN D (V \ B) a).erase x) ⊆ outN D (V \ swap B x h) a :=
    insert_subset (mem_outN.mpr ⟨hU, arc⟩) (old_row_sub a)
  have big := card_le_card more
  rw [card_insert_of_notMem fresh] at big
  omega

/-- After the exchange every short row points to the erased `x`, provided `h` keeps its quota. -/
theorem swap_shared (sub : B ⊆ V) (xu : x ∈ V \ B) (hb : h ∈ B)
    (other : ∀ a ∈ V \ B, a ≠ x → t ≤ (outN D (V \ B) a).card)
    (hrow : t ≤ (outN D (V \ swap B x h) h).card) :
    SharedParent D (V \ swap B x h) t x := by
  refine ⟨fun u uu short => ?_⟩
  have uh : u ≠ h := by
    rintro rfl
    omega
  exact (swap_short sub xu hb other uu uh short).1.2.2.1

/-- The own-return debt of the swapped bank, with `x` as the shared erased parent. -/
theorem swap_debt (free : QFree D V q) (hq : 1 ≤ q) (none : NoHost q t)
    (bank : Eligible V B q t) (xu : x ∈ V \ B) (hb : h ∈ B)
    (other : ∀ a ∈ V \ B, a ≠ x → t ≤ (outN D (V \ B) a).card)
    (hrow : t ≤ (outN D (V \ swap B x h) h).card) :
    OwnReturnDebt D (V \ swap B x h) q t x :=
  shared_debt free hq none (swap_eligible bank xu hb) (mem_sdiff.mp xu).1
    (swap_shared bank.sub xu hb other hrow)

/-- For every affordable cut on the swapped survivors, one tight parent of `x` that misses `h`
has an exact `(q-1)`-return from every surviving head of `x` it misses. -/
structure SwapReturn (D : CH.Digraph) (V B : Finset ℕ) (q t x h : ℕ) : Prop where
  at_cut : ∀ C : ℕ → Finset ℕ,
    (∀ c ∈ V \ swap B x h, (C c).card ≤ spare D (V \ swap B x h) t c) →
    ∃ v, TightParent D (V \ B) t x v ∧ D v h ≠ true ∧
      ∀ z ∈ V \ swap B x h, D x z = true → D v z ≠ true →
        Walk (cut D C) (V \ swap B x h) z v (q-1)

/-- **The swapped bank.** -/
theorem swap_return (free : QFree D V q) (hq : 1 ≤ q) (none : NoHost q t)
    (bank : Eligible V B q t) (xu : x ∈ V \ B) (hb : h ∈ B)
    (other : ∀ a ∈ V \ B, a ≠ x → t ≤ (outN D (V \ B) a).card)
    (hrow : t ≤ (outN D (V \ swap B x h) h).card) : SwapReturn D V B q t x h := by
  classical
  refine ⟨fun C budget => ?_⟩
  obtain ⟨u, uu, short, few⟩ := (swap_debt free hq none bank xu hb other hrow).at_cut C budget
  have uh : u ≠ h := by
    rintro rfl
    omega
  obtain ⟨tight, miss⟩ := swap_short bank.sub xu hb other uu uh short
  have keep := card_le_card (old_row_sub (D := D) (V := V) (B := B) (x := x) (h := h) u)
  have one := card_erase_add_one (show x ∈ outN D (V \ B) u from mem_outN.mpr ⟨xu, tight.2.2.1⟩)
  have full := tight.2.2.2
  have empty : JointShortcut.clear D (cut D C) (V \ swap B x h) q x u = ∅ :=
    card_eq_zero.mp (by omega)
  refine ⟨u, tight, miss, fun z zu xz uz => ?_⟩
  by_contra no
  have hit : z ∈ JointShortcut.clear D (cut D C) (V \ swap B x h) q x u :=
    mem_filter.mpr ⟨zu, xz, uz, no⟩
  rw [empty] at hit
  exact absurd hit (notMem_empty z)

/-- If `h` falls below quota after the exchange, it owes the same bill as before. -/
theorem swap_bill (deg : t < (outN D V h).card)
    (low : (outN D (V \ swap B x h) h).card < t) :
    2 ≤ (outN D B h).card + (if D h x = true then 1 else 0) := by
  by_cases hx : D h x = true
  · have cover : outN D V h ⊆ insert x (outN D (V \ swap B x h) h ∪ outN D B h) := by
      intro k hk
      obtain ⟨kv, arc⟩ := mem_outN.mp hk
      by_cases kx : k = x
      · exact mem_insert.mpr (Or.inl kx)
      · refine mem_insert_of_mem ?_
        by_cases kb : k ∈ B
        · exact mem_union_right _ (mem_outN.mpr ⟨kb, arc⟩)
        · refine mem_union_left _ (mem_outN.mpr ⟨mem_sdiff.mpr ⟨kv, fun hit => ?_⟩, arc⟩)
          rcases mem_insert.mp hit with e | e
          · exact kx e
          · exact kb (mem_of_mem_erase e)
    have le := card_le_card cover
    have ins := card_insert_le x (outN D (V \ swap B x h) h ∪ outN D B h)
    have parts := card_union_le (outN D (V \ swap B x h) h) (outN D B h)
    simp only [hx, ↓reduceIte]
    omega
  · have cover : outN D V h ⊆ outN D (V \ swap B x h) h ∪ outN D B h := by
      intro k hk
      obtain ⟨kv, arc⟩ := mem_outN.mp hk
      by_cases kb : k ∈ B
      · exact mem_union_right _ (mem_outN.mpr ⟨kb, arc⟩)
      · refine mem_union_left _ (mem_outN.mpr ⟨mem_sdiff.mpr ⟨kv, fun hit => ?_⟩, arc⟩)
        rcases mem_insert.mp hit with e | e
        · exact hx (e ▸ arc)
        · exact kb (mem_of_mem_erase e)
    have le := card_le_card cover
    have parts := card_union_le (outN D (V \ swap B x h) h) (outN D B h)
    simp only [hx]
    omega

/-! ### The capstone-facing fork on the same `x, y, h` -/

/-- **Lost head, both alternatives sharpened.** Keep the tight parent `y` and its erased head
`h`. Either `h` owes two slots inside the bank and the marked row, and then the source has order
at least `q(r-1)+3`; or the swapped bank has its own-return debt at tight parents missing `h`, and
a named candidate head `k` of `h` is blocked by a tight parent `v ≠ y` that misses `h`, along a
walk inside the candidate columns (of exactly `q-2` arcs when `x → h`). -/
theorem lost_head_deep {q r} {X : ShenMinimumOrder.Source q r} {m : Cell} {y h : ℕ}
    (hq : 2 ≤ q) (none : NoHost q (r-1)) (cell : Marked X m) (lone : LoneBlocked X m)
    (mark : LostAt X.D (X.V \ m.bank) m.bank (r-1) m.x y h) :
    (2 ≤ (outN X.D m.bank h).card + (if X.D h m.x = true then 1 else 0) ∧
      q*(r-1)+3 ≤ X.V.card) ∨
    (SwapReturn X.D X.V m.bank q (r-1) m.x h ∧
      ∃ k ∈ cols X.D (X.V \ m.bank) m.x, X.D h k = true ∧
        ∃ v l, Blocks X.D X.V (X.V \ m.bank) q (r-1) m.x v k l ∧ v ≠ y ∧ X.D v h ≠ true ∧
          (X.D m.x h = true → l + 2 = q)) := by
  have L := on_cell none cell lone
  have hb := mark.erased
  have hv := cell.sub hb
  have deg : r-1 < (outN X.D X.V h).card := by
    have := X.degree h hv
    have := cell.deficit
    omega
  by_cases hrow : r-1 ≤ (outN X.D (X.V \ swap m.bank m.x h) h).card
  · refine Or.inr ⟨swap_return X.free (by omega) none (marked_bank cell) cell.xu hb
      lone.paid_elsewhere hrow, ?_⟩
    rcases head_split L hv with sub | ⟨k, kc, arc, v, l, blk, miss, depth⟩
    · exfalso
      have keep := card_le_card sub
      have small : outN X.D (X.V \ swap m.bank m.x h) h ⊆
          (outN X.D (X.V \ m.bank) h).erase m.x := by
        intro k hk
        obtain ⟨kw, arc⟩ := mem_outN.mp hk
        obtain ⟨kv, off⟩ := mem_sdiff.mp kw
        have kx : k ≠ m.x := fun e => off (mem_insert.mpr (Or.inl e))
        have kh : k ≠ h := by
          rintro rfl
          exact loopfree X.free (by omega) hv arc
        have kb : k ∉ m.bank := fun hit =>
          off (mem_insert.mpr (Or.inr (mem_erase.mpr ⟨kh, hit⟩)))
        exact mem_erase.mpr ⟨kx, mem_outN.mpr ⟨mem_sdiff.mpr ⟨kv, kb⟩, arc⟩⟩
      have le := card_le_card small
      have row := L.row
      omega
    · exact ⟨k, kc, arc, v, l, blk, fun e => miss (e ▸ mark.lost), miss, depth⟩
  · have bill := swap_bill (B := m.bank) (x := m.x) deg (Nat.lt_of_not_ge hrow)
    exact Or.inl ⟨bill, slots_floor hq cell hb bill⟩

/-- Every erased label of a lone cell whose bank has two labels is in the second alternative. -/
theorem band_head {q r} {X : ShenMinimumOrder.Source q r} {m : Cell} {y h : ℕ}
    (hq : 2 ≤ q) (none : NoHost q (r-1)) (cell : Marked X m) (lone : LoneBlocked X m)
    (mark : LostAt X.D (X.V \ m.bank) m.bank (r-1) m.x y h)
    (band : X.V.card = q*(r-1)+2) :
    SwapReturn X.D X.V m.bank q (r-1) m.x h ∧
      ∃ k ∈ cols X.D (X.V \ m.bank) m.x, X.D h k = true ∧
        ∃ v l, Blocks X.D X.V (X.V \ m.bank) q (r-1) m.x v k l ∧ v ≠ y ∧ X.D v h ≠ true ∧
          (X.D m.x h = true → l + 2 = q) := by
  rcases lost_head_deep hq none cell lone mark with ⟨_, floor⟩ | deep
  · omega
  · exact deep

/-! ### Two deleted labels at the floor order -/

/-- At order `q(r-1)+2` every two labels have a common parent of native degree exactly `r`. -/
theorem pair_parent {r : ℕ} (none : NoHost q (r-1)) (free : QFree D V q) (hq : 1 ≤ q)
    (hr : 2 ≤ r) (deg : ∀ v ∈ V, r ≤ (outN D V v).card) (band : V.card = q*(r-1)+2)
    {u v : ℕ} (uV : u ∈ V) (vV : v ∈ V) (ne : u ≠ v) :
    ∃ a ∈ V, a ≠ u ∧ a ≠ v ∧ D a u = true ∧ D a v = true ∧ (outN D V a).card = r := by
  have sub : ({u, v} : Finset ℕ) ⊆ V := insert_subset uV (singleton_subset_iff.mpr vV)
  have two : ({u, v} : Finset ℕ).card = 2 := card_pair ne
  have card := card_sdiff_add_card_eq_card sub
  have pos : 0 < q*(r-1) := Nat.mul_pos (by omega) (by omega)
  have live : (V \ {u, v}).Nonempty := card_pos.mp (by omega)
  by_contra no
  apply none D (V \ {u, v}) live (by omega) (free.mono_set sdiff_subset)
  intro a aw
  by_contra low
  obtain ⟨av, off⟩ := mem_sdiff.mp aw
  have eq := missed_slots (D := D) a sub
  have big := deg a av
  have empty : ({u, v} : Finset ℕ) \ outN D {u, v} a = ∅ := card_eq_zero.mp (by omega)
  have inRow : ∀ j ∈ ({u, v} : Finset ℕ), D a j = true := by
    intro j hj
    by_contra miss
    have hit : j ∈ ({u, v} : Finset ℕ) \ outN D {u, v} a :=
      mem_sdiff.mpr ⟨hj, fun r => miss (mem_outN.mp r).2⟩
    rw [empty] at hit
    exact absurd hit (notMem_empty j)
  exact no ⟨a, av, fun e => off (by simp [e]), fun e => off (by simp [e]),
    inRow u (mem_insert_self u {v}), inRow v (mem_insert_of_mem (mem_singleton_self v)), by omega⟩

/-- On a lone cell at the floor order, every candidate column shares with `x` a parent of native
degree exactly `r`. -/
theorem band_column_parent {q r} {X : ShenMinimumOrder.Source q r} {m : Cell} (hq : 2 ≤ q)
    (none : NoHost q (r-1)) (cell : Marked X m) (band : X.V.card = q*(r-1)+2) {k : ℕ}
    (kc : k ∈ cols X.D (X.V \ m.bank) m.x) :
    ∃ a ∈ X.V, a ≠ m.x ∧ a ≠ k ∧ X.D a m.x = true ∧ X.D a k = true ∧
      (outN X.D X.V a).card = r := by
  obtain ⟨ku, kx, _⟩ := mem_cols.mp kc
  have row := cell.deficit
  exact pair_parent none X.free (by omega) (by omega) X.degree band (mem_sdiff.mp cell.xu).1
    (mem_sdiff.mp ku).1 (Ne.symm kx)

/-! ### Bypassing every tight parent -/

/-- One more arc out of a label that has no incoming arcs is always safe. -/
theorem source_add {K : CH.Digraph} {F : Finset Arc} {k : ℕ}
    (base : QFree (install K F) U q) (noin : ∀ c, install K F c x ≠ true) (kx : k ≠ x) :
    QFree (install K (insert (x, k) F)) U q := by
  have arc : ∀ a b, install K (insert (x, k) F) a b = true →
      install K F a b = true ∨ (a = x ∧ b = k) := by
    intro a b h
    rcases install_cases h with old | new
    · exact Or.inl (install_old old)
    · rcases mem_insert.mp new with e | e
      · exact Or.inr ⟨(Prod.mk.inj e).1, (Prod.mk.inj e).2⟩
      · exact Or.inl (install_new e)
  have off : ∀ {a b m}, Walk (install K (insert (x, k) F)) U a b m → a ≠ x →
      Walk (install K F) U a b m := by
    intro a b m w
    induction w with
    | refl => exact fun _ => .refl _
    | @step a c b m cu ac rest ih =>
      intro ax
      rcases arc a c ac with old | ⟨e, _⟩
      · exact .step cu old (ih (fun e => noin a (by rw [← e]; exact old)))
      · exact absurd e ax
  intro a m pos cap w
  by_cases ax : a = x
  · rw [ax] at w
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    obtain ⟨y, _, _, last⟩ := w.unsnoc
    rcases arc y x last with old | ⟨_, e⟩
    · exact noin y old
    · exact kx e.symm
  · exact base a m pos cap (off w ax)

/-- **Bypass law.** Remove every arc into `x`; then `x` lies on no closed walk and may take any
extra head, and each tight parent `y` needs one new head, which it may take among the heads of
`x` it misses. So for every further cut that is affordable on the survivors without `x`, some
tight parent has an exact `(q-1)`-return from every head of `x` it misses. -/
theorem parent_bypass (L : Lone D V U q t x) (hq : 1 ≤ q) {k : ℕ} (kc : k ∈ cols D U x)
    (C : ℕ → Finset ℕ) (budget : ∀ c ∈ U, (C c).card ≤ spare D (U.erase x) t c) :
    ∃ y, TightParent D U t x y ∧ ∀ a ∈ U, D x a = true → D y a ≠ true →
      Walk (cut D (fun c => insert x (C c))) U a y (q-1) := by
  classical
  by_contra no
  push Not at no
  choose! f hf using no
  let FT : Finset Arc := (U.filter (fun y => TightParent D U t x y)).image (fun y => (y, f y))
  have memFT : ∀ j, j ∈ FT → TightParent D U t x j.1 ∧ j.2 = f j.1 := by
    intro j hj
    obtain ⟨y, yT, rfl⟩ := mem_image.mp hj
    exact ⟨(mem_filter.mp yT).2, rfl⟩
  have xv := L.uv L.xu
  have noloop : D x x ≠ true := loopfree L.free hq xv
  obtain ⟨ku, kx, xk⟩ := mem_cols.mp kc
  have base : QFree (install (cut D (fun c => insert x (C c))) FT) U q := by
    apply safe_of_parent_order (par := fun _ => x) (ρ := fun _ => 0) L.free hq L.uv cut_sub
    · intro j hj
      obtain ⟨tight, e⟩ := memFT j hj
      rw [e]
      exact (hf _ tight).1
    · exact fun _ _ => xv
    · intro j hj
      obtain ⟨tight, e⟩ := memFT j hj
      rw [e]
      exact (hf _ tight).2.1
    · exact fun _ _ j' hj' _ => (memFT j' hj').1.2.2.1
    · intro j hj
      obtain ⟨tight, e⟩ := memFT j hj
      rw [e]
      exact (hf _ tight).2.2.2
  have noin : ∀ c, install (cut D (fun c => insert x (C c))) FT c x ≠ true := by
    intro c h
    rcases install_cases h with old | new
    · simp [cut] at old
    · obtain ⟨tight, e⟩ := memFT _ new
      have e' : x = f c := e
      have arc := (hf c tight).2.1
      rw [← e'] at arc
      exact noloop arc
  have safe := source_add base noin kx
  have inU : ∀ j ∈ insert (x, k) FT, j.2 ∈ U := by
    intro j hj
    rcases mem_insert.mp hj with rfl | hj
    · exact ku
    · obtain ⟨tight, e⟩ := memFT j hj
      rw [e]
      exact (hf _ tight).1
  have fresh : ∀ j ∈ insert (x, k) FT, D j.1 j.2 ≠ true := by
    intro j hj
    rcases mem_insert.mp hj with rfl | hj
    · exact xk
    · obtain ⟨tight, e⟩ := memFT j hj
      rw [e]
      exact (hf _ tight).2.2.1
  have pays : ∀ u ∈ U, t + (outN D U u ∩ insert x (C u)).card ≤
      (outN D U u).card + (newHeads (insert (x, k) FT) u).card := by
    intro u uu
    have b : (C u).card ≤ (outN D (U.erase x) u).card - t := budget u uu
    have er : outN D (U.erase x) u = (outN D U u).erase x := by
      ext j
      simp only [mem_outN, mem_erase]
      tauto
    rw [er] at b
    by_cases ux : D u x = true
    · have ne : u ≠ x := by
        rintro rfl
        exact noloop ux
      have one := card_erase_add_one (mem_outN.mpr ⟨L.xu, ux⟩)
      have ge := L.other u uu ne
      have capI : (outN D U u ∩ insert x (C u)).card ≤ (C u).card + 1 :=
        (card_le_card inter_subset_right).trans (card_insert_le _ _)
      by_cases tight : (outN D U u).card = t
      · have new : 0 < (newHeads (insert (x, k) FT) u).card :=
          card_pos.mpr ⟨f u, mem_newHeads.mpr (mem_insert_of_mem
            (mem_image.mpr ⟨u, mem_filter.mpr ⟨uu, uu, ne, ux, tight⟩, rfl⟩))⟩
        omega
      · omega
    · have capI : (outN D U u ∩ insert x (C u)).card ≤ (C u).card := by
        apply card_le_card
        intro j hj
        obtain ⟨jr, jc⟩ := mem_inter.mp hj
        rcases mem_insert.mp jc with e | e
        · exact absurd (e ▸ (mem_outN.mp jr).2) ux
        · exact e
      rw [erase_eq_of_notMem (fun hit => ux (mem_outN.mp hit).2)] at b
      by_cases e : u = x
      · have row := L.row
        have new : 0 < (newHeads (insert (x, k) FT) u).card :=
          card_pos.mpr ⟨k, mem_newHeads.mpr (by rw [e]; exact mem_insert_self _ _)⟩
        rw [e] at b capI ⊢
        rw [e] at new
        omega
      · have ge := L.other u uu e
        omega
  obtain ⟨E, free, deg⟩ := joint_host inU fresh pays safe
  exact L.none E U ⟨x, L.xu⟩ L.small free deg

/-- The bypass law as one packet: it holds for every affordable cut. -/
structure BypassReturn (D : CH.Digraph) (U : Finset ℕ) (q t x : ℕ) : Prop where
  at_cut : ∀ C : ℕ → Finset ℕ, (∀ c ∈ U, (C c).card ≤ spare D (U.erase x) t c) →
    ∃ y, TightParent D U t x y ∧ ∀ a ∈ U, D x a = true → D y a ≠ true →
      Walk (cut D (fun c => insert x (C c))) U a y (q-1)

/-- The bypass law on the live cell, with the marked target as the extra head of `x`. -/
theorem marked_bypass {q r} {X : ShenMinimumOrder.Source q r} {m : Cell} (hq : 2 ≤ q)
    (none : NoHost q (r-1)) (cell : Marked X m) (lone : LoneBlocked X m) :
    BypassReturn X.D (X.V \ m.bank) q (r-1) m.x := by
  have zx : m.target ≠ m.x := fun e =>
    digonfree X.free hq (cell.sub cell.erased) (mem_sdiff.mp cell.xu).1
      (by rw [← e]; exact cell.pz) cell.xp
  exact ⟨fun C budget => parent_bypass (on_cell none cell lone) (by omega)
    (mem_cols.mpr ⟨cell.zu, zx, cell.fresh⟩) C budget⟩

/-! ### The bank and the columns -/

/-- A blocking parent does not point to its column. -/
theorem Blocks.no_arc {y k l : ℕ} (b : Blocks D V U q t x y k l) (uv : U ⊆ V) :
    D y k ≠ true := fun yk =>
  b.returns 1 (by decide) (by have := b.short; omega) (.step (b.kv uv) yk (.refl k))

/-- **No candidate column is a head of every erased label.** Each column has a blocking tight
parent, and an erased head of that parent misses the column. -/
theorem column_bank (L : Lone D V U q t x) (deg : ∀ v ∈ V, t < (outN D V v).card) {k : ℕ}
    (kc : k ∈ cols D U x) :
    ∃ y l, Blocks D V U q t x y k l ∧ ∃ h ∈ V \ U, D y h = true ∧ D h k ≠ true := by
  obtain ⟨y, l, blk⟩ := column L kc
  exact ⟨y, l, blk, blk.erased_head L.uv (deg y (L.uv blk.parent.1))⟩

/-! ### The premise in carrier-free form -/

/-- No `q`-free digraph on at most `q t` labels has exactly one row short of `t`, short by one. -/
def NoNearHost (q t : ℕ) : Prop :=
  ∀ (E : CH.Digraph) (U : Finset ℕ) (x : ℕ), x ∈ U → U.card ≤ q * t → QFree E U q →
    (outN E U x).card + 1 = t → ¬ ∀ a ∈ U, a ≠ x → t ≤ (outN E U a).card

/-- The survivors of a lone cell are such a digraph. -/
theorem near_exit {q r} {X : ShenMinimumOrder.Source q r} {m : Cell}
    (near : NoNearHost q (r-1)) (cell : Marked X m) (lone : LoneBlocked X m) : False := by
  have size := cell.size
  have card := card_sdiff_add_card_eq_card cell.sub
  exact near X.D (X.V \ m.bank) m.x cell.xu (by omega) (X.free.mono_set sdiff_subset)
    cell.deficit lone.paid_elsewhere

/-- For a single short row, short by one, a far column is all that a lower-quota host needs:
without one, the survivors are a near-host in which every candidate column is blocked. -/
theorem near_table {E : CH.Digraph} {W : Finset ℕ} {x : ℕ} (none : NoHost q t)
    (xw : x ∈ W) (small : W.card ≤ q * t) (free : QFree E W q)
    (row : (outN E W x).card + 1 = t) (other : ∀ a ∈ W, a ≠ x → t ≤ (outN E W a).card)
    {k : ℕ} (kc : k ∈ cols E W x) : ∃ y l, Blocks E W W q t x y k l :=
  column ⟨none, small, free, Subset.rfl, xw, row, other⟩ kc

#print axioms column
#print axioms row_iff_far
#print axioms far_exit
#print axioms far_of_routes
#print axioms Blocks.no_route
#print axioms Blocks.deep
#print axioms Blocks.erased_head
#print axioms head_split
#print axioms head_bill
#print axioms slots_floor
#print axioms descendant_slots_floor
#print axioms swap_short
#print axioms swap_debt
#print axioms swap_return
#print axioms swap_bill
#print axioms lost_head_deep
#print axioms band_head
#print axioms pair_parent
#print axioms band_column_parent
#print axioms Blocks.no_arc
#print axioms column_bank
#print axioms near_exit
#print axioms near_table
#print axioms source_add
#print axioms parent_bypass
#print axioms marked_bypass
end LeanCH.BR.LoneRow
