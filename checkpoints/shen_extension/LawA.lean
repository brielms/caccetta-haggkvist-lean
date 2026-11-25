import checkpoints.shen_extension.HostTwo
import checkpoints.shen_extension.FatShort

/-!
# Law A: short heads of a thin root

Every out-degree is exactly `r`, no closed walk of length `1..q`. A root `u` has heads
`X = outN u` and second layer `Y = layer 2 u`; it is *thin* when `|Y| = r - 1`. A label is
*short* when its second layer has at most `r - 1` labels.

**Law A** (`law_A`, `law_A_4_9`): at a thin root, `4 ≤ q`, `r ≤ 2q + 1`, at most one head is
short. Mechanism (found by SAT, proved here): a short head `x` of a thin root points to every
other head (`short_head_heads_all`, "H1"); two short heads would then form a digon. The proof
reads only the rows of `u`, of `X` and of `B = F ∩ Y`, and uses exact out-degree only at `u` and
`x` (elsewhere only `≥ r`); the statements assume out-degree exactly `r` everywhere. SAT agrees:
the rows of `Y \ F` and the condition that every label of `Y` has a parent in `X` are not needed.

Notation for a head `x` of `u`: `F = outN x`, `L = layer 2 x`, `A = F ∩ X`, `B = F ∩ Y`,
`K = L ∩ X` (heads of `u` at distance two from `x`), `M = X \ ({x} ∪ F ∪ L)` (heads of `u` at
distance at least three from `x`). If `x` misses a head of `u` then `|B| = 1 + |K| + |M| ≥ 2`.

* `deficit_base`, `deficit_order` (generic): a `q`-free set of minimum out-degree `d ≥ 2` in which
  at most `t` rows have out-degree exactly `d` (`t + 2 ≤ q + d`, `t + 6 ≤ 2q + d`, `2 ≤ q`) has at
  least `2q + d + 1` labels — one more than `FatShort.order_deg` gives. Base `d = 2`: delete a
  label `w` headed by no deficient row; the rest is a rigid degree-two host (`host_two_out`), so
  every other full row heads `w`, the heads of `w` are deficient, and a deficient head of `w`
  reaches a full row within `q - 2` steps: a closed walk through `w`.
* `case_far` (case (i), `|L ∩ (X ∪ Y)| ≤ |Y \ F|`, e.g. `K = ∅`): rows of `A` keep a head in `A`;
  the lone rows of `A` head all of `B`; by `lone_near` every row of `A` reaches all of `B`
  within `q - 1` steps, so no row of `B` heads `A`; then `A` and `B` both have minimum out-degree
  one, `|A|, |B| ≥ q + 1`, against `|A| + |B| = r ≤ 2q + 1`.
* `case_near` (case (ii), `K ≠ ∅`, `|M| + 2 ≤ q`, `|M| + 6 ≤ 2q`): on `W = F ∪ K` rows of `A`
  and `K` have at least `|K| + 2` heads, rows of `B` at least `|K| + 1`; `deficit_order` gives
  `|W| ≥ 2q + |K| + 2 > r + |K| = |W|`.
* `ball_heavy` (generic): iterated `FatShort.grow_min` from a row with many heads.
* `case_deep` (case (iii), `K ≠ ∅`, `q ≤ |M| + 1`): on `W = F ∪ K` every in-degree is at most
  `|K| + 2` (`indeg_ball`, `ball_growth`), rows of `A` have at least `|B| + 1` heads and, by
  `ball_heavy`, in-degree `0` (`|K| ≥ 2`) or at most `1` (`|K| = 1`); in- and out-degrees
  balance (`arcs_between`): `|A| (|B| + 1 - ι) ≤ |B|`. Left: `|K| = |A| = 1`, where `A = {a}`
  heads all of `W`, so `W \ {a}` is a `q`-free set of `r` labels, minimum out-degree two, with
  a row of three heads: impossible (`order_deg`, `host_two_out`).
* `short_head_heads_all` (`4 ≤ q`, `r ≤ 2q + 1`): the three cases cover everything.
* `law_A_of_full` (generic): H1 for every short head gives at most one short head.
* `law_A`, `law_A_4_9`: Law A; `short_head_full`, `law_A_near`: the versions with `3 ≤ q` and
  `|M| + 2 ≤ q`, `|M| + 6 ≤ 2q` (cases (i)-(ii) only).

Not covered: `q = 3` with `|M| = 1` (SAT: Law A also holds at `q = 3`, `r ≤ 7`), and
`r ≥ 2q + 2`, where Law A is false (SAT: two short heads at `(q, r) = (3, 8)`; at `(5, 12)` a
short head with one head among the heads).
-/

set_option linter.style.longLine false
namespace LeanCH.BR.LawA
open Finset BRq2 BRq3 FifthStripAll RigidHost LoopCollar
open DotTwoPassShellTransport (layer layer_subset)
open ShapeClimbRoot (mem_layer)
open ThinSuppliers (lone mem_lone lone_subset lone_near lone_full)

variable {D : CH.Digraph} {q : ℕ}

/-! ### One more label than `order_deg` -/

/-- Heads inside `S.erase w`. -/
theorem outN_erase (S : Finset ℕ) (w v : ℕ) : outN D (S.erase w) v = (outN D S v).erase w := by
  ext z
  simp only [mem_outN, mem_erase]
  tauto

theorem card_outN_erase_ge (S : Finset ℕ) (w v : ℕ) :
    (outN D S v).card ≤ (outN D (S.erase w) v).card + 1 := by
  rw [outN_erase]
  have := pred_card_le_card_erase (s := outN D S v) (a := w)
  omega

theorem card_outN_erase_of_not (S : Finset ℕ) {w v : ℕ} (h : ¬ D v w = true) :
    (outN D (S.erase w) v).card = (outN D S v).card := by
  rw [outN_erase, erase_eq_of_notMem]
  intro hw
  exact h (mem_outN.mp hw).2

/-- **Base, `d = 2`.** A `q`-free set of minimum out-degree two in which at most `t` rows have
exactly two heads, `t ≤ q`, `t + 4 ≤ 2q`, has at least `2q + 3` labels. -/
theorem deficit_base {S : Finset ℕ} {t : ℕ} (free : QFree D S q) (hq : 2 ≤ q) (ne : S.Nonempty)
    (deg : ∀ v ∈ S, 2 ≤ (outN D S v).card)
    (few : (S.filter (fun v => (outN D S v).card ≤ 2)).card ≤ t) (ht : t ≤ q) (ht' : t + 4 ≤ 2 * q) :
    2 * q + 3 ≤ S.card := by
  classical
  set T := S.filter (fun v => (outN D S v).card ≤ 2) with hT
  have low := FatShort.order_deg free (by omega) 2 le_rfl deg ne
  by_contra big
  push Not at big
  rcases (show S.card = 2 * q + 1 ∨ S.card = 2 * q + 2 by omega) with e | e
  · -- a rigid host: every row is deficient
    have two := HostTwo.host_two_out free (by omega) e deg
    have all : T = S := filter_true_of_mem (fun v hv => (two v hv).le)
    rw [← all] at e
    omega
  · -- a label headed by no deficient row
    set H := T.biUnion (fun v => outN D S v) with hH
    have Hc : H.card ≤ 2 * t := by
      refine card_biUnion_le.trans ?_
      have : ∑ v ∈ T, (outN D S v).card ≤ ∑ _v ∈ T, 2 :=
        sum_le_sum (fun v hv => (mem_filter.mp hv).2)
      rw [sum_const, smul_eq_mul] at this
      omega
    obtain ⟨w, wS, wH⟩ : ∃ w ∈ S, w ∉ H := by
      by_contra h
      push Not at h
      have := card_le_card (show S ⊆ H from h)
      omega
    set S' := S.erase w with hS'
    have sub : S' ⊆ S := erase_subset _ _
    have notH : ∀ v ∈ T, ¬ D v w = true := by
      intro v hv vw
      exact wH (mem_biUnion.mpr ⟨v, hv, mem_outN.mpr ⟨wS, vw⟩⟩)
    have deg' : ∀ v ∈ S', 2 ≤ (outN D S' v).card := by
      intro v hv
      by_cases vT : v ∈ T
      · rw [hS', card_outN_erase_of_not S (notH v vT)]
        exact deg v (sub hv)
      · have : 3 ≤ (outN D S v).card := by
          by_contra h
          exact vT (mem_filter.mpr ⟨sub hv, by omega⟩)
        have := card_outN_erase_ge (D := D) S w v
        rw [← hS'] at this
        omega
    have size : S'.card = 2 * q + 1 := by rw [card_erase_of_mem wS]; omega
    have free' := free.mono_set sub
    have rig := HostTwo.host_two_out free' (by omega) size deg'
    -- every full row heads `w`
    have toW : ∀ v ∈ S', v ∉ T → D v w = true := by
      intro v hv vT
      by_contra vw
      have e1 := card_outN_erase_of_not S vw
      rw [← hS'] at e1
      have e2 := rig v hv
      exact vT (mem_filter.mpr ⟨sub hv, by omega⟩)
    -- a head of `w`, necessarily deficient
    obtain ⟨h, hh⟩ : (outN D S w).Nonempty := card_pos.mp (by have := deg w wS; omega)
    obtain ⟨hS, wh⟩ := mem_outN.mp hh
    have hw : h ≠ w := fun e' => loopfree free (by omega) wS (e' ▸ wh)
    have hS'm : h ∈ S' := mem_erase.mpr ⟨hw, hS⟩
    have hT' : h ∈ T := by
      by_contra hT'
      exact digonfree free (by omega) wS hS wh (toW h hS'm hT')
    -- the `(q-2)`-ball of `h` holds a full row
    have grow := ball_growth q (by omega) D S' free' (fun v hv => deg' v hv) h hS'm (q - 2) (by omega)
    obtain ⟨v, vb, vT⟩ : ∃ v ∈ ball D S' h (q - 2), v ∉ T := by
      by_contra none
      push Not at none
      have : ball D S' h (q - 2) ⊆ T := fun v hv => none v hv
      have := card_le_card this
      omega
    obtain ⟨vS', j, hj, walk⟩ := mem_ball.mp vb
    have vw := toW v vS' vT
    exact free w (j + 2) (by omega) (by omega)
      ((Walk.step hS wh (walk.mono sub)).snoc wS vw)

/-- **One more label.** A nonempty `q`-free set of minimum out-degree `d ≥ 2` in which at most
`t` rows have at most `d` heads, `t + 2 ≤ q + d`, `t + 6 ≤ 2q + d`, `2 ≤ q`, has at least
`2q + d + 1` labels. -/
theorem deficit_order (hq : 2 ≤ q) :
    ∀ d, 2 ≤ d → ∀ (t : ℕ) (S : Finset ℕ), QFree D S q → S.Nonempty →
      (∀ v ∈ S, d ≤ (outN D S v).card) →
      (S.filter (fun v => (outN D S v).card ≤ d)).card ≤ t →
      t + 2 ≤ q + d → t + 6 ≤ 2 * q + d → 2 * q + d + 1 ≤ S.card := by
  intro d hd
  induction d, hd using Nat.le_induction with
  | base =>
    intro t S free ne deg few h1 h2
    exact deficit_base free hq ne deg few (by omega) (by omega)
  | succ d hd ih =>
    intro t S free ne deg few h1 h2
    classical
    set T := S.filter (fun v => (outN D S v).card ≤ d + 1) with hT
    -- delete a deficient row, or any row
    obtain ⟨w, wS, wT⟩ : ∃ w ∈ S, (T.Nonempty → w ∈ T) := by
      by_cases tn : T.Nonempty
      · obtain ⟨w, hw⟩ := tn
        exact ⟨w, (mem_filter.mp hw).1, fun _ => hw⟩
      · obtain ⟨w, hw⟩ := ne
        exact ⟨w, hw, fun h => (tn h).elim⟩
    set S' := S.erase w with hS'
    have sub : S' ⊆ S := erase_subset _ _
    have deg' : ∀ v ∈ S', d ≤ (outN D S' v).card := by
      intro v hv
      have := card_outN_erase_ge (D := D) S w v
      rw [← hS'] at this
      have := deg v (sub hv)
      omega
    have few' : (S'.filter (fun v => (outN D S' v).card ≤ d)).card ≤ t - 1 := by
      have inc : S'.filter (fun v => (outN D S' v).card ≤ d) ⊆ T.erase w := by
        intro v hv
        obtain ⟨vS', vd⟩ := mem_filter.mp hv
        have := card_outN_erase_ge (D := D) S w v
        rw [← hS'] at this
        exact mem_erase.mpr ⟨(mem_erase.mp vS').1, mem_filter.mpr ⟨sub vS', by omega⟩⟩
      have c := card_le_card inc
      have fewT : T.card ≤ t := few
      by_cases tn : T.Nonempty
      · rw [card_erase_of_mem (wT tn)] at c
        omega
      · rw [not_nonempty_iff_eq_empty.mp tn, erase_empty, card_empty] at c
        omega
    have big : d + 2 ≤ S.card := by
      obtain ⟨v, hv⟩ := ne
      have h1 := deg v hv
      have sub2 : insert v (outN D S v) ⊆ S := insert_subset hv outN_subset
      have nv : v ∉ outN D S v := fun h => loopfree free (by omega) hv (mem_outN.mp h).2
      have := card_le_card sub2
      rw [card_insert_of_notMem nv] at this
      omega
    have ne' : S'.Nonempty := card_pos.mp (by rw [card_erase_of_mem wS]; omega)
    have := ih (t - 1) S' (free.mono_set sub) ne' deg' few' (by omega) (by omega)
    rw [card_erase_of_mem wS] at this
    omega

/-! ### The root and one of its heads -/

section root
variable {V : Finset ℕ} {u r : ℕ}

/-- A label of the second layer is neither the root nor a head. -/
theorem layer_two_off {v w : ℕ} (hv : v ∈ V) (hw : w ∈ layer D V 2 v) :
    w ≠ v ∧ w ∉ outN D V v := by
  have n1 : w ∉ ball D V v 1 := (mem_layer.mp hw).2
  refine ⟨fun e => n1 ?_, fun h => n1 ((mem_ball_one hv).mpr (Or.inr h))⟩
  rw [e]
  exact self_mem_ball hv

/-- Heads and second layer are disjoint. -/
theorem out_layer_disj {v : ℕ} (hv : v ∈ V) : Disjoint (outN D V v) (layer D V 2 v) :=
  disjoint_left.mpr (fun _ h1 h2 => (layer_two_off hv h2).2 h1)

/-- **Case (i): the second layer of `x` meets `X ∪ Y` in at most `|Y \ F|` labels.** A head `x`
of a thin root that misses another head is not short. Generic: `2 ≤ q`, `r ≤ 2q + 1`. -/
theorem case_far (free : QFree D V q) (hq : 2 ≤ q) (reg : ∀ v ∈ V, (outN D V v).card = r)
    (hu : u ∈ V) (thin : (layer D V 2 u).card + 1 = r) (hr : r ≤ 2 * q + 1)
    {x : ℕ} (hx : x ∈ outN D V u) (short : (layer D V 2 x).card + 1 ≤ r)
    (far : (layer D V 2 x ∩ (outN D V u ∪ layer D V 2 u)).card ≤
      (layer D V 2 u \ outN D V x).card)
    {c0 : ℕ} (hc0 : c0 ∈ outN D V u) (ne0 : c0 ≠ x) (miss : ¬ D x c0 = true) : False := by
  classical
  set X := outN D V u with hX
  set Y := layer D V 2 u with hY
  set F := outN D V x with hF
  set L := layer D V 2 x with hL
  have xV : x ∈ V := outN_subset hx
  have keepU := head_keep free hq hu
  have keepX := head_keep free hq xV
  have FXY : F ⊆ X ∪ Y := keepU x hx
  have disjXY : Disjoint X Y := out_layer_disj hu
  have xF : x ∉ F := fun h => loopfree free (by omega) xV (mem_outN.mp h).2
  set A := F ∩ X with hA
  set B := F ∩ Y with hB
  have AV : A ⊆ V := fun v hv => outN_subset (mem_inter.mp hv).1
  have BV : B ⊆ V := fun v hv => outN_subset (mem_inter.mp hv).1
  have AB : A.card + B.card = r := by
    have e : F = A ∪ B := by
      rw [hA, hB, ← inter_union_distrib_left, inter_eq_left.mpr FXY]
    have d : Disjoint A B := disjoint_left.mpr (fun v h1 h2 =>
      disjoint_left.mp disjXY (mem_inter.mp h1).2 (mem_inter.mp h2).2)
    rw [← card_union_of_disjoint d, ← e, hF, reg x xV]
  have cX : X.card = r := reg u hu
  have Asmall : A.card + 2 ≤ r := by
    have sub : A ⊆ (X.erase x).erase c0 := by
      intro v hv
      obtain ⟨vF, vX⟩ := mem_inter.mp hv
      exact mem_erase.mpr ⟨fun e => miss (e ▸ (mem_outN.mp vF).2),
        mem_erase.mpr ⟨fun e => xF (e ▸ vF), vX⟩⟩
    have := card_le_card sub
    have pos := card_pos.mpr ⟨c0, mem_erase.mpr ⟨ne0, hc0⟩⟩
    rw [card_erase_of_mem (mem_erase.mpr ⟨ne0, hc0⟩), card_erase_of_mem hx] at this
    rw [card_erase_of_mem hx] at pos
    omega
  have BY : B.card ≤ Y.card := card_le_card inter_subset_right
  -- the rows of `A`
  set BL := B ∪ (L ∩ (X ∪ Y)) with hBL
  have BLc : BL.card + 1 ≤ r := by
    have e := card_sdiff_add_card_inter Y F
    rw [inter_comm, ← hB] at e
    have := card_union_le B (L ∩ (X ∪ Y))
    rw [← hBL] at this
    omega
  have keepA : ∀ a ∈ A, outN D V a ⊆ A ∪ BL := by
    intro a ha w hw
    have w1 := keepU a (mem_inter.mp ha).2 hw
    rcases mem_union.mp (keepX a (mem_inter.mp ha).1 hw) with wF | wL
    · rcases mem_union.mp w1 with wX | wY
      · exact mem_union_left _ (mem_inter.mpr ⟨wF, wX⟩)
      · exact mem_union_right _ (mem_union_left _ (mem_inter.mpr ⟨wF, wY⟩))
    · exact mem_union_right _ (mem_union_right _ (mem_inter.mpr ⟨wL, w1⟩))
  have degA : ∀ a ∈ A, 1 ≤ (outN D A a).card :=
    DipCost.layer_host (fun a ha => (reg a (AV ha)).ge) keepA (by omega)
  -- lone rows of `A` head all of `B`, so every row of `A` reaches `B` within `q - 1`
  have noBA : ∀ y ∈ B, ∀ a ∈ A, ¬ D y a = true := by
    intro y hy a ha ya
    obtain ⟨l, lb, ll⟩ := lone_near (free.mono_set AV) hq degA (by omega) ha
    obtain ⟨lA, one⟩ := mem_lone.mp ll
    have full := lone_full (keepA l lA) (reg l (AV lA)).ge one BLc
    have ly : D l y = true := (mem_outN.mp (full (mem_union_left _ hy))).2
    obtain ⟨-, j, hj, walk⟩ := mem_ball.mp lb
    exact free a (j + 1 + 1) (by omega) (by omega)
      (((walk.mono AV).snoc (BV hy) ly).snoc (AV ha) ya)
  -- the rows of `B` keep a head in `B`
  have degB : ∀ y ∈ B, 1 ≤ (outN D B y).card := by
    intro y hy
    have cover : outN D V y ⊆ outN D B y ∪ L := by
      intro w hw
      rcases mem_union.mp (keepX y (mem_inter.mp hy).1 hw) with wF | wL
      · rcases mem_union.mp (FXY wF) with wX | wY
        · exact (noBA y hy w (mem_inter.mpr ⟨wF, wX⟩) (mem_outN.mp hw).2).elim
        · exact mem_union_left _ (mem_outN.mpr ⟨mem_inter.mpr ⟨wF, wY⟩, (mem_outN.mp hw).2⟩)
      · exact mem_union_right _ wL
    have c := (card_le_card cover).trans (card_union_le _ _)
    rw [reg y (BV hy)] at c
    omega
  have neA : A.Nonempty := card_pos.mp (by omega)
  have neB : B.Nonempty := card_pos.mp (by omega)
  have oA := DipCost.order_one q D A (free.mono_set AV) degA neA
  have oB := DipCost.order_one q D B (free.mono_set BV) degB neB
  omega

/-- **Case (ii): a head of `u` at distance two from `x`, few at distance three.** A head `x` of a
thin root that misses another head is not short. Generic: `3 ≤ q`, `r ≤ 2q + 1`;
`M` = heads of `u` outside `{x} ∪ F ∪ L`, `|M| + 2 ≤ q`, `|M| + 6 ≤ 2q`. -/
theorem case_near (free : QFree D V q) (hq : 3 ≤ q) (reg : ∀ v ∈ V, (outN D V v).card = r)
    (hu : u ∈ V) (thin : (layer D V 2 u).card + 1 = r) (hr : r ≤ 2 * q + 1)
    {x : ℕ} (hx : x ∈ outN D V u) (short : (layer D V 2 x).card + 1 ≤ r)
    (near : (layer D V 2 u \ outN D V x).card <
      (layer D V 2 x ∩ (outN D V u ∪ layer D V 2 u)).card)
    (fewM : (outN D V u \ insert x (outN D V x ∪ layer D V 2 x)).card + 2 ≤ q)
    (fewM' : (outN D V u \ insert x (outN D V x ∪ layer D V 2 x)).card + 6 ≤ 2 * q) : False := by
  classical
  set X := outN D V u with hX
  set Y := layer D V 2 u with hY
  set F := outN D V x with hF
  set L := layer D V 2 x with hL
  have xV : x ∈ V := outN_subset hx
  have keepU := head_keep free (by omega) hu
  have keepX := head_keep free (by omega) xV
  have FXY : F ⊆ X ∪ Y := keepU x hx
  have disjXY : Disjoint X Y := out_layer_disj hu
  have disjFL : Disjoint F L := out_layer_disj xV
  have xF : x ∉ F := fun h => loopfree free (by omega) xV (mem_outN.mp h).2
  have xL : x ∉ L := fun h => (layer_two_off xV h).1 rfl
  set A := F ∩ X with hA
  set B := F ∩ Y with hB
  set K := L ∩ X with hK
  set M := X \ insert x (F ∪ L) with hM
  have BV : B ⊆ V := fun v hv => outN_subset (mem_inter.mp hv).1
  have AB : A.card + B.card = r := by
    have e : F = A ∪ B := by
      rw [hA, hB, ← inter_union_distrib_left, inter_eq_left.mpr FXY]
    have d : Disjoint A B := disjoint_left.mpr (fun v h1 h2 =>
      disjoint_left.mp disjXY (mem_inter.mp h1).2 (mem_inter.mp h2).2)
    rw [← card_union_of_disjoint d, ← e, hF, reg x xV]
  -- `X = {x} ∪ A ∪ K ∪ M`, disjoint
  have cX : 1 + A.card + K.card + M.card = r := by
    have e : X = insert x ((A ∪ K) ∪ M) := by
      ext v
      simp only [hA, hK, hM, mem_insert, mem_union, mem_inter, mem_sdiff]
      constructor
      · intro vX
        by_cases e : v = x
        · exact Or.inl e
        · right
          by_cases vF : v ∈ F
          · exact Or.inl (Or.inl ⟨vF, vX⟩)
          · by_cases vL : v ∈ L
            · exact Or.inl (Or.inr ⟨vL, vX⟩)
            · exact Or.inr ⟨vX, by tauto⟩
      · rintro (rfl | (⟨-, h⟩ | ⟨-, h⟩) | ⟨h, -⟩)
        · exact hx
        all_goals exact h
    have dAK : Disjoint A K := disjoint_left.mpr (fun v h1 h2 =>
      disjoint_left.mp disjFL (mem_inter.mp h1).1 (mem_inter.mp h2).1)
    have dAKM : Disjoint (A ∪ K) M := by
      refine disjoint_left.mpr (fun v h1 h2 => ?_)
      have := (mem_sdiff.mp h2).2
      rcases mem_union.mp h1 with h | h
      · exact this (mem_insert_of_mem (mem_union_left _ (mem_inter.mp h).1))
      · exact this (mem_insert_of_mem (mem_union_right _ (mem_inter.mp h).1))
    have xn : x ∉ (A ∪ K) ∪ M := by
      intro h
      rcases mem_union.mp h with h | h
      · rcases mem_union.mp h with h | h
        · exact xF (mem_inter.mp h).1
        · exact xL (mem_inter.mp h).1
      · exact (mem_sdiff.mp h).2 (mem_insert_self _ _)
    have := reg u hu
    rw [← hX, e, card_insert_of_notMem xn, card_union_of_disjoint dAKM,
      card_union_of_disjoint dAK] at this
    omega
  -- `K` is nonempty
  have kpos : 1 ≤ K.card := by
    have split : L ∩ (X ∪ Y) ⊆ K ∪ (Y \ F) := by
      intro v hv
      obtain ⟨vL, vXY⟩ := mem_inter.mp hv
      rcases mem_union.mp vXY with vX | vY
      · exact mem_union_left _ (mem_inter.mpr ⟨vL, vX⟩)
      · exact mem_union_right _ (mem_sdiff.mpr ⟨vY, fun vF => disjoint_left.mp disjFL vF vL⟩)
    have := (card_le_card split).trans (card_union_le _ _)
    omega
  -- the carrier `W = F ∪ K`
  set W := F ∪ K with hW
  have WV : W ⊆ V := union_subset outN_subset (fun v hv => outN_subset (mem_inter.mp hv).2)
  have cW : W.card = r + K.card := by
    have d : Disjoint F K := disjoint_left.mpr (fun v h1 h2 =>
      disjoint_left.mp disjFL h1 (mem_inter.mp h2).1)
    rw [hW, card_union_of_disjoint d, hF, reg x xV]
  have cYF : (Y \ F).card + B.card + 1 = r := by
    have e := card_sdiff_add_card_inter Y F
    rw [inter_comm, ← hB] at e
    omega
  have cLX : (L \ X).card + K.card = L.card := card_sdiff_add_card_inter L X
  -- degrees in `W`
  have degA : ∀ a ∈ A, K.card + 2 ≤ (outN D W a).card := by
    intro a ha
    have cover : outN D V a ⊆ outN D W a ∪ (Y \ F) := by
      intro w hw
      have aw := (mem_outN.mp hw).2
      rcases mem_union.mp (keepX a (mem_inter.mp ha).1 hw) with wF | wL
      · exact mem_union_left _ (mem_outN.mpr ⟨mem_union_left _ wF, aw⟩)
      · rcases mem_union.mp (keepU a (mem_inter.mp ha).2 hw) with wX | wY
        · exact mem_union_left _ (mem_outN.mpr ⟨mem_union_right _ (mem_inter.mpr ⟨wL, wX⟩), aw⟩)
        · exact mem_union_right _ (mem_sdiff.mpr ⟨wY, fun wF => disjoint_left.mp disjFL wF wL⟩)
    have c := (card_le_card cover).trans (card_union_le _ _)
    rw [reg a (outN_subset (mem_inter.mp ha).1)] at c
    omega
  have degK : ∀ c ∈ K, K.card + 2 ≤ (outN D W c).card := by
    intro c hc
    obtain ⟨cL, cX'⟩ := mem_inter.mp hc
    have cx : ¬ D c x = true := no_back_arc free xV (mem_layer.mp cL).1 (by omega)
    have cover : outN D V c ⊆ outN D W c ∪ (M ∪ (Y \ F)) := by
      intro w hw
      have cw := (mem_outN.mp hw).2
      rcases mem_union.mp (keepU c cX' hw) with wX | wY
      · by_cases wF : w ∈ F
        · exact mem_union_left _ (mem_outN.mpr ⟨mem_union_left _ wF, cw⟩)
        · by_cases wL : w ∈ L
          · exact mem_union_left _ (mem_outN.mpr ⟨mem_union_right _ (mem_inter.mpr ⟨wL, wX⟩), cw⟩)
          · refine mem_union_right _ (mem_union_left _ (mem_sdiff.mpr ⟨wX, ?_⟩))
            intro h
            rcases mem_insert.mp h with rfl | h
            · exact cx cw
            · rcases mem_union.mp h with h | h
              · exact wF h
              · exact wL h
      · by_cases wF : w ∈ F
        · exact mem_union_left _ (mem_outN.mpr ⟨mem_union_left _ wF, cw⟩)
        · exact mem_union_right _ (mem_union_right _ (mem_sdiff.mpr ⟨wY, wF⟩))
    have cc := (card_le_card cover).trans ((card_union_le _ _).trans
      (Nat.add_le_add_left (card_union_le _ _) _))
    rw [reg c (outN_subset cX')] at cc
    omega
  have degB : ∀ y ∈ B, K.card + 1 ≤ (outN D W y).card := by
    intro y hy
    have cover : outN D V y ⊆ outN D W y ∪ (L \ X) := by
      intro w hw
      have yw := (mem_outN.mp hw).2
      rcases mem_union.mp (keepX y (mem_inter.mp hy).1 hw) with wF | wL
      · exact mem_union_left _ (mem_outN.mpr ⟨mem_union_left _ wF, yw⟩)
      · by_cases wX : w ∈ X
        · exact mem_union_left _ (mem_outN.mpr ⟨mem_union_right _ (mem_inter.mpr ⟨wL, wX⟩), yw⟩)
        · exact mem_union_right _ (mem_sdiff.mpr ⟨wL, wX⟩)
    have c := (card_le_card cover).trans (card_union_le _ _)
    rw [reg y (BV hy)] at c
    omega
  have memW : ∀ v ∈ W, v ∈ A ∨ v ∈ B ∨ v ∈ K := by
    intro v hv
    rcases mem_union.mp hv with vF | vK
    · rcases mem_union.mp (FXY vF) with vX | vY
      · exact Or.inl (mem_inter.mpr ⟨vF, vX⟩)
      · exact Or.inr (Or.inl (mem_inter.mpr ⟨vF, vY⟩))
    · exact Or.inr (Or.inr vK)
  have deg : ∀ v ∈ W, K.card + 1 ≤ (outN D W v).card := by
    intro v hv
    rcases memW v hv with h | h | h
    · have := degA v h; omega
    · exact degB v h
    · have := degK v h; omega
  have few : (W.filter (fun v => (outN D W v).card ≤ K.card + 1)).card ≤ B.card := by
    refine card_le_card (fun v hv => ?_)
    obtain ⟨vW, low⟩ := mem_filter.mp hv
    rcases memW v vW with h | h | h
    · have := degA v h; omega
    · exact h
    · have := degK v h; omega
  have neW : W.Nonempty := card_pos.mp (by omega)
  have big := deficit_order (D := D) (by omega) (K.card + 1) (by omega) B.card W
    (free.mono_set WV) neW deg few (by omega) (by omega)
  omega

/-- **A heavy start.** In a `q`-free set of minimum out-degree `d ≥ 2`, a row with at least `e`
heads has, for `1 ≤ j ≤ q`, a `j`-ball of at least `1 + e + (j - 1)(d - 1)` labels or of at
least `2q + d` labels (`FatShort.grow_min`, iterated). -/
theorem ball_heavy {S : Finset ℕ} {d e v : ℕ} (free : QFree D S q) (hq : 1 ≤ q) (hd : 2 ≤ d)
    (deg : ∀ w ∈ S, d ≤ (outN D S w).card) (hv : v ∈ S) (he : e ≤ (outN D S v).card) :
    ∀ j, 1 ≤ j → j ≤ q →
      (1 + e + (j - 1) * (d - 1) ≤ (ball D S v j).card ∨ 2 * q + d ≤ (ball D S v j).card) := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base =>
    intro _
    left
    rw [ReachLedger.ball_one free hq hv]
    simp only [Nat.sub_self, zero_mul, add_zero]
    omega
  | succ j hj ih =>
    intro hjq
    have g := FatShort.grow_min free hq hd deg hv hj (by omega) (rfl : j + 1 = j + 1)
    rw [min_le_iff] at g
    have mono := card_le_card (ball_mono_radius (D := D) (W := S) (u := v) (show j ≤ j + 1 by omega))
    have step : (j + 1 - 1) * (d - 1) = (j - 1) * (d - 1) + (d - 1) := by
      obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      ring
    rw [step]
    rcases ih (by omega) with h | h
    · omega
    · right; omega

/-- **Case (iii): a head of `u` at distance two from `x`, many at distance three.** A head `x` of
a thin root that misses another head is not short. Generic: `3 ≤ q`, `r ≤ 2q + 1`,
`q ≤ |M| + 1`. On `W = F ∪ K` (minimum out-degree `|K| + 1`) every in-degree is at most `|K| + 2`
(`indeg_ball` with the `(q-1)`-ball, `ball_growth`), while the rows of `A` have at least `|B| + 1`
heads and, by `ball_heavy`, in-degree `0` (`|K| ≥ 2`) or at most `1` (`|K| = 1`); in- and
out-degrees balance (`arcs_between`), which leaves only `|K| = |A| = 1`, where `A = {a}` heads
all of `W` and `W \ {a}` would be a degree-two host with a row of three heads. -/
theorem case_deep (free : QFree D V q) (hq : 3 ≤ q) (reg : ∀ v ∈ V, (outN D V v).card = r)
    (hu : u ∈ V) (thin : (layer D V 2 u).card + 1 = r) (hr : r ≤ 2 * q + 1)
    {x : ℕ} (hx : x ∈ outN D V u) (short : (layer D V 2 x).card + 1 ≤ r)
    (near : (layer D V 2 u \ outN D V x).card <
      (layer D V 2 x ∩ (outN D V u ∪ layer D V 2 u)).card)
    (deep : q ≤ (outN D V u \ insert x (outN D V x ∪ layer D V 2 x)).card + 1) : False := by
  classical
  set X := outN D V u with hX
  set Y := layer D V 2 u with hY
  set F := outN D V x with hF
  set L := layer D V 2 x with hL
  have xV : x ∈ V := outN_subset hx
  have keepU := head_keep free (by omega) hu
  have keepX := head_keep free (by omega) xV
  have FXY : F ⊆ X ∪ Y := keepU x hx
  have disjXY : Disjoint X Y := out_layer_disj hu
  have disjFL : Disjoint F L := out_layer_disj xV
  have xF : x ∉ F := fun h => loopfree free (by omega) xV (mem_outN.mp h).2
  have xL : x ∉ L := fun h => (layer_two_off xV h).1 rfl
  set A := F ∩ X with hA
  set B := F ∩ Y with hB
  set K := L ∩ X with hK
  set M := X \ insert x (F ∪ L) with hM
  have BV : B ⊆ V := fun v hv => outN_subset (mem_inter.mp hv).1
  have eF : F = A ∪ B := by
    rw [hA, hB, ← inter_union_distrib_left, inter_eq_left.mpr FXY]
  have dAB : Disjoint A B := disjoint_left.mpr (fun v h1 h2 =>
    disjoint_left.mp disjXY (mem_inter.mp h1).2 (mem_inter.mp h2).2)
  have AB : A.card + B.card = r := by
    rw [← card_union_of_disjoint dAB, ← eF, hF, reg x xV]
  have dAK : Disjoint A K := disjoint_left.mpr (fun v h1 h2 =>
    disjoint_left.mp disjFL (mem_inter.mp h1).1 (mem_inter.mp h2).1)
  have cX : 1 + A.card + K.card + M.card = r := by
    have e : X = insert x ((A ∪ K) ∪ M) := by
      ext v
      simp only [hA, hK, hM, mem_insert, mem_union, mem_inter, mem_sdiff]
      constructor
      · intro vX
        by_cases e : v = x
        · exact Or.inl e
        · right
          by_cases vF : v ∈ F
          · exact Or.inl (Or.inl ⟨vF, vX⟩)
          · by_cases vL : v ∈ L
            · exact Or.inl (Or.inr ⟨vL, vX⟩)
            · exact Or.inr ⟨vX, by tauto⟩
      · rintro (rfl | (⟨-, h⟩ | ⟨-, h⟩) | ⟨h, -⟩)
        · exact hx
        all_goals exact h
    have dAKM : Disjoint (A ∪ K) M := by
      refine disjoint_left.mpr (fun v h1 h2 => ?_)
      have := (mem_sdiff.mp h2).2
      rcases mem_union.mp h1 with h | h
      · exact this (mem_insert_of_mem (mem_union_left _ (mem_inter.mp h).1))
      · exact this (mem_insert_of_mem (mem_union_right _ (mem_inter.mp h).1))
    have xn : x ∉ (A ∪ K) ∪ M := by
      intro h
      rcases mem_union.mp h with h | h
      · rcases mem_union.mp h with h | h
        · exact xF (mem_inter.mp h).1
        · exact xL (mem_inter.mp h).1
      · exact (mem_sdiff.mp h).2 (mem_insert_self _ _)
    have := reg u hu
    rw [← hX, e, card_insert_of_notMem xn, card_union_of_disjoint dAKM,
      card_union_of_disjoint dAK] at this
    omega
  have kpos : 1 ≤ K.card := by
    have split : L ∩ (X ∪ Y) ⊆ K ∪ (Y \ F) := by
      intro v hv
      obtain ⟨vL, vXY⟩ := mem_inter.mp hv
      rcases mem_union.mp vXY with vX | vY
      · exact mem_union_left _ (mem_inter.mpr ⟨vL, vX⟩)
      · exact mem_union_right _ (mem_sdiff.mpr ⟨vY, fun vF => disjoint_left.mp disjFL vF vL⟩)
    have := (card_le_card split).trans (card_union_le _ _)
    omega
  set W := F ∪ K with hW
  have WV : W ⊆ V := union_subset outN_subset (fun v hv => outN_subset (mem_inter.mp hv).2)
  have dFK : Disjoint F K := disjoint_left.mpr (fun v h1 h2 =>
    disjoint_left.mp disjFL h1 (mem_inter.mp h2).1)
  have cW : W.card = r + K.card := by
    rw [hW, card_union_of_disjoint dFK, hF, reg x xV]
  have cYF : (Y \ F).card + B.card + 1 = r := by
    have e := card_sdiff_add_card_inter Y F
    rw [inter_comm, ← hB] at e
    omega
  have cLX : (L \ X).card + K.card = L.card := card_sdiff_add_card_inter L X
  -- out-degrees in `W`
  have degA : ∀ a ∈ A, B.card + 1 ≤ (outN D W a).card := by
    intro a ha
    have cover : outN D V a ⊆ outN D W a ∪ (Y \ F) := by
      intro w hw
      have aw := (mem_outN.mp hw).2
      rcases mem_union.mp (keepX a (mem_inter.mp ha).1 hw) with wF | wL
      · exact mem_union_left _ (mem_outN.mpr ⟨mem_union_left _ wF, aw⟩)
      · rcases mem_union.mp (keepU a (mem_inter.mp ha).2 hw) with wX | wY
        · exact mem_union_left _ (mem_outN.mpr ⟨mem_union_right _ (mem_inter.mpr ⟨wL, wX⟩), aw⟩)
        · exact mem_union_right _ (mem_sdiff.mpr ⟨wY, fun wF => disjoint_left.mp disjFL wF wL⟩)
    have c := (card_le_card cover).trans (card_union_le _ _)
    rw [reg a (outN_subset (mem_inter.mp ha).1)] at c
    omega
  have degK : ∀ c ∈ K, K.card + 2 ≤ (outN D W c).card := by
    intro c hc
    obtain ⟨cL, cX'⟩ := mem_inter.mp hc
    have cx : ¬ D c x = true := no_back_arc free xV (mem_layer.mp cL).1 (by omega)
    have cover : outN D V c ⊆ outN D W c ∪ (M ∪ (Y \ F)) := by
      intro w hw
      have cw := (mem_outN.mp hw).2
      rcases mem_union.mp (keepU c cX' hw) with wX | wY
      · by_cases wF : w ∈ F
        · exact mem_union_left _ (mem_outN.mpr ⟨mem_union_left _ wF, cw⟩)
        · by_cases wL : w ∈ L
          · exact mem_union_left _ (mem_outN.mpr ⟨mem_union_right _ (mem_inter.mpr ⟨wL, wX⟩), cw⟩)
          · refine mem_union_right _ (mem_union_left _ (mem_sdiff.mpr ⟨wX, ?_⟩))
            intro h
            rcases mem_insert.mp h with rfl | h
            · exact cx cw
            · rcases mem_union.mp h with h | h
              · exact wF h
              · exact wL h
      · by_cases wF : w ∈ F
        · exact mem_union_left _ (mem_outN.mpr ⟨mem_union_left _ wF, cw⟩)
        · exact mem_union_right _ (mem_union_right _ (mem_sdiff.mpr ⟨wY, wF⟩))
    have cc := (card_le_card cover).trans ((card_union_le _ _).trans
      (Nat.add_le_add_left (card_union_le _ _) _))
    rw [reg c (outN_subset cX')] at cc
    omega
  have degB : ∀ y ∈ B, K.card + 1 ≤ (outN D W y).card := by
    intro y hy
    have cover : outN D V y ⊆ outN D W y ∪ (L \ X) := by
      intro w hw
      have yw := (mem_outN.mp hw).2
      rcases mem_union.mp (keepX y (mem_inter.mp hy).1 hw) with wF | wL
      · exact mem_union_left _ (mem_outN.mpr ⟨mem_union_left _ wF, yw⟩)
      · by_cases wX : w ∈ X
        · exact mem_union_left _ (mem_outN.mpr ⟨mem_union_right _ (mem_inter.mpr ⟨wL, wX⟩), yw⟩)
        · exact mem_union_right _ (mem_sdiff.mpr ⟨wL, wX⟩)
    have c := (card_le_card cover).trans (card_union_le _ _)
    rw [reg y (BV hy)] at c
    omega
  have eW : W = (A ∪ B) ∪ K := by rw [hW, eF]
  have memW : ∀ v ∈ W, v ∈ A ∨ v ∈ B ∨ v ∈ K := by
    intro v hv
    rw [eW] at hv
    rcases mem_union.mp hv with vF | vK
    · rcases mem_union.mp vF with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr vK)
  have deg : ∀ v ∈ W, K.card + 1 ≤ (outN D W v).card := by
    intro v hv
    rcases memW v hv with h | h | h
    · have := degA v h; omega
    · exact degB v h
    · have := degK v h; omega
  have freeW := free.mono_set WV
  have AW : A ⊆ W := fun v hv => by rw [eW]; exact mem_union_left _ (mem_union_left _ hv)
  -- in-degrees in `W`
  have inAll : ∀ v ∈ W, (HostTwo.inN D W v).card ≤ K.card + 2 := by
    intro v hv
    have i1 := HostTwo.indeg_ball freeW (by omega) hv (j := q - 1) (by omega)
    have i2 := ball_growth q (by omega) D W freeW
      (fun w hw => le_trans (by omega) (deg w hw)) v hv (q - 1) (by omega)
    omega
  set ι := if 2 ≤ K.card then 0 else 1 with hι
  have inA : ∀ a ∈ A, (HostTwo.inN D W a).card ≤ ι := by
    intro a ha
    have aW := AW ha
    have i1 := HostTwo.indeg_ball freeW (by omega) aW (j := q - 1) (by omega)
    have hb := ball_heavy freeW (by omega) (show 2 ≤ K.card + 1 by omega)
      (fun w hw => deg w hw) aW (degA a ha) (q - 1) (by omega) (by omega)
    have mk : (q - 1 - 1) * (K.card + 1 - 1) = (q - 2) * K.card := by
      rw [show q - 1 - 1 = q - 2 by omega, Nat.add_sub_cancel]
    rw [mk] at hb
    by_cases h2 : 2 ≤ K.card
    · rw [hι]; simp only [h2, ↓reduceIte]
      have : (q - 2) * 2 ≤ (q - 2) * K.card := Nat.mul_le_mul_left _ h2
      rcases hb with hb | hb <;> omega
    · rw [hι]; simp only [h2, ↓reduceIte]
      have k1 : K.card = 1 := by omega
      rw [k1, mul_one] at hb
      rcases hb with hb | hb <;> omega
  -- balance of in- and out-degrees
  have total : ∑ v ∈ W, (outN D W v).card = ∑ v ∈ W, (HostTwo.inN D W v).card :=
    HostTwo.arcs_between W W
  have dABK : Disjoint (A ∪ B) K := by rw [← eF]; exact dFK
  have split : ∀ f : ℕ → ℕ, ∑ v ∈ W, f v = ∑ v ∈ A, f v + ∑ v ∈ B, f v + ∑ v ∈ K, f v := by
    intro f
    rw [eW, sum_union dABK, sum_union dAB]
  rw [split (fun v => (outN D W v).card), split (fun v => (HostTwo.inN D W v).card)] at total
  have sB : ∑ v ∈ B, (HostTwo.inN D W v).card ≤ ∑ v ∈ B, (outN D W v).card + B.card := by
    have := sum_le_sum (fun v hv => show (HostTwo.inN D W v).card ≤ (outN D W v).card + 1 by
      have := inAll v (by rw [eW]; exact mem_union_left _ (mem_union_right _ hv))
      have := degB v hv
      omega)
    rw [sum_add_distrib, sum_const, smul_eq_mul, mul_one] at this
    exact this
  have sK : ∑ v ∈ K, (HostTwo.inN D W v).card ≤ ∑ v ∈ K, (outN D W v).card := by
    refine sum_le_sum (fun v hv => ?_)
    have := inAll v (by rw [eW]; exact mem_union_right _ hv)
    have := degK v hv
    omega
  have ι1 : ι ≤ 1 := by rw [hι]; split_ifs <;> omega
  have sA : ∑ v ∈ A, (HostTwo.inN D W v).card + A.card * (B.card + 1 - ι) ≤
      ∑ v ∈ A, (outN D W v).card := by
    have := sum_le_sum (fun v hv => show (HostTwo.inN D W v).card + (B.card + 1 - ι) ≤
        (outN D W v).card by
      have := inA v hv
      have := degA v hv
      omega)
    rw [sum_add_distrib, sum_const, smul_eq_mul] at this
    exact this
  have bal : A.card * (B.card + 1 - ι) ≤ B.card := by omega
  have Apos : 1 ≤ A.card := by
    have := card_le_card (inter_subset_right : B ⊆ Y)
    omega
  by_cases k2 : 2 ≤ K.card
  · have i0 : ι = 0 := by rw [hι]; simp only [k2, ↓reduceIte]
    rw [i0] at bal
    have := Nat.le_mul_of_pos_left (B.card + 1 - 0) (show 0 < A.card by omega)
    omega
  · have i1 : ι = 1 := by rw [hι]; simp only [k2, ↓reduceIte]
    rw [i1] at bal
    have k1 : K.card = 1 := by omega
    by_cases a2 : 2 ≤ A.card
    · have := Nat.mul_le_mul_right (B.card + 1 - 1) a2
      omega
    · -- `A = {a}`: `a` heads all of `W`, and `W \ {a}` is a degree-two host with a fat row
      obtain ⟨a, ha⟩ := card_pos.mp (show 0 < A.card by omega)
      have aW := AW ha
      have full : outN D W a = W.erase a := by
        refine eq_of_subset_of_card_le (fun w hw => mem_erase.mpr
          ⟨fun e => loopfree freeW (by omega) aW (e ▸ (mem_outN.mp hw).2), outN_subset hw⟩) ?_
        rw [card_erase_of_mem aW]
        have := degA a ha
        omega
      have notA : ∀ v ∈ W.erase a, ¬ D v a = true := by
        intro v hv va
        have av : D a v = true := by
          have : v ∈ outN D W a := by rw [full]; exact hv
          exact (mem_outN.mp this).2
        exact digonfree freeW (by omega) aW (erase_subset _ _ hv) av va
      have same : ∀ v ∈ W.erase a, (outN D (W.erase a) v).card = (outN D W v).card :=
        fun v hv => card_outN_erase_of_not W (notA v hv)
      have deg0 : ∀ v ∈ W.erase a, 2 ≤ (outN D (W.erase a) v).card := by
        intro v hv
        rw [same v hv]
        have := deg v (erase_subset _ _ hv)
        omega
      obtain ⟨c, hc⟩ := card_pos.mp (show 0 < K.card by omega)
      have cW0 : c ∈ W.erase a := mem_erase.mpr ⟨fun e => disjoint_left.mp dAK (e ▸ ha) hc,
        by rw [eW]; exact mem_union_right _ hc⟩
      have free0 := freeW.mono_set (erase_subset a W)
      have size0 : (W.erase a).card = r := by rw [card_erase_of_mem aW]; omega
      have o0 := FatShort.order_deg free0 (by omega) 2 le_rfl deg0 ⟨c, cW0⟩
      have host := HostTwo.host_two_out free0 (by omega) (by omega) deg0 c cW0
      have := degK c hc
      rw [same c cW0] at host
      omega

/-- **`H1`, all cases.** At a thin root, `4 ≤ q`, `r ≤ 2q + 1`: a short head heads every other
head of the root. -/
theorem short_head_heads_all (free : QFree D V q) (hq : 4 ≤ q)
    (reg : ∀ v ∈ V, (outN D V v).card = r)
    (hu : u ∈ V) (thin : (layer D V 2 u).card + 1 = r) (hr : r ≤ 2 * q + 1)
    {x : ℕ} (hx : x ∈ outN D V u) (short : (layer D V 2 x).card + 1 ≤ r) :
    ∀ c ∈ outN D V u, c ≠ x → D x c = true := by
  intro c hc ne
  by_contra miss
  by_cases far : (layer D V 2 x ∩ (outN D V u ∪ layer D V 2 u)).card ≤
      (layer D V 2 u \ outN D V x).card
  · exact case_far free (by omega) reg hu thin hr hx short far hc ne miss
  · by_cases few : (outN D V u \ insert x (outN D V x ∪ layer D V 2 x)).card + 2 ≤ q
    · exact case_near free (by omega) reg hu thin hr hx short (by omega) few (by omega)
    · exact case_deep free (by omega) reg hu thin hr hx short (by omega) (by omega)

/-- **`H1` in cases (i) and (ii).** A short head `x` of a thin root, `3 ≤ q`, `r ≤ 2q + 1`, with
`|M| + 2 ≤ q` and `|M| + 6 ≤ 2q` (`M` = heads of `u` at distance at least three from `x`), heads
every other head of `u`. -/
theorem short_head_full (free : QFree D V q) (hq : 3 ≤ q) (reg : ∀ v ∈ V, (outN D V v).card = r)
    (hu : u ∈ V) (thin : (layer D V 2 u).card + 1 = r) (hr : r ≤ 2 * q + 1)
    {x : ℕ} (hx : x ∈ outN D V u) (short : (layer D V 2 x).card + 1 ≤ r)
    (fewM : (outN D V u \ insert x (outN D V x ∪ layer D V 2 x)).card + 2 ≤ q)
    (fewM' : (outN D V u \ insert x (outN D V x ∪ layer D V 2 x)).card + 6 ≤ 2 * q) :
    ∀ c ∈ outN D V u, c ≠ x → D x c = true := by
  intro c hc ne
  by_contra miss
  by_cases far : (layer D V 2 x ∩ (outN D V u ∪ layer D V 2 u)).card ≤
      (layer D V 2 u \ outN D V x).card
  · exact case_far free (by omega) reg hu thin hr hx short far hc ne miss
  · exact case_near free hq reg hu thin hr hx short (by omega) fewM fewM'

/-- **Law A from `H1`.** If every short head of `u` heads all other heads of `u`, at most one
head of `u` is short (`2 ≤ q`). -/
theorem law_A_of_full (free : QFree D V q) (hq : 2 ≤ q)
    (full : ∀ x ∈ outN D V u, (layer D V 2 x).card + 1 ≤ r →
      ∀ c ∈ outN D V u, c ≠ x → D x c = true) :
    ((outN D V u).filter (fun x => (layer D V 2 x).card + 1 ≤ r)).card ≤ 1 := by
  rw [card_le_one]
  intro a ha b hb
  by_contra ne
  obtain ⟨aX, sa⟩ := mem_filter.mp ha
  obtain ⟨bX, sb⟩ := mem_filter.mp hb
  exact digonfree free hq (outN_subset aX) (outN_subset bX)
    (full a aX sa b bX (Ne.symm ne)) (full b bX sb a aX ne)

/-- **Law A, near case.** At a thin root, `3 ≤ q`, `r ≤ 2q + 1`: at most one head is short,
provided every short head `x` has `|M| + 2 ≤ q` and `|M| + 6 ≤ 2q`, `M` = heads of `u` at
distance at least three from `x`. At `(q, r) = (4, 9)`: `|M| ≤ 2`. -/
theorem law_A_near (free : QFree D V q) (hq : 3 ≤ q) (reg : ∀ v ∈ V, (outN D V v).card = r)
    (hu : u ∈ V) (thin : (layer D V 2 u).card + 1 = r) (hr : r ≤ 2 * q + 1)
    (fewM : ∀ x ∈ outN D V u, (layer D V 2 x).card + 1 ≤ r →
      (outN D V u \ insert x (outN D V x ∪ layer D V 2 x)).card + 2 ≤ q ∧
      (outN D V u \ insert x (outN D V x ∪ layer D V 2 x)).card + 6 ≤ 2 * q) :
    ((outN D V u).filter (fun x => (layer D V 2 x).card + 1 ≤ r)).card ≤ 1 :=
  law_A_of_full free (by omega) (fun x hx sx =>
    short_head_full free hq reg hu thin hr hx sx (fewM x hx sx).1 (fewM x hx sx).2)

/-- **Law A.** At a thin root (`|layer 2 u| + 1 = r`), out-degree exactly `r` everywhere, no closed
walk of length `1..q`, `4 ≤ q`, `r ≤ 2q + 1`: at most one head of `u` has a second layer of at most
`r - 1` labels. At `(q, r) = (4, 9)`: `law_A_4_9`. -/
theorem law_A (free : QFree D V q) (hq : 4 ≤ q) (reg : ∀ v ∈ V, (outN D V v).card = r)
    (hu : u ∈ V) (thin : (layer D V 2 u).card + 1 = r) (hr : r ≤ 2 * q + 1) :
    ((outN D V u).filter (fun x => (layer D V 2 x).card + 1 ≤ r)).card ≤ 1 :=
  law_A_of_full free (by omega) (fun _ hx sx =>
    short_head_heads_all free hq reg hu thin hr hx sx)

/-- **Law A at `(q, r) = (4, 9)`.** -/
theorem law_A_4_9 (free : QFree D V 4) (reg : ∀ v ∈ V, (outN D V v).card = 9) (hu : u ∈ V)
    (short : (layer D V 2 u).card + 1 = 9) :
    ((outN D V u).filter (fun x => (layer D V 2 x).card + 1 ≤ 9)).card ≤ 1 :=
  law_A free le_rfl reg hu short (by norm_num)

end root

#print axioms case_far
#print axioms case_near
#print axioms ball_heavy
#print axioms case_deep
#print axioms short_head_heads_all
#print axioms law_A
#print axioms law_A_4_9
#print axioms short_head_full
#print axioms law_A_of_full
#print axioms law_A_near
#print axioms deficit_base
#print axioms deficit_order

end LeanCH.BR.LawA
