import checkpoints.shen_extension.BackwardBallBank

/-!
# Reach ledger: exact pair accounting at complementary radii

Lean 4.35.0. Everything is stated for an arbitrary digraph `D`, label set `V`, cutoff `q`, radii
`i`, `j`, `k`, floors `a`, `b`, host degree `r` and lower quota `t`. No order, cutoff or degree is
fixed anywhere in this file.

`ball D V v i` is the closed forward ball (it contains `v`), `reverseBall D V v j` the closed
backward ball, and `gap D V i j v` the labels in neither.

## The ledger (needs only `QFree D V q` and `i + j ≤ q`)

* `row_ledger`: `|ball v i| + |reverseBall v j| + |gap i j v| = |V| + 1`, for every row.
* `ledger`: `∑ |ball · i| + ∑ |ball · j| + ∑ |gap i j ·| = |V| (|V| + 1)`.
* `budget`: with floors `a`, `b` on the two radii, the excesses and the gaps together spend
  exactly `|V| (|V| + 1 - a - b)`.
* `levels`: an excess sum is the sum of its level counts, to any depth `m`.
* `gap_swap`, `covered`: the gap is transposed with the radii; a row with empty gap sees every
  other label forward or backward.

## Parents and suppliers

* `parent_cap`: `indeg v + |ball v i| ≤ |V|` whenever `i + 1 ≤ q`.
* `supplier`, `supplier_cap`: rows with a head in a set `S` are paid by the parents of `S`.
* `tight_supply`: floor, level counts, gaps and parent caps in one inequality: the rows at the
  floor that head no row two levels up are at least what the ledger leaves over.

## Fragments (needs `NoHost q t`)

* `fragment_row`, `fragment_escape`, `fragment_exit`: a fragment of at most `q t` labels has a row
  with fewer than `t` heads inside, hence at least `r + 1 - t` heads outside.
* `noHost_one`, `closed_chain`: quota one holds outright; a set closed under one chosen successor
  has more than `q` labels.
* `growth_row`, `ball_growth`: `|ball v (k+1)| ≥ |ball v k| + r + 1 - t` while the punctured
  ball has at most `q t` labels.
* `first_complete`: a root whose shell `k + 1` meets that bound has a row heading the whole
  shell.

## Shells

* `ball_succ`, `head_ball_lt`: a head's ball sits one radius deeper in the tail's ball.
* `row_escape`: a head's row is never inside the tail's row.
* `complete_row`: a row inside the `k`-ball that heads the whole shell `k + 1` reaches the whole
  shell `k + 2` within two steps, and the count that follows.
* `full_of_count`: a row of the `k`-ball with enough outside heads heads the whole shell `k + 1`.
* `tied_chain`: when the two-ball cap is tight against the shells of the root, complete rows
  hand completeness to a head inside the ball, so there are more than `q` of them.
* `same_shell_lt`, `same_shell_gapped`: rows with the same shell do not see each other.
* `gap_clique`, `shell_class`: rows of one degree sharing one second shell are pairwise gaps,
  and `m` of them cost `m (m - 1)` in the gap sums.
* `complete_or_fragment`: with no lower quota at all, a root with a small shell has a complete
  row or its punctured ball keeps `t` heads inside on every row.
* `tied_next`, `complete_floor`, `tied_disjoint`: complete rows pass completeness on, sit
  three above the bare count, and belong to one shell only.

## Classes of roots

* `class_count`: every distinct shell among a set of roots owns more than `q` capped rows.
* `class_roots`: all but one root of each second-shell class is paid for by gaps.
-/

set_option linter.style.longLine false

namespace LeanCH.BR.ReachLedger
open Finset BRq2 BRq3 BR45 BypassRepair

variable {D : CH.Digraph} {V : Finset ℕ} {q : ℕ}

/-! ### Rows of the ledger -/

/-- Labels that `v` does not reach within `i` steps and that do not reach `v` within `j` steps. -/
noncomputable def gap (D : CH.Digraph) (V : Finset ℕ) (i j v : ℕ) : Finset ℕ :=
  V \ (ball D V v i ∪ reverseBall D V v j)

theorem mem_reverse {j v w : ℕ} : w ∈ reverseBall D V v j ↔ w ∈ V ∧ v ∈ ball D V w j := by
  simp only [reverseBall, mem_filter]

theorem mem_gap {i j v w : ℕ} :
    w ∈ gap D V i j v ↔ w ∈ V ∧ w ∉ ball D V v i ∧ v ∉ ball D V w j := by
  simp only [gap, mem_sdiff, mem_union, mem_reverse, not_or, not_and]
  constructor
  · rintro ⟨wv, a, b⟩
    exact ⟨wv, a, b wv⟩
  · rintro ⟨wv, a, b⟩
    exact ⟨wv, a, fun _ => b⟩

/-- Transposition: a gap at radii `(i, j)` seen from `v` is a gap at `(j, i)` seen from `w`. -/
theorem gap_swap {i j v w : ℕ} (vv : v ∈ V) (h : w ∈ gap D V i j v) : v ∈ gap D V j i w := by
  obtain ⟨_, a, b⟩ := mem_gap.mp h
  exact mem_gap.mpr ⟨vv, b, a⟩

/-- A row with empty gap: every label it does not reach within `i` reaches it within `j`. -/
theorem covered {i j v w : ℕ} (none : gap D V i j v = ∅) (wv : w ∈ V)
    (off : w ∉ ball D V v i) : v ∈ ball D V w j := by
  by_contra miss
  have bad : w ∈ gap D V i j v := mem_gap.mpr ⟨wv, off, miss⟩
  rw [none] at bad
  simp at bad

theorem ball_inter_reverse {i j v : ℕ} (free : QFree D V q) (hij : i + j ≤ q) (vv : v ∈ V) :
    ball D V v i ∩ reverseBall D V v j = {v} := by
  ext w
  simp only [mem_inter, mem_singleton]
  constructor
  · rintro ⟨fw, bw⟩
    rcases mem_union.mp (reverseBall_subset_complement (v := v) free hij bw) with h | h
    · exact absurd fw (mem_sdiff.mp h).2
    · exact mem_singleton.mp h
  · intro e
    rw [e]
    exact ⟨self_mem_ball vv, mem_reverse.mpr ⟨vv, self_mem_ball vv⟩⟩

/-- **Row ledger.** Forward ball, backward ball and gap partition the labels, the row itself being
counted in both balls. -/
theorem row_ledger {i j v : ℕ} (free : QFree D V q) (hij : i + j ≤ q) (vv : v ∈ V) :
    (ball D V v i).card + (reverseBall D V v j).card + (gap D V i j v).card = V.card + 1 := by
  have sub : ball D V v i ∪ reverseBall D V v j ⊆ V :=
    union_subset ball_subset (fun w hw => (mem_reverse.mp hw).1)
  have both := card_union_add_card_inter (ball D V v i) (reverseBall D V v j)
  rw [ball_inter_reverse free hij vv, card_singleton] at both
  have rest : (gap D V i j v).card = V.card - (ball D V v i ∪ reverseBall D V v j).card :=
    card_sdiff_of_subset sub
  have le := card_le_card sub
  omega

/-- **Ledger.** Summed over the rows, the backward balls are the forward balls again. -/
theorem ledger {i j : ℕ} (free : QFree D V q) (hij : i + j ≤ q) :
    ∑ v ∈ V, (ball D V v i).card + ∑ v ∈ V, (ball D V v j).card
      + ∑ v ∈ V, (gap D V i j v).card = V.card * (V.card + 1) := by
  have rows : ∑ v ∈ V, ((ball D V v i).card + (reverseBall D V v j).card + (gap D V i j v).card)
      = ∑ _v ∈ V, (V.card + 1) := sum_congr rfl (fun v vv => row_ledger free hij vv)
  rw [sum_add_distrib, sum_add_distrib, sum_reverseBall_eq_sum_ball, sum_const, smul_eq_mul] at rows
  exact rows

theorem sum_excess {c : ℕ → ℕ} {a : ℕ} {S : Finset ℕ} (low : ∀ v ∈ S, a ≤ c v) :
    ∑ v ∈ S, (c v - a) + S.card * a = ∑ v ∈ S, c v := by
  have step : ∑ v ∈ S, (c v - a) + ∑ _v ∈ S, a = ∑ v ∈ S, c v := by
    rw [← sum_add_distrib]
    exact sum_congr rfl (fun v hv => Nat.sub_add_cancel (low v hv))
  rwa [sum_const, smul_eq_mul] at step

/-- **Budget.** With floors `a` and `b` on the two radii, the excesses over the floors and the gaps
spend exactly `|V| (|V| + 1 - a - b)`. -/
theorem budget {i j a b : ℕ} (free : QFree D V q) (hij : i + j ≤ q)
    (hi : ∀ v ∈ V, a ≤ (ball D V v i).card) (hj : ∀ v ∈ V, b ≤ (ball D V v j).card) :
    ∑ v ∈ V, ((ball D V v i).card - a) + ∑ v ∈ V, ((ball D V v j).card - b)
      + ∑ v ∈ V, (gap D V i j v).card + V.card * (a + b) = V.card * (V.card + 1) := by
  have total := ledger (D := D) (V := V) (i := i) (j := j) free hij
  have ea : ∑ v ∈ V, ((ball D V v i).card - a) + V.card * a = ∑ v ∈ V, (ball D V v i).card :=
    sum_excess hi
  have eb : ∑ v ∈ V, ((ball D V v j).card - b) + V.card * b = ∑ v ∈ V, (ball D V v j).card :=
    sum_excess hj
  have e : V.card * (a + b) = V.card * a + V.card * b := Nat.mul_add _ _ _
  omega

/-- One level of an excess sum. -/
theorem peel (c : ℕ → ℕ) (a : ℕ) (S : Finset ℕ) :
    ∑ v ∈ S, (c v - a) = (S.filter (fun v => a < c v)).card + ∑ v ∈ S, (c v - (a + 1)) := by
  rw [card_filter, ← sum_add_distrib]
  refine sum_congr rfl (fun v _ => ?_)
  split_ifs <;> omega

/-- **Levels.** An excess sum is the sum of its first `m` level counts plus the excess over the
`m`-th level. -/
theorem levels (c : ℕ → ℕ) (a m : ℕ) (S : Finset ℕ) :
    ∑ v ∈ S, (c v - a) =
      ∑ k ∈ range m, (S.filter (fun v => a + k < c v)).card + ∑ v ∈ S, (c v - (a + m)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ, ih, peel c (a + m) S]
    simp only [add_assoc]

/-! ### Parents and suppliers -/

theorem ball_one {v : ℕ} (free : QFree D V q) (hq : 1 ≤ q) (vv : v ∈ V) :
    (ball D V v 1).card = (outN D V v).card + 1 := by
  have eq : ball D V v 1 = insert v (outN D V v) := by
    ext w
    simp only [mem_ball, mem_insert, mem_outN]
    constructor
    · rintro ⟨wv, j, hj, walk⟩
      match j, hj, walk with
      | 0, _, walk =>
        cases walk
        exact Or.inl rfl
      | 1, _, walk =>
        cases walk with
        | step _ arc rest =>
          cases rest
          exact Or.inr ⟨wv, arc⟩
      | n + 2, hj, _ => omega
    · rintro (e | ⟨wv, arc⟩)
      · rw [e]
        exact ⟨vv, 0, by omega, .refl v⟩
      · exact ⟨wv, 1, le_rfl, .step wv arc (.refl w)⟩
  rw [eq, card_insert_of_notMem (fun h => loopfree free hq vv (mem_outN.mp h).2)]

theorem parents_reverse {v : ℕ} (free : QFree D V q) (hq : 1 ≤ q) (vv : v ∈ V) :
    (inN D V v).card + 1 ≤ (reverseBall D V v 1).card := by
  have sub : insert v (inN D V v) ⊆ reverseBall D V v 1 := by
    intro w hw
    rcases mem_insert.mp hw with e | hw
    · rw [e]
      exact mem_reverse.mpr ⟨vv, self_mem_ball vv⟩
    · obtain ⟨wv, arc⟩ := mem_inN.mp hw
      exact mem_reverse.mpr ⟨wv, ball_of_adj vv arc⟩
  have le := card_le_card sub
  rwa [card_insert_of_notMem (fun h => loopfree free hq vv (mem_inN.mp h).2)] at le

/-- **Parent cap.** A parent of `v` is never in the forward ball of radius `i` when `i + 1 ≤ q`. -/
theorem parent_cap {i v : ℕ} (free : QFree D V q) (hi : i + 1 ≤ q) (vv : v ∈ V) :
    (inN D V v).card + (ball D V v i).card ≤ V.card := by
  have a := parents_reverse free (by omega) vv
  have b := reverseBall_add_ball_le (v := v) free hi
  omega

/-- **Suppliers.** Every row of `T` either has no head in `S` or is a parent of a label of `S`. -/
theorem supplier (S T : Finset ℕ) (tv : T ⊆ V) :
    T.card ≤ (T.filter (fun v => outN D S v = ∅)).card + ∑ s ∈ S, (inN D V s).card := by
  classical
  have cover : T ⊆ T.filter (fun v => outN D S v = ∅) ∪ S.biUnion (fun s => inN D V s) := by
    intro v vt
    by_cases e : outN D S v = ∅
    · exact mem_union_left _ (mem_filter.mpr ⟨vt, e⟩)
    · obtain ⟨s, hs⟩ := nonempty_iff_ne_empty.mpr e
      obtain ⟨ss, arc⟩ := mem_outN.mp hs
      exact mem_union_right _ (mem_biUnion.mpr ⟨s, ss, mem_inN.mpr ⟨tv vt, arc⟩⟩)
  exact (card_le_card cover).trans
    ((card_union_le _ _).trans (Nat.add_le_add_left card_biUnion_le _))

/-- **Supplier cap.** The parents of `S` are capped by the forward balls of `S`. -/
theorem supplier_cap {i : ℕ} (free : QFree D V q) (hi : i + 1 ≤ q) {S T : Finset ℕ}
    (sv : S ⊆ V) (tv : T ⊆ V) :
    T.card + ∑ s ∈ S, (ball D V s i).card ≤
      (T.filter (fun v => outN D S v = ∅)).card + S.card * V.card := by
  have a := supplier (D := D) (V := V) S T tv
  have b : ∑ s ∈ S, ((inN D V s).card + (ball D V s i).card) ≤ ∑ _s ∈ S, V.card :=
    sum_le_sum (fun s ss => parent_cap free hi (sv ss))
  rw [sum_add_distrib, sum_const, smul_eq_mul] at b
  omega

/-- **Tight supply law.** Floor `a` at a radius `i` with `2 i ≤ q`, parents capped at a radius `j`
with `j + 1 ≤ q`. Write `T` for the rows at the floor and `S` for the rows at least two above it.
The rows of `T` with no head in `S` are bounded below by the ledger: the order, the size of `S`,
the excess of `S` over its level, the gaps and the forward balls of `S` all count against them. -/
theorem tight_supply {i j a : ℕ} (free : QFree D V q) (hi : i + i ≤ q) (hj : j + 1 ≤ q)
    (floor : ∀ v ∈ V, a ≤ (ball D V v i).card) :
    2 * (V.card + (V.filter (fun v => a + 1 < (ball D V v i).card)).card
        + ∑ v ∈ V, ((ball D V v i).card - (a + 2)))
      + ∑ v ∈ V, (gap D V i i v).card
      + 2 * ∑ s ∈ V.filter (fun v => a + 1 < (ball D V v i).card), (ball D V s j).card
      + V.card * (a + a)
    ≤ V.card * (V.card + 1)
      + 2 * ((V.filter (fun v => (ball D V v i).card = a)).filter
          (fun v => outN D (V.filter (fun v => a + 1 < (ball D V v i).card)) v = ∅)).card
      + 2 * ((V.filter (fun v => a + 1 < (ball D V v i).card)).card * V.card) := by
  classical
  have spend := budget free hi floor floor
  have lv := levels (fun v => (ball D V v i).card) a 2 V
  rw [sum_range_succ, sum_range_one] at lv
  have cap := supplier_cap (D := D) (V := V) free hj
    (S := V.filter (fun v => a + 1 < (ball D V v i).card))
    (T := V.filter (fun v => (ball D V v i).card = a)) (filter_subset _ _) (filter_subset _ _)
  have part : (V.filter (fun v => (ball D V v i).card = a)).card
      + (V.filter (fun v => a + 0 < (ball D V v i).card)).card = V.card := by
    rw [← card_union_of_disjoint, ← filter_or]
    · congr 1
      refine filter_true_of_mem (fun v vv => ?_)
      have := floor v vv
      omega
    · refine disjoint_filter.mpr (fun v _ e lt => ?_)
      omega
  simp only [add_zero] at lv part
  omega

/-! ### Fragments -/

/-- **Fragment row.** A fragment within the lower quota's range has a row short of the quota. -/
theorem fragment_row {t : ℕ} (none : NoHost q t) (free : QFree D V q) {S : Finset ℕ}
    (sv : S ⊆ V) (live : S.Nonempty) (small : S.card ≤ q*t) :
    ∃ x ∈ S, (outN D S x).card < t := by
  by_contra! paid
  exact none D S live small (free.mono_set sv) paid

/-- **Fragment exit.** No fragment within range keeps the quota on every row. -/
theorem fragment_exit {t : ℕ} (none : NoHost q t) (free : QFree D V q) {S : Finset ℕ}
    (sv : S ⊆ V) (live : S.Nonempty) (small : S.card ≤ q*t)
    (paid : ∀ x ∈ S, t ≤ (outN D S x).card) : False :=
  none D S live small (free.mono_set sv) paid

/-- **Fragment escape.** On a host of degree `r`, the short row has `r + 1 - t` heads outside. -/
theorem fragment_escape {t r : ℕ} (none : NoHost q t) (free : QFree D V q)
    (degree : ∀ v ∈ V, r ≤ (outN D V v).card) {S : Finset ℕ}
    (sv : S ⊆ V) (live : S.Nonempty) (small : S.card ≤ q*t) :
    ∃ x ∈ S, r + 1 ≤ (outN D (V \ S) x).card + t := by
  obtain ⟨x, xs, short⟩ := fragment_row none free sv live small
  have split := card_outN_union (D := D) (show Disjoint S (V \ S) from disjoint_sdiff) x
  rw [union_sdiff_of_subset sv] at split
  have deg := degree x (sv xs)
  exact ⟨x, xs, by omega⟩

/-- Quota one holds outright at every cutoff. -/
theorem noHost_one : NoHost q 1 := by
  intro E U live small free paid
  obtain ⟨s, su, sink⟩ := exists_sink free live (by omega)
  obtain ⟨y, hy⟩ := card_pos.mp (show 0 < (outN E U s).card from paid s su)
  exact sink y (mem_outN.mp hy).1 (mem_outN.mp hy).2

/-- **Closed chain.** A set in which every row has a head has more than `q` labels. -/
theorem closed_chain (free : QFree D V q) {S : Finset ℕ} (sv : S ⊆ V) (live : S.Nonempty)
    (next : ∀ x ∈ S, ∃ y ∈ S, D x y = true) : q < S.card := by
  by_contra small
  refine fragment_exit (t := 1) noHost_one free sv live (by omega) (fun x xs => ?_)
  obtain ⟨y, ys, arc⟩ := next x xs
  exact card_pos.mpr ⟨y, mem_outN.mpr ⟨ys, arc⟩⟩

/-- **Growth row.** While the punctured `k`-ball stays within the lower quota's range, one of its
rows has `r + 1 - t` heads in the shell `k + 1`. -/
theorem growth_row {t r k v : ℕ} (none : NoHost q t) (free : QFree D V q)
    (degree : ∀ v ∈ V, r ≤ (outN D V v).card) (hr : 1 ≤ r) (vv : v ∈ V)
    (hk : 1 ≤ k) (kq : k + 1 ≤ q) (small : (ball D V v k).card ≤ q*t + 1) :
    ∃ x ∈ ball D V v k, ∃ N ⊆ outN D V x,
      N ⊆ ball D V v (k+1) \ ball D V v k ∧ r + 1 ≤ N.card + t := by
  classical
  have vB : v ∈ ball D V v k := self_mem_ball vv
  have sv : (ball D V v k).erase v ⊆ V := (erase_subset _ _).trans ball_subset
  have cardS := card_erase_add_one vB
  have live : ((ball D V v k).erase v).Nonempty := by
    have deg := degree v vv
    obtain ⟨y, hy⟩ := card_pos.mp (show 0 < (outN D V v).card by omega)
    obtain ⟨yv, arc⟩ := mem_outN.mp hy
    refine ⟨y, mem_erase.mpr ⟨fun e => ?_, ball_mono_radius hk (ball_of_adj yv arc)⟩⟩
    rw [e] at arc
    exact loopfree free (by omega) vv arc
  obtain ⟨x, xs, many⟩ := fragment_escape none free degree sv live (by omega)
  have xB : x ∈ ball D V v k := (mem_erase.mp xs).2
  refine ⟨x, xB, outN D (V \ (ball D V v k).erase v) x, fun w hw => ?_, fun w hw => ?_, many⟩
  · obtain ⟨wm, arc⟩ := mem_outN.mp hw
    exact mem_outN.mpr ⟨(mem_sdiff.mp wm).1, arc⟩
  · obtain ⟨wm, arc⟩ := mem_outN.mp hw
    obtain ⟨wv, off⟩ := mem_sdiff.mp wm
    refine mem_sdiff.mpr ⟨ball_step xB wv arc, fun wB => ?_⟩
    by_cases e : w = v
    · rw [e] at arc
      exact no_back_arc free vv xB kq arc
    · exact off (mem_erase.mpr ⟨e, wB⟩)

/-- **Ball growth.** While the punctured ball stays within the lower quota's range, the next
radius gains at least `r + 1 - t` labels. -/
theorem ball_growth {t r k v : ℕ} (none : NoHost q t) (free : QFree D V q)
    (degree : ∀ v ∈ V, r ≤ (outN D V v).card) (hr : 1 ≤ r) (vv : v ∈ V)
    (hk : 1 ≤ k) (kq : k + 1 ≤ q) (small : (ball D V v k).card ≤ q*t + 1) :
    (ball D V v k).card + r + 1 ≤ (ball D V v (k+1)).card + t := by
  obtain ⟨x, _, N, _, inShell, many⟩ := growth_row none free degree hr vv hk kq small
  have incl : ball D V v k ⊆ ball D V v (k+1) := ball_mono_radius (by omega)
  have c := card_le_card inShell
  rw [card_sdiff_of_subset incl] at c
  have mono := card_le_card incl
  omega

/-- **First complete row.** A root whose shell `k + 1` is no larger than the growth bound has a
row in its `k`-ball that heads the whole shell. -/
theorem first_complete {t r k v : ℕ} (none : NoHost q t) (free : QFree D V q)
    (degree : ∀ v ∈ V, r ≤ (outN D V v).card) (hr : 1 ≤ r) (vv : v ∈ V)
    (hk : 1 ≤ k) (kq : k + 1 ≤ q) (small : (ball D V v k).card ≤ q*t + 1)
    (floor : (ball D V v (k+1) \ ball D V v k).card + t ≤ r + 1) :
    ∃ x ∈ ball D V v k, ball D V v (k+1) \ ball D V v k ⊆ outN D V x := by
  obtain ⟨x, xB, N, inRow, inShell, many⟩ := growth_row none free degree hr vv hk kq small
  have eq := eq_of_subset_of_card_le inShell (by omega)
  refine ⟨x, xB, ?_⟩
  rw [← eq]
  exact inRow

/-! ### Shells -/

/-- A head's ball sits one radius deeper in the tail's ball. -/
theorem ball_succ {v x k : ℕ} (xv : x ∈ V) (arc : D v x = true) :
    ball D V x k ⊆ ball D V v (k + 1) := by
  intro w hw
  obtain ⟨wv, j, hj, walk⟩ := mem_ball.mp hw
  exact mem_ball.mpr ⟨wv, j + 1, by omega, .step xv arc walk⟩

theorem head_ball_lt {v x k : ℕ} (free : QFree D V q) (vv : v ∈ V) (xv : x ∈ V)
    (arc : D v x = true) (kq : k + 1 ≤ q) :
    (ball D V x k).card + 1 ≤ (ball D V v (k + 1)).card := by
  have sub : insert v (ball D V x k) ⊆ ball D V v (k + 1) :=
    insert_subset (self_mem_ball vv) (ball_succ xv arc)
  have off : v ∉ ball D V x k := by
    intro h
    obtain ⟨_, j, hj, walk⟩ := mem_ball.mp h
    exact free v (j + 1) (by omega) (by omega) (.step xv arc walk)
  have le := card_le_card sub
  rwa [card_insert_of_notMem off] at le

/-- **Row escape.** A head's row is never inside its tail's row. -/
theorem row_escape {p x : ℕ} (free : QFree D V q) (hq : 1 ≤ q) (xv : x ∈ V)
    (arc : D p x = true) (le : (outN D V p).card ≤ (outN D V x).card) :
    ∃ z ∈ outN D V x, z ∉ outN D V p := by
  by_contra! inside
  have eq := eq_of_subset_of_card_le (fun z hz => inside z hz) le
  have self : x ∈ outN D V x := by
    rw [eq]
    exact mem_outN.mpr ⟨xv, arc⟩
  exact loopfree free hq xv (mem_outN.mp self).2

/-- **Complete row.** A row `x` of the `k`-ball of `v` that heads the whole shell `k + 1` reaches
the whole shell `k + 2` within two steps. With a head `b` of `x` inside the `k`-ball, the two-ball
of `x` also holds `x`, `b` and the heads of `b` inside the `k`-ball. -/
theorem complete_row {v x b k : ℕ} (free : QFree D V q) (hq : 2 ≤ q)
    (xk : x ∈ ball D V v k) (bk : b ∈ ball D V v k) (xb : D x b = true)
    (full : ball D V v (k+1) \ ball D V v k ⊆ outN D V x) :
    (ball D V v (k+2)).card + (outN D (ball D V v k) b).card + 2
      ≤ (ball D V x 2).card + (ball D V v k).card := by
  classical
  have xv : x ∈ V := ball_subset xk
  have bv : b ∈ V := ball_subset bk
  have far : ball D V v (k+2) \ ball D V v k ⊆ ball D V x 2 := by
    intro z hz
    obtain ⟨zin, zoff⟩ := mem_sdiff.mp hz
    by_cases near : z ∈ ball D V v (k+1)
    · exact ball_mono_radius (show 1 ≤ 2 by omega)
        (ball_of_adj (ball_subset near) (mem_outN.mp (full (mem_sdiff.mpr ⟨near, zoff⟩))).2)
    · obtain ⟨zv, j, hj, walk⟩ := mem_ball.mp zin
      have jeq : j = k + 2 := by
        by_contra ne
        exact near (mem_ball.mpr ⟨zv, j, by omega, walk⟩)
      subst jeq
      obtain ⟨y, wy, _, yz⟩ := walk.unsnoc
      have yv : y ∈ V := by
        obtain ⟨_, _, yv, _⟩ := wy.unsnoc
        exact yv
      have yin : y ∈ ball D V v (k+1) := mem_ball.mpr ⟨yv, k + 1, le_rfl, wy⟩
      have yoff : y ∉ ball D V v k := fun h => near (ball_step h zv yz)
      have xy := (mem_outN.mp (full (mem_sdiff.mpr ⟨yin, yoff⟩))).2
      exact mem_ball.mpr ⟨zv, 2, le_rfl, .step yv xy (.step zv yz (.refl z))⟩
  have core : insert x (insert b (outN D (ball D V v k) b)) ⊆ ball D V x 2 := by
    intro w hw
    rcases mem_insert.mp hw with e | hw
    · rw [e]
      exact self_mem_ball xv
    rcases mem_insert.mp hw with e | hw
    · rw [e]
      exact ball_mono_radius (show 1 ≤ 2 by omega) (ball_of_adj bv xb)
    · obtain ⟨wk, bw⟩ := mem_outN.mp hw
      exact mem_ball.mpr ⟨ball_subset wk, 2, le_rfl,
        .step bv xb (.step (ball_subset wk) bw (.refl w))⟩
  have inside : insert x (insert b (outN D (ball D V v k) b)) ⊆ ball D V v k := by
    intro w hw
    rcases mem_insert.mp hw with e | hw
    · rw [e]
      exact xk
    rcases mem_insert.mp hw with e | hw
    · rw [e]
      exact bk
    · exact (mem_outN.mp hw).1
  have dis : Disjoint (ball D V v (k+2) \ ball D V v k)
      (insert x (insert b (outN D (ball D V v k) b))) :=
    disjoint_left.mpr (fun w hw hi => (mem_sdiff.mp hw).2 (inside hi))
  have xnot : x ∉ insert b (outN D (ball D V v k) b) := by
    intro h
    rcases mem_insert.mp h with e | h
    · rw [e] at xb
      exact loopfree free (by omega) bv xb
    · exact digonfree free hq xv bv xb (mem_outN.mp h).2
  have bnot : b ∉ outN D (ball D V v k) b :=
    fun h => loopfree free (by omega) bv (mem_outN.mp h).2
  have size : (insert x (insert b (outN D (ball D V v k) b))).card
      = (outN D (ball D V v k) b).card + 2 := by
    rw [card_insert_of_notMem xnot, card_insert_of_notMem bnot]
  have incl : ball D V v k ⊆ ball D V v (k+2) := ball_mono_radius (by omega)
  have total := card_le_card (union_subset far core)
  rw [card_union_of_disjoint dis, size, card_sdiff_of_subset incl] at total
  have mono := card_le_card incl
  omega

/-- **Full by count.** A row of the `k`-ball whose degree covers its heads inside the ball plus
the size of shell `k + 1` heads the whole shell. -/
theorem full_of_count {v b k : ℕ} (bk : b ∈ ball D V v k)
    (count : (ball D V v (k+1) \ ball D V v k).card + (outN D (ball D V v k) b).card
      ≤ (outN D V b).card) :
    ball D V v (k+1) \ ball D V v k ⊆ outN D V b := by
  classical
  have split := card_outN_union (D := D)
    (show Disjoint (ball D V v k) (V \ ball D V v k) from disjoint_sdiff) b
  rw [union_sdiff_of_subset ball_subset] at split
  have sub : outN D (V \ ball D V v k) b ⊆ ball D V v (k+1) \ ball D V v k := by
    intro w hw
    obtain ⟨wm, arc⟩ := mem_outN.mp hw
    obtain ⟨wv, off⟩ := mem_sdiff.mp wm
    exact mem_sdiff.mpr ⟨ball_step bk wv arc, off⟩
  have eq := eq_of_subset_of_card_le sub (by omega)
  intro w hw
  rw [← eq] at hw
  obtain ⟨wm, arc⟩ := mem_outN.mp hw
  exact mem_outN.mpr ⟨(mem_sdiff.mp wm).1, arc⟩

/-- A row of the `k`-ball whose degree exceeds the shell `k + 1` has a head inside the ball. -/
theorem inner_head {v k r x : ℕ} (degree : ∀ y ∈ V, r ≤ (outN D V y).card)
    (room : (ball D V v (k+1) \ ball D V v k).card < r) (xk : x ∈ ball D V v k) :
    ∃ b ∈ ball D V v k, D x b = true := by
  classical
  obtain ⟨b, hb, boff⟩ : ∃ b ∈ outN D V x, b ∉ ball D V v (k+1) \ ball D V v k := by
    by_contra! all
    have le := card_le_card (fun b hb => all b hb)
    have deg := degree x (ball_subset xk)
    omega
  obtain ⟨bv, xb⟩ := mem_outN.mp hb
  refine ⟨b, ?_, xb⟩
  by_contra off
  exact boff (mem_sdiff.mpr ⟨ball_step xk bv xb, off⟩)

/-- **Tied successor.** When the two-ball of a complete row `x` is capped at `c` and `c` is tight
against the shells of the root, every head of `x` inside the `k`-ball is complete again. -/
theorem tied_next {v k r c x b : ℕ} (free : QFree D V q) (hq : 2 ≤ q)
    (degree : ∀ y ∈ V, r ≤ (outN D V y).card) (cap : (ball D V x 2).card ≤ c)
    (tight : (ball D V v (k+1) \ ball D V v k).card + c + (ball D V v k).card
      ≤ r + (ball D V v (k+2)).card + 2)
    (xk : x ∈ ball D V v k) (full : ball D V v (k+1) \ ball D V v k ⊆ outN D V x)
    (bk : b ∈ ball D V v k) (xb : D x b = true) :
    ball D V v (k+1) \ ball D V v k ⊆ outN D V b := by
  have row := complete_row free hq xk bk xb full
  have deg := degree b (ball_subset bk)
  exact full_of_count bk (by omega)

/-- **Tied chain.** Fix a root `v` and a radius `k`. Call a row of the `k`-ball complete when it
heads the whole shell `k + 1`. If the shell is smaller than the degree, complete rows have
two-balls of at most `c` labels, and `c` is tight against the shells of the root, then the
complete rows, once there is one, number more than `q`. -/
theorem tied_chain {v k r c : ℕ} (free : QFree D V q) (hq : 2 ≤ q)
    (degree : ∀ x ∈ V, r ≤ (outN D V x).card)
    (room : (ball D V v (k+1) \ ball D V v k).card < r)
    (cap : ∀ x ∈ ball D V v k, ball D V v (k+1) \ ball D V v k ⊆ outN D V x →
      (ball D V x 2).card ≤ c)
    (tight : (ball D V v (k+1) \ ball D V v k).card + c + (ball D V v k).card
      ≤ r + (ball D V v (k+2)).card + 2)
    (live : ∃ x ∈ ball D V v k, ball D V v (k+1) \ ball D V v k ⊆ outN D V x) :
    q < ((ball D V v k).filter
      (fun x => ball D V v (k+1) \ ball D V v k ⊆ outN D V x)).card := by
  classical
  refine closed_chain free (fun x hx => ball_subset (mem_filter.mp hx).1) ?_ ?_
  · obtain ⟨x, xk, full⟩ := live
    exact ⟨x, mem_filter.mpr ⟨xk, full⟩⟩
  · intro x hx
    obtain ⟨xk, full⟩ := mem_filter.mp hx
    obtain ⟨b, bk, xb⟩ := inner_head degree room xk
    exact ⟨b, mem_filter.mpr
      ⟨bk, tied_next free hq degree (cap x xk full) tight xk full bk xb⟩, xb⟩

/-- **Complete floor.** A complete row sits strictly above the bare count: its two-ball holds the
two outer shells of the root and three more labels. -/
theorem complete_floor {v k r x : ℕ} (free : QFree D V q) (hq : 2 ≤ q)
    (degree : ∀ y ∈ V, r ≤ (outN D V y).card)
    (room : (ball D V v (k+1) \ ball D V v k).card < r)
    (xk : x ∈ ball D V v k) (full : ball D V v (k+1) \ ball D V v k ⊆ outN D V x) :
    (ball D V v (k+2)).card + 3 ≤ (ball D V x 2).card + (ball D V v k).card := by
  obtain ⟨b, bk, xb⟩ := inner_head degree room xk
  obtain ⟨b', bk', bb⟩ := inner_head degree room bk
  have one : 0 < (outN D (ball D V v k) b).card := card_pos.mpr ⟨b', mem_outN.mpr ⟨bk', bb⟩⟩
  have row := complete_row free hq xk bk xb full
  omega

/-- Two subsets of one size inside a set one larger: a label missing from the first and present
in the set lies in the second, unless the two subsets coincide. -/
theorem odd_one {N A A' : Finset ℕ} {b : ℕ} (a : A ⊆ N) (a' : A' ⊆ N) (bn : b ∈ N)
    (ba : b ∉ A) (small : N.card ≤ A.card + 1) (same : A.card = A'.card) (ne : A ≠ A') :
    b ∈ A' := by
  by_contra ba'
  have e1 : insert b A = N :=
    eq_of_subset_of_card_le (insert_subset bn a) (by rw [card_insert_of_notMem ba]; exact small)
  have e2 : insert b A' = N :=
    eq_of_subset_of_card_le (insert_subset bn a') (by rw [card_insert_of_notMem ba']; omega)
  have h1 : A = N.erase b := by rw [← e1, erase_insert ba]
  have h2 : A' = N.erase b := by rw [← e2, erase_insert ba']
  exact ne (h1.trans h2.symm)

/-- **Tied rows belong to one shell.** A row whose degree is one more than the shell size cannot
be complete for two roots with different shells: its two inner heads would point at each other. -/
theorem tied_disjoint {v w k r c x : ℕ} (free : QFree D V q) (hq : 2 ≤ q)
    (degree : ∀ y ∈ V, r ≤ (outN D V y).card)
    (exact : (outN D V x).card ≤ (ball D V v (k+1) \ ball D V v k).card + 1)
    (room : (ball D V v (k+1) \ ball D V v k).card < r)
    (size : (ball D V v (k+1) \ ball D V v k).card = (ball D V w (k+1) \ ball D V w k).card)
    (ne : ball D V v (k+1) \ ball D V v k ≠ ball D V w (k+1) \ ball D V w k)
    (cap : (ball D V x 2).card ≤ c)
    (tightv : (ball D V v (k+1) \ ball D V v k).card + c + (ball D V v k).card
      ≤ r + (ball D V v (k+2)).card + 2)
    (tightw : (ball D V w (k+1) \ ball D V w k).card + c + (ball D V w k).card
      ≤ r + (ball D V w (k+2)).card + 2)
    (xv : x ∈ ball D V v k) (fullv : ball D V v (k+1) \ ball D V v k ⊆ outN D V x)
    (xw : x ∈ ball D V w k) (fullw : ball D V w (k+1) \ ball D V w k ⊆ outN D V x) :
    False := by
  obtain ⟨bv, bvk, xbv⟩ := inner_head degree room xv
  obtain ⟨bw, bwk, xbw⟩ := inner_head degree (by omega) xw
  have bvV := ball_subset bvk
  have bwV := ball_subset bwk
  have nv : bv ∉ ball D V v (k+1) \ ball D V v k := fun h => (mem_sdiff.mp h).2 bvk
  have nw : bw ∉ ball D V w (k+1) \ ball D V w k := fun h => (mem_sdiff.mp h).2 bwk
  have inW := odd_one fullv fullw (mem_outN.mpr ⟨bvV, xbv⟩) nv exact size ne
  have inV := odd_one fullw fullv (mem_outN.mpr ⟨bwV, xbw⟩) nw (by omega) size.symm ne.symm
  have cv := tied_next free hq degree cap tightv xv fullv bvk xbv
  have cw := tied_next free hq degree cap tightw xw fullw bwk xbw
  exact digonfree free hq bvV bwV (mem_outN.mp (cv inV)).2 (mem_outN.mp (cw inW)).2

/-- **Complete row or fragment.** Needs no lower quota. A root whose shell `k + 1` has at most
`r + 1 - t` labels either has a row in its `k`-ball heading the whole shell, or its punctured
`k`-ball keeps `t` heads inside on every row. -/
theorem complete_or_fragment {t r k v : ℕ} (free : QFree D V q)
    (degree : ∀ y ∈ V, r ≤ (outN D V y).card) (vv : v ∈ V) (kq : k + 1 ≤ q)
    (floor : (ball D V v (k+1) \ ball D V v k).card + t ≤ r + 1) :
    (∃ x ∈ ball D V v k, ball D V v (k+1) \ ball D V v k ⊆ outN D V x) ∨
      ∀ x ∈ (ball D V v k).erase v, t ≤ (outN D ((ball D V v k).erase v) x).card := by
  classical
  by_cases all : ∀ x ∈ (ball D V v k).erase v, t ≤ (outN D ((ball D V v k).erase v) x).card
  · exact Or.inr all
  left
  obtain ⟨x, hx⟩ := not_forall.mp all
  obtain ⟨xs, short⟩ := Classical.not_imp.mp hx
  have xB : x ∈ ball D V v k := (mem_erase.mp xs).2
  have sv : (ball D V v k).erase v ⊆ V := (erase_subset _ _).trans ball_subset
  have split := card_outN_union (D := D)
    (show Disjoint ((ball D V v k).erase v) (V \ (ball D V v k).erase v) from disjoint_sdiff) x
  rw [union_sdiff_of_subset sv] at split
  have deg := degree x (sv xs)
  have inShell : outN D (V \ (ball D V v k).erase v) x ⊆ ball D V v (k+1) \ ball D V v k := by
    intro w hw
    obtain ⟨wm, arc⟩ := mem_outN.mp hw
    obtain ⟨wv, off⟩ := mem_sdiff.mp wm
    refine mem_sdiff.mpr ⟨ball_step xB wv arc, fun wB => ?_⟩
    by_cases e : w = v
    · rw [e] at arc
      exact no_back_arc free vv xB kq arc
    · exact off (mem_erase.mpr ⟨e, wB⟩)
  have eq := eq_of_subset_of_card_le inShell (by omega)
  refine ⟨x, xB, ?_⟩
  rw [← eq]
  exact fun w hw => mem_outN.mpr ⟨(mem_sdiff.mp (mem_outN.mp hw).1).1, (mem_outN.mp hw).2⟩

/-! ### Rows with the same shell -/

/-- **Same shell.** If `v → w` and the two rows have the same shell `k + 1`, the `k`-ball of `w`
sits inside the `k`-ball of `v` and misses `v`. -/
theorem same_shell_lt {v w k : ℕ} (free : QFree D V q) (kq : k + 1 ≤ q) (vv : v ∈ V)
    (wv : w ∈ V) (arc : D v w = true)
    (same : ball D V v (k+1) \ ball D V v k = ball D V w (k+1) \ ball D V w k) :
    (ball D V w k).card + 1 ≤ (ball D V v k).card := by
  classical
  have sub : insert v (ball D V w k) ⊆ ball D V v k := by
    intro z hz
    rcases mem_insert.mp hz with e | hz
    · rw [e]
      exact self_mem_ball vv
    · by_contra off
      have deep : z ∈ ball D V v (k+1) \ ball D V v k :=
        mem_sdiff.mpr ⟨ball_succ wv arc hz, off⟩
      rw [same] at deep
      exact (mem_sdiff.mp deep).2 hz
  have off : v ∉ ball D V w k := by
    intro h
    obtain ⟨_, j, hj, walk⟩ := mem_ball.mp h
    exact free v (j + 1) (by omega) (by omega) (.step wv arc walk)
  have le := card_le_card sub
  rwa [card_insert_of_notMem off] at le

/-- Two rows with the same second shell, the second of no smaller degree: the first does not reach
the second within two steps. -/
theorem same_shell_gap {v w : ℕ} (free : QFree D V q) (hq : 2 ≤ q) (vv : v ∈ V) (wv : w ∈ V)
    (ne : w ≠ v) (le : (outN D V v).card ≤ (outN D V w).card)
    (same : ball D V v 2 \ ball D V v 1 = ball D V w 2 \ ball D V w 1) :
    w ∉ ball D V v 2 := by
  intro h
  by_cases near : w ∈ ball D V v 1
  · obtain ⟨_, j, hj, walk⟩ := mem_ball.mp near
    have arc : D v w = true := by
      match j, hj, walk with
      | 0, _, walk =>
        cases walk
        exact absurd rfl ne
      | 1, _, walk =>
        cases walk with
        | step _ arc rest =>
          cases rest
          exact arc
      | n + 2, hj, _ => omega
    have lt := same_shell_lt free (k := 1) (by omega) vv wv arc same
    rw [ball_one free (by omega) vv, ball_one free (by omega) wv] at lt
    omega
  · have deep : w ∈ ball D V v 2 \ ball D V v 1 := mem_sdiff.mpr ⟨h, near⟩
    rw [same] at deep
    exact (mem_sdiff.mp deep).2 (self_mem_ball wv)

/-- Two rows of equal degree with the same second shell are a gap at radii `(2, 2)`. -/
theorem same_shell_gapped {v w : ℕ} (free : QFree D V q) (hq : 2 ≤ q) (vv : v ∈ V)
    (wv : w ∈ V) (ne : w ≠ v) (eq : (outN D V v).card = (outN D V w).card)
    (same : ball D V v 2 \ ball D V v 1 = ball D V w 2 \ ball D V w 1) :
    w ∈ gap D V 2 2 v :=
  mem_gap.mpr ⟨wv, same_shell_gap free hq vv wv ne eq.le same,
    same_shell_gap free hq wv vv ne.symm eq.ge same.symm⟩

/-- **Gap clique.** Rows that are pairwise gaps pay for it in the gap sums. -/
theorem gap_clique {i j : ℕ} {R : Finset ℕ}
    (pair : ∀ v ∈ R, ∀ w ∈ R, w ≠ v → w ∈ gap D V i j v) :
    R.card * (R.card - 1) ≤ ∑ v ∈ R, (gap D V i j v).card := by
  classical
  have each : ∀ v ∈ R, R.card - 1 ≤ (gap D V i j v).card := by
    intro v vr
    rw [← card_erase_of_mem vr]
    exact card_le_card (fun w hw => pair v vr w (mem_erase.mp hw).2 (mem_erase.mp hw).1)
  have total := sum_le_sum each
  rwa [sum_const, smul_eq_mul] at total

/-- **Shell class.** Rows of one degree sharing one second shell are a gap clique at radius two. -/
theorem shell_class {r : ℕ} {R Y : Finset ℕ} (free : QFree D V q) (hq : 2 ≤ q) (rv : R ⊆ V)
    (deg : ∀ v ∈ R, (outN D V v).card = r)
    (mask : ∀ v ∈ R, ball D V v 2 \ ball D V v 1 = Y) :
    R.card * (R.card - 1) ≤ ∑ v ∈ R, (gap D V 2 2 v).card :=
  gap_clique (fun v vr w wr ne => same_shell_gapped free hq (rv vr) (rv wr) ne
    ((deg v vr).trans (deg w wr).symm) ((mask v vr).trans (mask w wr).symm))

/-! ### Classes of roots -/

/-- **Class count.** Roots `R` whose complete rows all lie in a set `H` of capped rows of degree
`r`, each root with shell `k + 1` of `r - 1` labels and the cap tight against its shells. Every
distinct shell among the roots owns more than `q` rows of `H`, and no row is owned twice. -/
theorem class_count {k r c : ℕ} {R H : Finset ℕ} (free : QFree D V q) (hq : 2 ≤ q)
    (degree : ∀ y ∈ V, r ≤ (outN D V y).card) (exact : ∀ y ∈ H, (outN D V y).card ≤ r)
    (cap : ∀ y ∈ H, (ball D V y 2).card ≤ c)
    (size : ∀ v ∈ R, (ball D V v (k+1) \ ball D V v k).card + 1 = r)
    (tight : ∀ v ∈ R, (ball D V v (k+1) \ ball D V v k).card + c + (ball D V v k).card
      ≤ r + (ball D V v (k+2)).card + 2)
    (live : ∀ v ∈ R, ∃ x ∈ ball D V v k, ball D V v (k+1) \ ball D V v k ⊆ outN D V x)
    (high : ∀ v ∈ R, ∀ x ∈ ball D V v k,
      ball D V v (k+1) \ ball D V v k ⊆ outN D V x → x ∈ H) :
    (q + 1) * (R.image (fun v => ball D V v (k+1) \ ball D V v k)).card ≤ H.card := by
  classical
  have pick : ∀ Y ∈ R.image (fun v => ball D V v (k+1) \ ball D V v k),
      ∃ v, v ∈ R ∧ ball D V v (k+1) \ ball D V v k = Y := fun Y hY => by
    obtain ⟨v, vR, e⟩ := mem_image.mp hY
    exact ⟨v, vR, e⟩
  choose! rep repR repY using pick
  have big : ∀ Y ∈ R.image (fun v => ball D V v (k+1) \ ball D V v k),
      q + 1 ≤ ((ball D V (rep Y) k).filter (fun x => Y ⊆ outN D V x)).card := by
    intro Y hY
    have vR := repR Y hY
    have e := repY Y hY
    have sz := size (rep Y) vR
    have chain := tied_chain free hq degree (by omega)
      (fun x xk full => cap x (high (rep Y) vR x xk full)) (tight (rep Y) vR) (live (rep Y) vR)
    rw [e] at chain
    exact chain
  have sub : (R.image (fun v => ball D V v (k+1) \ ball D V v k)).biUnion
      (fun Y => (ball D V (rep Y) k).filter (fun x => Y ⊆ outN D V x)) ⊆ H := by
    intro x hx
    obtain ⟨Y, hY, hxY⟩ := mem_biUnion.mp hx
    obtain ⟨xk, full⟩ := mem_filter.mp hxY
    refine high (rep Y) (repR Y hY) x xk ?_
    rw [repY Y hY]
    exact full
  have dis : ∀ Y ∈ R.image (fun v => ball D V v (k+1) \ ball D V v k),
      ∀ Y' ∈ R.image (fun v => ball D V v (k+1) \ ball D V v k), Y ≠ Y' →
      Disjoint ((ball D V (rep Y) k).filter (fun x => Y ⊆ outN D V x))
        ((ball D V (rep Y') k).filter (fun x => Y' ⊆ outN D V x)) := by
    intro Y hY Y' hY' hne
    rw [disjoint_left]
    intro x hx hx'
    obtain ⟨xk, full⟩ := mem_filter.mp hx
    obtain ⟨xk', full'⟩ := mem_filter.mp hx'
    have e := repY Y hY
    have e' := repY Y' hY'
    have fullv : ball D V (rep Y) (k+1) \ ball D V (rep Y) k ⊆ outN D V x := by
      rw [e]
      exact full
    have fullw : ball D V (rep Y') (k+1) \ ball D V (rep Y') k ⊆ outN D V x := by
      rw [e']
      exact full'
    have xH := high (rep Y) (repR Y hY) x xk fullv
    have sz := size (rep Y) (repR Y hY)
    have sz' := size (rep Y') (repR Y' hY')
    have ex := exact x xH
    exact tied_disjoint free hq degree (by omega) (by omega) (by omega)
      (fun h => hne (e.symm.trans (h.trans e'))) (cap x xH)
      (tight (rep Y) (repR Y hY)) (tight (rep Y') (repR Y' hY')) xk fullv xk' fullw
  calc (q + 1) * (R.image (fun v => ball D V v (k+1) \ ball D V v k)).card
      = ∑ _Y ∈ R.image (fun v => ball D V v (k+1) \ ball D V v k), (q + 1) := by
        rw [sum_const, smul_eq_mul, Nat.mul_comm]
    _ ≤ ∑ Y ∈ R.image (fun v => ball D V v (k+1) \ ball D V v k),
          ((ball D V (rep Y) k).filter (fun x => Y ⊆ outN D V x)).card := sum_le_sum big
    _ = ((R.image (fun v => ball D V v (k+1) \ ball D V v k)).biUnion
          (fun Y => (ball D V (rep Y) k).filter (fun x => Y ⊆ outN D V x))).card :=
        (card_biUnion dis).symm
    _ ≤ H.card := card_le_card sub

/-- **Class roots.** Roots of one degree: all but one root of each second-shell class is paid for
by the gaps at radius two. -/
theorem class_roots {r : ℕ} {R : Finset ℕ} (free : QFree D V q) (hq : 2 ≤ q) (rv : R ⊆ V)
    (deg : ∀ v ∈ R, (outN D V v).card = r) :
    2 * R.card ≤ 2 * (R.image (fun v => ball D V v 2 \ ball D V v 1)).card
      + ∑ v ∈ R, (gap D V 2 2 v).card := by
  classical
  have maps : ∀ v ∈ R, (fun v => ball D V v 2 \ ball D V v 1) v
      ∈ R.image (fun v => ball D V v 2 \ ball D V v 1) := fun v hv => mem_image_of_mem _ hv
  have each : ∀ Y ∈ R.image (fun v => ball D V v 2 \ ball D V v 1),
      2 * (R.filter (fun v => ball D V v 2 \ ball D V v 1 = Y)).card ≤
        2 + ∑ v ∈ R.filter (fun v => ball D V v 2 \ ball D V v 1 = Y), (gap D V 2 2 v).card := by
    intro Y _
    have law := shell_class (R := R.filter (fun v => ball D V v 2 \ ball D V v 1 = Y)) (Y := Y)
      free hq ((filter_subset _ _).trans rv) (fun v hv => deg v (mem_filter.mp hv).1)
      (fun v hv => (mem_filter.mp hv).2)
    by_cases two : 2 ≤ (R.filter (fun v => ball D V v 2 \ ball D V v 1 = Y)).card
    · have step := Nat.mul_le_mul_right
        ((R.filter (fun v => ball D V v 2 \ ball D V v 1 = Y)).card - 1) two
      omega
    · omega
  have total := sum_le_sum each
  rw [← mul_sum, ← card_eq_sum_card_image, sum_add_distrib, sum_const, smul_eq_mul,
    sum_fiberwise_of_maps_to maps] at total
  omega

#print axioms row_ledger
#print axioms ledger
#print axioms budget
#print axioms levels
#print axioms gap_swap
#print axioms covered
#print axioms ball_one
#print axioms parent_cap
#print axioms supplier
#print axioms supplier_cap
#print axioms tight_supply
#print axioms fragment_row
#print axioms fragment_exit
#print axioms fragment_escape
#print axioms noHost_one
#print axioms closed_chain
#print axioms growth_row
#print axioms ball_growth
#print axioms first_complete
#print axioms ball_succ
#print axioms head_ball_lt
#print axioms row_escape
#print axioms complete_row
#print axioms full_of_count
#print axioms complete_or_fragment
#print axioms tied_next
#print axioms tied_chain
#print axioms complete_floor
#print axioms tied_disjoint
#print axioms same_shell_lt
#print axioms same_shell_gapped
#print axioms gap_clique
#print axioms shell_class
#print axioms class_count
#print axioms class_roots
end LeanCH.BR.ReachLedger
