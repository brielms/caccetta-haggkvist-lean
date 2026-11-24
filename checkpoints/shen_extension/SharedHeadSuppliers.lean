import checkpoints.shen_extension.ReachLedgerCatalog
import checkpoints.shen_extension.ShortfallBridge

/-!
# Low banks, shared heads and high columns, in free `q`, `r`, `n`

Lean 4.35.0. No order, cutoff, degree or quota is fixed anywhere in this file. `t` is a lower
quota with `r = q t + 1`, so that the first layer of a root is exactly a boundary-order fragment
for quota `t`; boundary in-regularity at `(q, t)` (`QBoundaryInRegular q t`) is the supplied
lower-degree input, together with `NoHost` at quotas `t`, `t + 1` and one more quota `s`.

All balls are closed (`|ball v i| = f_i(v) + 1`).

## The second-ball floor

* `layer_floor`: from `NoHost q (t+1)` and `r ≤ q (t+1)`, every row has `2r + 1 ≤ |ball v 2| + t`.
* A *low root* has `|ball v 2| + t = 2r + 1`. `low_bank`: by in-regularity its first layer is
  exactly `t`-out internally and every first-layer row heads the whole second shell.
  `bank_third`: the third shell has more than `r - t` labels (`NoHost q t`). `bank_high`: a
  first-layer row reaches the two outer shells and `2t` first-layer labels within two.
  `low_root` assembles these: every bank row has `2r + 2 ≤ |ball x 2|`.
* `bank_meet`: the banks of two low roots are equal or disjoint. `same_layer_far`, `layer_roots`:
  low roots with one bank are pairwise gaps.
* `bank_excess`, `bank_budget`, `bank_ledger`: the radius-two budget with `k` distinct banks reads
  `2 t r k + 2n + 2 (excess of the rest) + 2 a n ≤ n (n + 1) + 2k`, `a = 2r + 1 - t`.
* `floor_by_budget`: if `n (n+1) + 2 < 2 t r + 2n + 2 a n` there is no low root:
  `a + 1 ≤ |ball v 2|` everywhere.
* `bank_cut`, `floor_by_cut`: with the tight-head rule, one bank is paid by the indegrees of the
  few labels above the tight value; regime `σ (n + s - (a + r + 2)) + 2t < 2r + 1`.

## Regime theorems (conclude `False`)

* `bank_regime`: `n + 1 < 2 (2r + 2 - t)` and the bank inequality.
* `tied_regime`: floor `b` everywhere, `n + 1 ≤ 2b` and the tight-head rule at `b`.

## Shared heads and high columns

* `common_head`, `shared_head`, `two_highs`: a tight row and a high head share a head; with the
  tight-head rule every tight row sees two highs within two, and each of its high heads reaches
  another of them within two.
* `mutual_far`, `one_direct`: a tight row that sees exactly two highs heads at most one.
* `column_count`, `inner_count`, `high_columns`: incoming high columns and outgoing high rows
  paid together: `2 C_T + 2 B + h (h + 1) ≤ 2 h (n + 1)`.
* `high_count`: with `E`, `S` the excesses, `2 (2 (n - h) + E) + 2 ((b+1) h + S) + h (h+1) ≤ 2 h (n+1)`.
* `excess_zero`, `excess_one`: excess at most one leaves a host of quota `r - 1` (or a unit graph)
  on the `n - h` tight rows: regime `n - h < q (r - 1)`.

## Supports

* `support_count`: a set whose rows keep at most one head inside, and whose outside labels have at
  most `m` parents inside, satisfies `|C| (r - 1) ≤ m (n - |C|)`. `support_regime` is the exit.
-/

set_option linter.style.longLine false

namespace LeanCH.BR.SharedHeadSuppliers
open Finset BRq2 BRq3 BR45 BypassRepair ReachLedger
open LeanCH.BR.Closure.BoundaryHub (QBoundaryInRegular)

variable {D : CH.Digraph} {V : Finset ℕ} {q : ℕ}

/-- **Tight-head rule at value `b`.** Every row whose closed two-ball has exactly `b` labels has a
head whose two-ball does not. (Paper step at `b = 2r`, not proved here.) -/
def TightHead (D : CH.Digraph) (V : Finset ℕ) (b : ℕ) : Prop :=
  ∀ y ∈ V, (ball D V y 2).card = b → ∃ w ∈ outN D V y, (ball D V w 2).card ≠ b

theorem prod_ge {P k : ℕ} (hP : 1 ≤ P) (hk : 1 ≤ k) : P + k ≤ P * k + 1 := by
  obtain ⟨x, rfl⟩ := Nat.exists_eq_add_of_le hP
  obtain ⟨y, rfl⟩ := Nat.exists_eq_add_of_le hk
  ring_nf
  omega

theorem prod_ge_two {P k : ℕ} (hP : 1 ≤ P) (hk : 2 ≤ k) : 2 * P + k ≤ P * k + 2 := by
  obtain ⟨x, rfl⟩ := Nat.exists_eq_add_of_le hP
  obtain ⟨y, rfl⟩ := Nat.exists_eq_add_of_le hk
  ring_nf
  omega

/-! ### First layer -/

/-- A head of a first-layer row lies in the first layer or in the second shell. -/
theorem layer_heads {v x y : ℕ} (free : QFree D V q) (hq : 2 ≤ q) (vv : v ∈ V)
    (hx : x ∈ outN D V v) (hy : y ∈ outN D V x) :
    y ∈ outN D V v ∨ y ∈ ball D V v 2 \ ball D V v 1 := by
  obtain ⟨xv, vx⟩ := mem_outN.mp hx
  obtain ⟨yv, xy⟩ := mem_outN.mp hy
  by_cases near : y ∈ ball D V v 1
  · rcases (mem_ball_one vv).mp near with e | h
    · rw [e] at xy
      exact absurd xy (fun h => digonfree free hq vv xv vx h)
    · exact Or.inl h
  · exact Or.inr (mem_sdiff.mpr ⟨ball_step (ball_of_adj xv vx) yv xy, near⟩)

theorem layer_split {v x : ℕ} (free : QFree D V q) (hq : 2 ≤ q) (vv : v ∈ V)
    (hx : x ∈ outN D V v) :
    (outN D V x).card ≤ (outN D (outN D V v) x).card + (ball D V v 2 \ ball D V v 1).card := by
  classical
  have sub : outN D V x ⊆ outN D (outN D V v) x ∪ (ball D V v 2 \ ball D V v 1) := by
    intro y hy
    rcases layer_heads free hq vv hx hy with h | h
    · exact mem_union_left _ (mem_outN.mpr ⟨h, (mem_outN.mp hy).2⟩)
    · exact mem_union_right _ h
  exact (card_le_card sub).trans (card_union_le _ _)

/-- **Layer floor.** From the quota `t + 1` one above: `2r + 1 ≤ |ball v 2| + t`. -/
theorem layer_floor {t r v : ℕ} (above : NoHost q (t+1)) (free : QFree D V q) (hq : 2 ≤ q)
    (exact : ∀ y ∈ V, (outN D V y).card = r) (hr : 1 ≤ r) (room : r ≤ q*(t+1)) (vv : v ∈ V) :
    2*r + 1 ≤ (ball D V v 2).card + t := by
  have one := ReachLedger.ball_one free (by omega) vv
  rw [exact v vv] at one
  have grow := ReachLedger.ball_growth (k := 1) above free (fun y hy => (exact y hy).ge) hr vv
    le_rfl (by omega) (by omega)
  simp only [Nat.reduceAdd] at grow
  omega

theorem low_shell {t r v : ℕ} (free : QFree D V q) (hq : 1 ≤ q)
    (exact : ∀ y ∈ V, (outN D V y).card = r) (vv : v ∈ V)
    (low : (ball D V v 2).card + t = 2*r + 1) :
    (ball D V v 2 \ ball D V v 1).card + t = r := by
  have incl : ball D V v 1 ⊆ ball D V v 2 := ball_mono_radius (by omega)
  have m := card_le_card incl
  have one := ReachLedger.ball_one free hq vv
  rw [exact v vv] at one
  rw [card_sdiff_of_subset incl]
  omega

/-- **Low bank.** At a low root the first layer is a boundary-order fragment: in-regularity makes
every row exactly `t`-out inside it, so every row heads the whole second shell. -/
theorem low_bank {t r v : ℕ} (free : QFree D V q) (hq : 2 ≤ q)
    (exact : ∀ y ∈ V, (outN D V y).card = r) (law : QBoundaryInRegular q t)
    (order : r = q*t + 1) (vv : v ∈ V)
    (shell : (ball D V v 2 \ ball D V v 1).card + t = r) :
    ∀ x ∈ outN D V v, (outN D (outN D V v) x).card = t ∧
      ball D V v 2 \ ball D V v 1 ⊆ outN D V x := by
  classical
  have xsub : outN D V v ⊆ V := outN_subset
  have floor : ∀ x ∈ outN D V v, t ≤ (outN D (outN D V v) x).card := by
    intro x hx
    have s := layer_split free hq vv hx
    have e := exact x (xsub hx)
    omega
  have inreg := law D (outN D V v) (free.mono_set xsub) (by rw [exact v vv]; omega) floor
  have sum := BR45.sum_out_in D (outN D V v)
  have eqs : ∑ x ∈ outN D V v, t = ∑ x ∈ outN D V v, (outN D (outN D V v) x).card := by
    rw [sum]
    exact (sum_congr rfl inreg).symm
  have each := (sum_eq_sum_iff_of_le floor).mp eqs
  intro x hx
  have tx := (each x hx).symm
  refine ⟨tx, ?_⟩
  have split := card_outN_union (D := D)
    (show Disjoint (outN D V v) (V \ outN D V v) from disjoint_sdiff) x
  rw [union_sdiff_of_subset xsub] at split
  have sub : outN D (V \ outN D V v) x ⊆ ball D V v 2 \ ball D V v 1 := by
    intro y hy
    obtain ⟨ym, xy⟩ := mem_outN.mp hy
    obtain ⟨yv, off⟩ := mem_sdiff.mp ym
    rcases layer_heads free hq vv hx (mem_outN.mpr ⟨yv, xy⟩) with h | h
    · exact absurd h off
    · exact h
  have e := exact x (xsub hx)
  have eq := eq_of_subset_of_card_le sub (by omega)
  intro y hy
  rw [← eq] at hy
  obtain ⟨ym, xy⟩ := mem_outN.mp hy
  exact mem_outN.mpr ⟨(mem_sdiff.mp ym).1, xy⟩

/-- A row heading the whole shell `k + 1` reaches the shells `k + 1` and `k + 2` within two. -/
theorem far_in_two {v x k : ℕ} (full : ball D V v (k+1) \ ball D V v k ⊆ outN D V x) :
    ball D V v (k+2) \ ball D V v k ⊆ ball D V x 2 := by
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

/-- **Third shell.** When every first-layer row heads the whole second shell, the second shell
cannot keep the quota `t` inside, so the third shell has more than `r - t` labels. -/
theorem bank_third {t r v : ℕ} (none : NoHost q t) (free : QFree D V q) (hq : 3 ≤ q)
    (degree : ∀ y ∈ V, r ≤ (outN D V y).card) (vv : v ∈ V)
    (full : ∀ x ∈ outN D V v, ball D V v 2 \ ball D V v 1 ⊆ outN D V x)
    (live : (ball D V v 2 \ ball D V v 1).Nonempty)
    (small : (ball D V v 2 \ ball D V v 1).card ≤ q*t) :
    r + 1 ≤ (ball D V v 3 \ ball D V v 2).card + t := by
  classical
  by_contra! few
  refine fragment_exit none free (sdiff_subset.trans ball_subset) live small (fun y hy => ?_)
  obtain ⟨y2, y1⟩ := mem_sdiff.mp hy
  have sub : outN D V y ⊆
      outN D (ball D V v 2 \ ball D V v 1) y ∪ (ball D V v 3 \ ball D V v 2) := by
    intro z hz
    obtain ⟨zv, yz⟩ := mem_outN.mp hz
    have z3 : z ∈ ball D V v 3 := ball_step y2 zv yz
    by_cases z2 : z ∈ ball D V v 2
    · by_cases z1 : z ∈ ball D V v 1
      · exfalso
        rcases (mem_ball_one vv).mp z1 with e | zx
        · rw [e] at yz
          exact no_back_arc free vv y2 (by omega) yz
        · exact digonfree free (by omega) (ball_subset y2) zv yz (mem_outN.mp (full z zx hy)).2
      · exact mem_union_left _ (mem_outN.mpr ⟨mem_sdiff.mpr ⟨z2, z1⟩, yz⟩)
    · exact mem_union_right _ (mem_sdiff.mpr ⟨z3, z2⟩)
  have c := (card_le_card sub).trans (card_union_le _ _)
  have d := degree y (ball_subset y2)
  omega

/-- **Bank row.** A first-layer row that heads the whole second shell, in a first layer that is
exactly `t`-out inside (`1 ≤ t ≤ q`), reaches both outer shells and `2t` first-layer labels
within two: take a sink among its `t` inner heads. -/
theorem bank_high {t v x : ℕ} (free : QFree D V q) (hq : 2 ≤ q) (tq : t ≤ q) (ht : 1 ≤ t)
    (_vv : v ∈ V) (inner : ∀ y ∈ outN D V v, (outN D (outN D V v) y).card = t)
    (full : ball D V v 2 \ ball D V v 1 ⊆ outN D V x) (hx : x ∈ outN D V v) :
    (ball D V v 3).card + 1 + 2*t ≤ (ball D V x 2).card + (ball D V v 1).card := by
  classical
  have X1 : outN D V v ⊆ ball D V v 1 :=
    fun y hy => ball_of_adj (mem_outN.mp hy).1 (mem_outN.mp hy).2
  have Xsub : outN D V v ⊆ V := outN_subset
  have xv : x ∈ V := Xsub hx
  have Afree : QFree D (outN D (outN D V v) x) q := free.mono_set (outN_subset.trans Xsub)
  have Acard := inner x hx
  obtain ⟨b, bA, sink⟩ := exists_sink Afree (card_pos.mp (by omega)) (by omega)
  obtain ⟨bX, xb⟩ := mem_outN.mp bA
  have bv : b ∈ V := Xsub bX
  have Bcard := inner b bX
  have dis : Disjoint (outN D (outN D V v) x) (outN D (outN D V v) b) :=
    disjoint_left.mpr (fun z za zb => sink z za (mem_outN.mp zb).2)
  have xA : x ∉ outN D (outN D V v) x ∪ outN D (outN D V v) b := by
    intro h
    rcases mem_union.mp h with h | h
    · exact loopfree free (by omega) xv (mem_outN.mp h).2
    · exact digonfree free hq xv bv xb (mem_outN.mp h).2
  have core2 : insert x (outN D (outN D V v) x ∪ outN D (outN D V v) b) ⊆ ball D V x 2 := by
    intro w hw
    rcases mem_insert.mp hw with e | hw
    · rw [e]
      exact self_mem_ball xv
    rcases mem_union.mp hw with h | h
    · obtain ⟨wX, xw⟩ := mem_outN.mp h
      exact ball_mono_radius (show 1 ≤ 2 by omega) (ball_of_adj (Xsub wX) xw)
    · obtain ⟨wX, bw⟩ := mem_outN.mp h
      exact mem_ball.mpr ⟨Xsub wX, 2, le_rfl, .step bv xb (.step (Xsub wX) bw (.refl w))⟩
  have core1 : insert x (outN D (outN D V v) x ∪ outN D (outN D V v) b) ⊆ ball D V v 1 := by
    intro w hw
    rcases mem_insert.mp hw with e | hw
    · rw [e]
      exact X1 hx
    rcases mem_union.mp hw with h | h
    · exact X1 (mem_outN.mp h).1
    · exact X1 (mem_outN.mp h).1
  have far := far_in_two (k := 1) full
  simp only [Nat.reduceAdd] at far
  have dis2 : Disjoint (ball D V v 3 \ ball D V v 1)
      (insert x (outN D (outN D V v) x ∪ outN D (outN D V v) b)) :=
    disjoint_left.mpr (fun w hw hc => (mem_sdiff.mp hw).2 (core1 hc))
  have incl : ball D V v 1 ⊆ ball D V v 3 := ball_mono_radius (by omega)
  have total := card_le_card (union_subset far core2)
  rw [card_union_of_disjoint dis2, card_insert_of_notMem xA, card_union_of_disjoint dis,
    card_sdiff_of_subset incl] at total
  have mono := card_le_card incl
  omega

/-- **Low root.** Assembly: at a low root `|ball v 2| + t = 2r + 1` with `r = q t + 1`, the bank
is exactly `t`-out inside and complete to the second shell, the third ball has at least
`3r + 2 - 2t` labels, and every bank row has `2r + 2 ≤ |ball x 2|`. -/
theorem low_root {t r v : ℕ} (none : NoHost q t) (law : QBoundaryInRegular q t)
    (free : QFree D V q) (hq : 3 ≤ q) (ht : 1 ≤ t) (tq : t ≤ q)
    (exact : ∀ y ∈ V, (outN D V y).card = r) (order : r = q*t + 1) (vv : v ∈ V)
    (low : (ball D V v 2).card + t = 2*r + 1) :
    (∀ x ∈ outN D V v, (outN D (outN D V v) x).card = t ∧
      ball D V v 2 \ ball D V v 1 ⊆ outN D V x) ∧
    3*r + 2 ≤ (ball D V v 3).card + 2*t ∧
    ∀ x ∈ outN D V v, 2*r + 2 ≤ (ball D V x 2).card := by
  have shell := low_shell free (by omega) exact vv low
  have bank := low_bank free (by omega) exact law order vv shell
  have qt : 1*t ≤ q*t := Nat.mul_le_mul_right t (by omega)
  have third := bank_third none free hq (fun y hy => (exact y hy).ge) vv
    (fun x hx => (bank x hx).2) (card_pos.mp (by omega)) (by omega)
  have i23 : ball D V v 2 ⊆ ball D V v 3 := ball_mono_radius (by omega)
  rw [card_sdiff_of_subset i23] at third
  have m23 := card_le_card i23
  have one := ReachLedger.ball_one free (by omega) vv
  rw [exact v vv] at one
  refine ⟨bank, by omega, fun x hx => ?_⟩
  have hi := bank_high free (by omega) tq ht vv (fun y hy => (bank y hy).1) (bank x hx).2 hx
  omega

/-! ### Banks meet only when equal -/

theorem row_eq {t r u x : ℕ} (exact : ∀ y ∈ V, (outN D V y).card = r)
    (shell : (ball D V u 2 \ ball D V u 1).card + t = r)
    (inner : (outN D (outN D V u) x).card = t)
    (full : ball D V u 2 \ ball D V u 1 ⊆ outN D V x) (xv : x ∈ V) :
    outN D V x = outN D (outN D V u) x ∪ (ball D V u 2 \ ball D V u 1) := by
  classical
  have dis : Disjoint (outN D (outN D V u) x) (ball D V u 2 \ ball D V u 1) := by
    refine disjoint_left.mpr (fun y hy hs => (mem_sdiff.mp hs).2 ?_)
    have h := (mem_outN.mp hy).1
    exact ball_of_adj (mem_outN.mp h).1 (mem_outN.mp h).2
  have sub : outN D (outN D V u) x ∪ (ball D V u 2 \ ball D V u 1) ⊆ outN D V x :=
    union_subset (fun y hy => mem_outN.mpr ⟨outN_subset (mem_outN.mp hy).1, (mem_outN.mp hy).2⟩)
      full
  have c := card_union_of_disjoint dis
  exact (eq_of_subset_of_card_le sub (by rw [c, exact x xv]; omega)).symm

/-- **Banks meet only when equal.** Two low banks that share a row share their second shells (a
label of one shell missing from the other would close a digon through the two complete
rectangles), hence the row's inner heads, so their intersection keeps the quota `t` inside and
must be the whole boundary-order fragment. -/
theorem bank_meet {t r u w : ℕ} (none : NoHost q t) (free : QFree D V q) (hq : 2 ≤ q)
    (exact : ∀ y ∈ V, (outN D V y).card = r) (order : r = q*t + 1)
    (su : (ball D V u 2 \ ball D V u 1).card + t = r)
    (sw : (ball D V w 2 \ ball D V w 1).card + t = r)
    (iu : ∀ x ∈ outN D V u, (outN D (outN D V u) x).card = t)
    (iw : ∀ x ∈ outN D V w, (outN D (outN D V w) x).card = t)
    (fu : ∀ x ∈ outN D V u, ball D V u 2 \ ball D V u 1 ⊆ outN D V x)
    (fw : ∀ x ∈ outN D V w, ball D V w 2 \ ball D V w 1 ⊆ outN D V x)
    (uv : u ∈ V) (wv : w ∈ V)
    (meet : (outN D V u ∩ outN D V w).Nonempty) : outN D V u = outN D V w := by
  classical
  obtain ⟨x, hx⟩ := meet
  obtain ⟨xu, xw⟩ := mem_inter.mp hx
  have xv : x ∈ V := outN_subset xu
  have eu := row_eq exact su (iu x xu) (fu x xu) xv
  have ew := row_eq exact sw (iw x xw) (fw x xw) xv
  have Y : ball D V u 2 \ ball D V u 1 = ball D V w 2 \ ball D V w 1 := by
    by_contra ne
    have n1 : ¬ (ball D V u 2 \ ball D V u 1 ⊆ ball D V w 2 \ ball D V w 1) := fun h =>
      ne (eq_of_subset_of_card_le h (by omega))
    have n2 : ¬ (ball D V w 2 \ ball D V w 1 ⊆ ball D V u 2 \ ball D V u 1) := fun h =>
      ne (eq_of_subset_of_card_le h (by omega)).symm
    obtain ⟨a, aYu, aYw⟩ := not_subset.mp n1
    obtain ⟨b, bYw, bYu⟩ := not_subset.mp n2
    have aX : a ∈ outN D (outN D V w) x := by
      have h : a ∈ outN D V x := fu x xu aYu
      rw [ew] at h
      rcases mem_union.mp h with h | h
      · exact h
      · exact absurd h aYw
    have bX : b ∈ outN D (outN D V u) x := by
      have h : b ∈ outN D V x := fw x xw bYw
      rw [eu] at h
      rcases mem_union.mp h with h | h
      · exact h
      · exact absurd h bYu
    have aw := (mem_outN.mp aX).1
    have bu := (mem_outN.mp bX).1
    have ab := (mem_outN.mp (fw a aw bYw)).2
    have ba := (mem_outN.mp (fu b bu aYu)).2
    exact digonfree free hq (outN_subset aw) (outN_subset bu) ab ba
  have closed : ∀ y ∈ outN D V u ∩ outN D V w,
      t ≤ (outN D (outN D V u ∩ outN D V w) y).card := by
    intro y hy
    obtain ⟨yu, yw⟩ := mem_inter.mp hy
    have yv : y ∈ V := outN_subset yu
    have ew' := row_eq exact sw (iw y yw) (fw y yw) yv
    have sub : outN D (outN D V u) y ⊆ outN D (outN D V u ∩ outN D V w) y := by
      intro z hz
      obtain ⟨zu, yz⟩ := mem_outN.mp hz
      have z1 : z ∈ outN D V y := mem_outN.mpr ⟨outN_subset zu, yz⟩
      rw [ew'] at z1
      rcases mem_union.mp z1 with h | h
      · exact mem_outN.mpr ⟨mem_inter.mpr ⟨zu, (mem_outN.mp h).1⟩, yz⟩
      · exfalso
        rw [← Y] at h
        exact (mem_sdiff.mp h).2 (ball_of_adj (outN_subset zu) (mem_outN.mp zu).2)
    have le := card_le_card sub
    rw [iu y yu] at le
    exact le
  have big : q*t + 1 ≤ (outN D V u ∩ outN D V w).card := by
    by_contra! small
    exact fragment_exit none free (inter_subset_left.trans outN_subset) ⟨x, hx⟩ (by omega) closed
  have cu := exact u uv
  have cw := exact w wv
  have e1 := eq_of_subset_of_card_le
    (inter_subset_left : outN D V u ∩ outN D V w ⊆ outN D V u) (by omega)
  have e2 := eq_of_subset_of_card_le
    (inter_subset_right : outN D V u ∩ outN D V w ⊆ outN D V w) (by omega)
  exact e1.symm.trans e2

/-- Two distinct rows with the same first layer do not reach each other within two. -/
theorem same_layer_far {u w : ℕ} (free : QFree D V q) (hq : 2 ≤ q) (wv : w ∈ V) (ne : u ≠ w)
    (same : outN D V u = outN D V w) : w ∉ ball D V u 2 := by
  intro h
  obtain ⟨_, j, hj, walk⟩ := mem_ball.mp h
  match j, hj, walk with
  | 0, _, walk =>
    cases walk
    exact ne rfl
  | 1, _, walk =>
    cases walk with
    | step _ arc rest =>
      cases rest
      have hw : w ∈ outN D V u := mem_outN.mpr ⟨wv, arc⟩
      rw [same] at hw
      exact loopfree free (by omega) wv (mem_outN.mp hw).2
  | 2, _, walk =>
    cases walk with
    | step av ua rest =>
      cases rest with
      | step _ aw rest' =>
        cases rest'
        have ha := mem_outN.mpr ⟨av, ua⟩
        rw [same] at ha
        exact digonfree free hq av wv aw (mem_outN.mp ha).2
  | n + 3, hj, _ => omega

/-- **Layer classes.** All but one root of each first-layer class is paid for by the gaps. -/
theorem layer_roots {R : Finset ℕ} (free : QFree D V q) (hq : 2 ≤ q) (rv : R ⊆ V) :
    2 * R.card ≤ 2 * (R.image (outN D V)).card + ∑ v ∈ R, (gap D V 2 2 v).card := by
  classical
  have maps : ∀ v ∈ R, outN D V v ∈ R.image (outN D V) := fun v hv => mem_image_of_mem _ hv
  have each : ∀ Y ∈ R.image (outN D V),
      2 * (R.filter (fun v => outN D V v = Y)).card ≤
        2 + ∑ v ∈ R.filter (fun v => outN D V v = Y), (gap D V 2 2 v).card := by
    intro Y _
    have law := gap_clique (D := D) (V := V) (i := 2) (j := 2)
      (R := R.filter (fun v => outN D V v = Y))
      (fun v hv w hw ne => mem_gap.mpr ⟨rv (mem_filter.mp hw).1,
        same_layer_far free hq (rv (mem_filter.mp hw).1) (Ne.symm ne)
          ((mem_filter.mp hv).2.trans (mem_filter.mp hw).2.symm),
        same_layer_far free hq (rv (mem_filter.mp hv).1) ne
          ((mem_filter.mp hw).2.trans (mem_filter.mp hv).2.symm)⟩)
    by_cases two : 2 ≤ (R.filter (fun v => outN D V v = Y)).card
    · have step := Nat.mul_le_mul_right ((R.filter (fun v => outN D V v = Y)).card - 1) two
      omega
    · omega
  have total := sum_le_sum each
  rw [← mul_sum, ← card_eq_sum_card_image, sum_add_distrib, sum_const, smul_eq_mul,
    sum_fiberwise_of_maps_to maps] at total
  omega

/-! ### The budget of the banks -/

theorem bank_union_card {r : ℕ} {L : Finset ℕ}
    (rows : ∀ u ∈ L, (outN D V u).card = r)
    (meet : ∀ u ∈ L, ∀ w ∈ L, (outN D V u ∩ outN D V w).Nonempty →
      outN D V u = outN D V w) :
    (L.biUnion (outN D V)).card = r * (L.image (outN D V)).card := by
  classical
  have e : L.biUnion (outN D V) = (L.image (outN D V)).biUnion id := by
    rw [image_biUnion]
    rfl
  have each : ∀ X ∈ L.image (outN D V), (id X).card = r := by
    intro X hX
    obtain ⟨u, hu, rfl⟩ := mem_image.mp hX
    exact rows u hu
  rw [e, card_biUnion, sum_congr rfl each, sum_const, smul_eq_mul, Nat.mul_comm]
  intro X hX Y hY ne
  obtain ⟨u, hu, rfl⟩ := mem_image.mp hX
  obtain ⟨w, hw, rfl⟩ := mem_image.mp hY
  show Disjoint (outN D V u) (outN D V w)
  by_contra h
  exact ne (meet u hu w hw (not_disjoint_iff_nonempty_inter.mp h))

/-- **Bank excess.** The banks of the roots `L` hold `r k` labels at excess at least `c`, the
roots themselves sit at the floor, and the rest sit at least one above it. -/
theorem bank_excess {a c r : ℕ} {L : Finset ℕ} (lv : L ⊆ V)
    (rows : ∀ u ∈ L, (outN D V u).card = r)
    (meet : ∀ u ∈ L, ∀ w ∈ L, (outN D V u ∩ outN D V w).Nonempty →
      outN D V u = outN D V w)
    (low : ∀ u ∈ L, (ball D V u 2).card = a) (hc : 1 ≤ c)
    (high : ∀ u ∈ L, ∀ x ∈ outN D V u, a + c ≤ (ball D V x 2).card)
    (rest : ∀ v ∈ V, v ∉ L → a + 1 ≤ (ball D V v 2).card) :
    c * (r * (L.image (outN D V)).card) + ((V \ L.biUnion (outN D V)) \ L).card
        + ∑ v ∈ (V \ L.biUnion (outN D V)) \ L, ((ball D V v 2).card - (a + 1))
      ≤ ∑ v ∈ V, ((ball D V v 2).card - a) ∧
    r * (L.image (outN D V)).card + L.card + ((V \ L.biUnion (outN D V)) \ L).card
      = V.card := by
  classical
  have ucard := bank_union_card rows meet
  have usub : L.biUnion (outN D V) ⊆ V := biUnion_subset.mpr (fun _ _ => outN_subset)
  have lsub : L ⊆ V \ L.biUnion (outN D V) := by
    intro u hu
    refine mem_sdiff.mpr ⟨lv hu, fun h => ?_⟩
    obtain ⟨w, hw, uw⟩ := mem_biUnion.mp h
    have h1 := high w hw u uw
    have h2 := low u hu
    omega
  have s1 := sum_sdiff (f := fun v => (ball D V v 2).card - a) usub
  have s2 := sum_sdiff (f := fun v => (ball D V v 2).card - a) lsub
  have onU : c * (L.biUnion (outN D V)).card ≤
      ∑ v ∈ L.biUnion (outN D V), ((ball D V v 2).card - a) := by
    have h := sum_le_sum (s := L.biUnion (outN D V)) (f := fun _ => c)
      (g := fun v => (ball D V v 2).card - a) (fun v hv => by
        obtain ⟨w, hw, vw⟩ := mem_biUnion.mp hv
        have := high w hw v vw
        omega)
    rw [sum_const, smul_eq_mul, Nat.mul_comm] at h
    exact h
  have onR : ∑ v ∈ (V \ L.biUnion (outN D V)) \ L, ((ball D V v 2).card - a)
      = ∑ v ∈ (V \ L.biUnion (outN D V)) \ L, (((ball D V v 2).card - (a + 1)) + 1) := by
    refine sum_congr rfl (fun v hv => ?_)
    have vV : v ∈ V := (mem_sdiff.mp (mem_sdiff.mp hv).1).1
    have := rest v vV (mem_sdiff.mp hv).2
    omega
  rw [sum_add_distrib, sum_const, smul_eq_mul, Nat.mul_one] at onR
  have c1 := card_sdiff_of_subset usub
  have c2 := card_sdiff_of_subset lsub
  have m1 := card_le_card usub
  have m2 := card_le_card lsub
  rw [ucard] at onU c1 m1
  constructor
  · omega
  · omega

/-- **Bank budget.** The radius-two ledger with floor `a`, roots `L` at the floor, banks of
excess `c`: `2 c r k + 2|R| + 2 (excess of R over a + 1) + 2|L| + 2 a n ≤ n (n + 1) + 2k`, where
`R` is everything outside the banks and the roots. -/
theorem bank_budget {a c r : ℕ} {L : Finset ℕ} (free : QFree D V q) (hq : 4 ≤ q) (lv : L ⊆ V)
    (rows : ∀ u ∈ L, (outN D V u).card = r)
    (meet : ∀ u ∈ L, ∀ w ∈ L, (outN D V u ∩ outN D V w).Nonempty →
      outN D V u = outN D V w)
    (low : ∀ u ∈ L, (ball D V u 2).card = a) (hc : 1 ≤ c)
    (high : ∀ u ∈ L, ∀ x ∈ outN D V u, a + c ≤ (ball D V x 2).card)
    (rest : ∀ v ∈ V, v ∉ L → a + 1 ≤ (ball D V v 2).card) :
    2 * (c * (r * (L.image (outN D V)).card)) + 2 * ((V \ L.biUnion (outN D V)) \ L).card
        + 2 * ∑ v ∈ (V \ L.biUnion (outN D V)) \ L, ((ball D V v 2).card - (a + 1))
        + 2 * L.card + V.card * (a + a)
      ≤ V.card * (V.card + 1) + 2 * (L.image (outN D V)).card ∧
    r * (L.image (outN D V)).card + L.card + ((V \ L.biUnion (outN D V)) \ L).card
      = V.card := by
  classical
  obtain ⟨ex, cards⟩ := bank_excess lv rows meet low hc high rest
  have floor : ∀ v ∈ V, a ≤ (ball D V v 2).card := fun v hv => by
    by_cases h : v ∈ L
    · exact (low v h).ge
    · have := rest v hv h
      omega
  have spend := ReachLedger.budget free (by omega : 2 + 2 ≤ q) floor floor
  have roots := layer_roots free (by omega) lv
  have gs : ∑ v ∈ L, (gap D V 2 2 v).card ≤ ∑ v ∈ V, (gap D V 2 2 v).card :=
    sum_le_sum_of_subset lv
  exact ⟨by omega, cards⟩

/-- **Bank ledger.** The bank budget at the low roots `L` (`|ball u 2| = a`, `a + t = 2r + 1`):
`2 t r k + 2n + 2 (excess of the rest) + 2 a n ≤ n (n + 1) + 2k`. -/
theorem bank_ledger {t r a : ℕ} {L : Finset ℕ} (none : NoHost q t)
    (law : QBoundaryInRegular q t) (free : QFree D V q) (hq : 4 ≤ q) (ht : 1 ≤ t) (tq : t ≤ q)
    (exact : ∀ y ∈ V, (outN D V y).card = r) (order : r = q*t + 1) (value : a + t = 2*r + 1)
    (floor : ∀ v ∈ V, a ≤ (ball D V v 2).card)
    (memL : ∀ u, u ∈ L ↔ u ∈ V ∧ (ball D V u 2).card = a) :
    2 * (t * r * (L.image (outN D V)).card) + 2 * V.card
        + 2 * ∑ v ∈ (V \ L.biUnion (outN D V)) \ L, ((ball D V v 2).card - (a + 1))
        + V.card * (a + a)
      ≤ V.card * (V.card + 1) + 2 * (L.image (outN D V)).card := by
  classical
  have lv : L ⊆ V := fun u hu => ((memL u).mp hu).1
  have info := fun u (hu : u ∈ L) =>
    low_root none law free (by omega) ht tq exact order ((memL u).mp hu).1
      (by have := ((memL u).mp hu).2; omega)
  have shell := fun u (hu : u ∈ L) =>
    low_shell (t := t) free (by omega) exact ((memL u).mp hu).1
      (by have := ((memL u).mp hu).2; omega)
  obtain ⟨main, cards⟩ := bank_budget (c := t + 1) free hq lv
    (fun u hu => exact u (lv hu))
    (fun u hu w hw m => bank_meet none free (by omega) exact order (shell u hu) (shell w hw)
      (fun x hx => ((info u hu).1 x hx).1) (fun x hx => ((info w hw).1 x hx).1)
      (fun x hx => ((info u hu).1 x hx).2) (fun x hx => ((info w hw).1 x hx).2)
      (lv hu) (lv hw) m)
    (fun u hu => ((memL u).mp hu).2) (by omega)
    (fun u hu x hx => by have := (info u hu).2.2 x hx; omega)
    (fun v hv hn => by
      have := floor v hv
      have : (ball D V v 2).card ≠ a := fun e => hn ((memL v).mpr ⟨hv, e⟩)
      omega)
  have e1 : (t + 1) * (r * (L.image (outN D V)).card)
      = t * r * (L.image (outN D V)).card + r * (L.image (outN D V)).card := by ring
  omega

/-- **Floor by budget.** If `n (n + 1) + 2 < 2 t r + 2n + 2 a n` (`a + t = 2r + 1`), no row sits at
the low value: `a + 1 ≤ |ball v 2|` everywhere. -/
theorem floor_by_budget {t r n a : ℕ} (none : NoHost q t) (above : NoHost q (t+1))
    (law : QBoundaryInRegular q t) (free : QFree D V q) (hq : 4 ≤ q) (ht : 1 ≤ t) (tq : t ≤ q)
    (exact : ∀ y ∈ V, (outN D V y).card = r) (size : V.card = n) (order : r = q*t + 1)
    (value : a + t = 2*r + 1) (arith : n*(n+1) + 2 < 2*(t*r) + 2*n + n*(a+a)) :
    ∀ v ∈ V, a + 1 ≤ (ball D V v 2).card := by
  classical
  have room : r ≤ q*(t+1) := by rw [Nat.mul_succ]; omega
  have floor : ∀ v ∈ V, a ≤ (ball D V v 2).card := fun v vv => by
    have := layer_floor above free (by omega) exact (by omega) room vv
    omega
  intro v vv
  by_contra! lt
  have main := bank_ledger (L := V.filter (fun v => (ball D V v 2).card = a)) none law free hq
    ht tq exact order value floor (fun u => mem_filter)
  have kpos : 1 ≤ ((V.filter (fun v => (ball D V v 2).card = a)).image (outN D V)).card :=
    card_pos.mpr ⟨_, mem_image_of_mem _ (mem_filter.mpr ⟨vv, by have := floor v vv; omega⟩)⟩
  have tr : 1 ≤ t*r := Nat.mul_pos (by omega) (by omega)
  have key := prod_ge tr kpos
  rw [size] at main
  omega

/-- **Bank regime.** Every `q`-free graph of minimum outdegree `r = q t + 1` on `n` labels closes
when `n + 1 < 2 (2r + 2 - t)` and `n (n+1) + 2 < 2 t r + 2n + 2 (2r + 1 - t) n`, given the quotas
`t`, `t + 1` and in-regularity at `(q, t)`. -/
theorem bank_regime {t r n : ℕ} (free : QFree D V q)
    (degree : ∀ v ∈ V, r ≤ (outN D V v).card) (size : V.card = n)
    (none : NoHost q t) (above : NoHost q (t+1)) (law : QBoundaryInRegular q t)
    (hq : 4 ≤ q) (ht : 1 ≤ t) (tq : t ≤ q) (order : r = q*t + 1)
    (arith : n*(n+1) + 2 < 2*(t*r) + 2*n + n*((2*r+1-t)+(2*r+1-t)))
    (small : n + 1 < 2*(2*r+2-t)) (hn : 1 ≤ n) : False := by
  obtain ⟨F, sub, eq⟩ := exists_outEq degree
  have freeF := qfree_sub sub free
  have fl := floor_by_budget (a := 2*r+1-t) none above law freeF hq ht tq eq size order
    (by omega) arith
  have ne : V.Nonempty := card_pos.mp (by omega)
  have two := card_ge_of_two_balls freeF (by omega : 2 + 2 ≤ q) fl fl ne
  omega

/-- **Tied regime.** With floor `b` everywhere and `n + 1 ≤ 2b`, the budget forces every row to the
floor; the tight-head rule at `b` then has no head to point to. -/
theorem tied_regime {b n : ℕ} (free : QFree D V q) (hq : 4 ≤ q) (size : V.card = n)
    (live : V.Nonempty) (floor : ∀ v ∈ V, b ≤ (ball D V v 2).card)
    (tight : TightHead D V b) (arith : n + 1 ≤ 2*b) : False := by
  have spend := ReachLedger.budget free (by omega : 2 + 2 ≤ q) floor floor
  have m := Nat.mul_le_mul_left n arith
  rw [size] at spend
  have zero : ∑ v ∈ V, ((ball D V v 2).card - b) = 0 := by
    have : n * (b + b) = n * (2 * b) := by ring
    omega
  have each := (sum_eq_zero_iff (s := V)).mp zero
  obtain ⟨v, vv⟩ := live
  obtain ⟨w, hw, ne⟩ := tight v vv (by have := each v vv; have := floor v vv; omega)
  have wv := (mem_outN.mp hw).1
  have := each w wv
  have := floor w wv
  omega

/-! ### One bank, paid by the indegrees of the labels above the tight value -/

/-- A label of the outer shells of a complete bank row never returns to the row nor to any of its
parents (cutoff at least four). -/
theorem far_no_return {v x y u : ℕ} (free : QFree D V q) (hq : 4 ≤ q)
    (full : ball D V v 2 \ ball D V v 1 ⊆ outN D V x) (xv : x ∈ V) (uv : u ∈ V)
    (hy : y ∈ ball D V v 3 \ ball D V v 1) (ux : D u x = true) :
    ¬ D y x = true ∧ ¬ D y u = true := by
  have far := far_in_two (k := 1) full
  simp only [Nat.reduceAdd] at far
  have y2 : y ∈ ball D V x 2 := far hy
  exact ⟨no_back_arc free xv y2 (by omega), no_back_arc free uv (ball_succ xv ux y2) (by omega)⟩

/-- **Bank cut.** All low roots `L` share the bank of `v`. The tight labels of the outer shells of
`v` head neither the bank nor a low root, so under the tight-head rule each heads a label of the
rest `R` above the tight value `a + 1`: the outer shells, less those labels, are paid by their
indegrees. -/
theorem bank_cut {a v : ℕ} {L : Finset ℕ} (free : QFree D V q) (hq : 4 ≤ q) (vv : v ∈ V)
    (full : ∀ x ∈ outN D V v, ball D V v 2 \ ball D V v 1 ⊆ outN D V x)
    (same : ∀ u ∈ L, outN D V u = outN D V v) (live : (outN D V v).Nonempty)
    (rest : ∀ y ∈ V, y ∉ L → a + 1 ≤ (ball D V y 2).card)
    (tight : TightHead D V (a + 1)) :
    ((ball D V v 3 \ ball D V v 1) \ ((V \ L.biUnion (outN D V)) \ L).filter
        (fun w => a + 2 ≤ (ball D V w 2).card)).card
      ≤ ∑ h ∈ ((V \ L.biUnion (outN D V)) \ L).filter (fun w => a + 2 ≤ (ball D V w 2).card),
          (inN D V h).card := by
  classical
  obtain ⟨x0, hx0⟩ := live
  have x0v : x0 ∈ V := outN_subset hx0
  have vx0 := (mem_outN.mp hx0).2
  have away : ∀ y ∈ ball D V v 3 \ ball D V v 1, ∀ w ∈ outN D V y,
      w ∈ (V \ L.biUnion (outN D V)) \ L := by
    intro y hy w hw
    obtain ⟨wv, yw⟩ := mem_outN.mp hw
    have notX : w ∉ outN D V v := fun h =>
      (far_no_return free hq (full w h) (outN_subset h) vv hy (mem_outN.mp h).2).1 yw
    refine mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨wv, fun h => ?_⟩, fun h => ?_⟩
    · obtain ⟨u, hu, uw⟩ := mem_biUnion.mp h
      rw [same u hu] at uw
      exact notX uw
    · have wx0 : D w x0 = true := by
        have h' : x0 ∈ outN D V w := by rw [same w h]; exact hx0
        exact (mem_outN.mp h').2
      exact (far_no_return free hq (full x0 hx0) x0v wv hy wx0).2 yw
  have tv : (ball D V v 3 \ ball D V v 1) \ ((V \ L.biUnion (outN D V)) \ L).filter
      (fun w => a + 2 ≤ (ball D V w 2).card) ⊆ V :=
    fun y hy => ball_subset (mem_sdiff.mp (mem_sdiff.mp hy).1).1
  have sup := supplier (D := D) (V := V)
    (((V \ L.biUnion (outN D V)) \ L).filter (fun w => a + 2 ≤ (ball D V w 2).card)) _ tv
  have empty : (((ball D V v 3 \ ball D V v 1) \ ((V \ L.biUnion (outN D V)) \ L).filter
      (fun w => a + 2 ≤ (ball D V w 2).card)).filter (fun y => outN D
        (((V \ L.biUnion (outN D V)) \ L).filter (fun w => a + 2 ≤ (ball D V w 2).card)) y = ∅))
      = ∅ := by
    refine filter_eq_empty_iff.mpr (fun y hy => ?_)
    obtain ⟨yfar, yH⟩ := mem_sdiff.mp hy
    have yv : y ∈ V := ball_subset (mem_sdiff.mp yfar).1
    have yR : y ∈ (V \ L.biUnion (outN D V)) \ L := by
      refine mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨yv, fun h => ?_⟩, fun h => ?_⟩
      · obtain ⟨u, hu, uy⟩ := mem_biUnion.mp h
        rw [same u hu] at uy
        exact (mem_sdiff.mp yfar).2 (ball_of_adj yv (mem_outN.mp uy).2)
      · have yx0 : D y x0 = true := by
          have h' : x0 ∈ outN D V y := by rw [same y h]; exact hx0
          exact (mem_outN.mp h').2
        exact (far_no_return free hq (full x0 hx0) x0v vv yfar vx0).1 yx0
    have yt : (ball D V y 2).card = a + 1 := by
      have h1 := rest y yv (mem_sdiff.mp yR).2
      have h2 : ¬ a + 2 ≤ (ball D V y 2).card := fun h => yH (mem_filter.mpr ⟨yR, h⟩)
      omega
    obtain ⟨w, hw, wne⟩ := tight y yv yt
    have wR := away y yfar w hw
    have wv := (mem_outN.mp hw).1
    have h1 := rest w wv (mem_sdiff.mp wR).2
    intro e
    have hwH : w ∈ outN D (((V \ L.biUnion (outN D V)) \ L).filter
        (fun w => a + 2 ≤ (ball D V w 2).card)) y :=
      mem_outN.mpr ⟨mem_filter.mpr ⟨wR, by omega⟩, (mem_outN.mp hw).2⟩
    rw [e] at hwH
    simp at hwH
  rw [empty, card_empty, zero_add] at sup
  exact sup

/-- **Floor by cut.** One bank at most (`n (n+1) + 4 < 4 t r + 2n + 2 a n`), a slack `σ` on the
rest (`n (n+1) + 2 < 2 t r + 2n + 2 a n + 2 (σ + 1)`), a quota `s` reaching the high labels
(`a + 1 + σ ≤ q s + 1`), and the cut `σ (n + s - (a + r + 2)) + 2t < 2r + 1`: with the tight-head
rule at `a + 1`, no row sits at the low value `a`. -/
theorem floor_by_cut {t r n a s σ : ℕ} (none : NoHost q t) (above : NoHost q (t+1))
    (law : QBoundaryInRegular q t) (quota : NoHost q s) (free : QFree D V q) (hq : 4 ≤ q)
    (ht : 1 ≤ t) (tq : t ≤ q) (exact : ∀ y ∈ V, (outN D V y).card = r) (size : V.card = n)
    (order : r = q*t + 1) (value : a + t = 2*r + 1) (tight : TightHead D V (a + 1))
    (two_banks : n*(n+1) + 4 < 4*(t*r) + 2*n + n*(a+a))
    (slack : n*(n+1) + 2 < 2*(t*r) + 2*n + n*(a+a) + 2*(σ+1))
    (reach : a + 1 + σ ≤ q*s + 1) (hs : a + r + 2 ≤ n + s)
    (cut : σ*(n + s - (a + r + 2)) + 2*t < 2*r + 1) :
    ∀ v ∈ V, a + 1 ≤ (ball D V v 2).card := by
  classical
  have room : r ≤ q*(t+1) := by rw [Nat.mul_succ]; omega
  have floor : ∀ v ∈ V, a ≤ (ball D V v 2).card := fun v vv => by
    have := layer_floor above free (by omega) exact (by omega) room vv
    omega
  intro v vv
  by_contra! lt
  have vlow : (ball D V v 2).card = a := by have := floor v vv; omega
  obtain ⟨L, hL⟩ : ∃ L, L = V.filter (fun v => (ball D V v 2).card = a) := ⟨_, rfl⟩
  have memL : ∀ u, u ∈ L ↔ u ∈ V ∧ (ball D V u 2).card = a := fun u => by rw [hL, mem_filter]
  have main := bank_ledger none law free hq ht tq exact order value floor memL
  rw [size] at main
  have vL : v ∈ L := (memL v).mpr ⟨vv, vlow⟩
  have kpos : 1 ≤ (L.image (outN D V)).card := card_pos.mpr ⟨_, mem_image_of_mem _ vL⟩
  have tr : 1 ≤ t*r := Nat.mul_pos (by omega) (by omega)
  have kone : (L.image (outN D V)).card = 1 := by
    by_contra! two
    have := prod_ge_two tr (show 2 ≤ (L.image (outN D V)).card by omega)
    omega
  rw [kone, Nat.mul_one] at main
  have same : ∀ u ∈ L, outN D V u = outN D V v := fun u hu =>
    card_le_one.mp kone.le _ (mem_image_of_mem _ hu) _ (mem_image_of_mem _ vL)
  have info := low_root none law free (by omega) ht tq exact order vv (by omega)
  have rest : ∀ y ∈ V, y ∉ L → a + 1 ≤ (ball D V y 2).card := fun y hy hn => by
    have := floor y hy
    have : (ball D V y 2).card ≠ a := fun e => hn ((memL y).mpr ⟨hy, e⟩)
    omega
  have cutb := bank_cut free hq vv (fun x hx => (info.1 x hx).2) same
    (card_pos.mp (by rw [exact v vv]; omega)) rest tight
  have sR : ∑ w ∈ (V \ L.biUnion (outN D V)) \ L, ((ball D V w 2).card - (a + 1)) ≤ σ := by
    omega
  have hH : ∀ h ∈ ((V \ L.biUnion (outN D V)) \ L).filter (fun w => a + 2 ≤ (ball D V w 2).card),
      (inN D V h).card + 1 ≤ n + s - (a + r + 2) := by
    intro h hh
    obtain ⟨hR, big⟩ := mem_filter.mp hh
    have hv : h ∈ V := (mem_sdiff.mp (mem_sdiff.mp hR).1).1
    have single := single_le_sum (f := fun w => (ball D V w 2).card - (a + 1))
      (fun _ _ => Nat.zero_le _) hR
    have grow := ReachLedger.ball_growth (k := 2) quota free (fun y hy => (exact y hy).ge)
      (by omega) hv (by omega) (by omega) (by omega)
    simp only [Nat.reduceAdd] at grow
    have cap := parent_cap (i := 3) free (by omega) hv
    omega
  have Hcard : (((V \ L.biUnion (outN D V)) \ L).filter
      (fun w => a + 2 ≤ (ball D V w 2).card)).card ≤ σ := by
    have sub := sum_le_sum_of_subset (f := fun w => (ball D V w 2).card - (a + 1))
      (filter_subset (fun w => a + 2 ≤ (ball D V w 2).card) ((V \ L.biUnion (outN D V)) \ L))
    have each : (((V \ L.biUnion (outN D V)) \ L).filter
        (fun w => a + 2 ≤ (ball D V w 2).card)).card ≤
        ∑ w ∈ ((V \ L.biUnion (outN D V)) \ L).filter (fun w => a + 2 ≤ (ball D V w 2).card),
          ((ball D V w 2).card - (a + 1)) := by
      rw [card_eq_sum_ones]
      exact sum_le_sum (fun w hw => by have := (mem_filter.mp hw).2; omega)
    omega
  have sumH := sum_le_sum hH
  simp only [sum_add_distrib, sum_const, smul_eq_mul, Nat.mul_one] at sumH
  have Hmul := Nat.mul_le_mul_right (n + s - (a + r + 2)) Hcard
  have i13 : ball D V v 1 ⊆ ball D V v 3 := ball_mono_radius (by omega)
  have farc := card_sdiff_of_subset i13
  have m13 := card_le_card i13
  have one := ReachLedger.ball_one free (by omega) vv
  rw [exact v vv] at one
  have split := card_le_card_sdiff_add_card (s := ball D V v 3 \ ball D V v 1)
    (t := ((V \ L.biUnion (outN D V)) \ L).filter (fun w => a + 2 ≤ (ball D V w 2).card))
  have f3 := info.2.1
  omega

/-! ### Shared heads -/

/-- **Common head.** A row and one of its heads whose rows together exceed the row's punctured
two-ball share a head. -/
theorem common_head {x j : ℕ} (free : QFree D V q) (hq : 2 ≤ q) (xv : x ∈ V) (jv : j ∈ V)
    (xj : D x j = true)
    (small : (ball D V x 2).card ≤ (outN D V x).card + (outN D V j).card) :
    ∃ y ∈ outN D V x, y ∈ outN D V j := by
  have sub : outN D V x ∪ outN D V j ⊆ (ball D V x 2).erase x := by
    intro y hy
    rcases mem_union.mp hy with h | h
    · obtain ⟨yv, xy⟩ := mem_outN.mp h
      refine mem_erase.mpr ⟨fun e => ?_, ball_mono_radius (show 1 ≤ 2 by omega) (ball_of_adj yv xy)⟩
      rw [e] at xy
      exact loopfree free (by omega) xv xy
    · obtain ⟨yv, jy⟩ := mem_outN.mp h
      refine mem_erase.mpr ⟨fun e => ?_, mem_ball.mpr ⟨yv, 2, le_rfl, .step jv xj (.step yv jy (.refl y))⟩⟩
      rw [e] at jy
      exact digonfree free hq xv jv xj jy
  have le := card_le_card sub
  have xin := card_erase_of_mem (self_mem_ball (D := D) (k := 2) xv)
  have ui := card_union_add_card_inter (outN D V x) (outN D V j)
  have bpos : 0 < (ball D V x 2).card := card_pos.mpr ⟨x, self_mem_ball xv⟩
  have pos : 0 < (outN D V x ∩ outN D V j).card := by omega
  obtain ⟨y, hy⟩ := card_pos.mp pos
  exact ⟨y, (mem_inter.mp hy).1, (mem_inter.mp hy).2⟩

/-- **Shared-head rule.** If every head of `x` outside `H` heads some label of `H`, then for each
head `j ∈ H` of `x` (with the common-head count) there is a `k ∈ H`, `k ≠ j`, that both `x` and `j`
reach within two. -/
theorem shared_head {x j : ℕ} {H : Finset ℕ} (free : QFree D V q) (hq : 2 ≤ q) (xv : x ∈ V)
    (jv : j ∈ V) (xj : D x j = true)
    (small : (ball D V x 2).card ≤ (outN D V x).card + (outN D V j).card)
    (supply : ∀ y ∈ outN D V x, y ∉ H → ∃ k ∈ H, D y k = true) (hv : H ⊆ V) :
    ∃ k ∈ H, k ≠ j ∧ k ∈ ball D V x 2 ∧ k ∈ ball D V j 2 := by
  obtain ⟨y, yx, yj⟩ := common_head free hq xv jv xj small
  obtain ⟨yv, xy⟩ := mem_outN.mp yx
  obtain ⟨_, jy⟩ := mem_outN.mp yj
  by_cases yH : y ∈ H
  · refine ⟨y, yH, fun e => ?_, ball_mono_radius (show 1 ≤ 2 by omega) (ball_of_adj yv xy),
      ball_mono_radius (show 1 ≤ 2 by omega) (ball_of_adj yv jy)⟩
    rw [e] at jy
    exact loopfree free (by omega) jv jy
  · obtain ⟨k, kH, yk⟩ := supply y yx yH
    have kv := hv kH
    refine ⟨k, kH, fun e => ?_, mem_ball.mpr ⟨kv, 2, le_rfl, .step yv xy (.step kv yk (.refl k))⟩,
      mem_ball.mpr ⟨kv, 2, le_rfl, .step yv jy (.step kv yk (.refl k))⟩⟩
    rw [e] at yk
    exact digonfree free hq jv yv jy yk

/-- **Two highs.** Such a row sees at least two labels of `H` within two. -/
theorem two_highs {x j : ℕ} {H : Finset ℕ} (free : QFree D V q) (hq : 2 ≤ q) (xv : x ∈ V)
    (jv : j ∈ V) (xj : D x j = true) (jH : j ∈ H)
    (small : (ball D V x 2).card ≤ (outN D V x).card + (outN D V j).card)
    (supply : ∀ y ∈ outN D V x, y ∉ H → ∃ k ∈ H, D y k = true) (hv : H ⊆ V) :
    2 ≤ (ball D V x 2 ∩ H).card := by
  classical
  obtain ⟨k, kH, kj, kx, _⟩ := shared_head free hq xv jv xj small supply hv
  have jx : j ∈ ball D V x 2 := ball_mono_radius (show 1 ≤ 2 by omega) (ball_of_adj jv xj)
  have sub : ({j, k} : Finset ℕ) ⊆ ball D V x 2 ∩ H := by
    intro z hz
    rcases mem_insert.mp hz with e | e
    · rw [e]
      exact mem_inter.mpr ⟨jx, jH⟩
    · rw [mem_singleton.mp e]
      exact mem_inter.mpr ⟨kx, kH⟩
  have le := card_le_card sub
  rwa [card_pair (Ne.symm kj)] at le

/-- Two distinct labels cannot reach each other within two each (cutoff at least four). -/
theorem mutual_far {a b : ℕ} (free : QFree D V q) (hq : 4 ≤ q) (av : a ∈ V) (ne : a ≠ b)
    (ab : b ∈ ball D V a 2) (ba : a ∈ ball D V b 2) : False := by
  have e := ball_inter_reverse (i := 2) (j := 2) free (by omega) av
  have h : b ∈ ball D V a 2 ∩ reverseBall D V a 2 :=
    mem_inter.mpr ⟨ab, mem_reverse.mpr ⟨ball_subset ab, ba⟩⟩
  rw [e] at h
  exact ne (mem_singleton.mp h).symm

/-- **One direct high.** A row that sees at most two labels of `H` within two heads at most one:
two direct highs would each reach the other within two. -/
theorem one_direct {x : ℕ} {H : Finset ℕ} (free : QFree D V q) (hq : 4 ≤ q) (hv : H ⊆ V)
    (xv : x ∈ V)
    (small : ∀ j ∈ outN D H x, (ball D V x 2).card ≤ (outN D V x).card + (outN D V j).card)
    (supply : ∀ y ∈ outN D V x, y ∉ H → ∃ k ∈ H, D y k = true)
    (few : (ball D V x 2 ∩ H).card ≤ 2) : (outN D H x).card ≤ 1 := by
  classical
  by_contra! many
  obtain ⟨a, ha, b, hb, ne⟩ := one_lt_card.mp many
  obtain ⟨aH, xa⟩ := mem_outN.mp ha
  obtain ⟨bH, xb⟩ := mem_outN.mp hb
  have a2 : a ∈ ball D V x 2 := ball_mono_radius (show 1 ≤ 2 by omega) (ball_of_adj (hv aH) xa)
  have b2 : b ∈ ball D V x 2 := ball_mono_radius (show 1 ≤ 2 by omega) (ball_of_adj (hv bH) xb)
  have comp : ∀ k ∈ H, k ∈ ball D V x 2 → k = a ∨ k = b := by
    intro k kH k2
    by_contra! h
    have three : 2 < (ball D V x 2 ∩ H).card := two_lt_card_iff.mpr
      ⟨a, b, k, mem_inter.mpr ⟨a2, aH⟩, mem_inter.mpr ⟨b2, bH⟩, mem_inter.mpr ⟨k2, kH⟩,
        ne, Ne.symm h.1, Ne.symm h.2⟩
    omega
  obtain ⟨k, kH, ka, k2, ka2⟩ := shared_head free (by omega) xv (hv aH) xa (small a ha) supply hv
  obtain ⟨k', kH', kb, k2', kb2⟩ := shared_head free (by omega) xv (hv bH) xb (small b hb) supply hv
  have kb' : k = b := (comp k kH k2).resolve_left ka
  have ka' : k' = a := (comp k' kH' k2').resolve_right kb
  rw [kb'] at ka2
  rw [ka'] at kb2
  exact mutual_far free hq (hv aH) ne ka2 kb2

/-! ### High columns -/

theorem swap_count (A B : Finset ℕ) :
    ∑ j ∈ A, (B.filter (fun x => j ∈ ball D V x 2)).card =
      ∑ x ∈ B, (A.filter (fun j => j ∈ ball D V x 2)).card := by
  simp only [card_eq_sum_ones, sum_filter]
  exact sum_comm

theorem ball_inter_eq {x : ℕ} (H : Finset ℕ) :
    ball D V x 2 ∩ H = H.filter (fun j => j ∈ ball D V x 2) := by
  ext j
  simp only [mem_inter, mem_filter]
  tauto

/-- **Column count.** The high columns: what reaches `H` within two, the gaps of `H` and the
two-balls of `H` fill `|H| (n + 1)` exactly. -/
theorem column_count {H : Finset ℕ} (free : QFree D V q) (hq : 4 ≤ q) (hv : H ⊆ V) :
    ∑ x ∈ V, (ball D V x 2 ∩ H).card + ∑ j ∈ H, (gap D V 2 2 j).card
      + ∑ j ∈ H, (ball D V j 2).card = H.card * (V.card + 1) := by
  classical
  have rows : ∑ j ∈ H, ((ball D V j 2).card + (reverseBall D V j 2).card + (gap D V 2 2 j).card)
      = ∑ _j ∈ H, (V.card + 1) := sum_congr rfl (fun j hj => row_ledger free (by omega) (hv hj))
  rw [sum_add_distrib, sum_add_distrib, sum_const, smul_eq_mul] at rows
  have swap : ∑ j ∈ H, (reverseBall D V j 2).card = ∑ x ∈ V, (ball D V x 2 ∩ H).card := by
    rw [sum_congr rfl (fun x _ => congrArg card (ball_inter_eq (D := D) (V := V) (x := x) H))]
    exact swap_count H V
  omega

/-- **Inner count.** Inside `H` every unordered pair is one reach or two gaps. -/
theorem inner_count {H : Finset ℕ} (free : QFree D V q) (hq : 4 ≤ q) (hv : H ⊆ V) :
    2 * ∑ j ∈ H, (ball D V j 2 ∩ H).card + ∑ j ∈ H, (gap D V 2 2 j ∩ H).card
      = H.card * (H.card + 1) := by
  classical
  have row : ∀ j ∈ H, (ball D V j 2 ∩ H).card + (reverseBall D V j 2 ∩ H).card
      + (gap D V 2 2 j ∩ H).card = H.card + 1 := by
    intro j hj
    have jv := hv hj
    have e := ball_inter_reverse (i := 2) (j := 2) free (by omega) jv
    have both := card_union_add_card_inter (ball D V j 2 ∩ H) (reverseBall D V j 2 ∩ H)
    have inter : (ball D V j 2 ∩ H) ∩ (reverseBall D V j 2 ∩ H)
        = (ball D V j 2 ∩ reverseBall D V j 2) ∩ H := by
      ext w
      simp only [mem_inter]
      tauto
    rw [inter, e, singleton_inter_of_mem hj, card_singleton] at both
    have gapEq : gap D V 2 2 j ∩ H = H \ ((ball D V j 2 ∩ H) ∪ (reverseBall D V j 2 ∩ H)) := by
      ext w
      have hw := @hv w
      simp only [gap, mem_inter, mem_sdiff, mem_union]
      tauto
    have sub : (ball D V j 2 ∩ H) ∪ (reverseBall D V j 2 ∩ H) ⊆ H :=
      union_subset inter_subset_right inter_subset_right
    rw [gapEq, card_sdiff_of_subset sub]
    have := card_le_card sub
    omega
  have total := sum_congr rfl row
  rw [sum_add_distrib, sum_add_distrib, sum_const, smul_eq_mul] at total
  have swap : ∑ j ∈ H, (reverseBall D V j 2 ∩ H).card = ∑ j ∈ H, (ball D V j 2 ∩ H).card := by
    have e1 : ∀ j ∈ H, (reverseBall D V j 2 ∩ H).card
        = (H.filter (fun x => j ∈ ball D V x 2)).card := by
      intro j _
      congr 1
      ext x
      have hx := @hv x
      simp only [reverseBall, mem_inter, mem_filter]
      tauto
    rw [sum_congr rfl e1, swap_count H H]
    exact sum_congr rfl (fun x _ => (congrArg card (ball_inter_eq (D := D) (V := V) (x := x) H)).symm)
  omega

/-- **High columns.** Incoming high columns and the outgoing high rows paid together:
`2 C_T + 2 B + h (h + 1) ≤ 2 h (n + 1)` with `C_T` the high reaches of the rows outside `H` and
`B` the two-balls of `H`. -/
theorem high_columns {H : Finset ℕ} (free : QFree D V q) (hq : 4 ≤ q) (hv : H ⊆ V) :
    2 * ∑ x ∈ V \ H, (ball D V x 2 ∩ H).card + 2 * ∑ j ∈ H, (ball D V j 2).card
      + H.card * (H.card + 1) ≤ 2 * (H.card * (V.card + 1)) := by
  have col := column_count free hq hv
  have inn := inner_count free hq hv
  have split := sum_sdiff (f := fun x => (ball D V x 2 ∩ H).card) hv
  have gle : ∑ j ∈ H, (gap D V 2 2 j ∩ H).card ≤ ∑ j ∈ H, (gap D V 2 2 j).card :=
    sum_le_sum (fun j _ => card_le_card inter_subset_left)
  omega

/-- Under the tight-head rule every non-high row heads a high row. -/
theorem head_supply {b : ℕ} {H : Finset ℕ} (floor : ∀ v ∈ V, b ≤ (ball D V v 2).card)
    (tight : TightHead D V b) (memH : ∀ v, v ∈ H ↔ v ∈ V ∧ b + 1 ≤ (ball D V v 2).card) :
    ∀ y ∈ V, y ∉ H → ∃ k ∈ H, D y k = true := by
  intro y yv yH
  have yb : (ball D V y 2).card = b := by
    have := floor y yv
    have : ¬ b + 1 ≤ (ball D V y 2).card := fun h => yH ((memH y).mpr ⟨yv, h⟩)
    omega
  obtain ⟨k, hk, kne⟩ := tight y yv yb
  obtain ⟨kv, yk⟩ := mem_outN.mp hk
  exact ⟨k, (memH k).mpr ⟨kv, by have := floor k kv; omega⟩, yk⟩

/-- Every non-high row sees at least two highs within two (`b ≤ 2r`). -/
theorem tight_sees_two {b r : ℕ} {H : Finset ℕ} (free : QFree D V q) (hq : 2 ≤ q)
    (exact : ∀ y ∈ V, (outN D V y).card = r) (wide : b ≤ r + r)
    (floor : ∀ v ∈ V, b ≤ (ball D V v 2).card) (tight : TightHead D V b)
    (memH : ∀ v, v ∈ H ↔ v ∈ V ∧ b + 1 ≤ (ball D V v 2).card) :
    ∀ x ∈ V \ H, 2 ≤ (ball D V x 2 ∩ H).card := by
  intro x hx
  obtain ⟨xv, xH⟩ := mem_sdiff.mp hx
  have hv : H ⊆ V := fun v h => ((memH v).mp h).1
  obtain ⟨j, hj, jH⟩ := head_supply floor tight memH x xv xH
  have jv := hv hj
  have xb : (ball D V x 2).card = b := by
    have := floor x xv
    have : ¬ b + 1 ≤ (ball D V x 2).card := fun h => xH ((memH x).mpr ⟨xv, h⟩)
    omega
  exact two_highs free hq xv jv jH hj (by rw [xb, exact x xv, exact j jv]; exact wide)
    (fun y hy yH => head_supply floor tight memH y (mem_outN.mp hy).1 yH) hv

/-- **High count.** With floor `b`, the tight-head rule, `H` the rows above `b`, `E` the excess of
the high reaches of the tight rows over two and `S` the excess of `H` over `b + 1`:
`2 (2 (n - h) + E) + 2 (h (b + 1) + S) + h (h + 1) ≤ 2 h (n + 1)`. -/
theorem high_count {b r : ℕ} {H : Finset ℕ} (free : QFree D V q) (hq : 4 ≤ q)
    (exact : ∀ y ∈ V, (outN D V y).card = r) (wide : b ≤ r + r)
    (floor : ∀ v ∈ V, b ≤ (ball D V v 2).card) (tight : TightHead D V b)
    (memH : ∀ v, v ∈ H ↔ v ∈ V ∧ b + 1 ≤ (ball D V v 2).card) :
    2 * ((V \ H).card * 2 + ∑ x ∈ V \ H, ((ball D V x 2 ∩ H).card - 2))
      + 2 * (H.card * (b + 1) + ∑ j ∈ H, ((ball D V j 2).card - (b + 1)))
      + H.card * (H.card + 1) ≤ 2 * (H.card * (V.card + 1)) := by
  have hv : H ⊆ V := fun v h => ((memH v).mp h).1
  have two := tight_sees_two free (by omega) exact wide floor tight memH
  have cols := high_columns free hq hv
  have eT := sum_excess (c := fun x => (ball D V x 2 ∩ H).card) (a := 2) two
  have eH := sum_excess (c := fun x => (ball D V x 2).card) (a := b + 1)
    (S := H) (fun j hj => ((memH j).mp hj).2)
  omega

/-- **Excess zero.** If every tight row sees at most two highs, each heads at most one, so the tight
rows keep `r - 1` heads among themselves: impossible on at most `q (r - 1)` labels. -/
theorem excess_zero {b r : ℕ} {H : Finset ℕ} (lower : NoHost q (r-1)) (free : QFree D V q)
    (hq : 4 ≤ q) (exact : ∀ y ∈ V, (outN D V y).card = r) (wide : b ≤ r + r)
    (floor : ∀ v ∈ V, b ≤ (ball D V v 2).card) (tight : TightHead D V b)
    (memH : ∀ v, v ∈ H ↔ v ∈ V ∧ b + 1 ≤ (ball D V v 2).card)
    (live : (V \ H).Nonempty) (small : (V \ H).card ≤ q*(r-1))
    (few : ∀ x ∈ V \ H, (ball D V x 2 ∩ H).card ≤ 2) : False := by
  classical
  have hv : H ⊆ V := fun v h => ((memH v).mp h).1
  refine fragment_exit lower free sdiff_subset live small (fun x hx => ?_)
  obtain ⟨xv, xH⟩ := mem_sdiff.mp hx
  have xb : (ball D V x 2).card = b := by
    have := floor x xv
    have : ¬ b + 1 ≤ (ball D V x 2).card := fun h => xH ((memH x).mpr ⟨xv, h⟩)
    omega
  have od := one_direct free hq hv xv
    (fun j hj => by rw [xb, exact x xv, exact j (hv (mem_outN.mp hj).1)]; exact wide)
    (fun y hy yH => head_supply floor tight memH y (mem_outN.mp hy).1 yH) (few x hx)
  have split := card_outN_union (D := D) (show Disjoint (V \ H) H from sdiff_disjoint) x
  rw [sdiff_union_of_subset hv] at split
  have := exact x xv
  omega

/-- **Excess one.** If the tight rows' high reaches exceed two by at most one in total, the tight
rows keep `r - 1` heads among themselves except for at most one row short by one (a unit graph),
or one row that no tight row heads: impossible below `q (r - 1)` labels (`r ≥ 4`). -/
theorem excess_one {b r : ℕ} {H : Finset ℕ} (lower : NoHost q (r-1)) (free : QFree D V q)
    (hq : 4 ≤ q) (hr : 4 ≤ r) (exact : ∀ y ∈ V, (outN D V y).card = r) (wide : b ≤ r + r)
    (floor : ∀ v ∈ V, b ≤ (ball D V v 2).card) (tight : TightHead D V b)
    (memH : ∀ v, v ∈ H ↔ v ∈ V ∧ b + 1 ≤ (ball D V v 2).card)
    (live : (V \ H).Nonempty) (small : (V \ H).card < q*(r-1))
    (excess : ∑ x ∈ V \ H, ((ball D V x 2 ∩ H).card - 2) ≤ 1) : False := by
  classical
  have hv : H ⊆ V := fun v h => ((memH v).mp h).1
  have two := tight_sees_two free (by omega) exact wide floor tight memH
  by_cases allTwo : ∀ x ∈ V \ H, (ball D V x 2 ∩ H).card ≤ 2
  · exact excess_zero lower free hq exact wide floor tight memH live small.le allTwo
  obtain ⟨x0, hx0, big⟩ : ∃ x0 ∈ V \ H, 2 < (ball D V x0 2 ∩ H).card := by
    by_contra! h
    exact allTwo h
  obtain ⟨x0v, x0H⟩ := mem_sdiff.mp hx0
  have others : ∀ u ∈ V \ H, u ≠ x0 → (ball D V u 2 ∩ H).card ≤ 2 := by
    intro u hu ne
    have sub : ({x0, u} : Finset ℕ) ⊆ V \ H := insert_subset hx0 (singleton_subset_iff.mpr hu)
    have le := sum_le_sum_of_subset (f := fun x => (ball D V x 2 ∩ H).card - 2) sub
    rw [sum_pair (Ne.symm ne)] at le
    omega
  have three : (ball D V x0 2 ∩ H).card ≤ 3 := by
    have le := single_le_sum (f := fun x => (ball D V x 2 ∩ H).card - 2)
      (fun _ _ => Nat.zero_le _) hx0
    omega
  have tb : ∀ x ∈ V \ H, (ball D V x 2).card = b := by
    intro x hx
    obtain ⟨xv, xH⟩ := mem_sdiff.mp hx
    have := floor x xv
    have : ¬ b + 1 ≤ (ball D V x 2).card := fun h => xH ((memH x).mpr ⟨xv, h⟩)
    omega
  have keep : ∀ x ∈ V \ H, (outN D V x).card = (outN D (V \ H) x).card + (outN D H x).card := by
    intro x _
    have split := card_outN_union (D := D) (show Disjoint (V \ H) H from sdiff_disjoint) x
    rwa [sdiff_union_of_subset hv] at split
  have rest : ∀ u ∈ V \ H, u ≠ x0 → r - 1 ≤ (outN D (V \ H) u).card := by
    intro u hu ne
    have uv := (mem_sdiff.mp hu).1
    have od := one_direct free hq hv uv
      (fun j hj => by rw [tb u hu, exact u uv, exact j (hv (mem_outN.mp hj).1)]; exact wide)
      (fun y hy yH => head_supply floor tight memH y (mem_outN.mp hy).1 yH) (others u hu ne)
    have := keep u hu
    have := exact u uv
    omega
  have dsub : outN D H x0 ⊆ ball D V x0 2 ∩ H := fun a ha =>
    mem_inter.mpr ⟨ball_mono_radius (show 1 ≤ 2 by omega)
      (ball_of_adj (hv (mem_outN.mp ha).1) (mem_outN.mp ha).2), (mem_outN.mp ha).1⟩
  have dle := card_le_card dsub
  have k0 := keep x0 hx0
  have e0 := exact x0 x0v
  by_cases d1 : (outN D H x0).card ≤ 1
  · refine fragment_exit lower free sdiff_subset live small.le (fun u hu => ?_)
    by_cases ne : u = x0
    · rw [ne]
      omega
    · exact rest u hu ne
  by_cases d2 : (outN D H x0).card = 2
  · have unit := ShortfallBridge.total_unit (t := r - 1) (D := D) hx0 (by omega)
      (fun u hu ne => rest u hu ne)
    have := ShortfallBridge.unit_card lower (by omega) (by omega) (free.mono_set sdiff_subset) unit
    omega
  -- three direct highs: no tight row heads `x0`
  have d3 : (outN D H x0).card = 3 := by omega
  have deq : outN D H x0 = ball D V x0 2 ∩ H := eq_of_subset_of_card_le dsub (by omega)
  have orphan : ∀ u ∈ V \ H, ¬ D u x0 = true := by
    intro u hu ux
    have uv := (mem_sdiff.mp hu).1
    by_cases ne : u = x0
    · rw [ne] at ux
      exact loopfree free (by omega) x0v ux
    have sub : outN D H x0 ⊆ ball D V u 2 ∩ H := fun a ha =>
      mem_inter.mpr ⟨mem_ball.mpr ⟨hv (mem_outN.mp ha).1, 2, le_rfl,
        .step x0v ux (.step (hv (mem_outN.mp ha).1) (mem_outN.mp ha).2 (.refl a))⟩,
        (mem_outN.mp ha).1⟩
    have := card_le_card sub
    have := others u hu ne
    omega
  have T1 : (V \ H).erase x0 ⊆ V := (erase_subset _ _).trans sdiff_subset
  obtain ⟨z, hz⟩ : (outN D (V \ H) x0).Nonempty := card_pos.mp (by omega)
  obtain ⟨zT, x0z⟩ := mem_outN.mp hz
  have zne : z ≠ x0 := fun e => by rw [e] at x0z; exact loopfree free (by omega) x0v x0z
  refine fragment_exit lower free T1 ⟨z, mem_erase.mpr ⟨zne, zT⟩⟩
    (by have := card_erase_of_mem hx0; omega) (fun u hu => ?_)
  obtain ⟨une, uT⟩ := mem_erase.mp hu
  have sub : outN D (V \ H) u ⊆ outN D ((V \ H).erase x0) u := by
    intro w hw
    obtain ⟨wT, uw⟩ := mem_outN.mp hw
    refine mem_outN.mpr ⟨mem_erase.mpr ⟨fun e => ?_, wT⟩, uw⟩
    rw [e] at uw
    exact orphan u uT uw
  exact (rest u uT une).trans (card_le_card sub)

/-! ### Supports -/

/-- **Support count.** A set `C` whose rows keep at most one head inside, and whose outside labels
have at most `m` parents in `C`, satisfies `|C| (r - 1) ≤ m (n - |C|)`. -/
theorem support_count {r m : ℕ} {C : Finset ℕ} (cv : C ⊆ V)
    (degree : ∀ x ∈ C, r ≤ (outN D V x).card) (inner : ∀ x ∈ C, (outN D C x).card ≤ 1)
    (parents : ∀ y ∈ V \ C, (inN D C y).card ≤ m) :
    C.card * (r - 1) ≤ m * (V.card - C.card) := by
  classical
  have swap : ∑ x ∈ C, (outN D (V \ C) x).card = ∑ y ∈ V \ C, (inN D C y).card := by
    simp only [outN, BR45.inN, card_eq_sum_ones, sum_filter]
    exact sum_comm
  have low : ∀ x ∈ C, r - 1 ≤ (outN D (V \ C) x).card := by
    intro x hx
    have split := card_outN_union (D := D) (show Disjoint C (V \ C) from disjoint_sdiff) x
    rw [union_sdiff_of_subset cv] at split
    have := degree x hx
    have := inner x hx
    omega
  have s1 := sum_le_sum low
  have s2 := sum_le_sum parents
  rw [sum_const, smul_eq_mul] at s1 s2
  rw [card_sdiff_of_subset cv] at s2
  rw [Nat.mul_comm m]
  omega

/-- **Support regime.** No such `C` exists when `m (n - c) < c (r - 1)`. -/
theorem support_regime {r m n : ℕ} {C : Finset ℕ} (size : V.card = n) (cv : C ⊆ V)
    (degree : ∀ x ∈ C, r ≤ (outN D V x).card) (inner : ∀ x ∈ C, (outN D C x).card ≤ 1)
    (parents : ∀ y ∈ V \ C, (inN D C y).card ≤ m)
    (arith : m * (n - C.card) < C.card * (r - 1)) : False := by
  have := support_count cv degree inner parents
  rw [size] at this
  omega

#print axioms prod_ge
#print axioms layer_floor
#print axioms low_bank
#print axioms bank_third
#print axioms bank_high
#print axioms low_root
#print axioms bank_meet
#print axioms same_layer_far
#print axioms layer_roots
#print axioms bank_excess
#print axioms bank_budget
#print axioms bank_ledger
#print axioms floor_by_budget
#print axioms bank_regime
#print axioms tied_regime
#print axioms bank_cut
#print axioms floor_by_cut
#print axioms common_head
#print axioms shared_head
#print axioms two_highs
#print axioms one_direct
#print axioms column_count
#print axioms inner_count
#print axioms high_columns
#print axioms tight_sees_two
#print axioms high_count
#print axioms excess_zero
#print axioms excess_one
#print axioms support_count
#print axioms support_regime
end LeanCH.BR.SharedHeadSuppliers
