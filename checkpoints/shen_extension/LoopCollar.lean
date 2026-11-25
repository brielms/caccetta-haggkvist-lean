import checkpoints.shen_extension.DipCost
import checkpoints.shen_extension.RigidHost

/-!
# The loop collar

The floors of the reach climb treat every root alone. This file records the facts that tie a
thin root to its neighbours. All of it is generic in `q` and `r`.

* `ball_grow`: in a `q`-free digraph of minimum out-degree at least one the `j`-ball has at
  least `j + 1` labels, for `j ≤ q`.
* `loop_unique_head`: a `q`-free digraph on exactly `q + 1` labels with minimum out-degree at
  least one has out-degree exactly one everywhere: it is a single loop of length `q + 1`.
* `collar`: a root `u` with exactly `q + 1` heads `X`, each of out-degree at least `r`, and at
  most `r - 1` labels at distance two. Then `X` is such a loop, every head has out-degree
  exactly `r`, the second layer has exactly `r - 1` labels, and every head points to all of it.
* `collar_inherit`: every label within `j + 1` of the root is the root, a head, or within `j` of
  each head. `collar_ball`: so `|B (j+1) u| + j ≤ |B j x| + q + 1` for each head `x`, `j ≤ q`:
  the heads are no thinner than the root one step later, plus their own walk round the loop.
* `twins_far`: two roots with the same nonempty set of heads are not within `q` of each other,
  in either direction.
-/

set_option linter.style.longLine false
namespace LeanCH.BR.LoopCollar
open Finset BRq2 BRq3 FifthStripAll RigidHost
open DotTwoPassShellTransport (layer)
open ShapeClimbRoot (mem_layer)
open MixedRadiusCompletion (Order)

variable {D : CH.Digraph} {q : ℕ}

/-- Linear growth at minimum out-degree one. -/
theorem ball_grow {S : Finset ℕ} {x : ℕ} (free : QFree D S q)
    (deg : ∀ v ∈ S, 1 ≤ (outN D S v).card) (hx : x ∈ S) :
    ∀ j, j ≤ q → j + 1 ≤ (ball D S x j).card := by
  intro j
  induction j with
  | zero => exact fun _ => card_pos.mpr ⟨x, self_mem_ball hx⟩
  | succ j ih =>
    intro hj
    have prev := ih (by omega)
    have sub : ball D S x j ⊆ ball D S x (j+1) := ball_mono_radius (Nat.le_succ j)
    by_contra small
    have eq : ball D S x j = ball D S x (j+1) :=
      eq_of_subset_of_card_le sub (by omega)
    have closed : ∀ v ∈ ball D S x j, outN D (ball D S x j) v = outN D S v := by
      intro v hv
      ext w
      simp only [mem_outN]
      constructor
      · exact fun h => ⟨ball_subset h.1, h.2⟩
      · exact fun h => ⟨eq ▸ ball_step hv h.1 h.2, h.2⟩
    have order := DipCost.order_one q D (ball D S x j) (free.mono_set ball_subset)
      (fun v hv => by rw [closed v hv]; exact deg v (ball_subset hv)) ⟨x, self_mem_ball hx⟩
    have le := card_le_card sub
    omega

/-- **The loop.** `q + 1` labels, no closed walk of length at most `q`, minimum out-degree at
least one: every out-degree is exactly one. -/
theorem loop_unique_head {S : Finset ℕ} (free : QFree D S q) (hq : 1 ≤ q)
    (size : S.card = q + 1) (deg : ∀ v ∈ S, 1 ≤ (outN D S v).card) :
    ∀ x ∈ S, (outN D S x).card = 1 := by
  have rev : ∀ v ∈ S, (reverseBall D S v 1).card ≤ 2 := by
    intro v hv
    have two := reverseBall_add_ball_le (v := v) (i := q - 1) (j := 1) free (by omega)
    have grow := ball_grow free deg hv (q - 1) (by omega)
    omega
  have total : ∑ v ∈ S, (ball D S v 1).card ≤ ∑ _v ∈ S, 2 := by
    rw [← sum_reverseBall_eq_sum_ball]
    exact Finset.sum_le_sum rev
  intro x hx
  by_contra ne
  have big : 2 < (ball D S x 1).card := by
    rw [ReachLedger.ball_one free hq hx]
    have := deg x hx
    omega
  have lt : ∑ _v ∈ S, 2 < ∑ v ∈ S, (ball D S v 1).card :=
    Finset.sum_lt_sum
      (fun v hv => by
        rw [ReachLedger.ball_one free hq hv]
        have := deg v hv
        omega)
      ⟨x, hx, big⟩
  omega

section collar
variable {V : Finset ℕ} {u r : ℕ}

/-- Heads of a head lie among the heads or in the second layer. -/
theorem head_keep (free : QFree D V q) (hq : 2 ≤ q) (hu : u ∈ V) :
    ∀ x ∈ outN D V u, outN D V x ⊆ outN D V u ∪ layer D V 2 u := by
  intro x hx w hw
  obtain ⟨xV, ux⟩ := mem_outN.mp hx
  obtain ⟨wV, xw⟩ := mem_outN.mp hw
  have xb : x ∈ ball D V u 1 := (mem_ball_one hu).mpr (Or.inr hx)
  have wb : w ∈ ball D V u 2 := ball_step xb wV xw
  by_cases near : w ∈ ball D V u 1
  · rcases (mem_ball_one hu).mp near with rfl | h
    · exact (digonfree free hq hu xV ux xw).elim
    · exact mem_union_left _ h
  · exact mem_union_right _ (mem_layer.mpr ⟨wb, near⟩)

/-- **The collar.** A root with exactly `q + 1` heads, each of out-degree at least `r`, and a
second layer of at most `r - 1` labels: the heads form a loop, each has out-degree exactly `r`
and points to the whole second layer, which has exactly `r - 1` labels. -/
theorem collar (free : QFree D V q) (hq : 2 ≤ q) (hu : u ∈ V)
    (heads : (outN D V u).card = q + 1) (quota : ∀ x ∈ outN D V u, r ≤ (outN D V x).card)
    (thin : (layer D V 2 u).card + 1 ≤ r) :
    (∀ x ∈ outN D V u, (outN D (outN D V u) x).card = 1) ∧
      (layer D V 2 u).card + 1 = r ∧
      ∀ x ∈ outN D V u, (outN D V x).card = r ∧ layer D V 2 u ⊆ outN D V x := by
  classical
  have keep := head_keep free hq hu
  have inner := DipCost.layer_host (X := outN D V u) (Y := layer D V 2 u) (c := 1) quota keep thin
  have one := loop_unique_head (free.mono_set outN_subset) (by omega) heads inner
  have cover : ∀ x ∈ outN D V u,
      outN D V x ⊆ outN D (outN D V u) x ∪ (layer D V 2 u ∩ outN D V x) := by
    intro x hx w hw
    rcases mem_union.mp (keep x hx hw) with h | h
    · exact mem_union_left _ (mem_outN.mpr ⟨h, (mem_outN.mp hw).2⟩)
    · exact mem_union_right _ (mem_inter.mpr ⟨h, hw⟩)
  have count : ∀ x ∈ outN D V u, r ≤ 1 + (layer D V 2 u ∩ outN D V x).card ∧
      (outN D V x).card ≤ 1 + (layer D V 2 u ∩ outN D V x).card := by
    intro x hx
    have c := (card_le_card (cover x hx)).trans (card_union_le _ _)
    rw [one x hx] at c
    exact ⟨(quota x hx).trans c, c⟩
  obtain ⟨x0, hx0⟩ : (outN D V u).Nonempty := card_pos.mp (by omega)
  have le0 := card_le_card (inter_subset_left : layer D V 2 u ∩ outN D V x0 ⊆ layer D V 2 u)
  have width : (layer D V 2 u).card + 1 = r := by
    have := (count x0 hx0).1
    omega
  refine ⟨one, width, fun x hx => ?_⟩
  have le := card_le_card (inter_subset_left : layer D V 2 u ∩ outN D V x ⊆ layer D V 2 u)
  have full : layer D V 2 u ∩ outN D V x = layer D V 2 u :=
    eq_of_subset_of_card_le inter_subset_left (by have := (count x hx).1; omega)
  refine ⟨?_, fun w hw => (mem_inter.mp (full ▸ hw)).2⟩
  have := (count x hx).2
  have := quota x hx
  omega

/-- **Inheritance.** Under the collar, everything within `j + 1` of the root is the root, a
head, or within `j` of each head. -/
theorem collar_inherit (hu : u ∈ V)
    (keep : ∀ x ∈ outN D V u, outN D V x ⊆ outN D V u ∪ layer D V 2 u)
    {x : ℕ} (hx : x ∈ outN D V u) (full : layer D V 2 u ⊆ outN D V x) :
    ∀ j, ball D V u (j+1) ⊆ insert u (outN D V u) ∪ ball D V x j := by
  classical
  have xV := (mem_outN.mp hx).1
  intro j
  induction j with
  | zero =>
    intro w hw
    rcases (mem_ball_one hu).mp hw with rfl | h
    · exact mem_union_left _ (mem_insert_self _ _)
    · exact mem_union_left _ (mem_insert_of_mem h)
  | succ j ih =>
    intro w hw
    have up : ball D V x j ⊆ ball D V x (j+1) := ball_mono_radius (Nat.le_succ j)
    by_cases old : w ∈ ball D V u (j+1)
    · rcases mem_union.mp (ih old) with h | h
      · exact mem_union_left _ h
      · exact mem_union_right _ (up h)
    · obtain ⟨y, yb, yw⟩ := ball_succ_pred hu hw old
      have wV : w ∈ V := ball_subset hw
      rcases mem_union.mp (ih yb) with h | h
      · rcases mem_insert.mp h with rfl | yX
        · exact mem_union_left _ (mem_insert_of_mem (mem_outN.mpr ⟨wV, yw⟩))
        · rcases mem_union.mp (keep y yX (mem_outN.mpr ⟨wV, yw⟩)) with a | a
          · exact mem_union_left _ (mem_insert_of_mem a)
          · have xw := (mem_outN.mp (full a)).2
            exact mem_union_right _ (ball_mono_radius (by omega : 1 ≤ j + 1)
              ((mem_ball_one xV).mpr (Or.inr (mem_outN.mpr ⟨wV, xw⟩))))
      · exact mem_union_right _ (ball_step h wV yw)

/-- **The heads are fat.** Under the collar, for each head `x` and each `j ≤ q`:
`|B (j+1) u| + j ≤ |B j x| + q + 1`. -/
theorem collar_ball (free : QFree D V q) (hq : 2 ≤ q) (hu : u ∈ V)
    (heads : (outN D V u).card = q + 1) (quota : ∀ x ∈ outN D V u, r ≤ (outN D V x).card)
    (thin : (layer D V 2 u).card + 1 ≤ r) {x : ℕ} (hx : x ∈ outN D V u) {j : ℕ} (hj : j ≤ q) :
    (ball D V u (j+1)).card + j ≤ (ball D V x j).card + q + 1 := by
  classical
  obtain ⟨one, -, all⟩ := collar free hq hu heads quota thin
  have keep := head_keep free hq hu
  have inh := collar_inherit hu keep hx (all x hx).2 j
  have xV := (mem_outN.mp hx).1
  have uX : u ∉ outN D V u := fun h => loopfree free (by omega) hu (mem_outN.mp h).2
  -- the walk round the loop stays inside the heads and inside the ball of `x`
  have loopBall : ball D (outN D V u) x j ⊆ ball D V x j ∩ outN D V u := by
    intro w hw
    obtain ⟨wX, i, hi, walk⟩ := mem_ball.mp hw
    exact mem_inter.mpr ⟨mem_ball.mpr ⟨outN_subset wX, i, hi, walk.mono outN_subset⟩, wX⟩
  have grow := ball_grow (free.mono_set (outN_subset (D := D) (W := V) (y := u)))
    (fun v hv => (one v hv).ge) hx j hj
  have inside := card_le_card loopBall
  -- split the ball of the root
  have split : ball D V u (j+1) ⊆ insert u (outN D V u) ∪ (ball D V x j \ outN D V u) := by
    intro w hw
    rcases mem_union.mp (inh hw) with h | h
    · exact mem_union_left _ h
    · by_cases wX : w ∈ outN D V u
      · exact mem_union_left _ (mem_insert_of_mem wX)
      · exact mem_union_right _ (mem_sdiff.mpr ⟨h, wX⟩)
  have c := (card_le_card split).trans (card_union_le _ _)
  rw [card_insert_of_notMem uX, heads] at c
  have parts := card_sdiff_add_card_inter (ball D V x j) (outN D V u)
  omega

/-- **Twins are far apart.** Two distinct roots with the same nonempty set of heads: neither
is within `q` of the other. -/
theorem twins_far (free : QFree D V q) {u' : ℕ} (hu' : u' ∈ V) (ne : u ≠ u')
    (same : outN D V u = outN D V u') : u' ∉ ball D V u q := by
  intro h
  obtain ⟨-, j, hj, walk⟩ := mem_ball.mp h
  cases walk with
  | refl => exact ne rfl
  | step aV ua rest =>
    rename_i a k
    have back : D u' a = true := (mem_outN.mp (same ▸ mem_outN.mpr ⟨aV, ua⟩)).2
    exact free a (k+1) (by omega) hj (rest.snoc aV back)

end collar

#print axioms ball_grow
#print axioms loop_unique_head
#print axioms collar
#print axioms collar_inherit
#print axioms collar_ball
#print axioms twins_far
end LeanCH.BR.LoopCollar
