import checkpoints.shen_extension.FifthStripAllCore
import OAI.Combinatorics.SecondNeighborhood.Main

/-!
# Fifth strip: the orders `qs - 1` and `qs`

Cutoff `q = 2a + 7`, degree `s = a + 7`, generic in `a`. `Top a n` is the decidable
local-advance check in a host of order `n`. With it:

* `local_floors`: every root of a host of order `n` has `|ball (a+3)| ≥ s(a+3) + 1` and
  `|ball (a+4)| ≥ s(a+4)`.
* `below_top_false`: no host of order `qs - 1`.
* `top_rigid`: at order `qs` both balls are exact at every root.
* `reach_seymour_false`: Seymour's second-neighbourhood theorem (vendored OAI proof) on the
  relation `y ∈ ball x k` forbids `2 |ball k| ≥ |ball 2k| + 2` at every root.
* `top_false_even`: for even `a` the exact `(a+4)`-ball at the top contradicts Seymour.
-/

set_option linter.style.longLine false
namespace LeanCH.BR.FifthStripAll
open Finset BRq2 BRq3 BR45 BypassRepair ReachLedger MixedRadiusCompletion

/-- One local floor advance, tested in a host of order `n`. -/
abbrev Win (a lo hi prev n M Lr : ℕ) : Prop :=
  ∀ x ∈ Icc lo hi, ∀ c ∈ range (x - prev + 1),
    Pass x c hi (a+7) (a+6) ((2*a+7)*(a+6)+1) ((a+6)*(a+3) + ((a+6)*(a+4)-1)) ∨
    Pass x c hi (a+7) (a+7) ((2*a+7)*(a+7)-1) ((a+7)*(a+3) + ((a+7)*(a+4)-1)) ∨
    ColT x c hi n prev M Lr (2*a+7) ((a+7)*(a+3) + ((a+7)*(a+4)-1)) ((2*a+7)*(a+7)-1) (a+7)

/-- The two local advances `s(a+3) → s(a+3)+1` and `s(a+4)-1 → s(a+4)` at order `n`. -/
def Top (a n : ℕ) : Prop :=
  Win a ((a+7)*(a+2)+1) ((a+7)*(a+3)) ((a+7)*(a+1)+1) n ((a+7)*(a+5)-3) (a+5) ∧
  Win a ((a+7)*(a+3)+1) ((a+7)*(a+4)-1) ((a+7)*(a+2)+1) n ((a+7)*(a+4)-1) (a+4)

instance (a n : ℕ) : Decidable (Top a n) := by unfold Top; infer_instance

theorem local_floors {a n : ℕ} (ha : 2 ≤ a) (L : LedgerFloors a) (tc : Top a n)
    {D : CH.Digraph} {V : Finset ℕ} (free : QFree D V (2*a+7))
    (degree : ∀ v ∈ V, a+7 ≤ (outN D V v).card) (size : V.card = n) :
    ∀ u ∈ V, (a+7)*(a+3)+1 ≤ (ball D V u (a+3)).card ∧ (a+7)*(a+4) ≤ (ball D V u (a+4)).card := by
  have e2 : (a+7)*(a+3) = (a+7)*(a+2) + (a+7) := by ring
  have e3 : (a+7)*(a+4) = (a+7)*(a+3) + (a+7) := by ring
  have h3 := local_advance (k := a+1) (n := n) free degree size
    (inner_floor (a+1) le_rfl D V free degree) (L.f2 D V free degree) (L.f5 D V free degree)
    (by omega) (by omega) (by omega) (by omega : a+6 ≤ a+7) (by omega : (a+3)+(a+4) ≤ 2*a+7)
    (low_order (by omega)) low3_floor low4_floor (by omega : (a+3)+(a+4) ≤ 2*a+7)
    (order_top1 ha) L.f3 L.f4 tc.1
  have h3' : ∀ v ∈ V, (a+7)*(a+3)+1 ≤ (ball D V v (a+3)).card := fun v hv => h3 v hv
  have h4 := local_advance (k := a+2) (n := n) free degree size
    (L.f2 D V free degree) h3' (L.f4 D V free degree)
    (by omega) (by omega) (by omega) (by omega : a+6 ≤ a+7) (by omega : (a+3)+(a+4) ≤ 2*a+7)
    (low_order (by omega)) low3_floor low4_floor (by omega : (a+3)+(a+4) ≤ 2*a+7)
    (order_top1 ha) L.f3 L.f4 tc.2
  intro u hu
  refine ⟨h3' u hu, ?_⟩
  have := h4 u hu
  rw [show a+2+2 = a+4 by omega] at this
  have p : 1 ≤ (a+7)*(a+4) := Nat.mul_pos (by omega) (by omega)
  omega

/-- No host of order `qs - 1`. -/
theorem below_top_false {a : ℕ} (ha : 2 ≤ a) (L : LedgerFloors a)
    (tc : Top a ((2*a+7)*(a+7)-1))
    {D : CH.Digraph} {V : Finset ℕ} (free : QFree D V (2*a+7))
    (degree : ∀ v ∈ V, a+7 ≤ (outN D V v).card) (ne : V.Nonempty)
    (size : V.card = (2*a+7)*(a+7)-1) : False := by
  have fl := local_floors ha L tc free degree size
  have h := card_ge_of_two_balls free (by omega : (a+3)+(a+4) ≤ 2*a+7)
    (fun v hv => (fl v hv).1) (fun v hv => (fl v hv).2) ne
  have e : (2*a+7)*(a+7) = (a+7)*(a+3)+(a+7)*(a+4) := by ring
  have p : 1 ≤ (a+7)*(a+4) := Nat.mul_pos (by omega) (by omega)
  omega

/-- At order `qs` both radii are exact at every root. -/
theorem top_rigid {a : ℕ} (ha : 2 ≤ a) (L : LedgerFloors a) (tc : Top a ((2*a+7)*(a+7)))
    {D : CH.Digraph} {V : Finset ℕ} (free : QFree D V (2*a+7))
    (degree : ∀ v ∈ V, a+7 ≤ (outN D V v).card)
    (size : V.card = (2*a+7)*(a+7)) :
    ∀ v ∈ V, (ball D V v (a+3)).card = (a+7)*(a+3)+1 ∧ (ball D V v (a+4)).card = (a+7)*(a+4) := by
  have fl := local_floors ha L tc free degree size
  have e : (2*a+7)*(a+7) = (a+7)*(a+3)+(a+7)*(a+4) := by ring
  have r := two_balls_boundary_cards free (by omega : (a+3)+(a+4) ≤ 2*a+7)
    (fun v hv => (fl v hv).1) (fun v hv => (fl v hv).2) (by omega)
  exact fun v hv => ⟨(r v hv).1, (r v hv).2.1⟩

/-- **Seymour on reach graphs.** If `2k ≤ q`, every `k`-ball has at least `f` labels and
every `2k`-ball at most `A`, then `2 f ≤ A + 1`. The relation `y ∈ ball x k`, `y ≠ x`, is an
oriented graph; its second neighbours lie in `ball 2k \ ball k`. -/
theorem reach_seymour {D : CH.Digraph} {V : Finset ℕ} {q k f A : ℕ}
    (free : QFree D V q) (hk : 2*k ≤ q) (ne : V.Nonempty)
    (first : ∀ v ∈ V, f ≤ (ball D V v k).card)
    (cap : ∀ v ∈ V, (ball D V v (2*k)).card ≤ A) : 2*f ≤ A+1 := by
  classical
  let r : V → V → Prop := fun x y => x ≠ y ∧ y.1 ∈ ball D V x.1 k
  have orient : OAI.SeymourSecondNeighborhood.IsOriented r := by
    refine ⟨fun v h => h.1 rfl, ?_⟩
    intro x y hxy hyx
    obtain ⟨-, j1, hj1, w1⟩ := mem_ball.mp hxy.2
    obtain ⟨-, j2, hj2, w2⟩ := mem_ball.mp hyx.2
    have pos : 1 ≤ j1 := by
      rcases Nat.eq_zero_or_pos j1 with h | h
      · subst h; exact (hxy.1 (Subtype.ext (walk_zero w1))).elim
      · exact h
    exact free x.1 (j1+j2) (by omega) (by omega) (w1.append w2)
  have : Nonempty V := ⟨⟨ne.choose, ne.choose_spec⟩⟩
  obtain ⟨y, good⟩ := OAI.SeymourSecondNeighborhood.exists_goodVertex r orient
  unfold OAI.SeymourSecondNeighborhood.GoodVertex at good
  let emb : V ↪ ℕ := Function.Embedding.subtype _
  have hfirst : (ball D V y.1 k).erase y.1 ⊆
      (OAI.SeymourSecondNeighborhood.firstNeighbors r y).map emb := by
    intro w hw
    obtain ⟨hwy, hwb⟩ := mem_erase.mp hw
    refine mem_map.mpr ⟨⟨w, ball_subset hwb⟩, ?_, rfl⟩
    simp only [OAI.SeymourSecondNeighborhood.firstNeighbors, mem_filter, mem_univ, true_and]
    exact ⟨fun h => hwy (congrArg Subtype.val h).symm, hwb⟩
  have hsecond : (OAI.SeymourSecondNeighborhood.secondNeighbors r y).map emb ⊆
      ball D V y.1 (2*k) \ ball D V y.1 k := by
    intro w hw
    obtain ⟨z, hz, rfl⟩ := mem_map.mp hw
    simp only [OAI.SeymourSecondNeighborhood.secondNeighbors, mem_filter, mem_univ, true_and]
      at hz
    obtain ⟨hzy, hnr, u, hyu, huz⟩ := hz
    refine mem_sdiff.mpr ⟨?_, fun hb => hnr ⟨fun h => hzy h.symm, hb⟩⟩
    have := ball_trans hyu.2 huz.2
    rwa [show k + k = 2*k by omega] at this
  have c1 := card_le_card hfirst
  rw [card_map] at c1
  have c2 := card_le_card hsecond
  rw [card_map] at c2
  have hy := y.2
  have e1 := card_erase_add_one (self_mem_ball hy : y.1 ∈ ball D V y.1 k)
  have e2 := card_sdiff_add_card_eq_card
    (ball_mono_radius (D := D) (W := V) (u := y.1) (show k ≤ 2*k by omega))
  have := first y.1 hy
  have := cap y.1 hy
  omega

/-- For even `a` the top order `qs` is impossible: the `(a/2+2)`-balls are too large for
the exact `(a+4)`-balls under Seymour. -/
theorem top_false_even {a m : ℕ} (ha : 2 ≤ a) (hm : a = 2*m) (L : LedgerFloors a)
    (tc : Top a ((2*a+7)*(a+7)))
    {D : CH.Digraph} {V : Finset ℕ} (free : QFree D V (2*a+7))
    (degree : ∀ v ∈ V, a+7 ≤ (outN D V v).card) (ne : V.Nonempty)
    (size : V.card = (2*a+7)*(a+7)) : False := by
  have rig := top_rigid ha L tc free degree size
  have h := reach_seymour (k := m+2) (f := (a+7)*(m+2)+1) (A := (a+7)*(a+4)) free
    (by omega) ne
    (fun v hv => ShenFifthStrip.inner_growth free degree hv (m+2) (by omega))
    (fun v hv => by rw [show 2*(m+2) = a+4 by omega, (rig v hv).2])
  have e : (a+7)*(a+4) = 2*((a+7)*(m+2)) := by rw [hm]; ring
  omega

#print axioms local_floors
#print axioms below_top_false
#print axioms top_rigid
#print axioms reach_seymour
#print axioms top_false_even
end LeanCH.BR.FifthStripAll
