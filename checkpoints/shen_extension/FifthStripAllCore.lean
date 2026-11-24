import checkpoints.shen_extension.FifthStripLedger

/-!
# Fifth strip, top two orders: generic core

Cutoff `q = 2s - 7`, degree `s = a + 7`. Everything here is generic in `a`, the host and
its order `n`. No number is fixed.

* `LedgerFloors`, `ledger_floors`: the universal floors at radii `a+1 … a+5` that
  `FifthStripLedger.Checks a` supplies (re-exported; the ledger keeps them private).
* `ColT`, `local_advance`: a floor advance that holds only in a host of order `n`.
  Profiles that fail both completion tests are tight at the inner radius; there the
  full columns of the prefix keep their `Lr`-balls in the complement of the prefix,
  whose size the order `n` controls. Unlike `MixedRadiusCompletion.ColumnPass` the shell
  `t` ranges over every value up to the target, and the deficit window is tested only at
  its two ends (`window_false`), so the check is cheap to decide.
-/

set_option linter.style.longLine false
namespace LeanCH.BR.FifthStripAll
open Finset BRq2 BRq3 BR45 BypassRepair ReachLedger MixedRadiusCompletion
open DotTwoPassShellTransport (shell layer holes fullColumns full_columns_bound)

/-! ### Universal floors supplied by the ledger checks -/

section Ledger
variable {a : ℕ}

theorem inner_floor (k : ℕ) (hk : k ≤ a + 1) : Floor (2*a+7) (a+7) k ((a+7)*k+1) :=
  fun _ _ free deg _ hu => ShenFifthStrip.inner_growth free deg hu k hk

theorem mid3_floor : Floor (2*a+7) (a+7) (a+3) ((a+7)*(a+3)-1) := fun _ _ free deg _ hu => by
  have := (ShenFifthStrip.middle_growth free deg hu).2.1
  omega

theorem mid4_floor : Floor (2*a+7) (a+7) (a+4) ((a+7)*(a+4)-3) := fun _ _ free deg _ hu => by
  have := (ShenFifthStrip.middle_growth free deg hu).2.2
  omega

theorem order_top3 : Order (2*a+7) (a+7) ((2*a+7)*(a+7)-3) := fun _ _ free deg ne => by
  have := ShenFifthStrip.order_to_three free deg ne
  omega

theorem low3_floor : Floor (2*a+7) (a+6) (a+3) ((a+6)*(a+3)) :=
  fun _ _ free deg _ hu => ShenThirdStrip.radius_R_growth free deg hu

theorem low4_floor : Floor (2*a+7) (a+6) (a+4) ((a+6)*(a+4)-1) := fun _ _ free deg _ hu => by
  have := ShenThirdStrip.radius_R1_growth free deg hu
  omega

theorem low_order (ha : 1 ≤ a) : Order (2*a+7) (a+6) ((2*a+7)*(a+6)+1) :=
  fun _ _ free deg ne => DotTwoPassShellTransport.order_third_strip_closed ha free deg ne

/-- The universal floors behind `FifthStripLedger.strip_regime`. -/
structure LedgerFloors (a : ℕ) : Prop where
  f2 : Floor (2*a+7) (a+7) (a+2) ((a+7)*(a+2)+1)
  f3 : Floor (2*a+7) (a+7) (a+3) ((a+7)*(a+3))
  f4 : Floor (2*a+7) (a+7) (a+4) ((a+7)*(a+4)-1)
  f5 : Floor (2*a+7) (a+7) (a+5) ((a+7)*(a+5)-3)

theorem ledger_floors (ha : 1 ≤ a) (checks : FifthStripLedger.Checks a) : LedgerFloors a := by
  obtain ⟨s1,s2,s3,s4,s5,s6,-⟩ := checks
  have e1 : (a+7)*(a+2) = (a+7)*(a+1) + (a+7) := by ring
  have e2 : (a+7)*(a+3) = (a+7)*(a+2) + (a+7) := by ring
  have e3 : (a+7)*(a+4) = (a+7)*(a+3) + (a+7) := by ring
  have e4 : (a+7)*(a+5) = (a+7)*(a+4) + (a+7) := by ring
  have e5 : (2*a+7)*(a+7) = (a+7)*(a+3) + (a+7)*(a+4) := by ring
  have p1 : 1 ≤ (a+7)*(a+1) := Nat.mul_pos (by omega) (by omega)
  have F2 : Floor (2*a+7) (a+7) (a+2) ((a+7)*(a+2)+1) :=
    advance (k := a) (inner_floor a (by omega)) (inner_floor (a+1) le_rfl) (by omega) (by omega)
      (by omega) (by omega) (low_order ha) low3_floor low4_floor le_rfl (by omega) order_top3
      mid3_floor mid4_floor s1
  have F3 : Floor (2*a+7) (a+7) (a+3) ((a+7)*(a+3)) :=
    (advance (k := a+1) (inner_floor (a+1) le_rfl) F2 (by omega) (by omega)
      (by omega) (by omega) (low_order ha) low3_floor low4_floor le_rfl (by omega) order_top3
      mid3_floor mid4_floor s2).weaken (by omega)
  have F4a : Floor (2*a+7) (a+7) (a+4) ((a+7)*(a+4)-2) :=
    (advance (k := a+2) F2 F3 (by omega) (by omega)
      (by omega) (by omega) (low_order ha) low3_floor low4_floor le_rfl (by omega) order_top3 F3
      mid4_floor s3).weaken (by omega)
  have F4 : Floor (2*a+7) (a+7) (a+4) ((a+7)*(a+4)-1) :=
    (advance (k := a+2) F2 F3 (by omega) (by omega)
      (by omega) (by omega) (low_order ha) low3_floor low4_floor le_rfl (by omega) order_top3 F3
      F4a s4).weaken (by omega)
  have ord : Order (2*a+7) (a+7) ((a+7)*(a+3) + ((a+7)*(a+4)-1) - 1) :=
    order_of_floors (by omega) F3 F4
  have F5a : Floor (2*a+7) (a+7) (a+5) ((a+7)*(a+5)-4) :=
    (advance (k := a+3) F3 F4 (by omega) (by omega)
      (by omega) (by omega) (low_order ha) low3_floor low4_floor le_rfl (by omega) ord F3 F4 s5).weaken
      (by omega)
  have F5 : Floor (2*a+7) (a+7) (a+5) ((a+7)*(a+5)-3) :=
    (advance (k := a+3) F3 F4 (by omega) (by omega)
      (by omega) (by omega) (low_order ha) low3_floor low4_floor le_rfl (by omega) ord F3 F4 s6).weaken
      (by omega)
  exact ⟨F2,F3,F4,F5⟩

/-- The universal order `qs - 1` (all degrees `s ≥ 9`). -/
theorem order_top1 (ha : 2 ≤ a) : Order (2*a+7) (a+7) ((2*a+7)*(a+7)-1) :=
  fun _ _ free deg ne => by
    have := FifthStripLedger.fifth_order free deg ne (by omega) (by omega)
    omega

end Ledger

/-! ### The local column advance -/

/-- Column test for a tight-inner profile `(x, c)` in a host of order `n`, uniformly over
every shell `t ≤ F - x` below the degree `r`. With `e = n + 1 - x - M` omissions, either the
deficit window `[L + 1 - x, c t]` is empty, or every deficit in it leaves `e + 2` full columns,
or the quadratic test fails at both ends of the part of the window that leaves fewer. -/
def ColT (x c F n p M Lr q S L r : ℕ) : Prop :=
  c + p = x ∧ Lr + (n+1-x-M) + 1 ≤ q ∧ (n+1-x-M)*(n+1-x-M+2) ≤ q ∧
    ∀ t ∈ range (F - x + 1), t < r →
      c*t + x < L + 1 ∨ (n+1-x-M) + 2 + c*t ≤ t + (L+1-x) ∨
      (1 ≤ c ∧ Pos c (x-1) S (L+1-x) ∧ Pos c (x-1) S (min (c*t) ((n+1-x-M)+1+c*t-t)))

instance (x c F n p M Lr q S L r : ℕ) : Decidable (ColT x c F n p M Lr q S L r) := by
  unfold ColT; infer_instance

/-- **Local advance.** In a host `V` of order `n`, floors `p` at radius `k` and `β` at radius
`k+1` (valid in `V`), a floor `M` at radius `Lr` (valid in `V`), a comparison supplier at degree
`d ≤ r` and the self supplier at degree `r`. If every root profile passes one of the two
completion tests or the column test, every root of `V` has `|ball (k+2)| ≥ F + 1`. -/
theorem local_advance {q r k p β F d L i j a b L' i' j' a' b' n M Lr : ℕ}
    {D : CH.Digraph} {V : Finset ℕ} (free : QFree D V q)
    (degree : ∀ v ∈ V, r ≤ (outN D V v).card) (size : V.card = n)
    (inner : ∀ v ∈ V, p ≤ (ball D V v k).card) (outer : ∀ v ∈ V, β ≤ (ball D V v (k+1)).card)
    (wide : ∀ v ∈ V, M ≤ (ball D V v Lr).card) (fit : k + 1 + Lr ≤ q)
    (hk : k + 2 ≤ q) (narrow : F < β + r)
    (hd : d ≤ r) (hij : i + j ≤ q) (order : Order q d L) (fi : Floor q d i a) (fj : Floor q d j b)
    (hij' : i' + j' ≤ q) (order' : Order q r L') (fi' : Floor q r i' a') (fj' : Floor q r j' b')
    (arith : ∀ x ∈ Icc β F, ∀ c ∈ range (x - p + 1),
      Pass x c F r d L (a + b) ∨ Pass x c F r r L' (a' + b') ∨
        ColT x c F n p M Lr q (a' + b') L' r) :
    ∀ u ∈ V, F + 1 ≤ (ball D V u (k+2)).card := by
  classical
  intro u hu
  by_contra! small
  have y0 := inner u hu
  have x0 := outer u hu
  have inc1 : ball D V u k ⊆ ball D V u (k+1) := ball_mono_radius (by omega)
  have inc2 : ball D V u (k+1) ⊆ ball D V u (k+2) := ball_mono_radius (by omega)
  have lay : (layer D V (k+1) u).card + (ball D V u k).card = (ball D V u (k+1)).card := by
    simpa only [layer, Nat.add_sub_cancel] using card_sdiff_add_card_eq_card inc1
  have sh : (shell D V (k+1) u).card + (ball D V u (k+1)).card = (ball D V u (k+2)).card :=
    card_sdiff_add_card_eq_card inc2
  have er : ((ball D V u (k+1)).erase u).card + 1 = (ball D V u (k+1)).card :=
    card_erase_add_one (self_mem_ball hu)
  have ht : (shell D V (k+1) u).card < r := by omega
  have hx : (ball D V u (k+1)).card ∈ Icc β F := mem_Icc.mpr ⟨x0, by omega⟩
  have hc : (layer D V (k+1) u).card ∈ range ((ball D V u (k+1)).card - p + 1) :=
    mem_range.mpr (by omega)
  rcases arith _ hx _ hc with pass | pass | ⟨hcp, hret, hcyc, cols⟩
  · obtain ⟨G, Q, hG, -, hL, cauchy, pairs⟩ :=
      prefix_completion hij order fi fj hd free degree hu hk ht
    exact pass_false er (by omega) hG hL cauchy pairs pass
  · obtain ⟨G, Q, hG, -, hL, cauchy, pairs⟩ :=
      prefix_completion (d := r) hij' order' fi' fj' le_rfl free degree hu hk ht
    exact pass_false er (by omega) hG hL cauchy pairs pass
  · -- the tight-inner column case
    set x := (ball D V u (k+1)).card with hxdef
    set c := (layer D V (k+1) u).card with hcdef
    set t := (shell D V (k+1) u).card with htdef
    set e := n + 1 - x - M with hedef
    have tight : (ball D V u k).card ≤ p := by omega
    have hit := hit_of_floor hu inner tight
    obtain ⟨G, Q, hG, hh, hL, cauchy, pairs⟩ :=
      prefix_completion (d := r) hij' order' fi' fj' le_rfl free degree hu hk ht
    have hG' : G ≤ c * t := by
      have : r + t - r = t := by omega
      rw [this] at hG; exact hG
    have np := not_pos cauchy pairs
    have xm : x - 1 = ((ball D V u (k+1)).erase u).card := by omega
    have gain : e + 2 + c * t ≤ t + G := by
      have tmem : t ∈ range (F - x + 1) := mem_range.mpr (by omega)
      rcases cols t tmem ht with emp | low | ⟨c1, e0, e1⟩
      · omega
      · omega
      · by_contra! bad
        rw [xm] at e0 e1
        exact window_false (G0 := L' + 1 - x) (G1 := min (c*t) (e+1+c*t-t)) (by omega)
          (le_min hG' (by omega)) c1 cauchy pairs e0 e1
    have many := full_columns_bound (D := D) (V := V) (R := k+1) (u := u)
    change t ≤ (fullColumns D V (k+1) u).card + holes D V (k+1) u at many
    have hh' : G + holes D V (k+1) u ≤ c * t := hh
    have room : V.card ≤ ((ball D V u (k+1)).erase u).card + M + e := by
      rw [size, hedef]; omega
    have ncols : e + 2 ≤ (fullColumns D V (k+1) u).card := by omega
    exact column_exit (e := e) free hu fit hit wide room ncols hret hcyc

#print axioms ledger_floors
#print axioms order_top1
#print axioms local_advance
end LeanCH.BR.FifthStripAll
