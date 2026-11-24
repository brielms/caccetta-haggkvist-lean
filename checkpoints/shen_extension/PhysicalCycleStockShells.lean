import checkpoints.shen_extension.FullRowEscape
import checkpoints.shen_extension.ShellCycleSupply

namespace LeanCH.BR.PhysicalCycleStock
open Finset BRq2 BRq3 BR45 BRsGen RetainedMixedCapacity RetainedLayerCapacity ExteriorPacking

/-- The first-layer rows in the punctured second ball are full. At the one
size where the rank-three growth table stops, their third-ball demand
excludes that fragment under the displayed strict pair-capacity inequality. -/
theorem low_third_second {D V q r v} (free : QFree D V q) (hq : 6 ≤ q)
    (reg : OutEq r D V) (root : v ∈ V) (room : r + 2 ≤ 2*q)
    (late : 2*r+3 ≤ 3*q+1) (ceiling : 3*r ≤ 4*q+1)
    (capacity : (2*r+1)*(2*r+2) < r*(2*(r+4))+(r+1)*14)
    (low : (ball D V v 3).card ≤ 3*r) :
    (ball D V v 2).card ≤ 2*r+1 := by
  by_contra! excess
  have degree x (hx : x ∈ V) := (reg x hx).ge
  by_cases seam : (ball D V v 2).card = 2*r+2
  · have incr := card_sdiff_add_card_eq_card
      (ball_mono_radius (D := D) (W := V) (u := v) (by decide : 2 ≤ 3))
    have bill := prefix_capacity (a := 1) (i := 3) (j := 3) (base := 14) (high := 2*(r+4))
      free root (by omega) (by omega) degree
      (show 2+(ball D V v 3 \ ball D V v 2).card ≤ r by omega)
      (fun _ ff rr x hx => by
        have grow := ball_growth q (by omega) _ _ ff rr x hx 3 (by omega)
        omega)
      (fun _ ff rr x hx hxfull => by
        have high := FullRowEscape.high_third ff (by omega) rr hx hxfull room
        omega)
    have first : ((ball D V v 1).erase v).card = r := by
      rw [card_erase_of_mem (self_mem_ball root), card_B1 (free.mono_bound (by omega : 4 ≤ q)) root,
        reg v root]
      omega
    have second : ((ball D V v 2).erase v).card = 2*r+1 := by
      rw [card_erase_of_mem (self_mem_ball root), seam]
      omega
    simp only [Nat.reduceAdd, first, second] at bill
    rw [show 2*r+1-r=r+1 by omega, show 2*r+1+1=2*r+2 by omega] at bill
    omega
  · have grow := PrefixDegreeGrowth.raise_floor (j := 2) (lo := 2*r+3) (target := 3*r+1)
      free root (by omega) degree (by omega) (by omega) (by omega) (by
        intro m lower upper
        by_cases fits : m ≤ 3*q+1
        · exact ⟨3, by decide, by decide, by omega, by omega⟩
        · exact ⟨4, by decide, by decide, by omega, by omega⟩)
    change 3*r+1 ≤ (ball D V v 3).card at grow
    omega

/-- A narrow first layer with two equal exterior shells supplies a literal
shortest cycle even when the first layer has one extra label. Its actual
second layer is a complete bank to the third layer. Every cycle row reaches
that whole portion of the third ball and all fourth-shell labels in time. -/
theorem narrow_cycle {D V q r u} (free : QFree D V q) (hq : 4 ≤ q) (reg : OutEq r D V)
    (hu : u ∈ V) (fit : r ≤ q+2) (hr : 4 ≤ r)
    (second : (N2 D V u).card = r-1) (third : (N3 D V u).card = r-1) :
    ∃ C ⊆ outN D V u, q+1 ≤ C.card ∧ C.card ≤ r ∧
      (∀ v ∈ C, Rooted D V v C) ∧
      (exterior D V C).card ≤ r ∧ N2 D V u ⊆ exterior D V C ∧
      (∀ v ∈ N2 D V u, Rooted D V v (N2 D V u) ∧ outN D (N3 D V u) v = N3 D V u) ∧
      ∀ v ∈ C, 4 + ((ball D V u 4).card - (ball D V u 1).card) ≤ (ball D V v 3).card := by
  classical
  let X := outN D V u
  let Y := N2 D V u
  let Z := N3 D V u
  have xv : X ⊆ V := outN_subset
  have yv : Y ⊆ V := fun _ h => N2_subV h
  have zv : Z ⊆ V := fun _ h => N3_subV h
  have xy : Disjoint X Y := disjXY
  have yz : Disjoint Y Z := disjoint_left.mpr (fun _ hm hn => (mem_N3.mp hn).2 (mem_N2.mp hm).1)
  have xcard : X.card = r := reg u hu
  have ycard : Y.card = r-1 := second
  have zcard : Z.card = r-1 := third
  have interior v (hv : v ∈ X) :=
    OneSpareGrowth.internal_positive free hq hu reg (by omega : (N2 D V u).card+1=r) hv
  obtain ⟨p, C, hp, fp, cx, ccard, internal⟩ := exists_minimal_cycle_support (by omega)
    (free.mono_set xv) interior (card_pos.mp (by omega))
  have cr v (hv : v ∈ C) : Rooted D V v C := by
    have localRoot := ShellCycleSupply.rooted_on_small_set fp (by omega)
      cx ccard.le (fun a ha => (internal a ha).ge) hv
    exact ⟨cx.trans xv, hv, localRoot.one, localRoot.reaches⟩
  have size := card_le_card cx
  have firstCover : ∀ x ∈ X, ∀ y ∈ Y, ∃ k, 0 < k ∧ k ≤ 2 ∧ Walk D V x y k :=
    BankReachTransfer.reaches_bank (k := 1) free (by omega) xv yv xy
      (fun v hv => by rw [reg v hv]; omega)
      (fun v hv => by
        rw [← outN_X_eq (free.mono_bound hq) hu hv, reg v (xv hv)]
        omega) (by omega) (by omega) (by omega)
  have yrow y (hm : y ∈ Y) : outN D V y ⊆ outN D (Y ∪ Z) y := by
    intro w hw
    obtain ⟨vw, yw⟩ := mem_outN.mp hw
    refine mem_outN.mpr ⟨?_, yw⟩
    rcases headY (free.mono_bound hq) hu hm vw yw with early | hz
    · rcases mem_union.mp early with wx | wy
      · obtain ⟨i, pos, len, path⟩ := firstCover w wx y hm
        exact (free w _ (by omega) (by omega) (path.snoc vw yw)).elim
      · exact mem_union_left _ wy
    · exact mem_union_right _ hz
  have ydegree y (hm : y ∈ Y) : 1 ≤ (outN D Y y).card := by
    have room := card_le_card (yrow y hm)
    rw [reg y (yv hm), card_outN_union yz] at room
    have limit : (outN D Z y).card ≤ Z.card := card_le_card outN_subset
    omega
  have yr y (hm : y ∈ Y) : Rooted D V y Y :=
    ShellCycleSupply.rooted_on_small_set free (by omega) yv (by omega) ydegree hm
  have yfull y (hm : y ∈ Y) : outN D Z y = Z := by
    have room := card_le_card (yrow y hm)
    rw [reg y (yv hm), card_outN_union yz, (yr y hm).one y hm] at room
    exact eq_of_subset_of_card_le outN_subset (by omega)
  have yparents y (hm : y ∈ Y) : (inN D Y y).Nonempty := by
    have enough : q < Y.card := by
      by_contra! small
      obtain ⟨a, ha, sink⟩ := exists_sink (free.mono_set yv) ⟨y, hm⟩ small
      obtain ⟨w, hw⟩ := card_pos.mp (ydegree a ha)
      exact sink w (outN_subset hw) (mem_outN.mp hw).2
    have rules := dt_reg (by omega : 1≤q) (ball_q_one q (by omega)) (free.mono_set yv)
      ydegree (show Y.card=q*1+1 by omega)
    exact card_pos.mp (by rw [rules.2 y hm]; decide)
  have coverage v (hm : v ∈ C) : r-2 ≤ (outN D Y v).card := by
    have loss := card_sdiff_add_card_eq_card cx
    have cap : outN D X v ⊆ outN D C v ∪ (X \ C) := by
      intro w hw
      by_cases wc : w ∈ C
      · exact mem_union_left _ (mem_outN.mpr ⟨wc, (mem_outN.mp hw).2⟩)
      · exact mem_union_right _ (mem_sdiff.mpr ⟨outN_subset hw, wc⟩)
    have a := (card_le_card cap).trans (card_union_le _ _)
    rw [internal v hm] at a
    have b := reg v (xv (cx hm))
    rw [outN_X_eq (free.mono_bound hq) hu (cx hm), card_outN_union xy] at b
    omega
  have reachY v (hm : v ∈ C) : Y ⊆ ball D V v 2 := by
    intro y hy
    by_cases edge : D v y = true
    · exact ball_mono_radius (by decide : 1 ≤ 2) (ball_of_adj (yv hy) edge)
    have row : outN D Y v = Y.erase y :=
      eq_of_subset_of_card_le (fun _ hw => mem_erase.mpr
        ⟨fun e => edge (e ▸ (mem_outN.mp hw).2), outN_subset hw⟩)
        (by have := coverage v hm; rw [card_erase_of_mem hy]; omega)
    obtain ⟨a, ha⟩ := yparents y hy
    have apart : a ≠ y := by
      rintro rfl
      exact loopfree free (by omega) (yv hy) (mem_inN.mp ha).2
    have hit : a ∈ outN D Y v := row.symm ▸ mem_erase.mpr ⟨apart, (mem_inN.mp ha).1⟩
    exact ball_step (ball_of_adj (yv (outN_subset hit)) (mem_outN.mp hit).2) (yv hy) (mem_inN.mp ha).2
  have ex : exterior D V C ⊆ Y ∪ (X \ C) := by
    intro w hw
    obtain ⟨hits, away⟩ := mem_sdiff.mp hw
    obtain ⟨v, hv, vw⟩ := mem_biUnion.mp hits
    rw [outN_X_eq (free.mono_bound hq) hu (cx hv)] at vw
    rcases mem_union.mp (outN_subset vw) with wx | wy
    · exact mem_union_right _ (mem_sdiff.mpr ⟨wx, away⟩)
    · exact mem_union_left _ wy
  have yin : Y ⊆ exterior D V C := by
    intro y hy
    -- A one-head row on the first layer is complete to Y.
    have light := LocalBallTransfer.light_supply (free.mono_set xv) (by omega)
      (show X.Nonempty from card_pos.mp (by omega)) interior (by omega : X.card ≤ 2*q)
    let L := X.filter (fun w => (outN D X w).card = 1)
    change 2*q+2 ≤ X.card+L.card at light
    have count := card_sdiff_add_card_eq_card cx
    have existsLight : (C ∩ L).Nonempty := by
      by_contra no
      have order : L ⊆ X \ C := by
        intro w hw
        exact mem_sdiff.mpr ⟨(mem_filter.mp hw).1, fun wc => no ⟨w, mem_inter.mpr ⟨wc, hw⟩⟩⟩
      have := card_le_card order
      omega
    obtain ⟨w, hw⟩ := existsLight
    obtain ⟨wc, wl⟩ := mem_inter.mp hw
    have arc := OneSpareGrowth.sends_layer free hq hu reg (by omega) (cx wc)
      (mem_filter.mp wl).2 y hy
    exact mem_sdiff.mpr ⟨mem_biUnion.mpr ⟨w, wc,
      mem_outN.mpr ⟨yv hy, arc⟩⟩,
      fun hit => (disjoint_left.mp xy) (cx hit) hy⟩
  have outer := (card_le_card ex).trans (card_union_le _ _)
  have outside := card_sdiff_add_card_eq_card cx
  refine ⟨C, cx, by omega, by omega, cr, by omega, yin, fun y hy => ⟨yr y hy, yfull y hy⟩, ?_⟩
  intro v hv
  let A := ball D C v 3 ∪ Y
  have reachZ : Z ⊆ ball D V v 2 := by
    obtain ⟨a, ha⟩ := card_pos.mp (show 0 < (outN D Y v).card by have := coverage v hv; omega)
    intro z hz
    have az : z ∈ outN D Z a := (yfull a (outN_subset ha)).symm ▸ hz
    exact ball_step (ball_of_adj (yv (outN_subset ha)) (mem_outN.mp ha).2) (zv hz) (mem_outN.mp az).2
  have early : A ⊆ ball D V u 2 := union_subset
    (fun _ h => ball_mono_radius (by decide : 1 ≤ 2) (X_B1 (cx (ball_subset h))))
    (fun _ h => (mem_N2.mp h).1)
  have rows : A ⊆ ball D V v 3 := union_subset (ShellCycleSupply.lift_ball (cx.trans xv))
    (fun _ h => ball_mono_radius (by decide : 2 ≤ 3) (reachY v hv h))
  have bill := BankReachTransfer.count_with_prefix (j := 2) (d := 2) (k := 1) hu early rows reachZ
  have inner := ball_one_growth (fp.mono_set cx) (fun w hw => (internal w hw).ge) hv 3 (by omega)
  have acard : A.card = (ball D C v 3).card + Y.card :=
    card_union_of_disjoint (xy.mono_left (ball_subset.trans cx))
  have split := @card_B2 D V u
  simp only [Nat.reduceAdd] at bill
  have mono := card_le_card (ball_mono_radius (D := D) (W := V) (u := u) (by decide : 2 ≤ 4))
  omega

/-- The first two possible third-ball sizes are tested with their marked
third-ball demands. Larger sizes use the lower-degree theorem on the actual
punctured third ball. All size cutoffs are arithmetic conditions on the
parameters and the retained second prefix size. -/
theorem anchored_fourth {D V q r u b target} (free : QFree D V q) (hq : 6 ≤ q)
    (reg : OutEq r D V) (hu : u ∈ V) (near : q+1 ≤ r) (room : r+2 ≤ 2*q)
    (third : b ≤ (ball D V u 3).card)
    (loss : target+2 ≤ b+r+1)
    (fit4 : b+2 ≤ 4*q+1) (fit5 : target ≤ 5*q+2)
    (cap2 : ∀ a, 2*r-1 ≤ a → a ≤ b-1 →
      (b-1)*b < (b-1-a)*14+(a-r)*(2*(r+4))+r*(4*r))
    (cap3 : ∀ a, 2*r-1 ≤ a → a ≤ b →
      b*(b+1) < (b-a)*20+(a-r)*(2*(q+7))+r*(4*r)) :
    target ≤ (ball D V u 4).card := by
  by_contra! small
  have degree x (hx : x ∈ V) := (reg x hx).ge
  have atRoot := GuardedLayerGrowth.second_floor free (by omega) reg (by omega) (by omega) hu
  have nearRow x (hx : x ∈ (ball D V u 1).erase u) : 2*r ≤ (ball D V x 2).card :=
    GuardedLayerGrowth.second_floor free (by omega) reg (by omega) (by omega)
      (ball_subset (mem_of_mem_erase hx))
  have next := card_sdiff_add_card_eq_card
    (ball_mono_radius (D := D) (W := V) (u := u) (by decide : 3 ≤ 4))
  have first : ((ball D V u 1).erase u).card = r := by
    rw [card_erase_of_mem (self_mem_ball hu), card_B1 (free.mono_bound (by omega : 4≤q)) hu, reg u hu]
    omega
  have second : ((ball D V u 2).erase u).card = (ball D V u 2).card-1 :=
    card_erase_of_mem (self_mem_ball hu)
  have mono := card_le_card (ball_mono_radius (D := D) (W := V) (u := u) (by decide : 2 ≤ 3))
  by_cases bottom : (ball D V u 3).card = b
  · have bill := prefix_three_scores (k := 3) (a := 2) (b := 1) (i := 3) (j := 2) (l := 3)
      (base := 14) (high := 2*(r+4)) (near := 4*r)
      free hu (by omega) (by omega) (by decide) (by decide) (by decide) (by decide) (by decide) degree
      (show 2+(ball D V u 4 \ ball D V u 3).card ≤ r by omega) nearRow (by omega) (by
        intro W ff hm x hx
        have floor := ball_growth q (by omega) D W ff hm x hx 3 (by omega)
        refine ⟨by omega, fun full => ?_⟩
        have high := FullRowEscape.high_third ff (by omega) hm hx full room
        omega)
    simp only [card_erase_of_mem (self_mem_ball hu (k := 3)), bottom, first] at bill
    rw [show b-1+1=b by omega] at bill
    exact (not_lt_of_ge bill) (cap2 ((ball D V u 2).erase u).card (by omega) (by omega))
  by_cases upper : (ball D V u 3).card = b+1
  · have bill := prefix_three_scores (k := 3) (a := 2) (b := 1) (i := 3) (j := 2) (l := 3)
      (base := 20) (high := 2*(q+7)) (near := 4*r)
      free hu (by omega) (by omega) (by decide) (by decide) (by decide) (by decide) (by decide) degree
      (show 3+(ball D V u 4 \ ball D V u 3).card ≤ r by omega) nearRow (by omega) (by
        intro W ff hm x hx
        have floor := ball_of_min (BRq3.ball_all 4 (by decide)) (ff.mono_bound (by omega)) hm x hx
        change 10 ≤ (ball D W x 3).card at floor
        refine ⟨by omega, fun full => ?_⟩
        have high := high_row_ball_three_min (by decide : 2 ≤ 3) (by omega) ff hm hx (near.trans full)
        omega)
    simp only [card_erase_of_mem (self_mem_ball hu (k := 3)), upper, Nat.add_sub_cancel, first] at bill
    exact (not_lt_of_ge bill) (cap3 ((ball D V u 2).erase u).card (by omega) (by omega))
  by_cases seam : (ball D V u 3).card = b+2
  · have grow := PrefixDegreeGrowth.small_rank_step (d := 4) (j := 3) free hu (by omega) degree
      (by omega) (by decide) (by decide) (by omega) (by omega)
    change (ball D V u 3).card+r < (ball D V u 4).card+4 at grow
    omega
  · have grow := PrefixDegreeGrowth.small_rank_step (d := 5) (j := 3) free hu (by omega) degree
      (by omega) (by decide) (by decide) (by omega) (by omega)
    change (ball D V u 3).card+r < (ball D V u 4).card+5 at grow
    omega

#print axioms low_third_second
#print axioms narrow_cycle
#print axioms anchored_fourth

end LeanCH.BR.PhysicalCycleStock
