import checkpoints.shen_extension.ShortLargeSecondEscape

namespace LeanCH.BR.LowShellCycleSelection
open Finset BRq2 BRq3 BR45 BRsGen ExteriorPacking PhysicalCycleStock RetainedMixedCapacity
open scoped Classical

/-- The narrow-middle fragment calculation applies to a supplied physical
cycle. Both its count of one-head rows and the price floor now refer to this
cycle even when several cycles coexist in the original first layer. -/
theorem actual_narrow_middle {D V q r u C} (free : QFree D V q) (hq : 6≤q)
    (reg : OutEq r D V) (hu : u∈V) (fit : r≤q+2) (hr : 4≤r)
    (room : r+2≤2*q) (second : (N2 D V u).card=r-1) (third : (N3 D V u).card=r)
    (capacity : (2*r-1)*(2*r)<(r-1)*(2*(r+4))+r*14)
    (cx : C⊆outN D V u) (ccard : q<C.card) (roots : ∀v∈C,Rooted D V v C) :
    (3*q+3-2*r≤(C.filter (fun x=>(outN D (outN D V u) x).card=1)).card) ∧
    ∀x∈C,(outN D (outN D V u) x).card=1 → 3*r+2≤(ball D V x 3).card := by
  classical
  let X := outN D V u
  let Y := N2 D V u
  let Z := N3 D V u
  let W := ball D V u 4 \ ball D V u 3
  let L := X.filter (fun x => (outN D X x).card = 1)
  have xv : X ⊆ V := outN_subset
  have yv : Y ⊆ V := fun _ h => N2_subV h
  have zv : Z ⊆ V := fun _ h => N3_subV h
  have xy : Disjoint X Y := disjXY
  have yz : Disjoint Y Z := disjoint_left.mpr (fun _ hm hn => (mem_N3.mp hn).2 (mem_N2.mp hm).1)
  have xcard : X.card = r := reg u hu
  have ycard : Y.card = r-1 := second
  have zcard : Z.card = r := third
  have interior v (hv : v ∈ X) :=
    OneSpareGrowth.internal_positive free (by omega) hu reg (by omega : (N2 D V u).card+1=r) hv
  have firstCover : ∀ x ∈ X, ∀ y ∈ Y, ∃ k, 0 < k ∧ k ≤ 2 ∧ Walk D V x y k :=
    BankReachTransfer.reaches_bank (k := 1) free (by omega) xv yv xy
      (fun v hv => by rw [reg v hv]; omega)
      (fun v hv => by
        rw [← outN_X_eq (free.mono_bound (by omega : 4 ≤ q)) hu hv, reg v (xv hv)]
        omega) (by omega) (by omega) (by omega)
  have reachZ x (hx : x ∈ X) z (hz : z ∈ Z) : ∃ i : ℕ, 0 < i ∧ i ≤ 3 ∧ Walk D V x z i := by
    obtain ⟨y, hy, arc⟩ := ball_succ_pred hu (mem_N3.mp hz).1 (mem_N3.mp hz).2
    have iny : y ∈ Y := mem_N2.mpr ⟨hy, fun early => (mem_N3.mp hz).2 (ball_step early (zv hz) arc)⟩
    obtain ⟨k, pos, fit, path⟩ := firstCover x hx y iny
    exact ⟨k+1, by omega, by omega, path.snoc (zv hz) arc⟩
  have yrow y (hm : y ∈ Y) : outN D V y = outN D (Y ∪ Z) y := by
    refine Subset.antisymm ?_ (outN_mono (union_subset yv zv) _)
    intro w hw
    obtain ⟨vw, yw⟩ := mem_outN.mp hw
    refine mem_outN.mpr ⟨?_, yw⟩
    rcases headY (free.mono_bound (by omega : 4 ≤ q)) hu hm vw yw with early | hz
    · rcases mem_union.mp early with wx | wy
      · obtain ⟨i, pos, len, path⟩ := firstCover w wx y hm
        exact (free w _ (by omega) (by omega) (path.snoc vw yw)).elim
      · exact mem_union_left _ wy
    · exact mem_union_right _ hz
  have zrow z (hz : z ∈ Z) : outN D V z ⊆ outN D (Y ∪ Z) z ∪ W := by
    intro v vm
    obtain ⟨vv, zv'⟩ := mem_outN.mp vm
    by_cases far : v ∈ ball D V u 3
    · have front : v ∈ Y ∪ Z := by
        by_cases two : v ∈ ball D V u 2
        · by_cases one : v ∈ ball D V u 1
          · rcases (mem_ball_one hu).mp one with rfl | vx
            · exact (no_back_arc free hu (mem_N3.mp hz).1 (by omega) zv').elim
            obtain ⟨l, pos, fit, path⟩ := reachZ v vx z hz
            exact (free v _ (by omega) (by omega) (path.snoc vv zv')).elim
          · exact mem_union_left _ (mem_N2.mpr ⟨two, one⟩)
        · exact mem_union_right _ (mem_N3.mpr ⟨far, two⟩)
      exact mem_union_left _ (mem_outN.mpr ⟨front, zv'⟩)
    · exact mem_union_right _ (mem_sdiff.mpr ⟨ball_step (mem_N3.mp hz).1 vv zv', far⟩)
  have fourth : r-1 ≤ W.card := by
    by_contra! small
    let J := Y ∪ Z
    have ff : QFree D J q := free.mono_set (union_subset yv zv)
    have paid (x) (hx : x ∈ J) : 2 ≤ (outN D J x).card := by
      rcases mem_union.mp hx with yy | zz
      · rw [← yrow x yy, reg x (yv yy)]
        omega
      · have size := (card_le_card (zrow x zz)).trans (card_union_le _ _)
        rw [reg x (zv zz)] at size
        change r ≤ (outN D J x).card + W.card at size
        omega
    have bill := mixed_capacity (i := 3) (j := 3) (base := 14) (high := 2*(r+4))
      ff (by omega) (H := Y) (subset_union_left : Y ⊆ J)
      (fun x hx => by
        have floor := ball_growth q (by omega) D J ff paid x hx 3 (by omega)
        omega)
      (fun x hx => by
        have full : r ≤ (outN D J x).card := by rw [←yrow x hx, reg x (yv hx)]
        have high := FullRowEscape.high_third ff (by omega) paid
          (mem_union_left _ hx) full room
        omega)
    have whole : J.card = 2*r-1 := by
      rw [card_union_of_disjoint yz, ycard, zcard]
      omega
    rw [whole, ycard, show (2*r-1)-(r-1)=r by omega, show (2*r-1)+1=2*r by omega] at bill
    omega
  have light := LocalBallTransfer.light_supply (free.mono_set xv) (by omega)
    (show X.Nonempty from card_pos.mp (by omega)) interior (by omega : X.card ≤ 2*q)
  change 2*q+2 ≤ X.card+L.card at light
  have count : L.card ≤ (C.filter (fun x => (outN D X x).card = 1)).card+(X \ C).card := by
    have sub : L ⊆ C.filter (fun x => (outN D X x).card = 1) ∪ (X \ C) := by
      intro x hx
      by_cases inc : x ∈ C
      · exact mem_union_left _ (mem_filter.mpr ⟨inc, (mem_filter.mp hx).2⟩)
      · exact mem_union_right _ (mem_sdiff.mpr ⟨(mem_filter.mp hx).1, inc⟩)
    exact (card_le_card sub).trans (card_union_le _ _)
  have cBound := card_le_card cx
  have gap := card_sdiff_add_card_eq_card (show C⊆X from cx)
  have nRows : 3*q+3-2*r ≤ (C.filter (fun x => (outN D X x).card = 1)).card := by omega
  refine ⟨nRows,?_⟩
  intro x hx one
  have seen : Y ⊆ ball D V x 1 := fun y hy =>
    ball_of_adj (yv hy) (OneSpareGrowth.sends_layer free (by omega) hu reg (by omega) (cx hx) one y hy)
  have bill := BankReachTransfer.count_with_prefix (j := 1) (d := 1) (k := 2) hu
    (A := ball D C x 3) (fun _ h => X_B1 (cx (ball_subset h)))
    (ShellCycleSupply.lift_ball (cx.trans xv)) seen
  simp only [Nat.reduceAdd] at bill
  have inner := ball_one_growth (free.mono_set (cx.trans xv)) (fun w hw => ((roots w hw).one w hw).ge) hx 3 (by omega)
  have shell2 := @card_B2 D V u
  have shell3 := @card_B3 D V u
  have shell4 := card_sdiff_add_card_eq_card
    (ball_mono_radius (D := D) (W := V) (u := u) (by decide : 3 ≤ 4))
  change W.card + _ = _ at shell4
  change (N2 D V u).card = r-1 at ycard
  change (N3 D V u).card = r at zcard
  omega

#print axioms actual_narrow_middle
end LeanCH.BR.LowShellCycleSelection
