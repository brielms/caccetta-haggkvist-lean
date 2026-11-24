import checkpoints.shen_extension.PhysicalCycleStockReplay

namespace LeanCH.BR.PhysicalCycleStock
open Finset BRq2 BRq3 BR45 BRsGen

/-- A suffix of a q-free walk contains its distinct physical labels, all
reaching the same terminal within the suffix length. -/
private theorem last_labels {D W q a y n k} (free : QFree D W q) (ha : a ∈ W)
    (road : Walk D W a y n) (kn : k ≤ n) (kq : k ≤ q) :
    ∃ H ⊆ W, H.card = k+1 ∧ ∀ x∈H, y ∈ ball D W x k := by
  classical
  let R : CH.Digraph := fun s t => D t s
  have back : Walk R W y a n := road.reverse_of_mem ha
  obtain ⟨f, fy, _, steps⟩ := back.toFun
  let I := range (k+1)
  have yv : y ∈ W := by
    rcases road.end_mem_or with e | hy
    · exact e ▸ ha
    · exact hy
  have mw (i) (li : i ≤ k) : f i ∈ W := by
    by_cases z : i=0
    · rw [z, fy]
      exact yv
    · obtain ⟨hv, _⟩ := steps (i-1) (by omega)
      rwa [show i-1+1=i by omega] at hv
  have inj : Set.InjOn f (I : Set ℕ) := by
    intro i hi j hj eq
    have ik := mem_range.mp (show i ∈ I from hi)
    have jk := mem_range.mp (show j ∈ I from hj)
    by_contra ne
    rcases lt_or_gt_of_ne ne with ilt | jlt
    · have loop := walk_between steps ilt.le (by omega : j ≤ n)
      rw [←eq] at loop
      exact free.reverse (f i) _ (by omega) (by omega) loop
    · have loop := walk_between steps jlt.le (by omega : i ≤ n)
      rw [eq] at loop
      exact free.reverse (f j) _ (by omega) (by omega) loop
  refine ⟨I.image f, ?_, by rw [card_image_of_injOn inj, card_range], ?_⟩
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hx
    exact mw i (by have := mem_range.mp hi; omega)
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hx
    have bound := mem_range.mp hi
    have route := walk_between steps (show 0 ≤ i by omega) (by omega : i ≤ n)
    rw [fy, Nat.sub_zero] at route
    exact mem_ball.mpr ⟨yv, i, by omega, route.reverse_of_mem yv⟩

/-- In the two acyclic shells, a positive number of forced returns for
each sink creates too many distinct physical omission cells. The exact
inequality depends on the allowed size of the late first-shell bank. -/
theorem dag_omission {D V q r u} (free : QFree D V q) (hq : 4 ≤ q) (reg : OutEq r D V)
    (hu : u ∈ V) (second : (N2 D V u).card = r) (escapes : (N3 D V u).card < r)
    (firstDAG : QFree D (outN D V u) (outN D V u).card)
    (secondDAG : QFree D (N2 D V u) (N2 D V u).card)
    (wide : r-(q-2) ≤ q-1) :
    2*(r*(r-(N3 D V u).card)) ≤ (r-(q-2))*((r-(q-2))-1) := by
  classical
  let X := outN D V u
  let Y := N2 D V u
  let Z := N3 D V u
  let late := X.filter (fun x => ∀ s∈X, (∀ z∈X,D s z ≠ true) → s ∉ ball D X x (q-3))
  let P := Y.biUnion (fun y => outN D X y)
  have xv : X ⊆ V := outN_subset
  have yv : Y ⊆ V := fun _ h => N2_subV h
  have zv : Z ⊆ V := fun _ h => N3_subV h
  have xcard : X.card = r := reg u hu
  have ycard : Y.card = r := second
  have zcard : Z.card < r := escapes
  have xy : Disjoint X Y := disjXY
  have px : P ⊆ X := by
    intro x hx
    obtain ⟨y, _, yx⟩ := mem_biUnion.mp hx
    exact outN_subset yx
  have xsends s (hs : s∈X) (sink : ∀ z∈X, D s z ≠ true) : ∀ y∈Y,D s y = true := by
    have degree := reg s (xv hs)
    rw [outN_X_eq (free.mono_bound hq) hu hs, card_outN_union xy] at degree
    have none : outN D X s = ∅ := eq_empty_iff_forall_notMem.mpr
      (fun z hz => sink z (outN_subset hz) (mem_outN.mp hz).2)
    rw [none, card_empty, zero_add] at degree
    have eq : outN D Y s = Y := eq_of_subset_of_card_le outN_subset (by omega)
    exact fun y hy => (mem_outN.mp (eq.symm ▸ hy)).2
  have lateReturn x (hx : x ∈ P) s (hs : s ∈ X) (sink : ∀ z∈X,D s z ≠ true)
      {n : ℕ} (road : Walk D X x s n) : q-1 ≤ n := by
    obtain ⟨y, hy, edge⟩ := mem_biUnion.mp hx
    by_contra! quick
    have closed := (((road.mono xv).snoc (yv hy) (xsends s hs sink y hy)).snoc
      (xv (px hx)) (mem_outN.mp edge).2)
    exact free x _ (by omega) (by omega) closed
  have inLate x (hx : x ∈ P) : x ∈ late := by
    refine mem_filter.mpr ⟨px hx, fun s hs sink hit => ?_⟩
    obtain ⟨_, n, le, road⟩ := mem_ball.mp hit
    have := lateReturn x hx s hs sink road
    omega
  have keep x (hx : x∈P) : outN D X x = outN D late x := by
    refine Subset.antisymm ?_ (outN_mono (filter_subset _ _) _)
    intro w hw
    obtain ⟨wx, arc⟩ := mem_outN.mp hw
    refine mem_outN.mpr ⟨mem_filter.mpr ⟨wx, fun s hs sink hit => ?_⟩, arc⟩
    obtain ⟨_, n, le, road⟩ := mem_ball.mp hit
    have := lateReturn x hx s hs sink (.step wx arc road)
    omega
  have returnNeed y (hy : y∈Y) (sink : ∀ z∈Y,D y z ≠ true) :
      r-Z.card ≤ (outN D X y).card := by
    have sub : outN D V y ⊆ outN D X y ∪ Z := by
      intro z hz
      obtain ⟨zv', yz⟩ := mem_outN.mp hz
      rcases headY (free.mono_bound hq) hu hy zv' yz with old | new
      · rcases mem_union.mp old with first | second
        · exact mem_union_left _ (mem_outN.mpr ⟨first, yz⟩)
        · exact (sink z second yz).elim
      · exact mem_union_right _ new
    have cap := (card_le_card sub).trans (card_union_le _ _)
    rw [reg y (yv hy)] at cap
    omega
  obtain ⟨y, hy, ysink⟩ := exists_sink secondDAG (card_pos.mp (by omega : 0<Y.card)) le_rfl
  have yret := returnNeed y hy ysink
  obtain ⟨p, hp⟩ := card_pos.mp (show 0 < (outN D X y).card by omega)
  have pP : p ∈ P := mem_biUnion.mpr ⟨y, hy, hp⟩
  obtain ⟨s, hs, ssink, n, _, road⟩ := reach_sink_of_card firstDAG le_rfl (px pP)
  have long := lateReturn p pP s hs ssink road
  obtain ⟨H, hsub, hc, seen⟩ := last_labels (free.mono_set xv) (px pP) road
    (show q-3≤n by omega) (by omega : q-3 ≤ q)
  have apart : Disjoint H late := by
    refine disjoint_left.mpr (fun x hx hit => ?_)
    exact (mem_filter.mp hit).2 s hs ssink (seen x hx)
  have lateSub : late ⊆ X := filter_subset _ _
  have room := card_le_card (union_subset hsub lateSub)
  rw [card_union_of_disjoint apart, hc, xcard] at room
  have size : late.card ≤ r-(q-2) := by omega
  have omitted x (hx : x∈P) : (Y \ outN D V x).card = (outN D late x).card := by
    have off : Y \ outN D V x = Y \ outN D Y x := by
      ext z
      simp only [mem_sdiff, mem_outN]
      exact ⟨fun ⟨zy, no⟩ => ⟨zy, fun hit => no ⟨yv zy, hit.2⟩⟩,
        fun ⟨zy, no⟩ => ⟨zy, fun hit => no ⟨zy, hit.2⟩⟩⟩
    have de := reg x (xv (px hx))
    rw [outN_X_eq (free.mono_bound hq) hu (px hx), card_outN_union xy, keep x hx] at de
    rw [off, card_sdiff_of_subset (outN_subset : outN D Y x ⊆ Y), ycard]
    omega
  have rowBound x (hx : x ∈ P) : (Y \ outN D V x).card ≤ late.card-1 := by
    rw [omitted x hx]
    have sub : outN D late x ⊆ late.erase x := by
      intro z hz
      exact mem_erase.mpr ⟨fun eq => loopfree free (by omega) (xv (px hx)) (eq ▸ (mem_outN.mp hz).2),
        outN_subset hz⟩
    exact (card_le_card sub).trans_eq (card_erase_of_mem (inLate x hx))
  have block {a y x l} (ha : a∈Y) (hy : y∈Y) (xr : x∈outN D X y)
      (walk : Walk D Y a y l) (fit : l≤q-2) : a ∈ Y \ outN D V x := by
    refine mem_sdiff.mpr ⟨ha, fun hit => ?_⟩
    have close := ((walk.mono yv).snoc (xv (outN_subset xr)) (mem_outN.mp xr).2).snoc
      (yv ha) (mem_outN.mp hit).2
    exact free a _ (by omega) (by omega) close
  have sinkOf (a) (ha : a∈Y) : ∃ y∈Y, (∀z∈Y,D y z ≠ true) ∧ ∃l,Walk D Y a y l := by
    obtain ⟨y, hy, sink, l, _, path⟩ := reach_sink_of_card secondDAG le_rfl ha
    exact ⟨y, hy, sink, l, path⟩
  let yOf := fun a => if ha : a∈Y then Classical.choose (sinkOf a ha) else 0
  have chosen a (ha : a∈Y) : yOf a∈Y ∧ (∀z∈Y,D (yOf a) z ≠ true) ∧ ∃l,Walk D Y a (yOf a) l := by
    simpa only [yOf, dite_eq_left ha] using Classical.choose_spec (sinkOf a ha)
  let R := fun a x => x∈outN D X (yOf a)
  have demands a (ha : a∈Y) : r-Z.card ≤ (late.bipartiteAbove R a).card := by
    obtain ⟨hy, sink, _, _⟩ := chosen a ha
    apply (returnNeed _ hy sink).trans (card_le_card ?_)
    intro x hx
    exact (mem_bipartiteAbove _).mpr ⟨inLate x (mem_biUnion.mpr ⟨yOf a, hy, hx⟩), hx⟩
  have cells x (hx : x∈late) :
      (Y.bipartiteBelow R x).card ≤ (outN D late x).card := by
    rcases (Y.bipartiteBelow R x).eq_empty_or_nonempty with empty | ⟨a, ha⟩
    · simp [empty]
    have hpair := (mem_bipartiteBelow _).mp ha
    have xp : x∈P := mem_biUnion.mpr ⟨yOf a, (chosen a hpair.1).1, hpair.2⟩
    rw [←omitted x xp]
    apply card_le_card
    intro a ha
    obtain ⟨ay, returned⟩ := (mem_bipartiteBelow _).mp ha
    obtain ⟨hy, sink, l, path⟩ := chosen a ay
    by_cases small : l≤q-2
    · exact block ay hy returned path small
    · obtain ⟨M, msub, mc, together⟩ := last_labels (free.mono_set yv) ay path
        (show q-2≤l by omega) (by omega : q-2≤q)
      have all : M ⊆ Y \ outN D V x := by
        intro m hm
        obtain ⟨_, d, bound, chain⟩ := mem_ball.mp (together m hm)
        exact block (msub hm) hy returned chain bound
      have exceeded := (card_le_card all).trans (rowBound x xp)
      omega
  have lower := sum_le_sum demands
  have upper := sum_le_sum cells
  rw [sum_const_nat (fun _ _ => rfl), ycard] at lower
  have same := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (s := Y) (t := late) R
  have cost := lower.trans (same.le.trans upper)
  have lv : late ⊆ V := lateSub.trans xv
  have budget := DotClonePairCompletion.incomparable_reach_identity (free.mono_set lv) (by omega : 1+1≤q)
  have sumEq : (∑ x ∈ late, (ball D late x 1).card) =
      late.card + (∑ x ∈ late, (outN D late x).card) := by
    rw [sum_congr rfl (fun x hx => card_B1 ((free.mono_set lv).mono_bound hq) hx),
      sum_add_distrib, sum_const_nat (fun _ _ => rfl)]
    omega
  rw [sumEq, Nat.mul_add, show late.card*(late.card+1)=late.card*late.card+late.card by
    rw [Nat.mul_add, Nat.mul_one]] at budget
  have paid : 2*(∑ x ∈ late, (outN D late x).card) ≤ late.card*(late.card-1) := by
    rw [Nat.mul_sub_left_distrib, Nat.mul_one]
    omega
  have buy := Nat.mul_le_mul_left 2 cost
  have compare := Nat.mul_le_mul size (Nat.sub_le_sub_right size 1)
  exact buy.trans (paid.trans compare)

#print axioms dag_omission
end LeanCH.BR.PhysicalCycleStock
