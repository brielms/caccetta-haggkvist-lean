import checkpoints.shen_extension.PhysicalCycleStockReplay

namespace LeanCH.BR.PhysicalCycleStock
open Finset BRq2 BRq3 BR45 BRsGen ExteriorPacking

/-- A narrow primary cycle permits at most two physical turns at each
of its rows, even in a mixed family with omission two. The single possible
extra first-layer label cannot be the sink of three candidate turns. -/
theorem primary_two_turns {D V q r d u v C F} (free : QFree D V q) (hq : 4 ≤ q)
    (reg : OutEq r D V) (hu : u ∈ V) (fit : r ≤ q+2) (gap : d+4 < r)
    (chosen : C ∈ F) (vc : v ∈ C) (first : C ⊆ outN D V u) (size : q+1 ≤ C.card)
    (second : (N2 D V u).card = r-1)
    (sparse : ∀ y ∈ N2 D V u, (outN D (N2 D V u) y).card ≤ d)
    (rooted : ∀ A ∈ F,∀ x ∈ A, Rooted D V x A)
    (width : ∀ A ∈ F, omissions D V A r ≤ 2)
    (narrow : omissions D V C r ≤ 1) :
    (turns D F v).card ≤ 2 := by
  classical
  let T := turns D F v
  let s := internalHead D C v
  let X := outN D V u
  let Y := N2 D V u
  have crude := turns_bound (v := v) free (by omega : 2+2≤q) rooted reg width
  change T.card ≤ 3 at crude
  by_contra! more
  change 2 < T.card at more
  have three : T.card = 3 := by omega
  have origin {w} (hw : w ∈ T) : ∃ A ∈ F, v ∈ A ∧ internalHead D A v = w := by
    obtain ⟨A, ha, eq⟩ := mem_image.mp hw
    exact ⟨A, (mem_filter.mp ha).1, (mem_filter.mp ha).2, eq⟩
  have head {w} (hw : w ∈ T) : w ∈ outN D V v := by
    obtain ⟨A, af, av, eq⟩ := origin hw
    have root := rooted A af v av
    exact eq ▸ outN_mono root.sub v (successor_mem root)
  have subT : T ⊆ V := fun _ hw => outN_subset (head hw)
  have st : s ∈ T := mem_image.mpr ⟨C, mem_filter.mpr ⟨chosen, vc⟩, rfl⟩
  obtain ⟨w, wt, sink⟩ := exists_sink (free.mono_set subT) ⟨s, st⟩ (by omega)
  have outside {A} (af : A ∈ F) (av : v ∈ A) {t} (tt : t ∈ T)
      (ne : t ≠ internalHead D A v) : t ∈ exterior D V A := by
    exact (mem_inter.mp ((row_exterior (rooted A af v av)) ▸ mem_erase.mpr ⟨ne, head tt⟩)).1
  have capture {A} (af : A ∈ F) (av : v ∈ A) (uses : internalHead D A v = w) :
      T.erase w ⊆ exterior D V A \ outN D V w := by
    intro t ht
    obtain ⟨ne, tt⟩ := mem_erase.mp ht
    exact mem_sdiff.mpr ⟨outside af av tt (uses.symm ▸ ne),
      fun hit => sink t tt (mem_outN.mp hit).2⟩
  have wc {A} (af : A ∈ F) (av : v ∈ A) (uses : internalHead D A v = w) : w ∈ A := by
    exact uses ▸ outN_subset (successor_mem (rooted A af v av))
  have cards : (T.erase w).card = 2 := by rw [card_erase_of_mem wt, three]
  have diff : w ≠ s := by
    intro same
    have cap := card_le_card (capture chosen vc same.symm)
    rw [cards, row_omissions (rooted C chosen w (wc chosen vc same.symm)) (reg w (subT wt))] at cap
    omega
  obtain ⟨A, af, av, uses⟩ := origin wt
  have missing : exterior D V A \ outN D V w = T.erase w := by
    apply (eq_of_subset_of_card_le (capture af av uses) ?_).symm
    rw [cards, row_omissions (rooted A af w (wc af av uses)) (reg w (subT wt))]
    exact width A af
  let B := outN D V v \ T
  have bsize : B.card = r-3 := by
    rw [show B = outN D V v \ T from rfl, card_sdiff_of_subset (fun _ t => head t), three,
      reg v ((rooted C chosen v vc).sub vc)]
  have fromCommon {K} (kf : K ∈ F) (kv : v ∈ K) : B ⊆ exterior D V K := by
    intro t ht
    obtain ⟨tv, tt⟩ := mem_sdiff.mp ht
    have turn : internalHead D K v ∈ T := mem_image.mpr ⟨K, mem_filter.mpr ⟨kf, kv⟩, rfl⟩
    have ne : t ≠ internalHead D K v := fun eq => tt (eq.symm ▸ turn)
    have z := mem_erase.mpr ⟨ne, tv⟩
    exact (mem_inter.mp ((row_exterior (rooted K kf v kv)) ▸ z)).1
  have sends : B ⊆ outN D V w := by
    intro t ht
    by_contra miss
    have spent : t ∈ exterior D V A \ outN D V w :=
      mem_sdiff.mpr ⟨fromCommon af av ht, miss⟩
    exact (mem_sdiff.mp ht).2 (mem_of_mem_erase (missing ▸ spent))
  have geometry : exterior D V C ⊆ Y ∪ (X \ C) := by
    intro t ht
    obtain ⟨seen, off⟩ := mem_sdiff.mp ht
    obtain ⟨x, xc, arc⟩ := mem_biUnion.mp seen
    rw [outN_X_eq (free.mono_bound hq) hu (first xc)] at arc
    rcases mem_union.mp (outN_subset arc) with old | new
    · exact mem_union_right _ (mem_sdiff.mpr ⟨old, off⟩)
    · exact mem_union_left _ new
  have xsize : X.card=r := reg u hu
  have roomX := card_sdiff_add_card_eq_card first
  change (X \ C).card+C.card=X.card at roomX
  have ysize : Y.card=r-1 := second
  have direct : (B \ Y).card ≤ (X \ C).card := by
    apply card_le_card
    intro x hx
    exact (mem_union.mp (geometry (fromCommon chosen vc (mem_sdiff.mp hx).1))).resolve_left (mem_sdiff.mp hx).2
  have cut := card_sdiff_add_card_eq_card (inter_subset_left : B ∩ Y ⊆ B)
  rw [inter_comm, sdiff_inter_self_right, inter_comm] at cut
  have notY : w ∉ Y := by
    intro wy
    have paid : B ∩ Y ⊆ outN D Y w := by
      intro t ht
      exact mem_outN.mpr ⟨(mem_inter.mp ht).2, (mem_outN.mp (sends (mem_inter.mp ht).1)).2⟩
    have cap := (card_le_card paid).trans (sparse w wy)
    omega
  have wEx := outside chosen vc wt diff
  have wx := (mem_union.mp (geometry wEx)).resolve_left notY
  have xp : X = insert w C := by
    have notC := (mem_sdiff.mp wx).2
    have sub := insert_subset (mem_sdiff.mp wx).1 first
    have enough := card_le_card sub
    rw [card_insert_of_notMem notC, xsize] at enough
    exact (eq_of_subset_of_card_le sub (by rw [card_insert_of_notMem notC, xsize]; omega)).symm
  have actual : C.card=q+1 := by
    rw [xp, card_insert_of_notMem (mem_sdiff.mp wx).2] at xsize
    omega
  have cv : C ⊆ V := (rooted C chosen v vc).sub
  have cdeg : OutEq 1 D C := fun x hx => (rooted C chosen x hx).one x hx
  have cmin x (hx : x∈C) : 1 ≤ (outN D C x).card := (cdeg x hx).ge
  let R : CH.Digraph := fun a b => D b a
  let S := ball R C v (q-2)
  have reverseDegree x (hx : x∈C) : 1 ≤ (outN R C x).card := by
    have deg := (dt_reg (by omega : 1≤q) (ball_q_one q (by omega)) (free.mono_set cv) cmin
      (show C.card=q*1+1 by omega)).2 x hx
    have eq : outN R C x = inN D C x := by
      ext y
      simp only [mem_outN, mem_inN, R]
    rw [eq, deg]
  have sBound := ball_one_growth (free.reverse.mono_set cv) reverseDegree vc (q-2) (by omega)
  change (q-2)+1 ≤ S.card at sBound
  have sv : s ∈ C := outN_subset (successor_mem (rooted C chosen v vc))
  have vs := (mem_outN.mp (successor_mem (rooted C chosen v vc))).2
  have vw := (mem_outN.mp (head wt)).2
  have sw : D w s ≠ true := sink s st
  have offS : s ∉ S := by
    intro hit
    obtain ⟨_, k, fit, road⟩ := mem_ball.mp hit
    have back := (road.reverse_of_mem vc).mono cv
    exact free v _ (by omega) (by omega) (.step (cv sv) vs back)
  have restricted : outN D C w ⊆ (C \ S).erase s := by
    intro y hy
    obtain ⟨yc, wy⟩ := mem_outN.mp hy
    refine mem_erase.mpr ⟨fun eq => sw (eq ▸ wy), mem_sdiff.mpr ⟨yc, ?_⟩⟩
    intro hit
    obtain ⟨_, k, fit, road⟩ := mem_ball.mp hit
    have back := (road.reverse_of_mem vc).mono cv
    exact free v _ (by omega) (by omega) (.step (subT wt) vw (.step (cv yc) wy back))
  have roomS := card_sdiff_add_card_eq_card (ball_subset : S ⊆ C)
  change (C \ S).card+S.card=C.card at roomS
  have cap := card_le_card restricted
  have ssmall : s ∈ C \ S := mem_sdiff.mpr ⟨sv, offS⟩
  rw [card_erase_of_mem ssmall] at cap
  have wheads : outN D X w = outN D C w := by
    apply Subset.antisymm ?_ (outN_mono first w)
    intro y hy
    rcases mem_insert.mp (xp ▸ (show y ∈ X from outN_subset hy)) with e | hc
    · exact (loopfree free (by omega) (subT wt) (e ▸ (mem_outN.mp hy).2)).elim
    · exact mem_outN.mpr ⟨hc, (mem_outN.mp hy).2⟩
  have allY : outN D Y w = Y := by
    have degree := reg w (subT wt)
    rw [outN_X_eq (free.mono_bound hq) hu (mem_sdiff.mp wx).1,
      card_outN_union disjXY, wheads] at degree
    change (outN D C w).card+(outN D Y w).card=r at degree
    exact eq_of_subset_of_card_le outN_subset (by omega)
  have noThird : T ⊆ {w,s} := by
    intro t ht
    by_cases tw : t=w
    · exact mem_insert.mpr (.inl tw)
    by_cases ts : t=s
    · exact mem_insert.mpr (.inr (mem_singleton.mpr ts))
    have ty := mem_union.mp (geometry (outside chosen vc ht ts))
    rcases ty with inside | before
    · exact (sink t ht (mem_outN.mp (allY.symm ▸ inside)).2).elim
    · exact (tw ((mem_insert.mp (xp ▸ (mem_sdiff.mp before).1)).resolve_right (mem_sdiff.mp before).2)).elim
  have card2 := (card_le_card noThird).trans (card_insert_le w ({s} : Finset ℕ))
  rw [card_singleton] at card2
  omega

#print axioms primary_two_turns
end LeanCH.BR.PhysicalCycleStock
