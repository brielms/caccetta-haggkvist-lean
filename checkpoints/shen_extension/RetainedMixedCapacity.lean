import checkpoints.shen_extension.GuardedDegreeFrontier
import checkpoints.shen_extension.dot_tensor_research.DiagonalEight

namespace LeanCH.BR.RetainedMixedCapacity
open Finset BRq2 BRq3 BR45 BRsGen

/-- Count each row of H at its marked score and each remaining row at its
ordinary score. The two forward budgets use one graph and one carrier. -/
theorem mixed_capacity {D W q i j base high} {H : Finset ℕ}
    (free : QFree D W q) (radii : i+j≤q) (sub : H⊆W)
    (ordinary : ∀ x∈W, base≤(ball D W x i).card+(ball D W x j).card)
    (marked : ∀ x∈H, high≤(ball D W x i).card+(ball D W x j).card) :
    H.card*high+(W.card-H.card)*base ≤ W.card*(W.card+1) := by
  classical
  let score := fun x => (ball D W x i).card+(ball D W x j).card
  have paid := sum_le_sum marked
  have rest := sum_le_sum (s:=W\H) (fun x hx => ordinary x (mem_sdiff.mp hx).1)
  rw [sum_const_nat (fun _ _ => rfl)] at paid rest
  rw [card_sdiff_of_subset sub] at rest
  have part := sum_sdiff sub (f:=score)
  have space := sum_le_sum (s:=W) (fun v _ => reverseBall_add_ball_le (v:=v) free radii)
  rw [sum_add_distrib,sum_reverseBall_eq_sum_ball,sum_const_nat (fun _ _ => rfl)] at space
  dsimp only [score] at part
  rw [sum_add_distrib (s:=W)] at part
  omega

/-- In a punctured prefix the earlier punctured ball keeps its native
outgoing heads. The intervening layer controls the minimum degree of the
whole prefix. The capacity is evaluated on precisely those two sets. -/
theorem prefix_capacity {D V q v a i j r t base high} (free : QFree D V q)
    (root : v∈V) (dist : a+2≤q) (radii : i+j≤q)
    (degree : ∀ x∈V, r≤(outN D V x).card)
    (retain : t+(ball D V v (a+2) \ ball D V v (a+1)).card≤r)
    (ordinary : ∀ (W : Finset ℕ), QFree D W q → (∀ x∈W, t≤(outN D W x).card) →
      ∀ x∈W, base≤(ball D W x i).card+(ball D W x j).card)
    (marked : ∀ (W : Finset ℕ), QFree D W q → (∀ x∈W, t≤(outN D W x).card) →
      ∀ x∈W, r≤(outN D W x).card → high≤(ball D W x i).card+(ball D W x j).card) :
    let W := (ball D V v (a+1)).erase v
    let H := (ball D V v a).erase v
    H.card*high+(W.card-H.card)*base ≤ W.card*(W.card+1) := by
  let W := (ball D V v (a+1)).erase v
  let H := (ball D V v a).erase v
  have wv : W⊆V := (erase_subset _ _).trans ball_subset
  have sub : H⊆W := erase_subset_erase v (ball_mono_radius (Nat.le_succ a))
  have ff := free.mono_set wv
  have rank := minOut_prefix_erase free root dist degree retain
  exact mixed_capacity ff radii sub (ordinary W ff rank) (fun x hx =>
    marked W ff rank x (sub hx) ((degree x (wv (sub hx))).trans (card_le_card
      (outN_prefix_erase_root free root (by omega : a+1≤q) (mem_of_mem_erase hx)))))

/-- At equality the smaller radius has constant size. A named witness
giving a larger ball on the same carrier then improves the order by one. -/
theorem strict_order {D V q i j a b} (free : QFree D V q) (live : V.Nonempty)
    (radii : i+j≤q) (left : ∀ v∈V, a≤(ball D V v i).card)
    (right : ∀ v∈V, b≤(ball D V v j).card)
    (move : ∀ u∈V, (ball D V u i).card=a → ∃ v∈V, a<(ball D V v i).card) :
    a+b≤V.card := by
  have lo := card_ge_of_two_balls free radii left right live
  by_contra! small
  have flat := two_balls_boundary_cards free radii left right (by omega : a+b=V.card+1)
  obtain ⟨u,hu⟩ := live
  obtain ⟨v,hv,tall⟩ := move u hu (flat u hu).1
  exact (Nat.ne_of_gt tall) (flat v hv).1

private theorem min_three_score {D V q} (free : QFree D V q) (hq : 9≤q)
    (rank : ∀ x∈V, 3≤(outN D V x).card) (x) (hx : x∈V) :
    29≤(ball D V x 4).card+(ball D V x 5).card := by
  have a := ball_of_min (BRq3.ball_all 5 (by decide)) (free.mono_bound (by omega)) rank x hx
  have b := ball_of_min (BRq3.ball_all 6 (by decide)) (free.mono_bound (by omega)) rank x hx
  change 13≤(ball D V x 4).card at a
  change 16≤(ball D V x 5).card at b
  omega

private theorem high_radii {D V q} (free : QFree D V q) (hq : 9≤q)
    (rank : ∀ x∈V, 3≤(outN D V x).card) (x) (hx : x∈V) (high : 8≤(outN D V x).card) :
    14≤(ball D V x 3).card ∧ 16≤(ball D V x 4).card ∧ 18≤(ball D V x 5).card := by
  have b3 := high_row_ball_three_min (by decide : 2≤3) (by decide : 2*3≤7+1)
    (free.mono_bound (by omega : 7≤q)) rank hx high
  have grow {j lo : ℕ} (dist : j+1≤q) (lo' : lo≤(ball D V x j).card)
      (pos : 1<lo) (room : lo+2≤2*q+2) : lo+2≤(ball D V x (j+1)).card := by
    apply PrefixDegreeGrowth.raise_floor free hx dist rank (by omega) lo' pos
    intro m lm mb
    exact ⟨2,by decide,by decide,by omega,by omega⟩
  have b4 := grow (j:=3) (lo:=14) (by omega) b3 (by decide) (by omega)
  have b5 := grow (j:=4) (lo:=16) (by omega) b4 (by decide) (by omega)
  change 16≤(ball D V x 4).card at b4
  change 18≤(ball D V x 5).card at b5
  exact ⟨b3,b4,b5⟩

private theorem high_score {D V q} (free : QFree D V q) (hq : 9≤q)
    (rank : ∀ x∈V, 3≤(outN D V x).card) (x) (hx : x∈V) (high : 8≤(outN D V x).card) :
    34≤(ball D V x 4).card+(ball D V x 5).card := by
  obtain ⟨_,h4,h5⟩ := high_radii free hq rank x hx high
  omega

/-- A minimum degree of eight and cutoff at least nine force 38
vertices within five steps of every marked root, including the root. -/
theorem fifth_floor {D V q v} (free : QFree D V q) (hq : 9≤q)
    (root : v∈V) (degree : ∀ x∈V, 8≤(outN D V x).card) : 38≤(ball D V v 5).card := by
  have eight := free.mono_bound (by omega : 8≤q)
  have b3 := DiagonalEight.three25 eight degree root
  have b4 := DiagonalEight.fourth32 eight degree root
  by_contra! small
  by_cases short : (ball D V v 4).card=32
  · have delta := card_sdiff_add_card_eq_card (ball_mono_radius (D:=D) (W:=V) (u:=v) (by decide : 4≤5))
    have bill := prefix_capacity (a:=3) (i:=4) (j:=5) free root (by omega) (by omega) degree
      (show 3+(ball D V v 5 \ ball D V v 4).card≤8 by omega)
      (fun _ ff => min_three_score ff hq) (fun _ ff => high_score ff hq)
    dsimp only at bill
    rw [card_erase_of_mem (self_mem_ball root),card_erase_of_mem (self_mem_ball root),short] at bill
    have size := card_le_card (ball_mono_radius (D:=D) (W:=V) (u:=v) (by decide : 3≤4))
    omega
  · have mono := card_le_card (ball_mono_radius (D:=D) (W:=V) (u:=v) (by decide : 4≤5))
    have step := PrefixDegreeGrowth.small_rank_step (j:=4) (d:=4) free root (by omega) degree
      (by omega) (by decide) (by decide) (by omega) (by omega)
    change (ball D V v 4).card+8<(ball D V v 5).card+4 at step
    omega

theorem order_bound {D V q} (free : QFree D V q) (hq : 9≤q) (live : V.Nonempty)
    (degree : ∀ x∈V, 8≤(outN D V x).card) : 70≤V.card := by
  obtain ⟨F,sub,reg⟩ := exists_outEq degree
  have ff := qfree_sub sub free
  have eight := ff.mono_bound (by omega : 8≤q)
  have deg x (hx : x∈V) := (reg x hx).ge
  exact strict_order ff live (by omega : 4+5≤q) (fun _ hv => DiagonalEight.fourth32 eight deg hv)
    (fun _ hv => fifth_floor ff hq hv deg) (fun u hu eq => by
      obtain ⟨v,head,tall,_⟩ := DiagonalEight.short_to_tall eight reg hu eq.le
      exact ⟨v,outN_subset head,tall⟩)

/-- If a punctured prefix is small enough, retaining even one head from
each row is impossible in the presence of r actual full rows. -/
theorem full_layer {D V q r v a} (free : QFree D V q) (root : v∈V)
    (hr : 3≤r) (diag : r≤q) (dist : a+2≤q) (degree : ∀x∈V,r≤(outN D V x).card)
    (many : r+1≤(ball D V v a).card) (small : (ball D V v (a+1)).card≤q+r+1) :
    r≤(ball D V v (a+2) \ ball D V v (a+1)).card := by
  classical
  let W := (ball D V v (a+1)).erase v
  let H := (ball D V v a).erase v
  have sub : H⊆W := erase_subset_erase v (ball_mono_radius (Nat.le_succ a))
  have wv : W⊆V := (erase_subset _ _).trans ball_subset
  have wc : W.card+1=(ball D V v (a+1)).card := card_erase_add_one (self_mem_ball root)
  have hc : H.card+1=(ball D V v a).card := card_erase_add_one (self_mem_ball root)
  by_contra! short
  have rank := minOut_prefix_erase (d:=1) free root dist degree
    (show 1+(ball D V v (a+2) \ ball D V v (a+1)).card≤r by omega)
  have cost := small_one_high_degree_count_of_le hr diag (free.mono_set wv) (by omega) rank sub
    (fun x hx => (degree x (wv (sub hx))).trans (card_le_card (outN_prefix_erase_root free root
      (by omega : a+1≤q) (mem_of_mem_erase hx))))
  omega

/-- A small set of rows in a q-free graph must offer at least d labelled
exits at distinct tails when each row has degree at least d. -/
theorem exit_rows {D W L q d} (free : QFree D W q) (sub : L⊆W)
    (degree : ∀x∈L,d≤(outN D W x).card) (small : L.card≤q) (room : d≤L.card) :
    ∃ P⊆L, P.card=d ∧ ∀x∈P,∃y∈W\L, D x y=true := by
  classical
  let E := L.filter (fun x => ∃y∈W\L, D x y=true)
  have enough : d≤E.card := by
    by_contra! few
    have nonempty := sdiff_nonempty_of_card_lt_card (lt_of_lt_of_le few room)
    obtain ⟨x,xm,sink⟩ := exists_sink (T:=L\E) (free.mono_set (sdiff_subset.trans sub)) nonempty
      ((card_le_card sdiff_subset).trans small)
    obtain ⟨xl,off⟩ := mem_sdiff.mp xm
    have inside : outN D W x⊆E := by
      intro y hit
      by_contra ye
      by_cases yl : y∈L
      · exact sink y (mem_sdiff.mpr ⟨yl,ye⟩) (mem_outN.mp hit).2
      · exact off (mem_filter.mpr ⟨xl,y,mem_sdiff.mpr ⟨outN_subset hit,yl⟩,(mem_outN.mp hit).2⟩)
    exact (not_lt_of_ge ((degree x xl).trans (card_le_card inside))) few
  obtain ⟨P,pe,num⟩ := exists_subset_card_eq enough
  exact ⟨P,pe.trans (filter_subset _ _),num,fun x xp => (mem_filter.mp (pe xp)).2⟩

theorem forward_gain {D W q j x y} (free : QFree D W q) (radius : j+1≤q)
    (xw : x∈W) (edge : y∈outN D W x) : (ball D W y j).card+1≤(ball D W x (j+1)).card := by
  have yw := outN_subset edge
  have xy := (mem_outN.mp edge).2
  have off : x∉ball D W y j := fun hit => no_back_arc free yw hit radius xy
  have sub : insert x (ball D W y j)⊆ball D W x (j+1) := by
    intro v hit
    rcases mem_insert.mp hit with rfl|reached
    · exact self_mem_ball xw
    · obtain ⟨vw,i,le,path⟩ := mem_ball.mp reached
      exact mem_ball.mpr ⟨vw,i+1,by omega,.step yw xy path⟩
  simpa only [card_insert_of_notMem off] using card_le_card sub

theorem fourth_floor {D V q v} (free : QFree D V q) (hq : 9≤q)
    (root : v∈V) (degree : ∀x∈V,8≤(outN D V x).card) : 33≤(ball D V v 4).card := by
  obtain ⟨F,sub,reg⟩ := exists_outEq degree
  apply le_trans _ (card_le_card (ball_sub (u:=v) (k:=4) sub))
  have ff := qfree_sub sub free
  by_contra! low
  obtain ⟨b2,b3,_⟩ := DiagonalEight.short_profile (ff.mono_bound (by omega : 8≤q)) reg root (by omega)
  have b1 := card_B1 (ff.mono_bound (by omega : 4≤q)) root
  rw [reg v root] at b1
  have extra := full_layer (a:=1) ff root (by decide : 3≤8) (by omega) (by omega)
    (fun x hx => (reg x hx).ge) (by simpa using b1.ge) (by simp only [Nat.reduceAdd]; omega)
  have count := card_sdiff_add_card_eq_card (ball_mono_radius (D:=F) (W:=V) (u:=v) (by decide : 2≤3))
  change 8≤(ball F V v 3 \ ball F V v 2).card at extra
  omega

/-- Mixed scores with an arbitrary row-dependent price retain the labels
of the receiver, its parents and their complementary carrier. -/
theorem weighted_rows {D W q i j} (free : QFree D W q) (radii : i+j≤q) {score : ℕ→ℕ}
    (paid : ∀x∈W,score x≤(ball D W x i).card+(ball D W x j).card) :
    ∑x∈W,score x ≤ W.card*(W.card+1) := by
  have bill := sum_le_sum paid
  have space := sum_le_sum (s:=W) (fun x _ => reverseBall_add_ball_le (v:=x) free radii)
  rw [sum_add_distrib] at bill
  rw [sum_add_distrib,sum_reverseBall_eq_sum_ball,sum_const_nat (fun _ _=>rfl)] at space
  omega

private theorem dense32 {D W H q} (free : QFree D W q) (hq : 9≤q) (wc : W.card=32)
    (rank : ∀x∈W,3≤(outN D W x).card) (sub : H⊆W) (hc : H.card=24)
    (full : ∀x∈H,8≤(outN D W x).card) : False := by
  classical
  let L := W\H
  have lc : L.card=8 := by rw [card_sdiff_of_subset sub,wc,hc]
  have lw : L⊆W := sdiff_subset
  obtain ⟨P,pl,pc,exits⟩ := exit_rows free lw (fun x xl=>rank x (lw xl)) (by omega) (by omega : 3≤L.card)
  let score := fun x => (ball D W x 4).card+(ball D W x 5).card
  have parent (x) (xp : x∈P) : 32≤score x := by
    obtain ⟨y,ym,xy⟩ := exits x xp
    obtain ⟨yw,off⟩ := mem_sdiff.mp ym
    have yh : y∈H := by by_contra miss; exact off (mem_sdiff.mpr ⟨yw,miss⟩)
    obtain ⟨b3,b4,_⟩ := high_radii free hq rank y yw (full y yh)
    have e := mem_outN.mpr ⟨yw,xy⟩
    have left := forward_gain (j:=3) free (by omega) (lw (pl xp)) e
    have right := forward_gain (j:=4) free (by omega) (lw (pl xp)) e
    simp only [Nat.reduceAdd] at left right
    change 32≤(ball D W x 4).card+(ball D W x 5).card
    omega
  have highs := sum_le_sum (s:=H) (fun x hx=> high_score free hq rank x (sub hx) (full x hx))
  have parents := sum_le_sum parent
  have rest := sum_le_sum (s:=L\P) (fun x hx=>min_three_score free hq rank x (lw (mem_sdiff.mp hx).1))
  rw [sum_const_nat (fun _ _=>rfl),hc] at highs
  rw [sum_const_nat (fun _ _=>rfl),pc] at parents
  rw [sum_const_nat (fun _ _=>rfl),card_sdiff_of_subset pl,lc,pc] at rest
  have comp := sum_sdiff sub (f:=score)
  change (∑x∈L,score x)+_=_ at comp
  have comp' := sum_sdiff pl (f:=score)
  have space := weighted_rows (i:=4) (j:=5) free (by omega) (score:=score) (fun _ _=>le_rfl)
  rw [wc] at space
  change 24*34≤∑ x∈H,score x at highs
  change _≤∑ x∈L\P,score x at rest
  omega

theorem fifth_floor_strong {D V q v} (free : QFree D V q) (hq : 9≤q)
    (root : v∈V) (degree : ∀x∈V,8≤(outN D V x).card) : 39≤(ball D V v 5).card := by
  classical
  have b4 := fourth_floor free hq root degree
  have b3 := DiagonalEight.three25 (free.mono_bound (by omega : 8≤q)) degree root
  by_contra! low
  by_cases small : (ball D V v 4).card=33
  · let W := (ball D V v 4).erase v
    let H := (ball D V v 3).erase v
    have wv : W⊆V := (erase_subset _ _).trans ball_subset
    have hw : H⊆W := erase_subset_erase v (ball_mono_radius (by decide : 3≤4))
    have wc : W.card=32 := by dsimp [W]; rw [card_erase_of_mem (self_mem_ball root),small]
    have hc : H.card+1=(ball D V v 3).card := card_erase_add_one (self_mem_ball root)
    obtain ⟨A,ah,ac⟩ := exists_subset_card_eq (show 24≤H.card by omega)
    have diff := card_sdiff_add_card_eq_card (ball_mono_radius (D:=D) (W:=V) (u:=v) (by decide : 4≤5))
    have rank := minOut_prefix_erase (d:=3) free root (by omega : 4+1≤q) degree
      (show 3+(ball D V v 5 \ ball D V v 4).card≤8 by omega)
    exact dense32 (free.mono_set wv) hq wc rank (ah.trans hw) ac (fun x hx =>
      (degree x (wv (hw (ah hx)))).trans (card_le_card
        (outN_prefix_erase_root free root (by omega : 3+1≤q) (mem_of_mem_erase (ah hx)))))
  · have mono := card_le_card (ball_mono_radius (D:=D) (W:=V) (u:=v) (by decide : 4≤5))
    by_cases mid : (ball D V v 4).card≤37
    · have step := PrefixDegreeGrowth.small_rank_step (j:=4) (d:=4) free root (by omega) degree
        (by omega) (by decide) (by decide) (by omega) (by omega)
      change (ball D V v 4).card+8<(ball D V v 5).card+4 at step
      omega
    · have step := PrefixDegreeGrowth.small_rank_step (j:=4) (d:=5) free root (by omega) degree
        (by omega) (by decide) (by decide) (by omega) (by omega)
      change (ball D V v 4).card+8<(ball D V v 5).card+5 at step
      omega

theorem order_bound_strong {D V q} (free : QFree D V q) (hq : 9≤q) (live : V.Nonempty)
    (degree : ∀x∈V,8≤(outN D V x).card) : 71≤V.card := by
  have := card_ge_of_two_balls free (by omega : 4+5≤q)
    (fun _ hv=>fourth_floor free hq hv degree) (fun _ hv=>fifth_floor_strong free hq hv degree) live
  omega

/-- The previously checked degree-transfer rule transports the capacity
bound to every larger degree for which the deletion budget suffices. -/
@[aesop safe forward (immediate := [source]) (rule_sets := [CHGraphFamilies])]
theorem direct_window {p : CHRuleCatalog.Input} (source : CHRuleCatalog.Bad p) :
    9≤CHRuleCatalog.cutoff p → 8≤p.s → 70+p.s<p.n+8 := by
  have bound : GuardedFamilyRules.OrderBound 9 8 70 :=
    ⟨by decide,fun _ _ f live degree => order_bound_strong f (by decide) live degree⟩
  intro hq degree
  by_contra! size
  exact GuardedFamilyRules.forbidden source bound ⟨hq,degree,size⟩

attribute [aesop safe forward (immediate := [free,radii,sub,ordinary,marked]) (rule_sets := [CHGraphFamilies])] mixed_capacity
attribute [aesop safe forward (immediate := [free,root,dist,radii,degree,retain,ordinary,marked]) (rule_sets := [CHGraphFamilies])] prefix_capacity
attribute [aesop safe forward (immediate := [free,live,radii,left,right,move]) (rule_sets := [CHGraphFamilies])] strict_order
attribute [aesop safe forward (immediate := [free,root,hr,diag,dist,degree,many,small]) (rule_sets := [CHGraphFamilies])] full_layer
attribute [aesop safe forward (immediate := [free,sub,degree,small,room]) (rule_sets := [CHGraphFamilies])] exit_rows
attribute [aesop safe forward (immediate := [free,radii,paid]) (rule_sets := [CHGraphFamilies])] weighted_rows

#print axioms mixed_capacity
#print axioms prefix_capacity
#print axioms strict_order
#print axioms fifth_floor
#print axioms order_bound
#print axioms direct_window
#print axioms full_layer
#print axioms exit_rows
#print axioms forward_gain
#print axioms weighted_rows
#print axioms fourth_floor
#print axioms fifth_floor_strong
#print axioms order_bound_strong
end LeanCH.BR.RetainedMixedCapacity
