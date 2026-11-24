import checkpoints.shen_extension.RetainedLayerOrders
import LeanCH.BR.BREqualPair

namespace LeanCH.BR.EqualShellEscape
open Finset BRq2 BRq3 BR45 BRsGen OneSpareGrowth BankReachTransfer RetainedMixedCapacity RetainedLayerCapacity

/-- On at most q+1 labels a positive carrier has just one internal head
per row. The outgoing head remains a vertex of the same carrier. -/
theorem one_head {D X q} (free : QFree D X q) (hq : 1≤q) (small : X.card≤q+1)
    (positive : ∀w∈X,1≤(outN D X w).card) (w) (wx : w∈X) : (outN D X w).card=1 := by
  have p := positive w wx
  by_contra ne
  have cap := small_one_core_high_count hq free positive ⟨w,wx⟩ (by omega)
    (singleton_subset_iff.mpr wx) (fun y ym=>by
      obtain rfl := mem_singleton.mp ym
      omega)
  rw [card_singleton] at cap
  omega

private theorem lifted_ball {D V X w j} (sub : X⊆V) : ball D X w j⊆ball D V w j := by
  intro y ym
  obtain ⟨yx,l,fit,path⟩ := mem_ball.mp ym
  exact mem_ball.mpr ⟨sub yx,l,fit,path.mono sub⟩

/-- Under simultaneous equality of the two global radius bounds, the
only possible second ball has two equal shells. -/
theorem second_flat {D V q r} (free : QFree D V q) (hq : 7≤q) (hr : 6≤r) (fit : r≤q+1)
    (reg : OutEq r D V) (flat3 : ∀x∈V,(ball D V x 3).card=3*r)
    (flat4 : ∀x∈V,(ball D V x 4).card=4*r-1) (u) (um : u∈V) :
    (ball D V u 2).card=2*r+1 := by
  let X := outN D V u
  have xv : X⊆V := outN_subset
  have deg x (xm : x∈V) := (reg x xm).ge
  have xsize : X.card=r := reg u um
  have base := GuardedLayerGrowth.second_floor free (by omega : 4≤q) reg (by omega : 0<r) (by omega) um
  have three := flat3 u um
  have four := flat4 u um
  have one := card_B1 (free.mono_bound (by omega : 4≤q)) um
  have ru := reg u um
  by_cases low : (ball D V u 2).card=2*r
  · have b := @card_B2 D V u
    have short : (N2 D V u).card+1=r := by omega
    have pos x (h : x∈X) := internal_positive free (by omega : 4≤q) um reg short h
    have light := LocalBallTransfer.light_supply (free.mono_set xv) (by omega)
      (card_pos.mp (by omega : 0<X.card)) pos (by omega)
    obtain ⟨w,hit⟩ := card_pos.mp (show 0<(X.filter (fun w=>(outN D X w).card=1)).card by omega)
    obtain ⟨wx,oneW⟩ := mem_filter.mp hit
    have cover := sends_layer free (by omega : 4≤q) um reg short wx oneW
    have seen : N2 D V u ⊆ ball D V w 1 := fun y ym=>
      (mem_ball_one (xv wx)).mpr (Or.inr (mem_outN.mpr ⟨N2_subV ym,cover y ym⟩))
    have count := count_with_prefix (j:=1) (d:=1) (k:=2) um
      (show ball D X w 3⊆ball D V u 1 from fun _ h=>X_B1 (ball_subset h)) (lifted_ball xv) seen
    have growth := ball_one_growth (free.mono_set xv) pos wx 3 (by omega)
    change _+((ball D V u 4).card-(ball D V u 1).card)≤(ball D V w 3).card at count
    have := flat3 w (xv wx)
    omega
  by_cases mid : (ball D V u 2).card=2*r+2
  · let W := (ball D V u 2).erase u
    have sub : X⊆W := by
      rw [show X=(ball D V u 1).erase u from (erase_ball_one_eq_outN free (by omega) um).symm]
      exact erase_subset_erase _ (ball_mono_radius (by decide : 1≤2))
    have diff := card_sdiff_add_card_eq_card (ball_mono_radius (D:=D) (W:=V) (u:=u) (by decide : 2≤3))
    have rr := minOut_prefix_erase (d:=2) free um (by omega : 2+1≤q) deg
      (show 2+(ball D V u 3 \ ball D V u 2).card≤r by omega)
    exact False.elim (high_half_two_core_false (by omega : 5≤r)
      ((free.mono_bound (by omega : r-1≤q)).mono_set (show W⊆V from (erase_subset _ _).trans ball_subset))
      (by dsimp [W]; rw [card_erase_of_mem (self_mem_ball um),mid]; omega) rr sub xsize
      (fun x xm=>(deg x (xv xm)).trans (card_le_card
        (outN_prefix_erase_root free um (by omega : 1+1≤q) (X_B1 xm)))))
  by_contra miss
  have grow := PrefixDegreeGrowth.raise_floor (j:=2) (lo:=2*r+3) (target:=3*r+1)
    free um (by omega) deg (by omega) (by omega) (by omega) (by
      intro m lo hi
      by_cases fit : m≤3*q+1
      · exact ⟨3,by decide,by decide,by omega,by omega⟩
      · exact ⟨4,by decide,by decide,by omega,by omega⟩)
  change 3*r+1≤(ball D V u 3).card at grow
  omega

/-- When the first two shells each have r labels and the next has r-1,
no return from the second shell is possible. Its rows have one internal
head and cover the entire third shell. -/
theorem flat_exit {D V q r u} (free : QFree D V q) (hq : 4≤q) (hr : 5≤r)
    (fit : r≤q+1) (reg : OutEq r D V) (um : u∈V)
    (ys : (N2 D V u).card=r) (zs : (N3 D V u).card+1=r) :
    ∀y∈N2 D V u, outN D V y⊆N2 D V u∪N3 D V u ∧ ∀z∈N3 D V u,D y z=true := by
  let X := outN D V u
  let Y := N2 D V u
  let Z := N3 D V u
  have sub : X∪Y⊆V := union_subset outN_subset (fun _ ym=>N2_subV ym)
  have f4 := free.mono_bound hq
  have live y (ym : y∈Y) : 1≤(outN D (X∪Y) y).card := by
    have cover : outN D V y⊆outN D (X∪Y) y ∪ Z := by
      intro w wm
      rcases headY f4 um ym (outN_subset wm) (mem_outN.mp wm).2 with hit|last
      · exact mem_union_left _ (mem_outN.mpr ⟨hit,(mem_outN.mp wm).2⟩)
      · exact mem_union_right _ last
    have count := (card_le_card cover).trans (card_union_le _ _)
    rw [reg y (N2_subV ym)] at count
    dsimp [Z] at count
    omega
  have no := equal_pair_no_back hr ((free.mono_bound (by omega : r-1≤q)).mono_set sub)
    (disjXY (E:=D) (V:=V) (u:=u)) (reg u um) ys
    (fun x xm=>by rw [←outN_X_eq f4 um xm,reg x (outN_subset xm)]) live
  have only y (ym : y∈Y) : outN D V y⊆Y∪Z := by
    intro w wm
    rcases headY f4 um ym (outN_subset wm) (mem_outN.mp wm).2 with hit|last
    · rcases mem_union.mp hit with xx|yy
      · exact (no y ym w xx (mem_outN.mp wm).2).elim
      · exact mem_union_left _ yy
    · exact mem_union_right _ last
  have positive y (ym : y∈Y) : 1≤(outN D Y y).card := by
    have count := live y ym
    have eq : outN D X y=∅ := eq_empty_iff_forall_notMem.mpr (fun w wm=>
      no y ym w (outN_subset wm) (mem_outN.mp wm).2)
    rw [card_outN_union disjXY,eq,card_empty,Nat.zero_add] at count
    exact count
  intro y ym
  have one := one_head (free.mono_set (show Y⊆V from fun _ m=>N2_subV m)) (by omega)
    (ys.le.trans fit) positive y ym
  have all : outN D V y=outN D (Y∪Z) y := Subset.antisymm (fun w h=>mem_outN.mpr
    ⟨only y ym h,(mem_outN.mp h).2⟩) (outN_mono (union_subset (fun _ m=>N2_subV m) (fun _ m=>N3_subV m)) _)
  have count := reg y (N2_subV ym)
  have yz : Disjoint Y Z := disjoint_left.mpr (fun _ a b=>(mem_N3.mp b).2 (mem_N2.mp a).1)
  rw [all,card_outN_union yz,one] at count
  have full : outN D Z y=Z := eq_of_subset_of_card_le outN_subset (by dsimp [Z] at *; omega)
  exact ⟨only y ym,fun z zm=>(mem_outN.mp (full.symm ▸ zm : z∈outN D Z y)).2⟩

attribute [aesop safe forward (immediate := [free,hq,small,positive,wx])
  (rule_sets := [CHGraphFamilies])] one_head
attribute [aesop safe forward (immediate := [free,hq,hr,fit,reg,flat3,flat4,um])
  (rule_sets := [CHGraphFamilies])] second_flat
attribute [aesop safe forward (immediate := [free,hq,hr,fit,reg,um,ys,zs])
  (rule_sets := [CHGraphFamilies])] flat_exit

/-- A flat (2,3,4) profile would force a first-shell sink, or a row with
one internal head. The sink has too small a two-ball. The other row
retains three internal steps together with the third and fourth shells. -/
theorem flat_impossible {D V q r} (free : QFree D V q) (hq : 7≤q) (hr : 6≤r) (fit : r≤q+1)
    (reg : OutEq r D V) (live : V.Nonempty) (flat3 : ∀x∈V,(ball D V x 3).card=3*r)
    (flat4 : ∀x∈V,(ball D V x 4).card=4*r-1) : False := by
  classical
  obtain ⟨u,um⟩ := live
  let X := outN D V u
  let Y := N2 D V u
  let Z := N3 D V u
  have xv : X⊆V := outN_subset
  have yv : Y⊆V := fun _ ym=>N2_subV ym
  have zv : Z⊆V := fun _ zm=>N3_subV zm
  have f4 := free.mono_bound (by omega : 4≤q)
  have sec x (xm : x∈V) := second_flat free hq hr fit reg flat3 flat4 x xm
  have cur := sec u um
  have third := flat3 u um
  have fourth := flat4 u um
  have b1 := card_B1 f4 um
  have b2 := @card_B2 D V u
  have b3 := @card_B3 D V u
  have degree := reg u um
  have ys : Y.card=r := by dsimp [Y]; omega
  have zs : Z.card+1=r := by dsimp [Z]; omega
  have escort := flat_exit free (by omega) (by omega) fit reg um ys zs
  have high (w) (wx : w∈X) : (outN D X w).card+(outN D Y w).card=r := by
    have sum := reg w (xv wx)
    rwa [outN_X_eq f4 um wx,card_outN_union disjXY] at sum
  have pos (w) (wx : w∈X) : 1≤(outN D X w).card := by
    by_contra! none
    have sum := high w wx
    have all : outN D V w=Y := by
      have no := card_eq_zero.mp (show (outN D X w).card=0 by omega)
      have eq : outN D Y w=Y := eq_of_subset_of_card_le outN_subset (by omega)
      have pair : outN D (X∪Y) w=outN D X w ∪ outN D Y w := by
        ext v
        simp only [mem_outN,mem_union]
        tauto
      rw [outN_X_eq f4 um wx]
      change outN D (X∪Y) w=Y
      rw [pair,no,empty_union,eq]
    have bound : ball D V w 2⊆insert w (Y∪Z) := by
      intro t tm
      by_cases early : t∈ball D V w 1
      · rcases (mem_ball_one (xv wx)).mp early with rfl|head
        · exact mem_insert_self _ _
        · exact mem_insert_of_mem (mem_union_left _ (all ▸ head))
      obtain ⟨a,am,arc⟩ := ball_succ_pred (xv wx) tm early
      rcases (mem_ball_one (xv wx)).mp am with aw|head
      · subst a
        have hit : t∈outN D V w := mem_outN.mpr ⟨ball_subset tm,arc⟩
        rw [all] at hit
        exact mem_insert_of_mem (mem_union_left _ hit)
      · rw [all] at head
        exact mem_insert_of_mem ((escort _ head).1 (mem_outN.mpr ⟨ball_subset tm,arc⟩))
    have card := (card_le_card bound).trans (card_insert_le w (Y∪Z))
    have both := card_union_le Y Z
    have := sec w (xv wx)
    omega
  have nonempty : X.Nonempty := card_pos.mp (show 0<X.card by change 0<(outN D V u).card; omega)
  obtain ⟨w,wx⟩ := nonempty
  have one := one_head (free.mono_set xv) (by omega) (degree.le.trans fit) pos w wx
  have sum := high w wx
  have many : 0<(outN D Y w).card := by omega
  obtain ⟨y,ym⟩ := card_pos.mp many
  have yes : Z⊆ball D V w 2 := by
    intro z zm
    exact mem_ball.mpr ⟨zv zm,2,le_rfl,.step (yv (outN_subset ym)) (mem_outN.mp ym).2
      (.step (zv zm) ((escort y (outN_subset ym)).2 z zm) (.refl z))⟩
  let A := ball D X w 3 ∪ outN D Y w
  have a2 : A⊆ball D V u 2 := union_subset (fun _ m=>ball_mono_radius (by decide : 1≤2) (X_B1 (ball_subset m)))
    (fun _ m=>(mem_N2.mp (outN_subset m)).1)
  have a3 : A⊆ball D V w 3 := union_subset (lifted_ball xv) (fun _ m=>
    ball_mono_radius (by decide : 1≤3) (X_B1 ((outN_mono yv w) m)))
  have dis : Disjoint (ball D X w 3) (outN D Y w) := Disjoint.mono ball_subset outN_subset disjXY
  have bill := count_with_prefix (j:=2) (d:=2) (k:=1) um a2 a3 yes
  have aCard : A.card=(ball D X w 3).card+(outN D Y w).card := card_union_of_disjoint dis
  have inner := ball_one_growth (free.mono_set xv) pos wx 3 (by omega)
  change A.card+((ball D V u 4).card-(ball D V u 2).card)≤(ball D V w 3).card at bill
  have := flat3 w (xv wx)
  omega

theorem order_floor {D V q r} (free : QFree D V q) (hq : 7≤q) (hr : 6≤r)
    (fit : r≤q+1) (room : FourthRoom r) (live : V.Nonempty) (degree : ∀v∈V,r≤(outN D V v).card) :
    7*r-1≤V.card := by
  obtain ⟨F,sub,reg⟩ := exists_outEq degree
  have ff := qfree_sub sub free
  have a x (xm : x∈V) := diagonal_third (k:=q-2) ff xm reg hq (by omega) fit
    (by omega) (by omega) room.1
  have b x (xm : x∈V) := diagonal_fourth ff hq hr fit room reg xm
  have lo := diagonal_order free hq hr fit room live degree
  by_contra! small
  have exactRows := two_balls_boundary_cards ff (by omega : 3+4≤q) a b (by omega)
  exact flat_impossible ff hq hr fit reg live (fun x xm=>(exactRows x xm).1) (fun x xm=>(exactRows x xm).2.1)

attribute [aesop safe forward (immediate := [free,hq,hr,fit,reg,live,flat3,flat4])
  (rule_sets := [CHGraphFamilies])] flat_impossible
#print axioms flat_impossible
#print axioms order_floor

#print axioms one_head
#print axioms second_flat
#print axioms flat_exit
end LeanCH.BR.EqualShellEscape

