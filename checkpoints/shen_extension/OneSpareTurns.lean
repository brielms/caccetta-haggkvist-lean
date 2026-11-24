import checkpoints.shen_extension.OneSpareGrowth

namespace LeanCH.BR.OneSpareGrowth
open Finset BRq2 BRq3 BR45 BRsGen

theorem internal_positive {D V q r u a} (free : QFree D V q) (hq : 4≤q)
    (uv : u∈V) (reg : OutEq r D V) (short : (N2 D V u).card+1=r)
    (ax : a∈outN D V u) : 0<(outN D (outN D V u) a).card := by
  have sum := reg a (outN_subset ax)
  rw [outN_X_eq (free.mono_bound hq) uv ax,card_outN_union disjXY] at sum
  have cap := card_le_card (outN_subset : outN D (N2 D V u) a⊆N2 D V u)
  omega

theorem sends_layer {D V q r u a} (free : QFree D V q) (hq : 4≤q)
    (uv : u∈V) (reg : OutEq r D V) (short : (N2 D V u).card+1=r)
    (ax : a∈outN D V u) (one : (outN D (outN D V u) a).card=1) :
    ∀y∈N2 D V u,D a y=true := by
  have sum := reg a (outN_subset ax)
  rw [outN_X_eq (free.mono_bound hq) uv ax,card_outN_union disjXY,one] at sum
  have eq : outN D (N2 D V u) a=N2 D V u := eq_of_subset_of_card_le outN_subset (by omega)
  intro y ym
  exact (mem_outN.mp (show y∈outN D (N2 D V u) a by rw [eq]; exact ym)).2

theorem third_parent {D V u z} (uv : u∈V) (zm : z∈N3 D V u) :
    ∃y∈N2 D V u,D y z=true := by
  obtain ⟨y,ym,edge⟩ := ball_succ_pred uv (mem_N3.mp zm).1 (mem_N3.mp zm).2
  exact ⟨y,mem_sdiff.mpr ⟨ym,fun low=>(mem_N3.mp zm).2 (ball_step low (N3_subV zm) edge)⟩,edge⟩

/-- If a row with one internal head is short, its successor has exactly one
internal head c, and every returning arc from layer two hits c. -/
theorem propagate {D V q r u a b} (free : QFree D V q) (hq : 4≤q)
    (uv : u∈V) (degree : OutEq r D V) (short : (N2 D V u).card+1=r)
    (floor : r≤(N3 D V u).card+2) (ax : a∈outN D V u)
    (turn : outN D (outN D V u) a={b}) (budget : (ball D V a 2).card≤2*r) :
    ∃c,outN D (outN D V u) b={c} ∧ (N3 D V u).card+2=r ∧
      ∀y∈N2 D V u,∀x∈outN D V u,D y x=true → x=c := by
  classical
  let X := outN D V u
  let Y := N2 D V u
  let Z := N3 D V u
  let H := outN D X b
  have f4 := free.mono_bound hq
  have av := outN_subset ax
  have ab' : b∈outN D X a := turn.symm ▸ mem_singleton_self b
  obtain ⟨bx,ab⟩ := mem_outN.mp ab'
  have bv := outN_subset bx
  have ne : a≠b := fun eq => n1 f4 av (eq ▸ ab)
  have allY := sends_layer free hq uv degree short ax (by rw [turn,card_singleton])
  have yy : Y⊆ball D V a 2 := fun y ym=>ball_mono_radius (by decide : 1≤2) (ball_of_adj (N2_subV ym) (allY y ym))
  have zz : Z⊆ball D V a 2 := by
    intro z zm
    obtain ⟨y,ym,yz⟩ := third_parent uv zm
    exact ball_step (ball_of_adj (N2_subV ym) (allY y ym)) (N3_subV zm) yz
  have disZY : Disjoint Y Z := disjoint_left.mpr (fun _ ym zm=>(mem_N3.mp zm).2 (mem_N2.mp ym).1)
  have disX : Disjoint (Y∪Z) X := by
    apply disjoint_left.mpr
    intro x hit xm
    rcases mem_union.mp hit with ym|zm
    · exact (mem_N2.mp ym).2 (X_B1 xm)
    · exact (mem_N3.mp zm).2 (ball_mono_radius (by decide : 1≤2) (X_B1 xm))
  have disH : Disjoint ({a,b} : Finset ℕ) H := by
    apply disjoint_left.mpr
    intro x xm hx
    rcases mem_insert.mp xm with eq|single
    · subst x
      exact n2 f4 av bv ab (mem_outN.mp hx).2
    · obtain rfl := mem_singleton.mp single
      exact n1 f4 bv (mem_outN.mp hx).2
  let K := ({a,b} : Finset ℕ) ∪ H
  have kx : K⊆X := union_subset (insert_subset ax (singleton_subset_iff.mpr bx)) outN_subset
  have da : Disjoint (Y∪Z) K := disX.mono_right kx
  have reach : (Y∪Z)∪K⊆ball D V a 2 := by
    apply union_subset (union_subset yy zz)
    apply union_subset (insert_subset (self_mem_ball av) (singleton_subset_iff.mpr
      (ball_mono_radius (by decide : 1≤2) (ball_of_adj bv ab))))
    intro c cm
    exact ball_step (ball_of_adj bv ab) (outN_subset (mem_outN.mp cm).1) (mem_outN.mp cm).2
  have size : ((Y∪Z)∪K).card=Y.card+Z.card+(2+H.card) := by
    rw [card_union_of_disjoint da,card_union_of_disjoint disZY]
    dsimp only [K]
    rw [card_union_of_disjoint disH,card_pair ne]
  have ysize : Y.card+1=r := short
  have zsize : r≤Z.card+2 := floor
  have hpos : 0<H.card := internal_positive free hq uv degree short bx
  have cap := (card_le_card reach).trans budget
  rw [size] at cap
  have hone : H.card=1 := by omega
  obtain ⟨c,cs⟩ := card_eq_one.mp hone
  have exactly : ball D V a 2=(Y∪Z)∪K :=
    (eq_of_subset_of_card_le reach (by rw [size]; omega)).symm
  have byAll := sends_layer free hq uv degree short bx hone
  refine ⟨c,cs,by change Z.card+2=r; omega,?_⟩
  intro y ym x xm yx
  have atRow : x∈ball D V a 2 := ball_step (ball_of_adj (N2_subV ym) (allY y ym)) (outN_subset xm) yx
  rw [exactly] at atRow
  rcases mem_union.mp atRow with bad|kk
  · exact (disjoint_left.mp disX bad xm).elim
  rcases mem_union.mp kk with abx|hc
  · rcases mem_insert.mp abx with eq|sing
    · subst x; exact (n2 f4 av (N2_subV ym) (allY y ym) yx).elim
    · obtain rfl := mem_singleton.mp sing
      exact (n2 f4 bv (N2_subV ym) (byAll y ym) yx).elim
  · exact mem_singleton.mp (cs ▸ hc)

#print axioms propagate

theorem tall_successor {D V q r u} (free : QFree D V q) (hq : 4≤q)
    (uv : u∈V) (degree : OutEq r D V) (pos : 2≤r) (room : r≤2*q)
    (short : (N2 D V u).card+1=r) (floor : r≤(N3 D V u).card+2) :
    ∃w∈outN D V u,2*r<(ball D V w 2).card ∧ (outN D (outN D V u) w).card=1 := by
  classical
  let X := outN D V u
  let Y := N2 D V u
  have f4 := free.mono_bound hq
  have xsize : X.card=r := degree u uv
  have thin : ∃a∈X,(outN D X a).card<2 := by
    by_contra! large
    have subV : X⊆V := outN_subset
    have xn : X.Nonempty := card_pos.mp (by omega)
    have bound : 2*q+1≤X.card := corB (by omega : 1≤q) (free.mono_set subV) large xn
    omega
  obtain ⟨a,ax,small⟩ := thin
  have apos : 0<(outN D X a).card := internal_positive free hq uv degree short ax
  have one : (outN D X a).card=1 := by omega
  by_cases tall : 2*r<(ball D V a 2).card
  · exact ⟨a,ax,tall,one⟩
  obtain ⟨b,ab⟩ := card_eq_one.mp one
  obtain ⟨c,bc,zsize,ret⟩ := propagate free hq uv degree short floor ax ab (by omega)
  have bx : b∈X := outN_subset (ab.symm ▸ mem_singleton_self b : b∈outN D X a)
  have cx : c∈X := outN_subset (bc.symm ▸ mem_singleton_self c : c∈outN D X b)
  have bone : (outN D X b).card=1 := by rw [bc,card_singleton]
  refine ⟨b,bx,?_,bone⟩
  by_contra! low
  obtain ⟨d,cd,_,again⟩ := propagate free hq uv degree short floor bx bc low
  have no : ∀y∈Y,∀x∈X,D y x≠true := by
    intro y ym x xm edge
    have first := ret y ym x xm edge
    have second := again y ym x xm edge
    have same : d=c := second.symm.trans first
    have loop : c∈outN D X c := by rw [cd,same]; exact mem_singleton_self c
    exact n1 f4 (outN_subset cx) (mem_outN.mp loop).2
  have internal (y) (ym : y∈Y) : 2≤(outN D Y y).card := by
    have sub : outN D V y⊆outN D Y y∪N3 D V u := by
      intro w wm
      obtain ⟨wv,yw⟩ := mem_outN.mp wm
      rcases headY f4 uv ym wv yw with hit|zm
      · rcases mem_union.mp hit with xm|inY
        · exact (no y ym w xm yw).elim
        · exact mem_union_left _ (mem_outN.mpr ⟨inY,yw⟩)
      · exact mem_union_right _ zm
    have cap := (card_le_card sub).trans (card_union_le _ _)
    rw [degree y (N2_subV ym)] at cap
    omega
  have yc : Y.card+1=r := short
  have bound := corB (by omega : 1≤q) (free.mono_set (fun _ (ym : _∈Y)=>N2_subV ym))
    internal (card_pos.mp (by omega))
  omega

/-- The uniform two-ball count excludes all orders below 4r. The condition
on r is exactly the local fragment budget used by the argument. -/
theorem below_four_times {D V q r} (free : QFree D V q) (hq : 4≤q)
    (live : V.Nonempty) (degree : ∀v∈V,r≤(outN D V v).card) (pos : 2≤r) (room : r≤2*q)
    (deficit : (r+(r-1))*(r+(r-1)+1)<2*(r*(r+3)+(r-1)*7)) : 4*r≤V.card := by
  classical
  obtain ⟨G,sub,reg⟩ := exists_outEq degree
  have gf := qfree_sub sub free
  have floor v (vm : v∈V) : 2*r≤(ball G V v 2).card := by
    have count := reg v vm
    have nn := second_layer gf hq vm (fun w wm=>(reg w wm).ge) (by omega) (by omega)
    rw [card_B2,card_B1 (gf.mono_bound hq) vm,count]
    omega
  have size := card_ge_of_two_balls gf (by omega : 2+2≤q) floor floor live
  by_contra! small
  have eq := two_balls_boundary_cards gf (by omega : 2+2≤q) floor floor (by omega)
  obtain ⟨v,vm⟩ := live
  have two := (eq v vm).1
  rw [card_B2,card_B1 (gf.mono_bound hq) vm,reg v vm] at two
  have short : (N2 G V v).card+1=r := by omega
  obtain ⟨w,wm,tall,_⟩ := tall_successor gf hq vm reg pos room short (third_layer gf hq vm reg room short deficit)
  have := (eq w (outN_subset wm)).1
  omega

#print axioms tall_successor
#print axioms below_four_times
end LeanCH.BR.OneSpareGrowth
