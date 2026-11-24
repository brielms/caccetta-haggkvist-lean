import checkpoints.shen_extension.SingleOmissionPartition
import checkpoints.shen_extension.ExtremalSinkReturn
namespace LeanCH.BR.OneOmissionSinkBank
open Finset BRq2 BRq3 BR45 BRsGen SinkReturnAncestors

/-- The single-omission expansion at the tighter cutoff. Each retained
second-shell sink fills Z. The two possible origins of a discarded
second-shell label both give returns too short to let Z point to it. -/
theorem boundary_expansion {D V X Y Z W q r} (free : QFree D V q) (xv : X⊆V)
    (yv : Y⊆V) (zv : Z⊆V) (apart : Disjoint X Y) (yz : Disjoint Y Z)
    (hr : 7≤r) (time : r+1≤q) (dx : X.card=r) (dy : Y.card=r+1) (dz : Z.card≤r)
    (degree : ∀v∈V,r≤(outN D V v).card)
    (first : ∀x∈X,outN D V x⊆X∪Y) (second : ∀y∈Y,outN D V y⊆(X∪Y)∪Z)
    (third : ∀z∈Z,outN D V z⊆((X∪Y)∪Z)∪W) : r≤W.card := by
  classical
  have quota x (xm : x∈X) : r≤(outN D (X∪Y) x).card := by
    apply (degree x (xv xm)).trans (card_le_card ?_)
    exact fun a am=>mem_outN.mpr ⟨first x xm am,(mem_outN.mp am).2⟩
  have budget s (sx : s∈X) (sink : Sink D X s) : (Y\outN D V s).card≤1 := by
    have sub : outN D V s⊆Y := fun a am=>(mem_union.mp (first s sx am)).resolve_left
      (fun ax=>sink a ax (mem_outN.mp am).2)
    rw [card_sdiff_of_subset sub]
    have := degree s (xv sx)
    omega
  obtain ⟨E,ey,oe,cap,avoid,access,origin⟩ := partition free xv yv apart dx dy time hr budget quota
  let A := Y\E
  have ay : A⊆Y := sdiff_subset
  have av := ay.trans yv
  have keep t (ta : t∈A) : outN D V t⊆A∪Z := by
    intro a am
    rcases mem_union.mp (second t (ay ta) am) with early|az
    · apply mem_union_left
      rcases mem_union.mp early with ax|amem
      · exact ((mem_sdiff.mp ta).2 (oe (mem_filter.mpr ⟨ay ta,a,mem_outN.mpr ⟨ax,(mem_outN.mp am).2⟩⟩))).elim
      · exact mem_sdiff.mpr ⟨amem,fun ae=>avoid t ta a ae (mem_outN.mp am).2⟩
    · exact mem_union_right _ az
  have covers t (ta : t∈A) (stop : Sink D A t) : outN D V t=Z :=
    eq_of_subset_of_card_le (fun a am=>(mem_union.mp (keep t ta am)).resolve_left
      (fun aa=>stop a aa (mem_outN.mp am).2)) (dz.trans (degree t (av ta)))
  have transit x (xm : x∈X) := quick_sink free xv yv apart dx dy time hr xm (quota x xm) budget cap access
  obtain ⟨x,xm⟩ := card_pos.mp (by omega : 0<X.card)
  obtain ⟨s,sa,stop,_⟩ := transit x xm
  have paid := degree s (av sa)
  rw [covers s sa stop] at paid
  have head t (ta : t∈A) (ss : Sink D A t) z (zm : z∈Z) : D t z=true :=
    (mem_outN.mp ((covers t ta ss).symm ▸ zm)).2
  apply ExtremalSinkReturn.exit_bank free av zv (yz.mono_left ay)
    ((card_le_card ay).trans (by omega)) _ (by omega) (by omega) (by omega) _
    (fun z zm=>degree z (zv zm))
  · intro v vm
    apply (degree v (av vm)).trans (card_le_card ?_)
    exact fun a am=>mem_outN.mpr ⟨keep v vm am,(mem_outN.mp am).2⟩
  · intro z zm a am
    have arc := (mem_outN.mp am).2
    rcases mem_union.mp (third z zm am) with early|aw
    · apply mem_union_left
      rcases mem_union.mp early with prior|az
      · apply mem_union_left
        rcases mem_union.mp prior with ax|ay'
        · obtain ⟨t,ta,ss,k,le,walk⟩ := transit a ax
          exact (free a _ (by omega) (by omega) ((walk.snoc (zv zm) (head t ta ss z zm)).snoc (xv ax) arc)).elim
        · apply mem_sdiff.mpr ⟨ay',?_⟩
          intro ae
          rcases origin a ae with ⟨v,vm,toV⟩|⟨b,bm,v,vm,ab,bv,all⟩
          · obtain ⟨t,ta,ss,k,le,walk⟩ := transit v vm
            exact free v _ (by omega) (by omega) (((walk.snoc (zv zm) (head t ta ss z zm)).snoc (yv ay') arc).snoc (xv vm) toV)
          · exact free v 5 (by decide) (by omega) (.step (av sa) (mem_outN.mp (all sa)).2
              (.step (zv zm) (head s sa stop z zm) (.step (yv ay') arc (.step (yv bm) ab (.step (xv vm) bv (.refl v))))))
      · exact mem_union_right _ az
    · exact mem_union_right _ aw

theorem fourth_at_boundary {D V q r u} (free : QFree D V q) (root : u∈V)
    (degree : ∀v∈V,r≤(outN D V v).card)
    (hr : 7≤r) (time : r+1≤q) (row : (outN D V u).card=r)
    (width : (N2 D V u).card=r+1) (thirdSize : (N3 D V u).card≤r) :
    r≤(ball D V u 4\ball D V u 3).card := by
  have ff := free.mono_bound (show 4≤q by omega)
  apply boundary_expansion free outN_subset (fun _ h=>N2_subV h) (fun _ h=>N3_subV h)
    disjXY (disjoint_left.mpr (fun _ hy hz=>(mem_N3.mp hz).2 (mem_N2.mp hy).1)) hr time row width thirdSize degree
  · exact fun _ xm _ am=>headX ff root xm (outN_subset am) (mem_outN.mp am).2
  · exact fun _ ym _ am=>mem_union.mpr (headY ff root ym (outN_subset am) (mem_outN.mp am).2)
  · intro z zm a am
    have arc := (mem_outN.mp am).2
    have a4 := ball_step (mem_N3.mp zm).1 (outN_subset am) arc
    by_cases a3 : a∈ball D V u 3
    · apply mem_union_left
      by_cases a2 : a∈ball D V u 2
      · apply mem_union_left
        by_cases a1 : a∈ball D V u 1
        · exact mem_union_left _ (((mem_ball_one root).mp a1).resolve_left
            (fun eq=>no_back_arc free root (mem_N3.mp zm).1 (by omega) (eq ▸ arc)))
        · exact mem_union_right _ (mem_sdiff.mpr ⟨a2,a1⟩)
      · exact mem_union_right _ (mem_sdiff.mpr ⟨a3,a2⟩)
    · exact mem_union_right _ (mem_sdiff.mpr ⟨a4,a3⟩)

attribute [aesop safe forward (immediate := [free,xv,yv,zv,apart,yz,hr,time,dx,dy,dz,degree,first,second,third]) (rule_sets := [CHGraphFamilies])] boundary_expansion
attribute [aesop safe forward (immediate := [free,root,degree,hr,time,row,width,thirdSize]) (rule_sets := [CHGraphFamilies])] fourth_at_boundary
#print axioms fourth_at_boundary
#print axioms boundary_expansion
end LeanCH.BR.OneOmissionSinkBank
