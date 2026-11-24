import checkpoints.shen_extension.ClosedHeadBank
namespace LeanCH.BR.ReturnBankEscape
open Finset BRq2 BRq3 BR45 BRsGen BankReachTransfer ClosedHeadBank

theorem two_step_entry {D V X C q d} (free : QFree D V q) (xv : X⊆V) (cv : C⊆V)
    (hq : 2≤q) (low : 0<d) (small : d≤q) (size : X.card≤2*d)
    (charge : ∀x∈X,outN D C x=∅ → d≤(outN D X x).card) :
    ∀x∈X,∃c∈C,c∈ball D V x 2 := by
  classical
  intro x xm
  by_contra! none
  have miss a (hit : a∈ball D V x 1) : outN D C a=∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro c cm
    exact none c (outN_subset cm) (ball_step hit (cv (outN_subset cm)) (mem_outN.mp cm).2)
  have one := charge x xm (miss x (self_mem_ball (xv xm)))
  have big := two_row_size free xv xm low small hq one (fun y ym=>charge y (outN_subset ym)
    (miss y (ball_of_adj (xv (outN_subset ym)) (mem_outN.mp ym).2)))
  omega

/-- In a four-layer window with a single return destination b, the
heads of b generate a closed part C of Y. Keep with Z only those Y rows
that miss C. They have many Z heads, and Z can lose only W. This bounds
the same retained carrier from both sides at degree two. -/
theorem window {D V X Y Z W q r b m} (free : QFree D V q)
    (xv : X⊆V) (yv : Y⊆V) (zv : Z⊆V) (yz : Disjoint Y Z)
    (hq : 5≤q) (dx : X.card=r) (dy : Y.card=r) (dz : Z.card+1=r)
    (quota : ∀x∈V,r≤(outN D V x).card) (xrow : ∀x∈X,outN D V x⊆X∪Y)
    (yrow : ∀y∈Y,outN D V y⊆(Y∪Z)∪{b}) (zrow : ∀z∈Z,outN D V z⊆((X∪Y)∪Z)∪W)
    (bx : b∈X) (parent : (inN D Y b).Nonempty)
    (missed : Y.card≤(outN D Y b).card+m) (guard : m+2≤q)
    (width : r≤q+3) (large : r≤2*(min q (r-m))) (fits : Z.card+m≤2*q)
    (paid : m+3≤r) (few : W.card+2≤r) : False := by
  classical
  obtain ⟨C,cy,head,closed,stopped⟩ := at_anchor free yv (xv bx) (show Y.card-(outN D Y b).card+2≤q by omega)
  have cv := cy.trans yv
  have hc := card_le_card head
  have diff := card_sdiff_add_card_eq_card cy
  have wc : (Y\C).card≤m := by omega
  obtain ⟨y,ym⟩ := parent
  have oy : y∈Y\C := mem_sdiff.mpr ⟨(mem_inN.mp ym).1,fun yc=>stopped y yc (mem_inN.mp ym).2⟩
  have room := card_pos.mpr (show (Y\C).Nonempty from ⟨y,oy⟩)
  have cz : Disjoint C Z := yz.mono_left cy
  have native x (xm : x∈V) := (show 2≤r by omega).trans (quota x xm)
  have stay c (cm : c∈C) : outN D V c⊆outN D (C∪Z) c := by
    intro a am
    have arc := (mem_outN.mp am).2
    rcases mem_union.mp (yrow c (cy cm) am) with early|ab
    · rcases mem_union.mp early with ay|az
      · exact mem_outN.mpr ⟨mem_union_left _ (closed c cm (mem_outN.mpr ⟨ay,arc⟩)),arc⟩
      · exact mem_outN.mpr ⟨mem_union_right _ az,arc⟩
    · exact (stopped c cm ((mem_singleton.mp ab) ▸ arc)).elim
  have pay c (cm : c∈C) : Z.card+1≤(outN D (C∪Z) c).card :=
    dz ▸ (quota c (cv cm)).trans (card_le_card (stay c cm))
  have way := reaches_bank (k:=1) free (by omega) cv zv cz native pay (by omega) (by omega) (by omega)
  have c_to_z c (cm : c∈C) z (zm : z∈Z) : z∈ball D V c 2 := by
    obtain ⟨i,_,le,p⟩ := way c cm z zm
    exact mem_ball.mpr ⟨zv zm,i,le,p⟩
  have entry := two_step_entry (d:=min q (r-m)) free xv cv (by omega) (by omega) (min_le_left _ _)
    (by omega) (by
      intro x xm off
      have oo := quota x (xv xm)
      have sub : outN D V x⊆outN D X x ∪ (Y\C) := by
        intro a am
        have arc := (mem_outN.mp am).2
        rcases mem_union.mp (xrow x xm am) with ax|ay
        · exact mem_union_left _ (mem_outN.mpr ⟨ax,arc⟩)
        · refine mem_union_right _ (mem_sdiff.mpr ⟨ay,fun cc=>?_⟩)
          exact notMem_empty a (off ▸ mem_outN.mpr ⟨cc,arc⟩)
      have count := (card_le_card sub).trans (card_union_le _ _)
      omega)
  let S := Y.filter (fun y=>outN D C y=∅)
  have sc : S⊆Y\C := by
    intro a am
    obtain ⟨ay,empty⟩ := mem_filter.mp am
    refine mem_sdiff.mpr ⟨ay,fun ac=>?_⟩
    have deg := pay a ac
    rw [card_outN_union cz,empty,card_empty,zero_add] at deg
    have := card_le_card (outN_subset : outN D Z a⊆Z)
    omega
  have hs := card_le_card sc
  have newRank a (am : a∈Z∪S) : 2≤(outN D (Z∪S) a).card := by
    rcases mem_union.mp am with az|as'
    · have sub : outN D V a⊆outN D (Z∪S) a ∪ W := by
        intro v vm
        have arc := (mem_outN.mp vm).2
        rcases mem_union.mp (zrow a az vm) with early|last
        · apply mem_union_left
          apply mem_outN.mpr
          refine ⟨?_,arc⟩
          rcases mem_union.mp early with xy'|vz
          · rcases mem_union.mp xy' with vx|vy
            · obtain ⟨c,cm,via⟩ := entry v vx
              exact (no_back_arc free (xv vx) (ball_trans via (c_to_z c cm a az)) (by omega) arc).elim
            · apply mem_union_right
              refine mem_filter.mpr ⟨vy,eq_empty_iff_forall_notMem.mpr ?_⟩
              intro c cm
              have via := ball_of_adj (cv (outN_subset cm)) (mem_outN.mp cm).2
              exact no_back_arc free (yv vy) (ball_trans via (c_to_z c (outN_subset cm) a az)) (by omega) arc
          · exact mem_union_left _ vz
        · exact mem_union_right _ last
      have count := (card_le_card sub).trans (card_union_le _ _)
      have := quota a (zv az)
      omega
    · obtain ⟨ay,off⟩ := mem_filter.mp as'
      have sub : outN D V a⊆outN D (Z∪S) a ∪ ((Y\C)∪{b}) := by
        intro v vm
        have arc := (mem_outN.mp vm).2
        rcases mem_union.mp (yrow a ay vm) with yz'|vb
        · rcases mem_union.mp yz' with vy|vz
          · refine mem_union_right _ (mem_union_left _ (mem_sdiff.mpr ⟨vy,fun vc=>?_⟩))
            exact notMem_empty v (off ▸ mem_outN.mpr ⟨vc,arc⟩)
          · exact mem_union_left _ (mem_outN.mpr ⟨mem_union_left _ vz,arc⟩)
        · exact mem_union_right _ (mem_union_right _ vb)
      have total := (card_le_card sub).trans (card_union_le _ _)
      have lim := card_union_le (Y\C) {b}
      rw [card_singleton] at lim
      have := quota a (yv ay)
      omega
  have bound := corB (by omega : 1≤q) (free.mono_set (union_subset zv ((sc.trans sdiff_subset).trans yv))) newRank
    ((card_pos.mp (by omega : 0<Z.card)).mono subset_union_left)
  have := card_union_le Z S
  omega

attribute [aesop safe forward (immediate := [free,xv,cv,hq,low,small,size,charge])
  (rule_sets := [CHGraphFamilies])] two_step_entry
attribute [aesop safe forward (immediate := [free,xv,yv,zv,yz,hq,dx,dy,dz,quota,xrow,yrow,zrow,bx,parent,missed,guard,width,large,fits,paid,few])
  (rule_sets := [CHGraphFamilies])] window
#print axioms two_step_entry
#print axioms window
end LeanCH.BR.ReturnBankEscape
