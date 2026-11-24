import checkpoints.shen_extension.ShellCycleSupply

namespace LeanCH.BR.ShellCycleSupply
open Finset BRq2 BRq3 BR45 BRsGen ExteriorPacking BankReachTransfer

/-- At equal first and second shells the two alternatives remember the actual
first-shell vertex. At a sink both the second and the third ball stay in the
exterior. With no sink each cycle row covers the second shell within two. -/
theorem equal_rows_marked {D V q r u} (free : QFree D V q) (hq : 4≤q) (hr : 5≤r)
    (fit : r≤q+1) (reg : OutEq r D V) (uv : u∈V) (ys : (N2 D V u).card=r)
    (zs : (N3 D V u).card+1=r) :
    (∃s∈outN D V u, outN D V s=N2 D V u ∧ (ball D V s 2).card≤2*r ∧
      (ball D V s 3).card+r≤(ball D V u 4).card) ∨
    ∀w∈outN D V u, Rooted D V w (outN D V u) ∧
      4+r+((ball D V u 4).card-(ball D V u 2).card)≤(ball D V w 3).card := by
  classical
  let X := outN D V u
  let Y := N2 D V u
  let Z := N3 D V u
  have xv : X⊆V := outN_subset
  have yv : Y⊆V := fun _ h=>N2_subV h
  have zv : Z⊆V := fun _ h=>N3_subV h
  have xd : X.card=r := reg u uv
  have f4 := free.mono_bound hq
  have bank := EqualShellEscape.flat_exit free hq hr fit reg uv ys zs
  have sumX (x) (xm : x∈X) : (outN D X x).card+(outN D Y x).card=r := by
    have row := reg x (xv xm)
    rwa [outN_X_eq f4 uv xm,card_outN_union disjXY] at row
  have intoY (x) (xm : x∈X) : (outN D Y x).Nonempty := by
    have part := sumX x xm
    have off : outN D X x ⊆ X.erase x := by
      intro a am
      exact mem_erase.mpr ⟨fun e=>loopfree free (by omega) (xv xm) (e ▸ (mem_outN.mp am).2),outN_subset am⟩
    have count := card_le_card off
    rw [card_erase_of_mem xm,xd] at count
    exact card_pos.mp (by omega)
  have zseen (w) (wm : w∈X) : Z⊆ball D V w 2 := by
    obtain ⟨y,hy⟩ := intoY w wm
    intro z zm
    exact ball_step (ball_of_adj (yv (outN_subset hy)) (mem_outN.mp hy).2) (zv zm) ((bank y (outN_subset hy)).2 z zm)
  have internalY (y) (ym : y∈Y) : 1≤(outN D Y y).card := by
    have inc : outN D V y⊆outN D Y y∪Z := by
      intro a am
      rcases mem_union.mp ((bank y ym).1 am) with ya|za
      · exact mem_union_left _ (mem_outN.mpr ⟨ya,(mem_outN.mp am).2⟩)
      · exact mem_union_right _ za
    have lim := (card_le_card inc).trans (card_union_le _ _)
    rw [reg y (yv ym)] at lim
    change Z.card+1=r at zs
    omega
  by_cases inner : ∀x∈X,1≤(outN D X x).card
  · right
    have parents y (ym : y∈Y) : (inN D Y y).Nonempty := by
      have small : Y.card≤q+1 := ys.le.trans fit
      have large : q<Y.card := by
        by_contra! stop
        obtain ⟨a,am,sink⟩ := exists_sink (free.mono_set yv) ⟨y,ym⟩ stop
        obtain ⟨b,bm⟩ := card_pos.mp (internalY a am)
        exact sink b (outN_subset bm) (mem_outN.mp bm).2
      have laws := dt_reg (by omega : 1≤q) (ball_q_one q (by omega))
        (free.mono_set yv) internalY (show Y.card=q*1+1 by omega)
      exact card_pos.mp (by rw [laws.2 y ym]; decide)
    intro w wm
    have cr := rooted_on_small_set free (by omega) xv (xd.le.trans fit) inner wm
    refine ⟨cr,?_⟩
    have row := sumX w wm
    rw [cr.one w wm] at row
    have yseen : Y⊆ball D V w 2 := by
      intro y ym
      by_cases hit : y∈outN D Y w
      · exact ball_mono_radius (by decide : 1≤2) (ball_of_adj (yv ym) (mem_outN.mp hit).2)
      obtain ⟨b,bm⟩ := parents y ym
      have eq : outN D Y w=Y.erase y := eq_of_subset_of_card_le
        (fun a h=>mem_erase.mpr ⟨fun e=>hit (e ▸ h),outN_subset h⟩)
        (by rw [card_erase_of_mem ym]; change Y.card=r at ys; omega)
      have byNe : b≠y := fun eq=>loopfree free (by omega) (yv ym) (eq ▸ (mem_inN.mp bm).2)
      have head : b∈outN D Y w := eq.symm ▸ mem_erase.mpr ⟨byNe,(mem_inN.mp bm).1⟩
      exact ball_step (ball_of_adj (yv (outN_subset head)) (mem_outN.mp head).2) (yv ym) (mem_inN.mp bm).2
    let A := ball D X w 3 ∪ Y
    have av : A⊆ball D V u 2 := union_subset
      (fun _ h=>ball_mono_radius (by decide : 1≤2) (X_B1 (ball_subset h))) (fun _ h=>(mem_N2.mp h).1)
    have aw : A⊆ball D V w 3 := union_subset (lift_ball xv)
      (fun a am=>ball_mono_radius (by decide : 2≤3) (yseen am))
    have bill := count_with_prefix (j:=2) (d:=2) (k:=1) uv av aw (zseen w wm)
    have cA : A.card=(ball D X w 3).card+Y.card := card_union_of_disjoint (disjXY.mono_left ball_subset)
    have walk := ball_one_growth (free.mono_set xv) inner wm 3 (by omega)
    change A.card+((ball D V u 4).card-(ball D V u 2).card)≤(ball D V w 3).card at bill
    change Y.card=r at ys
    omega
  · left
    push Not at inner
    obtain ⟨s,sm,no⟩ := inner
    have sum := sumX s sm
    have covers : outN D Y s=Y := eq_of_subset_of_card_le outN_subset (by change Y.card=r at ys; omega)
    have actual : outN D V s=Y := by
      apply (eq_of_subset_of_card_le (s:=Y) (t:=outN D V s) ?_ ?_).symm
      · rw [←covers]; exact outN_mono yv s
      · rw [reg s (xv sm)]; exact ys.ge
    have includes : ball D V s 2⊆insert s (Y∪Z) := by
      intro a am
      by_cases short : a∈ball D V s 1
      · rcases (mem_ball_one (xv sm)).mp short with eq|head
        · exact mem_insert.mpr (.inl eq)
        · exact mem_insert_of_mem (mem_union_left _ (actual ▸ head))
      obtain ⟨b,bm,edge⟩ := ball_succ_pred (xv sm) am short
      rcases (mem_ball_one (xv sm)).mp bm with eq|head
      · subst b
        exact (short (ball_of_adj (ball_subset am) edge)).elim
      · rw [actual] at head
        exact mem_insert_of_mem ((bank b head).1 (mem_outN.mpr ⟨ball_subset am,edge⟩))
    have ub := (card_le_card includes).trans (card_insert_le s (Y∪Z))
    have yz := card_union_le Y Z
    change Y.card=r at ys
    change Z.card+1=r at zs
    refine ⟨s,sm,actual,by omega,?_⟩
    let E := ball D V u 4 \ ball D V u 1
    have wide : ball D V s 3⊆insert s E := by
      intro a am
      by_cases as' : a=s
      · exact mem_insert.mpr (.inl as')
      apply mem_insert_of_mem
      have outer : a∈ball D V u 4 := by
        obtain ⟨av,l,fit,path⟩ := mem_ball.mp am
        exact mem_ball.mpr ⟨av,1+l,by omega,by simpa [Nat.add_comm] using
          (Walk.step (xv sm) (mem_outN.mp sm).2 path)⟩
      refine mem_sdiff.mpr ⟨outer,?_⟩
      intro early
      by_cases b2 : a∈ball D V s 2
      · have outside := (mem_insert.mp (includes b2)).resolve_left as'
        rcases mem_union.mp outside with yy|zz
        · exact (mem_N2.mp yy).2 early
        · exact (mem_N3.mp zz).2 (ball_mono_radius (by decide : 1≤2) early)
      obtain ⟨b,bm,ba⟩ := ball_succ_pred (xv sm) am b2
      rcases mem_insert.mp (includes bm) with eq|far
      · subst b
        exact b2 (ball_mono_radius (by decide : 1≤2) (ball_of_adj (ball_subset am) ba))
      rcases mem_union.mp far with yy|zz
      · rcases mem_union.mp ((bank b yy).1 (mem_outN.mpr ⟨ball_subset am,ba⟩)) with ay|az
        · exact (mem_N2.mp ay).2 early
        · exact (mem_N3.mp az).2 (ball_mono_radius (by decide : 1≤2) early)
      · rcases (mem_ball_one uv).mp early with eq|ax
        · subst a
          exact no_back_arc free uv (mem_N3.mp zz).1 (by omega : 3+1≤q) ba
        · obtain ⟨_,l,fit,path⟩ := mem_ball.mp (zseen _ ax zz)
          exact free _ _ (by omega) (by omega) (path.snoc (ball_subset am) ba)
    have lim := (card_le_card wide).trans (card_insert_le s E)
    have cardE : E.card+(ball D V u 1).card=(ball D V u 4).card :=
      card_sdiff_add_card_eq_card (ball_mono_radius (by decide : 1≤4))
    have := card_B1 f4 uv
    have du := reg u uv
    omega

theorem equal_rows {D V q r u} (free : QFree D V q) (hq : 4≤q) (hr : 5≤r)
    (fit : r≤q+1) (reg : OutEq r D V) (uv : u∈V) (ys : (N2 D V u).card=r)
    (zs : (N3 D V u).card+1=r) :
    (∃s∈outN D V u, (ball D V s 2).card≤2*r ∧
      (ball D V s 3).card+r≤(ball D V u 4).card) ∨
    ∀w∈outN D V u, Rooted D V w (outN D V u) ∧
      4+r+((ball D V u 4).card-(ball D V u 2).card)≤(ball D V w 3).card := by
  rcases equal_rows_marked free hq hr fit reg uv ys zs with ⟨s,sm,_,two,three⟩|rows
  · exact Or.inl ⟨s,sm,two,three⟩
  · exact Or.inr rows

attribute [aesop safe forward (immediate := [free,hq,hr,fit,reg,uv,ys,zs])
  (rule_sets := [CHGraphFamilies])] equal_rows

#print axioms equal_rows_marked
#print axioms equal_rows
end LeanCH.BR.ShellCycleSupply
