import checkpoints.shen_extension.MixedShellUniform
import checkpoints.shen_extension.SinkReturnAncestors
namespace LeanCH.BR.SinkBankReturn
open Finset BRq2 BRq3 BR45 BRsGen BankReachTransfer SinkReturnAncestors

/-- Every return from the second layer has the same destination when a
first-layer sink leaves one extra slot in its own two-ball. Charge its
actual internal heads separately from the complete fourth shell. -/
theorem single_target {D V q r u s} (free : QFree D V q) (hq : 4≤q) (reg : OutEq r D V)
    (root : u∈V) (sx : s∈outN D V u) (sink : Sink D (outN D V u) s)
    (width : (N2 D V u).card=r) (third : (N3 D V u).card+1=r)
    (second : (ball D V s 2).card=2*r+1) :
    let X := outN D V u
    let Y := N2 D V u
    let W := ball D V u 4\ball D V u 3
    ∃b∈X,b≠s ∧ (inN D Y b).Nonempty ∧
      (∀y∈Y,∀x∈X,D y x=true → x=b) ∧
      W.card+(outN D X b).card+2*r+1≤(ball D V s 3).card := by
  classical
  let X := outN D V u
  let Y := N2 D V u
  let Z := N3 D V u
  let W := ball D V u 4\ball D V u 3
  let K := (ball D V s 2).erase s
  have sv := outN_subset sx
  have xv : X⊆V := outN_subset
  have yv : Y⊆V := fun _ h=>N2_subV h
  have zv : Z⊆V := fun _ h=>N3_subV h
  have f4 := free.mono_bound hq
  have sy : outN D V s=Y := by
    apply eq_of_subset_of_card_le _ (width.le.trans (reg s sv).ge)
    exact fun _ h=>(mem_union.mp (headX f4 root sx (outN_subset h) (mem_outN.mp h).2)).resolve_left
      (fun a=>sink _ a (mem_outN.mp h).2)
  have init : Y ⊆ ball D V s 1 := fun a am=>
    ball_of_adj (yv am) (mem_outN.mp (show a∈outN D V s by rwa [sy])).2
  have yz : Disjoint Y Z := disjoint_left.mpr (fun a ya za=>(mem_N3.mp za).2 (mem_N2.mp ya).1)
  have bank : Y∪Z = ball D V u 3\ball D V u 1 := by
    ext a
    simp only [Y,Z,mem_union,mem_N2,mem_N3,mem_sdiff]
    have ab := @ball_mono_radius D V u 1 2 (by decide)
    have bc := @ball_mono_radius D V u 2 3 (by decide)
    grind
  have covered : Y∪Z ⊆K := by
    intro a am
    have in3 := bank ▸ am
    obtain ⟨reach,early⟩ := mem_sdiff.mp in3
    have reachS := shells (j:=1) (d:=1) root init 1 (mem_sdiff.mpr ⟨reach,early⟩)
    exact mem_erase.mpr ⟨fun eq=>early (eq ▸ X_B1 sx),reachS⟩
  have total := card_union_of_disjoint yz
  change (Y∪Z).card=Y.card+Z.card at total
  change Y.card=r at width
  change Z.card+1=r at third
  have dw : K.card=2*r := by dsimp [K]; rw [card_erase_of_mem (self_mem_ball sv),second,Nat.add_sub_cancel]
  have slots := card_sdiff_add_card_eq_card covered
  obtain ⟨b,bb⟩ := card_pos.mp (show 0<(K\(Y∪Z)).card by omega)
  obtain ⟨bk,off⟩ := mem_sdiff.mp bb
  have bs := (mem_erase.mp bk).1
  have parent : ∃y∈Y,D y b=true := by
    have late : b∉ball D V s 1 := by
      intro hit
      have row := ((mem_ball_one sv).mp hit).resolve_left bs
      exact off (mem_union_left _ (sy ▸ row))
    obtain ⟨y,ym,e⟩ := ball_succ_pred sv (mem_of_mem_erase bk) late
    have yy : y≠s := by rintro rfl; exact late (ball_of_adj (ball_subset (mem_of_mem_erase bk)) e)
    exact ⟨y,sy ▸ (((mem_ball_one sv).mp ym).resolve_left yy),e⟩
  obtain ⟨y,ym,yb⟩ := parent
  have bv := ball_subset (mem_of_mem_erase bk)
  have bx : b∈X := by
    rcases headY f4 root ym bv yb with xy|zz
    · exact (mem_union.mp xy).resolve_right (fun by'=>off (mem_union_left _ by'))
    · exact (off (mem_union_right _ zz)).elim
  have ret b' (bx' : b'∈X) y' (yy : y'∈Y) (e : D y' b'=true) : b'=b := by
    have hit := ball_step (init yy) (xv bx') e
    have ne : b'≠s := by
      intro same
      subst b' 
      exact free s 2 (by decide) (by omega) (.step (yv yy) (mem_outN.mp (sy.symm ▸ yy)).2 (.step sv e (.refl s)))
    have missed : b'∉Y∪Z := fun h=>(mem_sdiff.mp (bank ▸ h)).2 (X_B1 bx')
    exact card_le_one.mp (by omega : (K\(Y∪Z)).card≤1) b' (mem_sdiff.mpr ⟨mem_erase.mpr ⟨ne,hit⟩,missed⟩) b bb
  refine ⟨b,bx,bs,⟨y,mem_inN.mpr ⟨ym,yb⟩⟩,fun y' yy b' bx' e=>ret b' bx' y' yy e,?_⟩
  have dist : (outN D X b)⊆X.erase s := by
    intro a am
    refine mem_erase.mpr ⟨?_,outN_subset am⟩
    intro same
    subst a
    exact free s 3 (by decide) (by omega) (.step (yv ym) (mem_outN.mp (sy.symm ▸ ym)).2
      (.step bv yb (.step sv (mem_outN.mp am).2 (.refl s))))
  have nb : b∉outN D X b := fun hit=>loopfree free (by omega) bv (mem_outN.mp hit).2
  have sep : s∉insert b (outN D X b) := fun m=>(mem_insert.mp m).elim bs.symm (fun h=>notMem_erase _ _ (dist h))
  let A := insert s (insert b (outN D X b))
  have sub : A⊆ball D V u 1 := fun _ h=>X_B1 (insert_subset sx (insert_subset bx outN_subset) h)
  have ins : A⊆ball D V s 3 := by
    intro a am
    rcases mem_insert.mp am with rfl|other
    · exact self_mem_ball sv
    rcases mem_insert.mp other with rfl|ba
    · exact ball_mono_radius (by decide : 2≤3) (mem_of_mem_erase bk)
    · exact ball_step (mem_of_mem_erase bk) (xv (outN_subset ba)) (mem_outN.mp ba).2
  have grow := count_with_prefix (j:=1) (d:=1) (k:=2) root sub ins init
  have sz : A.card=(outN D X b).card+2 := by dsimp [A]; rw [card_insert_of_notMem sep,card_insert_of_notMem nb]
  have diff := card_sdiff_add_card_eq_card (ball_mono_radius (D:=D) (W:=V) (u:=u) (by decide : 3≤4))
  have one := card_B1 f4 root
  rw [reg u root] at one
  have two := @card_B2 D V u
  have three := @card_B3 D V u
  change W.card+_=_ at diff
  change _+((ball D V u 4).card-(ball D V u 1).card)≤(ball D V s 3).card at grow
  change _ = _+Y.card at two
  change _ = _+Z.card at three
  change W.card+(outN D X b).card+2*r+1≤(ball D V s 3).card
  omega

attribute [aesop safe forward (immediate := [free,hq,reg,root,sx,sink,width,third,second])
  (rule_sets := [CHGraphFamilies])] single_target
#print axioms single_target
end LeanCH.BR.SinkBankReturn
