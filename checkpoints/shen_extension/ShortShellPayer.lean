import checkpoints.shen_extension.FullPrimaryComplete

namespace LeanCH.BR.LowShellCycleSelection
open Finset BRq2 BRq3 BR45 BRsGen PhysicalCycleStock ExteriorPacking

/-- This cycle keeps its entire row stock whenever the other cycles'
omission bound is too small to escape across its sparse exterior. -/
structure CompletePayer (D : CH.Digraph) (V : Finset ℕ) (r d : ℕ) (C : Finset ℕ) : Prop where
  rooted : ∀v∈C,Rooted D V v C
  width : (exterior D V C).card=r-1
  sparse : ∀z∈exterior D V C,(outN D (exterior D V C) z).card≤d

/-- Exact consecutive shells give an actual choice of payer. If the fourth
shell is large the first-layer cycle has strict surplus on all rows. If
small, the literal second shell is a complete payer with a cyclic exterior. -/
theorem short_shell_payer {D V q r u} (free : QFree D V q) (hq : 4≤q)
    (reg : OutEq r D V) (uv : u∈V) (fit : r≤q+2) (hr : 4≤r)
    (second : (N2 D V u).card=r-1) (third : (N3 D V u).card=r-1) :
    let W := ball D V u 4\ball D V u 3
    (r≤W.card ∧ ∃C⊆outN D V u,q<C.card ∧ (∀x∈C,Rooted D V x C) ∧
      (exterior D V C).card≤r ∧ ∀x∈C,3*r+2≤(ball D V x 3).card) ∨
    (W.card=r-1 ∧ exterior D V (N2 D V u)=N3 D V u ∧
      exterior D V (N3 D V u)=W ∧ CompletePayer D V r 1 (N2 D V u)) := by
  classical
  let X := outN D V u
  let Y := N2 D V u
  let Z := N3 D V u
  let W := ball D V u 4\ball D V u 3
  change (r≤W.card ∧ _) ∨ (W.card=r-1 ∧ _)
  obtain ⟨C,cx,len,_,roots,ec,_,bank,reach⟩ := narrow_cycle free hq reg uv fit hr second third
  by_cases big : r≤W.card
  · refine Or.inl ⟨big,C,cx,by omega,roots,ec,?_⟩
    have s2 := @card_B2 D V u
    have s3 := @card_B3 D V u
    have s4 := card_sdiff_add_card_eq_card (ball_mono_radius (D:=D) (W:=V) (u:=u) (by decide : 3≤4))
    change W.card+_=_ at s4
    intro v vm
    have := reach v vm
    omega
  right
  have xv : X⊆V := outN_subset
  have yv : Y⊆V := fun _ m=>N2_subV m
  have zv : Z⊆V := fun _ m=>N3_subV m
  have dx : X.card=r := reg u uv
  have yr : ∀y∈Y,Rooted D V y Y := fun y ym=>(bank y ym).1
  have send y (ym : y∈Y) z (zm : z∈Z) : D y z=true :=
    (mem_outN.mp ((bank y ym).2.symm ▸ zm : z∈outN D Z y)).2
  have live : Y.Nonempty := card_pos.mp (by change 0<(N2 D V u).card; omega)
  have dis : Disjoint Y Z := disjoint_left.mpr (fun _ ym zm=>(mem_N3.mp zm).2 (mem_N2.mp ym).1)
  have exteriorY : exterior D V Y=Z := by
    have row y (ym : y∈Y) : (outN D V y).erase (internalHead D Y y)=Z := by
      symm
      refine eq_of_subset_of_card_le ?_ ?_
      · intro z zm
        refine mem_erase.mpr ⟨?_,mem_outN.mpr ⟨zv zm,send y ym z zm⟩⟩
        intro eq
        exact disjoint_left.mp dis (eq.symm ▸ outN_subset (successor_mem (yr y ym))) zm
      · rw [card_erase_of_mem (outN_mono yv _ (successor_mem (yr y ym))),reg y (yv ym)]
        exact third.ge
    ext z
    constructor
    · intro h
      obtain ⟨y,ym,edge⟩ := mem_biUnion.mp (mem_sdiff.mp h).1
      exact row y ym ▸ mem_erase.mpr ⟨fun eq=>(mem_sdiff.mp h).2 (eq.symm ▸ outN_subset (successor_mem (yr y ym))),edge⟩
    · intro zm
      obtain ⟨y,ym⟩ := live
      exact mem_sdiff.mpr ⟨mem_biUnion.mpr ⟨y,ym,mem_outN.mpr ⟨zv zm,send y ym z zm⟩⟩,disjoint_right.mp dis zm⟩
  have xy := BankReachTransfer.reaches_bank (k:=1) free (by omega) xv yv (disjXY (E:=D) (V:=V) (u:=u))
    (fun v vm=>(show 2≤r by omega).trans (reg v vm).ge)
    (fun v vm=>by rw [←outN_X_eq (free.mono_bound hq) uv vm,reg v (xv vm)]; change (N2 D V u).card+1≤r; omega)
    (by omega) (by omega) (by omega)
  have ext : exterior D V Z⊆W := by
    intro a am
    obtain ⟨z,zm,edge⟩ := mem_biUnion.mp (mem_sdiff.mp am).1
    obtain ⟨av,za⟩ := mem_outN.mp edge
    refine mem_sdiff.mpr ⟨ball_step (mem_N3.mp zm).1 av za,?_⟩
    intro early
    have two : a∈ball D V u 2 := by by_contra off; exact (mem_sdiff.mp am).2 (mem_N3.mpr ⟨early,off⟩)
    by_cases one : a∈ball D V u 1
    · rcases (mem_ball_one uv).mp one with rfl|ax
      · exact no_back_arc free uv (mem_N3.mp zm).1 (by omega) za
      obtain ⟨y,ym⟩ := live
      obtain ⟨i,_,bound,path⟩ := xy a ax y ym
      exact free a (i+1+1) (by omega) (by omega) ((path.snoc (zv zm) (send y ym z zm)).snoc av za)
    · exact digonfree free (by omega) av (zv zm) (send a (mem_N2.mpr ⟨two,one⟩) z zm) za
  have small := card_le_card ext
  obtain ⟨sz,zr⟩ := short_exterior free (by omega) reg zv (by change (N3 D V u).card≤q+1; omega)
    (card_pos.mp (by change 0<(N3 D V u).card; omega)) (by omega) (by omega)
  refine ⟨by omega,exteriorY,eq_of_subset_of_card_le ext (by change W.card≤(exterior D V Z).card; omega),yr,exteriorY.symm ▸ third,?_⟩
  rw [exteriorY]
  exact fun z zm=>((zr z zm).one z zm).le

attribute [aesop safe forward (immediate := [free,hq,reg,uv,fit,hr,second,third]) (rule_sets := [CHGraphFamilies])] short_shell_payer
ch_family_split_result short_shell_payer
#print axioms short_shell_payer
end LeanCH.BR.LowShellCycleSelection
