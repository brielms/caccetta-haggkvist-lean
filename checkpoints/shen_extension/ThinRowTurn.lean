import checkpoints.shen_extension.MixedShellUniform
namespace LeanCH.BR.ThinRowTurn
open Finset BRq2 BRq3 BR45 BRsGen

/-- A first row that sees a whole outside bank in two steps has only
one vacant label beside its own heads. Two inner successors would be
forced to head one another. Its unique successor inherits the *same*
outer heads, so this rule can fire again there. -/
theorem forced_turn {D V X Y Z q r x y} (free : QFree D V q) (t : 2≤q)
    (xv : X⊆V) (yv : Y⊆V) (zv : Z⊆V) (xy : Disjoint X Y) (zsep : Disjoint (X∪Y) Z)
    (quota : OutEq r D V) (rows : ∀v∈X,outN D V v⊆X∪Y)
    (inside : ∀v∈X,(outN D X v).Nonempty)
    (xm : x∈X) (hit : y∈outN D Y x) (full : Z⊆outN D V y)
    (bank : Z.card+1=r) (size : (ball D V x 2).card≤2*r+1) :
    ∃p∈X,outN D X x={p} ∧ outN D Y p=outN D Y x ∧ (outN D Y x).card+1=r := by
  classical
  let W := (ball D V x 2).erase x
  let K := W\Z
  have disX z (zm : z∈Z) : z∉X := fun zx=>disjoint_left.mp zsep (mem_union_left _ zx) zm
  have yz := mem_outN.mp hit
  have seen : Z⊆W := by
    intro z zm
    exact mem_erase.mpr ⟨fun e=>disX z zm (e ▸ xm),ball_step (ball_of_adj (yv yz.1) yz.2)
      (zv zm) (mem_outN.mp (full zm)).2⟩
  have cost : K.card≤r+1 := by
    have sum := card_sdiff_add_card_eq_card seen
    have cw := card_erase_add_one (a:=x) (self_mem_ball (D:=D) (k:=2) (xv xm))
    change W.card+1=_ at cw
    change K.card+Z.card=_ at sum
    omega
  have heads : outN D V x⊆K := by
    intro a am
    have arc := (mem_outN.mp am).2
    exact mem_sdiff.mpr ⟨mem_erase.mpr ⟨fun e=>loopfree free (by omega) (xv xm) (e ▸ arc),
      ball_mono_radius (by decide : 1≤2) (ball_of_adj (outN_subset am) arc)⟩,disjoint_left.mp zsep (rows x xm am)⟩
  have filled p (ph : p∈outN D X x) : outN D V p=K.erase p := by
    have px := outN_subset ph
    have pv := xv px
    have pk := heads (outN_mono xv x ph)
    apply eq_of_subset_of_card_le
    · intro a am
      have arc := (mem_outN.mp am).2
      have nonloop : a≠p := fun e=>loopfree free (by omega) pv (e ▸ arc)
      have distinct : a≠x := by
        intro e
        subst a
        exact free x 2 (by decide) t (.step pv (mem_outN.mp ph).2 (.step (xv xm) arc (.refl x)))
      exact mem_erase.mpr ⟨nonloop,mem_sdiff.mpr ⟨mem_erase.mpr ⟨distinct,
        ball_step (ball_of_adj pv (mem_outN.mp ph).2) (outN_subset am) arc⟩,disjoint_left.mp zsep (rows p px am)⟩⟩
    · rw [card_erase_of_mem pk,quota p pv]
      omega
  have one v (vm : v∈X) : (outN D X v).card+(outN D Y v).card=r := by
    rw [←card_outN_union xy,←quota v (xv vm)]
    exact congrArg card (Subset.antisymm (outN_mono (union_subset xv yv) v)
      (fun a am=>mem_outN.mpr ⟨rows v vm am,(mem_outN.mp am).2⟩))
  obtain ⟨p,pm⟩ := inside x xm
  have px := outN_subset pm
  have unique : outN D X x={p} := by
    apply eq_singleton_iff_unique_mem.mpr
    refine ⟨pm,?_⟩
    intro v vm
    by_contra ne
    have vh := heads (outN_mono xv x vm)
    have ph := heads (outN_mono xv x pm)
    have vp := (filled v vm).symm ▸ mem_erase.mpr ⟨Ne.symm ne,ph⟩
    have pv := (filled p pm).symm ▸ mem_erase.mpr ⟨ne,vh⟩
    exact free p 2 (by decide) t (.step (xv (outN_subset vm)) (mem_outN.mp pv).2
      (.step (xv px) (mem_outN.mp vp).2 (.refl p)))
  have dx := one x xm
  rw [unique,card_singleton] at dx
  have dp := one p px
  have take : outN D Y x⊆outN D Y p := by
    intro v vm
    have vy := outN_subset vm
    have ne : v≠p := fun e=>disjoint_left.mp xy (e ▸ px) vy
    have head := (filled p pm).symm ▸ mem_erase.mpr ⟨ne,heads (outN_mono yv x vm)⟩
    exact mem_outN.mpr ⟨vy,(mem_outN.mp head).2⟩
  have pos := card_pos.mpr (inside p px)
  exact ⟨p,px,unique,(eq_of_subset_of_card_le take (by omega)).symm,by omega⟩

attribute [aesop safe forward (immediate := [free,t,xv,yv,zv,xy,zsep,quota,rows,inside,xm,hit,full,bank,size])
  (rule_sets := [CHGraphFamilies])] forced_turn
#print axioms forced_turn
end LeanCH.BR.ThinRowTurn
