import checkpoints.shen_extension.ReceiverReadyReplay

namespace LeanCH.BR.LabelledCompromiseRecipe
open Finset BRq2 BRq3 BR45 BypassRepair AvoidedHeadQuota CHRuleCatalog

/-- The columns in H missed by all rows of Z in the incoming direction. -/
def missedBy {D : CH.Digraph} (H Z : Finset ℕ) : Finset ℕ :=
  H.filter (fun h=>∀z∈Z,D h z≠true)

/-- Every row in B loses all Z as shell targets. Its internal heads must
lie in the same column set as B. One sparse row of B prices both losses. -/
theorem return_capacity {D V q r v a} {Z B : Finset ℕ}
    (free : QFree D V q) (cut : 3≤q) (vm : v∈V) (reg : OutEq r D V)
    (zs : Z⊆ball D V v 2 \ ball D V v 1) (bh : B⊆outN D V v)
    (live : B.Nonempty) (small : B.card≤q*a) (lower : NoHost q a)
    (turns : ∀z∈Z,∀b∈B,D z b=true) :
    r+Z.card+B.card+1≤(ball D V v 2 \ ball D V v 1).card+
      (missedBy (D:=D) (outN D V v) Z).card+a := by
  classical
  let H:=outN D V v
  let Y:=ball D V v 2 \ ball D V v 1
  let M:=missedBy (D:=D) H Z
  have bv : B⊆V := bh.trans outN_subset
  have zv : Z⊆V := zs.trans (sdiff_subset.trans ball_subset)
  have safe (b) (bm : b∈B) (z) (zm : z∈Z) : D b z≠true :=
    digonfree free (by omega) (zv zm) (bv bm) (turns z zm b bm)
  have contained : B⊆M := fun b bm=>mem_filter.mpr ⟨bh bm,safe b bm⟩
  obtain ⟨b,bm,low⟩ : ∃b∈B,(outN D B b).card<a := by
    by_contra! all
    exact lower D B live small (free.mono_set bv) all
  have inside : outN D H b⊆M := by
    intro h hm
    obtain ⟨hh,arc⟩ := mem_outN.mp hm
    refine mem_filter.mpr ⟨hh,?_⟩
    intro z zm hz
    exact free z 3 (by decide) cut (.step (bv bm) (turns z zm b bm)
      (.step (outN_subset hh) arc (.step (zv zm) hz (.refl _))))
  have cover : outN D H b⊆outN D B b ∪ (M\B) := by
    intro h hm
    by_cases hb : h∈B
    · exact mem_union_left _ (mem_outN.mpr ⟨hb,(mem_outN.mp hm).2⟩)
    · exact mem_union_right _ (mem_sdiff.mpr ⟨inside hm,hb⟩)
  have cost := (card_le_card cover).trans (card_union_le ..)
  have slots := card_sdiff_add_card_eq_card contained
  have losses : Z⊆Y\outN D V b := fun z zm=>
    mem_sdiff.mpr ⟨zs zm,fun hit=>safe b bm z zm (mem_outN.mp hit).2⟩
  have pay := missing_count free (by omega) vm (bh bm) (reg b (bv bm))
  change (Y\outN D V b).card+r=Y.card+(outN D H b).card at pay
  have lost := card_le_card losses
  change r+Z.card+B.card+1≤Y.card+M.card+a
  omega

attribute [aesop safe forward (immediate := [free,cut,vm,reg,zs,bh,live,small,lower,turns])
  (rule_sets := [CHGraphFamilies])] return_capacity
#print axioms return_capacity
end LeanCH.BR.LabelledCompromiseRecipe
