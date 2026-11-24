import checkpoints.shen_extension.ReceiverPrivateReturnReplay

namespace LeanCH.BR.BoundaryTightParentReach
open Finset BRq2 BRq3 BR45

/-- Distinct shell rows returning outside g's own head set consume two
disjoint resources: distinct tight parents and distinct neutral targets.
The two injective maps can use any choices of the labelled witnesses. -/
theorem private_packing {D V H Y q t g} (free : QFree D V q) (cut : 3≤q)
    (hv : H⊆V) (yv : Y⊆V) (gm : g∈H) (full : Y⊆outN D V g)
    (returns : ∀z∈Y,∀b∈H,D z b=true → D g b≠true →
      ∃a∈tight D H t g,Walk D H b a (q-2) ∧ Y\outN D V a={z}) :
    let S:=Y.filter fun z=>∃b∈H,D z b=true ∧ D g b≠true
    S.card≤(tight D H t g).card ∧ S.card≤(neutral D H g).card ∧
    2*S.card+(outN D H g).card+1≤H.card := by
  classical
  let S:=Y.filter fun z=>∃b∈H,D z b=true ∧ D g b≠true
  have witness (z : ↥S) :
      ∃b∈neutral D H g,D z b=true ∧ ∃a∈tight D H t g,
        Walk D H b a (q-2) ∧ Y\outN D V a={z.val} := by
    obtain ⟨zm,b,bm,zb,miss⟩ := mem_filter.mp z.property
    have gz := (mem_outN.mp (full zm)).2
    have neq : b≠g := fun e=>digonfree free (by omega) (hv gm) (yv zm) gz (e ▸ zb)
    have ng : D b g≠true := fun bg=>free g 3 (by decide) cut
      (.step (yv zm) gz (.step (hv bm) zb (.step (hv gm) bg (.refl _))))
    exact ⟨b,mem_sdiff.mpr ⟨mem_erase.mpr ⟨neq,bm⟩,fun m=>
      (mem_union.mp m).elim (fun k=>miss (mem_outN.mp k).2) (fun k=>ng (mem_inN.mp k).2)⟩,
      zb,returns z zm b bm zb miss⟩
  choose b bm zb a am w holes using witness
  let parents (z : ↥S) : ↥(tight D H t g) := ⟨a z,am z⟩
  let heads (z : ↥S) : ↥(neutral D H g) := ⟨b z,bm z⟩
  have pi : Function.Injective parents := by
    intro z u eq
    have same : a z=a u := congrArg Subtype.val eq
    exact Subtype.ext (singleton_inj.mp ((holes z).symm.trans (same ▸ holes u)))
  have bi : Function.Injective heads := by
    intro z u eq
    have same : b z=b u := congrArg Subtype.val eq
    have uh := (mem_filter.mp u.property).1
    have bv := (mem_erase.mp (mem_sdiff.mp (bm u)).1).2
    have route := (w z).mono hv
    have blocked : D (a z) u≠true := fun az=>free (a z) (q-2+1+1) (by omega) (by omega)
      (.step (yv uh) az (.step (hv bv) (zb u) (same ▸ route)))
    have hole : u.val∈Y\outN D V (a z) := mem_sdiff.mpr ⟨uh,fun m=>blocked (mem_outN.mp m).2⟩
    rw [holes] at hole
    exact Subtype.ext (mem_singleton.mp hole).symm
  have pc : S.card≤(tight D H t g).card := by simpa using Fintype.card_le_of_injective parents pi
  have bc : S.card≤(neutral D H g).card := by simpa using Fintype.card_le_of_injective heads bi
  have marg := partition_card (free.mono_set hv) (by omega) gm
  have sub : tight D H t g⊆inN D H g := fun _ m=>mem_inN.mpr ⟨(mem_filter.mp m).1,(mem_filter.mp m).2.1⟩
  have := card_le_card sub
  exact ⟨pc,bc,by change 2*S.card+(outN D H g).card+1≤H.card; omega⟩

theorem marked_packing {D V q v t g} {law : LabelledCompromiseRecipe.ReceiverLaw}
    (free : QFree D V q) (_vm : v∈V) (gm : g∈outN D V v)
    (fit : LabelledCompromiseRecipe.FullWindow q law.degree law.shell law.missing law.lowerCount)
    (sole : ((outN D V v).filter fun a=>(ball D V v 2\ball D V v 1)⊆outN D V a)={g})
    (returns : ∀z∈ball D V v 2\ball D V v 1,∀b∈outN D V v,D z b=true → D g b≠true →
      ∃a∈tight D (outN D V v) t g,Walk D (outN D V v) b a (q-2) ∧
        (ball D V v 2\ball D V v 1)\outN D V a={z}) :
    let H:=outN D V v
    let Y:=ball D V v 2\ball D V v 1
    2*(Y.filter fun z=>∃b∈H,D z b=true ∧ D g b≠true).card+(outN D H g).card+1≤H.card := by
  have fg : g∈((outN D V v).filter fun a=>(ball D V v 2\ball D V v 1)⊆outN D V a) := sole ▸ mem_singleton_self g
  exact (private_packing free fit.1 outN_subset (sdiff_subset.trans ball_subset) gm (mem_filter.mp fg).2 returns).2.2

attribute [aesop safe forward (immediate := [free,_vm,gm,fit,sole,returns]) (rule_sets := [CHGraphFamilies])]
  marked_packing
#print axioms marked_packing
attribute [aesop safe forward (immediate := [free,cut,hv,yv,gm,full,returns]) (rule_sets := [CHGraphFamilies])]
  private_packing
ch_family_split_result private_packing
#print axioms private_packing
end LeanCH.BR.BoundaryTightParentReach
