import checkpoints.shen_extension.CompromiseReceiverReplay

namespace LeanCH.BR.LabelledCompromiseRecipe
open Finset BRq2 BRq3 BR45 CompromiseQuotaTransfer

private abbrev lab (U : Finset ℕ) : ↥U ↪ ℕ := ⟨Subtype.val,Subtype.val_injective⟩

private theorem map_heads {D U} (x : ↥(U : Finset ℕ)) :
    (CH.CompromiseSeven.outN (adjacency D U) x).map (lab U)=outN D U x := by
  rw [map_eq_image]; exact image_heads x

private theorem map_parents {D U} (x : ↥(U : Finset ℕ)) :
    (CH.CompromiseSeven.inN (adjacency D U) x).map (lab U)=inN D U x := by
  have rev : CH.CompromiseSeven.inN (adjacency D U) x=CH.CompromiseSeven.outN (adjacency (fun a b=>D b a) U) x := by
    ext; simp [adjacency]
  rw [rev]
  exact map_heads (D:=fun a b=>D b a) x

private theorem map_shell {D U} (x : ↥(U : Finset ℕ)) :
    (CH.CompromiseSeven.second (adjacency D U) x).map (lab U)=ball D U x 2 \ ball D U x 1 := by
  rw [map_eq_image]; exact image_shell x

/-- The exceptional columns, their missing parents and the charged
heads all refer to one chosen vertex of the same native subgraph. -/
theorem physical {D U} {law : ReceiverLaw} (witness : law.on D U) :
    ∃y∈U, let H:=outN D U y
           let Y:=ball D U y 2 \ ball D U y 1
           let X:=Y.filter fun z=>law.missing≤(H\inN D U z).card
           (inN D U y).card=law.parents ∧ Y.card=law.shell ∧
           (∑h∈H,(law.degree-(inN D U h).card))≤law.charge ∧
           law.lowerCount≤X.card ∧ X.card≤law.upperCount ∧
           ∃h∈H,law.degree≤(inN D U h).card ∧ ∃z∈X,D h z=true ∧ ∃b∈H,D z b=true := by
  classical
  obtain ⟨y,parents,sh,charge,low,high,h,hm,heavy,z,zm,hz,bill,b,bm,zb⟩ := witness
  let A := adjacency D U
  let H := CH.CompromiseSeven.outN A y
  let Y := CH.CompromiseSeven.second A y
  have pcard (x : ↥U) : (CH.CompromiseSeven.inN A x).card=(inN D U x).card := by
    rw [←map_parents x,card_map]
  have missing (x : ↥U) : (H\CH.CompromiseSeven.inN A x).card=(outN D U y\inN D U x).card := by
    rw [←map_heads y,←map_parents x,←Finset.map_sdiff,card_map]
  have xeq : (Y.filter (fun x=>law.missing≤(H\CH.CompromiseSeven.inN A x).card)).map (lab U)=
      (ball D U y 2 \ ball D U y 1).filter (fun x=>law.missing≤(outN D U y\inN D U x).card) := by
    rw [←map_shell y]
    ext v
    simp only [mem_map,mem_filter]
    constructor
    · rintro ⟨x,⟨xm,ok⟩,rfl⟩
      exact ⟨⟨x,xm,rfl⟩,(missing x) ▸ ok⟩
    · rintro ⟨⟨x,xm,rfl⟩,ok⟩
      exact ⟨x,⟨xm,(missing x).symm ▸ ok⟩,rfl⟩
  have xc := congrArg card xeq
  rw [card_map] at xc
  have zm' : z.val ∈ ball D U y 2 \ ball D U y 1 := by
    rw [←map_shell y]; exact mem_map.mpr ⟨z,zm,rfl⟩
  have head {a : ↥U} (inH : a∈H) : a.val∈outN D U y := by
    rw [←map_heads y]; exact mem_map.mpr ⟨a,inH,rfl⟩
  refine ⟨y.val,y.property,?_,?_,?_,?_,?_,h.val,head hm,?_,z.val,
    mem_filter.mpr ⟨zm',(missing z) ▸ bill⟩,hz,b.val,head bm,zb⟩
  · rw [←pcard]; exact parents
  · rw [←map_shell y,card_map]; exact sh
  · rw [←map_heads y,sum_map]
    change (∑x∈H,(law.degree-(inN D U x.val).card))≤law.charge
    change (∑x∈H,(law.degree-(CH.CompromiseSeven.inN A x).card))≤law.charge at charge
    simpa only [pcard] using charge
  · exact xc ▸ low
  · exact xc ▸ high
  · exact (pcard h) ▸ heavy

-- Replay opens the receiver packet once, in ReceiverMarkedRoot. This theorem stays available to ordinary proofs.
#print axioms physical
end LeanCH.BR.LabelledCompromiseRecipe
