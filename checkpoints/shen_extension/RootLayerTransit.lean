import checkpoints.shen_extension.EqualLayerTransit
import LeanCH.BR.BRTightChain
namespace LeanCH.BR.EqualLayerTransit
open Finset BRq2 BRq3 BR45 BRsGen

/-- With equal actual breadth-first layers, the next layer again supports
the degree. The depth allowance comes from two routes through consecutive
layers and depends on half the degree. -/
theorem next_layer {D V q r h u} (free : QFree D V q) (uv : u∈V)
    (degree : ∀x∈V,r≤(outN D V x).card)
    (hr : 2≤r) (hq : r<q) (height : r/2+h≤q) (depth : 0<h)
    (layers : ∀i,i<h → (ball D V u (i+1) \ ball D V u i).card=r) :
    r≤(ball D V u (h+1) \ ball D V u h).card := by
  let L := fun i=>ball D V u (i+1) \ ball D V u i
  have sub i : L i⊆V := fun _ hm=>ball_subset (mem_sdiff.mp hm).1
  apply end_capacity L free (by omega) hq height depth sub layers
  · intro i _
    exact disjoint_left.mpr (fun x xm ym=>(mem_sdiff.mp ym).2 (mem_sdiff.mp xm).1)
  · exact fun i _ x xm=>degree x (sub i xm)
  · intro i ih v vm x xm
    have arc := (mem_outN.mp xm).2
    have forward := ball_step (mem_sdiff.mp vm).1 (outN_subset xm) arc
    have ne : x≠u := by
      rintro rfl
      exact no_back_arc free uv (mem_sdiff.mp vm).1 (by omega) arc
    obtain ⟨j,pos,le,hit⟩ := ball_mem_positive_layer forward ne
    exact ⟨j-1,by omega,by simpa only [L,Nat.sub_add_cancel pos] using hit⟩

attribute [aesop safe forward (immediate := [free,uv,degree,hr,hq,height,depth,layers])
  (rule_sets := [CHGraphFamilies])] next_layer
#print axioms next_layer
end LeanCH.BR.EqualLayerTransit
