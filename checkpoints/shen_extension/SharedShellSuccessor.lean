import checkpoints.shen_extension.PrimaryShellEntry

namespace LeanCH.BR.LowShellCycleSelection
open Finset BRq2 BRq3 BR45 BRsGen ExteriorPacking PhysicalCycleStock
open scoped Classical

/-- A contact of two physical origins screens both exceptional labels
from the entire exterior. Its next bank is confined to the source's
actual third shell. No bound on the order or either row's degree occurs. -/
theorem successor_inside_third {D V q u v w C b k} (free : QFree D V q)
    (hq : 4≤q) (time : k+2≤q) (uv : u∈V) (vv : v∈V) (ne : u≠v)
    (first : outN D V u=insert w C) (common : C⊆outN D V v)
    (slots : (outN D V v\C).card≤1) (live : C.Nonempty)
    (paid : ∀c∈C,exterior D V C⊆outN D V c)
    (covered : exterior D V C⊆N2 D V u)
    (exception : N2 D V u\exterior D V C={b})
    (budget : (N2 D V v).card≤(outN D V b).card) (hit : v∈ball D V u k) :
    exterior D V (exterior D V C)⊆N3 D V u := by
  classical
  obtain ⟨c,cm⟩ := live
  have vc := common cm
  have wv : w∈V := outN_subset (first.symm ▸ mem_insert_self w C)
  intro j jm
  obtain ⟨heads,off⟩ := mem_sdiff.mp jm
  obtain ⟨e,em,ej⟩ := mem_biUnion.mp heads
  have ce := paid c cm em
  have ev := outN_subset ce
  have eb : D e b≠true := fun arc=>
    exterior_screens_single_exception free hq uv vv ne first common slots ⟨c,cm⟩ exception em
      (fun x xm=>(mem_outN.mp (paid x xm em)).2) arc budget (by omega) hit
  have ew : D e w≠true := by
    intro edge
    have path : Walk D V v w 3 := .step (outN_subset vc) (mem_outN.mp vc).2
      (.step ev (mem_outN.mp ce).2 (.step wv edge (.refl w)))
    have eq := first_side_contact free (t:=3) (by omega) (by decide) vv ne first common
      (mem_ball.mpr ⟨wv,3,le_rfl,path⟩) hit
    subst w; exact free v 3 (by decide) (by omega) path
  apply (headY (free.mono_bound hq) uv (covered em) (outN_subset ej) (mem_outN.mp ej).2).resolve_left
  intro early
  rcases mem_union.mp early with x|y
  · rcases mem_insert.mp (first ▸ x) with eq|jc
    · exact ew (eq ▸ (mem_outN.mp ej).2)
    · exact digonfree free (by omega) ev (outN_subset ej) (mem_outN.mp ej).2 (mem_outN.mp (paid j jc em)).2
  · have eq : j=b := mem_singleton.mp (exception ▸ (mem_sdiff.mpr ⟨y,off⟩ : j∈N2 D V u\exterior D V C))
    exact eb (eq ▸ (mem_outN.mp ej).2)

attribute [aesop safe forward (immediate := [free,hq,time,uv,vv,ne,first,common,slots,live,paid,covered,exception,budget,hit]) (rule_sets := [CHGraphFamilies])] successor_inside_third
#print axioms successor_inside_third
end LeanCH.BR.LowShellCycleSelection
