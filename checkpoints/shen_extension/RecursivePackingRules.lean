import checkpoints.shen_extension.CHRuleCatalog
import checkpoints.shen_extension.CycleExteriorPacking
import checkpoints.shen_extension.ParentCutPacking
import checkpoints.shen_extension.PrefixDegreeGrowth

namespace LeanCH.BR.RecursivePackingRules
open Finset BRq2 BRq3 BR45 CHRuleCatalog ShenCycleSuccessor
open Closure.MarkedCyclePeeling

/-- Facts recomputed from the descendant's graph, for any marked subcarrier
and any retained arcs. A different descendant may have a different cutoff. -/
structure Laws (D : CH.Digraph) (V : Finset ℕ) (q : ℕ) : Prop where
  cycleColumn : ∀F : Closure.MarkedCyclePeeling.Family,(∀C∈F,Cycle D V q C) → ∀e : Arc,
    (∑C∈col D F e,(1:ℚ)/2^((ExteriorPacking.exterior D V C\(outN D V e.1).erase e.2).card)) ≤ 1
  prefixStep : ∀a∈V,∀j r lo target,j+1≤q → (∀v∈V,r≤(outN D V v).card) → 5≤q →
    lo≤(ball D V a j).card → 1<lo →
    (∀m,lo≤m → m<target → ∃d,2≤d ∧ d≤5 ∧ m≤q*d+1 ∧ target+d≤m+r+1) →
    target≤(ball D V a (j+1)).card
  parentCut : ∀a∈V,∀k r (S : Finset ℕ),k+2≤q → S⊆inN D V a →
    (∀v∈V,(outN D V v).card≤r) →
    (∀x∈V,∀y∈V,x≠y → ∃v∈V,D v x=true ∧ D v y=true) →
    S.card*(V\S).card≤(V.card-(ball D V a k).card)*(r*r/4)

theorem on_free {D V q} (hq : 1≤q) (free : QFree D V q) : Laws D V q where
  cycleColumn := ExteriorPacking.arc_budget hq free
  prefixStep := fun _ av _ _ _ _ dist deg gt lo pos table =>
    PrefixDegreeGrowth.raise_floor free av dist deg gt lo pos table
  parentCut := by
    intro a av k r S dist ss deg pairs
    have cut := ParentCutPacking.cross_capacity (outN D V)
      (fun v vm=>deg v (mem_sdiff.mp vm).1) (ParentCutPacking.covers_outside_ball free av dist ss pairs)
    simpa only [card_sdiff_of_subset (ball_subset : ball D V a k⊆V)] using cut

/-- Re-enter the same rules at every depth of the catalog's child relation.
Both the zero-step path and all finite nonempty paths are included. -/
theorem at_descendant {src node : Input} (bad : Bad src)
    (trace : Relation.ReflTransGen Child src node)
    {W : Finset ℕ} (sub : W⊆range node.n) {E : CH.Digraph}
    (arcs : ∀v w,E v w=true → node.D v w=true) (hq : 1≤cutoff node) :
    Laws E W (cutoff node) := by
  have b := bad_descendant bad trace
  have native := qfree_of_noShort b.loopless b.missing
  have free := native.mono_set sub
  have lift {a z k} (walk : Walk E W a z k) : Walk node.D W a z k := by
    induction walk with
    | refl => exact .refl _
    | step vv edge _ ih => exact .step vv (arcs _ _ edge) ih
  exact on_free hq (fun a k pos fit w=>free a k pos fit (lift w))

#print axioms on_free
#print axioms at_descendant
end LeanCH.BR.RecursivePackingRules
