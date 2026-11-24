import checkpoints.shen_extension.InsertionTests
import checkpoints.shen_extension.WeightedJointCatalog

namespace LeanCH.BR.InsertionTestCatalog
open Finset BRq2 JointShortcut Closure SeparatedReturnBank

/-- Build safety only for the proposed hub on these actual heads and parents. -/
@[aesop safe forward (immediate := [fresh,heads,old,clear]) (rule_sets := [CHGraphFamilies])]
theorem safe_hub {D : CH.Digraph} {W I H : Finset ℕ} {q z} (fresh : z∉W) (heads : H⊆W)
    (old : QFree D W q) (clear : ∀ h∈H, ∀ i∈I, ∀ k, k+2≤q → ¬Walk D W h i k) :
    QFree (hub D z I H) (insert z W) q :=
  (InsertionTests.hub_iff fresh heads).mpr ⟨old,clear⟩

@[aesop safe forward (immediate := [fresh,heads,safe]) (rule_sets := [CHGraphFamilies])]
theorem hub_returns {D : CH.Digraph} {W I H : Finset ℕ} {q z} (fresh : z∉W) (heads : H⊆W)
    (safe : QFree (hub D z I H) (insert z W) q) :
    ∀ h∈H, ∀ i∈I, ∀ k, k+2≤q → ¬Walk D W h i k :=
  ((InsertionTests.hub_iff fresh heads).mp safe).2

@[aesop safe forward (immediate := [sub,inside,fresh,budget,clear]) (rule_sets := [CHGraphFamilies])]
theorem admissible {q s} {O : Origin q s} {U : Finset ℕ} (sub : U⊆O.V)
    {F : Finset (ℕ × ℕ)} (inside : F⊆U×ˢU) (fresh : ∀p∈F,O.G p.1 p.2≠true)
    (budget : ∀u∈U,(row F u).card≤cap O U u)
    (clear : ∀i∈F,∀c,0<c → c≤q → ¬Trail O.G U F i i c) : Admissible O U F :=
  (InsertionTests.admissible_iff_trail O sub).mpr ⟨inside,fresh,budget,clear⟩

@[aesop safe forward (immediate := [sub,accepted]) (rule_sets := [CHGraphFamilies])]
theorem no_closed_trail {q s} {O : Origin q s} {U : Finset ℕ} (sub : U⊆O.V)
    {F : Finset (ℕ × ℕ)} (accepted : Admissible O U F) :
    ∀i∈F,∀c,0<c → c≤q → ¬Trail O.G U F i i c :=
  ((InsertionTests.admissible_iff_trail O sub).mp accepted).2.2.2

attribute [aesop safe forward (immediate := [hU,hne]) (rule_sets := [CHGraphFamilies])]
  InsertionTests.static_trail_minimum

#print axioms safe_hub
#print axioms hub_returns
#print axioms admissible
#print axioms no_closed_trail
end LeanCH.BR.InsertionTestCatalog
