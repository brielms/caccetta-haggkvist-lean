import checkpoints.shen_extension.CoverageContradictions

namespace LeanCH.BR.LabelledCompromiseRecipe
open Finset BRq2 BRq3 JointShortcut

/-- All targets reachable through Y from the debtor and from each of its
zero-spare parents fit into its boundary quota, together with its old heads.
The intermediate label may depend on both the target and the parent. -/
theorem protected_menu {D V H Y q t g} {B : Finset ℕ}
    (free : QFree D V q) (hv : H⊆V) (yv : Y⊆V) (cut : 1≤q)
    (size : H.card=q*t+1) (br : Compose.Boundary.BoundaryRegular q t)
    (gm : g∈H) (bh : B⊆H) (absent : g∉B)
    (others : ∀a∈H,a≠g → t≤(outN D H a).card)
    (targets : meetsMenu D Y B g)
    (guarded : ∀a∈H,D a g=true → (outN D H a).card=t → meetsMenu D Y B a) :
    (outN D H g∪B).card≤t := by
  classical
  let F : Finset ℕ := {g}
  let K:=menuCut D F Y B
  let E:=install K (F×ˢB)
  have safe : QFree E H q := menu_safe free hv bh (by simpa [F] using absent) yv
  have old a : outN K H a⊆outN E H a := fun _ m=>
    mem_outN.mpr ⟨(mem_outN.mp m).1,install_old (mem_outN.mp m).2⟩
  have same : outN K H g=outN D H g := menu_row.trans (ite_eq_left targets)
  have filled : outN D H g∪B⊆outN E H g := by
    intro u um
    rcases mem_union.mp um with was|new
    · exact old g (same.symm ▸ was)
    · exact mem_outN.mpr ⟨bh new,install_new (mem_product.mpr ⟨mem_singleton_self g,new⟩)⟩
  by_contra! excess
  have strict := excess.trans_le (card_le_card filled)
  apply WeightedSD.boundary_regular_no_excess cut br safe size _ gm strict
  intro a am
  by_cases ag : a=g
  · simpa [ag] using strict.le
  apply le_trans _ (card_le_card (old a))
  change t≤(outN (menuCut D F Y B) H a).card
  rw [menu_row]
  split
  next => exact others a am ag
  next blocked =>
    have quota := others a am ag
    by_cases edge : g∈outN D H a
    · have slack : t<(outN D H a).card := by
        by_contra! exactQuota
        exact blocked (guarded a am (mem_outN.mp edge).2 (Nat.le_antisymm exactQuota quota))
      have debit := card_erase_add_one edge
      simpa only [F,sdiff_singleton_eq_erase] using (show t≤((outN D H a).erase g).card by omega)
    · simpa [F,sdiff_singleton_eq_erase,erase_eq_of_notMem edge] using quota

/-- A single named set of candidate labels and the common cut that pays them
are inferred from the receiver. No enumeration of choices of B is needed. -/
theorem maximal_protected_menu {D V H Y q t g}
    (free : QFree D V q) (hv : H⊆V) (yv : Y⊆V) (cut : 1≤q)
    (size : H.card=q*t+1) (br : Compose.Boundary.BoundaryRegular q t)
    (gm : g∈H) (others : ∀a∈H,a≠g → t≤(outN D H a).card) :
    let B:=(H.erase g).filter fun b=>
      (∃z∈Y,D g z=true ∧ D z b=true) ∧
      ∀a∈H,D a g=true → (outN D H a).card=t → ∃z∈Y,D a z=true ∧ D z b=true
    (outN D H g∪B).card≤t := by
  apply protected_menu free hv yv cut size br gm (filter_subset .. |>.trans (erase_subset ..))
    (fun m=>notMem_erase _ _ (mem_filter.mp m).1) others
  · intro b bm
    exact (mem_filter.mp bm).2.1
  · intro a am arc cost b bm
    exact (mem_filter.mp bm).2.2 a am arc cost

attribute [aesop safe forward (immediate := [free,hv,yv,cut,size,br,gm,others])
  (rule_sets := [CHGraphFamilies])] maximal_protected_menu
#print axioms protected_menu
#print axioms maximal_protected_menu
end LeanCH.BR.LabelledCompromiseRecipe
