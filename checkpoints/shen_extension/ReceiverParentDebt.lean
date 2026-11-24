import checkpoints.shen_extension.BoundaryDebtColumns
import checkpoints.shen_extension.ReceiverTurnCounts

namespace LeanCH.BR.LabelledCompromiseRecipe
open Finset BRq2 BRq3 BR45 AvoidedHeadQuota RetainedShortfall Closure.DeficitLevels

/-- Every column x of the marked head bank must be paid by the full rows
and its own parents that omit at most one shell column. A full x costs one
extra unit. This is one simultaneous condition on the same omission table. -/
theorem parent_debt {D V q r t v} (free : QFree D V q) (cut : 2≤q) (vm : v∈V)
    (reg : OutEq r D V) (mult : r=q*t+1) (two : 2≤t)
    (br : Compose.Boundary.BoundaryRegular q t)
    (one : (ball D V v 2 \ ball D V v 1).card+t=r+1) :
    let H:=outN D V v
    let Y:=ball D V v 2 \ ball D V v 1
    let F:=H.filter fun a=>Y⊆outN D V a
    ∀x∈H, 2+(if x∈F then 1 else 0)≤F.card+
      ((H.erase x).filter fun u=>D u x=true ∧ (Y\outN D V u).card≤1).card := by
  classical
  let H:=outN D V v
  let Y:=ball D V v 2 \ ball D V v 1
  let F:=H.filter fun a=>Y⊆outN D V a
  change Y.card+t=r+1 at one
  have size : H.card=r := reg v vm
  have row (a) (am : a∈H) : (Y\outN D V a).card+r=Y.card+(outN D H a).card :=
    missing_count free cut vm am (reg a (outN_subset am))
  have cost_row (a) (am : a∈H) : cost t D H a=(if Y⊆outN D V a then 1 else 0) := by
    have budget := row a am
    unfold cost
    split
    next yes =>
      rw [sdiff_eq_empty_iff_subset.mpr yes,card_empty] at budget
      omega
    next no =>
      have pos : 0<(Y\outN D V a).card := by
        by_contra! zero
        exact no (sdiff_eq_empty_iff_subset.mp (card_eq_zero.mp (by omega)))
      omega
  have count : total t D H=F.card := by
    unfold total
    rw [sum_congr rfl cost_row,←card_filter]
  change ∀x∈H, 2+(if x∈F then 1 else 0)≤F.card+
    ((H.erase x).filter fun u=>D u x=true ∧ (Y\outN D V u).card≤1).card
  intro x xm
  have live : (H.erase x).Nonempty := by
    have s := card_erase_add_one xm
    have prod := Nat.le_mul_of_pos_left t (by omega : 0<q)
    exact card_pos.mp (by omega)
  have cap := regular_column br (by omega) two (free.mono_set (show H⊆V from outN_subset)) xm live (by omega)
  rw [count,cost_row x xm] at cap
  have cols : ((H.erase x).filter fun a=>D a x=true ∧ (outN D H a).card≤t)=
      ((H.erase x).filter fun a=>D a x=true ∧ (Y\outN D V a).card≤1) := by
    ext a
    by_cases am : a∈H.erase x
    · have budget := row a (mem_erase.mp am).2
      simp only [mem_filter,am,true_and]
      constructor <;> rintro ⟨arc,deg⟩ <;> exact ⟨arc,by omega⟩
    · simp [am]
  rw [cols] at cap
  simpa only [F,mem_filter,xm,true_and] using cap

/-- The already marked receiver table supplies the free parameters of the
column theorem when its shell is one slot above the boundary. -/
theorem marked_parent_debt {D V q} {law : ReceiverLaw} {v}
    (free : QFree D V q) (vm : v∈V) (reg : OutEq law.degree D V)
    (size : (ball D V v 2 \ ball D V v 1).card=law.shell)
    (fit : FullWindow q law.degree law.shell law.missing law.lowerCount)
    (one : law.shell+(law.degree-1)/q=law.degree+1) :
    let H:=outN D V v
    let Y:=ball D V v 2 \ ball D V v 1
    let F:=H.filter fun a=>Y⊆outN D V a
    ∀x∈H, 2+(if x∈F then 1 else 0)≤F.card+
      ((H.erase x).filter fun u=>D u x=true ∧ (Y\outN D V u).card≤1).card := by
  obtain ⟨cut,two,region,mult,_,_⟩ := fit
  exact parent_debt free (by omega) vm reg mult two
    (WeightedSD.boundary_regular_outside_pressure_region cut two region) (size ▸ one)

attribute [aesop safe forward (immediate := [free,vm,reg,size,fit,one])
  (rule_sets := [CHGraphFamilies])] marked_parent_debt
attribute [aesop safe forward (immediate := [free,cut,vm,reg,mult,two,br,one])
  (rule_sets := [CHGraphFamilies])] parent_debt
#print axioms parent_debt
#print axioms marked_parent_debt
end LeanCH.BR.LabelledCompromiseRecipe
