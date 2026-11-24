import checkpoints.shen_extension.BookedShortPrice

namespace LeanCH.BR.LowShellCycleSelection
open Finset BRq2 BRq3 BR45 BRsGen ExteriorPacking PhysicalCycleStock
open scoped Classical

/-- If a surviving one-omission payer has any short first claimant, then it
has one whose second shell fills the whole degree. The second and third
shells named in the conclusion belong to the same representative. -/
theorem short_first_frontier {D V q r target δ cap C A} (free : QFree D V q) (reg : OutEq r D V)
    (t : Selection D V q r 3 (3*r)) (policy : ShellBooking t) (ready : RoutingRoom q r V.card target)
    (mark : RemainingPayer t C δ cap A) (width : (exterior D V C).card=r)
    (size : C.card+1=r) (margin : 4*6<3*C.card+6)
    (existsShort : ∃Y∈claims t C,C⊆outN D V (t.rep Y) ∧ (ball D V (t.rep Y) 3).card<3*r) :
    ∃Y∈claims t C,C⊆outN D V (t.rep Y) ∧ (ball D V (t.rep Y) 3).card<3*r ∧
      Y.card=r ∧ (N3 D V (t.rep Y)).card=r-2 := by
  classical
  have hq := ready.cycle.1
  have hr := ready.growth.2.1
  have fit := ready.close
  by_contra! no
  have narrow Y (ym : Y∈claims t C) (first : C⊆outN D V (t.rep Y)) (sh : (ball D V (t.rep Y) 3).card<3*r) :
      Y.card=r-1 := by
    have key := (mem_filter.mp ym).1
    have shape := short_shapes free reg ready (rep_native t key) sh
    rw [rep_key t key] at shape
    exact shape.resolve_right (fun pair=>no Y ym first sh pair.1 pair.2) |>.1
  let S := exterior D V C\mutualExterior D V C
  have unique Y (ym : Y∈claims t C) (first : C⊆outN D V (t.rep Y)) (sh : (ball D V (t.rep Y) 3).card<3*r) :
      Y=S := by
    have key := (mem_filter.mp ym).1
    have e := rep_key t key
    exact e.symm.trans (recover_first_key free (by omega) reg (rep_native t key) hr fit first size width
      ((congrArg card e).trans (narrow Y ym first sh)))
  have other Y (ym : Y∈claims t C) (first : C⊆outN D V (t.rep Y)) (ne : Y≠S) :
      shellDebt D V 3 (3*r) Y≤1 := by
    have high : 3*r≤(ball D V (t.rep Y) 3).card := by
      by_contra! low
      exact ne (unique Y ym first low)
    apply (class_residual (m:=1) _).trans (by decide)
    intro v vm
    have least := t.least Y (mem_filter.mp ym).1 v vm
    have upper := (mem_filter.mp (mem_filter.mp vm).1).2
    rw [show (ball D V v 3).card=3*r by omega]; simp [debit]
  have excess : shellDebt D V 3 (3*r) S≤1+3 := by
    apply (class_residual (m:=3) _).trans (by decide)
    intro v vm; unfold debit; split_ifs <;> omega
  have off : C∉shortSwitches t := by
    intro sw; have := (switched_shell_paid free reg t (by omega) hr fit sw).1.width; omega
  have bound := first_exception_budget free reg t ready policy off width.ge (by omega) excess other
  obtain ⟨Y,ym,first,sh⟩ := existsShort
  have price := booked_short_price free reg t policy ready ym first width size sh (narrow Y ym first sh)
  have empty : A=∅ := eq_empty_iff_forall_notMem.mpr (fun T tm=>by
    have := (mark.routed T tm).2.2.2.2.1.nextSize; omega)
  have due := mark.due
  rw [empty,sum_empty,add_zero] at due
  have strict : (24:ℚ)<3*(C.card:ℚ)+6 := by exact_mod_cast margin
  push_cast at price
  norm_num at bound
  linarith only [price,strict,bound,due]

#print axioms short_first_frontier
end LeanCH.BR.LowShellCycleSelection
