import checkpoints.shen_extension.SameExteriorPayment

namespace LeanCH.BR.LowShellCycleSelection
open Finset BRq2 BRq3 BR45 BRsGen ExteriorPacking PhysicalCycleStock CHRuleCatalog
open scoped Classical

theorem one_omission_paid {D V q r δ cap C A} (free : QFree D V q) (hq : 6≤q)
    (reg : OutEq r D V) (t : Selection D V q r 3 (3*r)) (mark : RemainingPayer t C δ cap A)
    (mid : MiddleRows t C) (fit : r≤q+2) (width : (exterior D V C).card=r)
    (size : C.card+1=r) (room : 4*(r-q+1)<C.card+6) (reserve : 2*(r-q+1)<C.card) : False := by
  obtain ⟨all,stock⟩ := unique_middle_claim free hq reg t mark mid fit width size room
  have scale K (km : K∈booked t) : omissions D V K r≤r-q := by
    obtain ⟨Z,zk,rfl⟩ := mem_image.mp km; exact t.loss _ (t.assigned _ zk)
  have om : omissions D V C r=1 := by unfold omissions; rw [width]; omega
  obtain ⟨v,vm,low⟩ := booked_small_row free reg t (by omega : r-q+2≤q) scale mark.bookedHere (allowance:=1)
    (by simpa using stock) (by rw [om,pow_one,one_mul]; omega)
  let Y := exterior D V C
  have ym : Y∈claims t C := all ▸ mem_singleton_self Y
  have key := (mem_filter.mp ym).1
  have id := (mem_filter.mp ym).2
  have eq := rep_key t key
  obtain ⟨first,y,z,_⟩ := mid.each Y ym
  have len := t.length _ (t.assigned _ key)
  have roots := t.rooted _ (t.assigned _ key)
  rw [id] at len roots
  exact low.not_gt (same_exterior_high free hq reg (rep_native t key) first len roots fit size
    ((congrArg card eq).trans y) (by omega) eq.symm v vm)

theorem remaining_widths {D V q r δ cap C A target} (free : QFree D V q) (reg : OutEq r D V)
    (t : Selection D V q r 3 (3*r)) (policy : ShellBooking t) (ready : RoutingRoom q r V.card target)
    (due : RemainingPayer t C δ cap A) : (exterior D V C).card=r-1 ∨ (exterior D V C).card=r := by
  classical
  by_cases mv : C∈shortSwitches t
  · exact Or.inl (switched_shell_paid free reg t (by have := ready.cycle.1; omega) ready.growth.2.1 ready.close mv).1.width
  · have proper : PrimaryShort t cap C := by
      refine ⟨due.bookedHere,due.first,?_,?_⟩
      · intro Z zm cycle
        have id := (mem_filter.mp zm).2
        have notMoved : Z∉shortSwitches t := fun h=>mv (((policy.secondary Z h).symm.trans id) ▸ h)
        exact id ▸ policy.primary Z (mem_filter.mp zm).1 notMoved cycle
      · apply due.due.trans
        apply add_le_add_right
        by_cases terminal : StrongTerminal D V r C
        · rw [ite_eq_left terminal]
          have units := sum_le_sum (fun Z (zm : Z∈A)=>(due.routed Z zm).2.2.2.1)
          simp only [sum_const,nsmul_eq_mul,mul_one] at units
          exact units.trans (by exact_mod_cast due.bounded)
        · have empty : A=∅ := eq_empty_iff_forall_notMem.mpr (fun Z zm=>terminal (due.routed Z zm).2.2.2.2.1)
          simp [empty,terminal]
    exact primary_widths free reg proper ready

theorem remaining_complete {D V q r δ cap C A target} (free : QFree D V q) (reg : OutEq r D V)
    (t : Selection D V q r 3 (3*r)) (policy : ShellBooking t) (ready : RoutingRoom q r V.card target)
    (due : RemainingPayer t C δ cap A) (size : C.card+1=r) (reserve : 2*(r-q+1)<C.card)
    (margin : 4*6<3*C.card+6) (capacity : (2*r-1)*(2*r)<(r-1)*(2*(r+4))+r*14)
    (narrow : 4*(r-q+1)<3*(3*q+3-2*r)) (room : 4*(r-q+1)<C.card+6) :
    (exterior D V C).card=r-1 := by
  refine (remaining_widths free reg t policy ready due).resolve_right (fun ew=>?_ )
  exact one_omission_paid free ready.cycle.1 reg t due
    (pure_middle_rows free reg t policy ready due ew size reserve margin capacity narrow)
    ready.close ew size room reserve

attribute [aesop safe forward (immediate := [free,hq,reg,mark,mid,fit,width,size,room,reserve]) (rule_sets := [CHGraphFamilies])] one_omission_paid
attribute [aesop safe forward (immediate := [free,reg,policy,ready,due,size,reserve,margin,capacity,narrow,room]) (rule_sets := [CHGraphFamilies])] remaining_complete
#print axioms one_omission_paid
#print axioms remaining_complete
end LeanCH.BR.LowShellCycleSelection
