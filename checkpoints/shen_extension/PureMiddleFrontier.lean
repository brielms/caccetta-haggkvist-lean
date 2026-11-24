import checkpoints.shen_extension.MarkedMiddlePrice

namespace LeanCH.BR.LowShellCycleSelection
open Finset BRq2 BRq3 BR45 BRsGen ExteriorPacking PhysicalCycleStock
open scoped Classical

structure MiddleRows {D V q r} (t : Selection D V q r 3 (3*r)) (C : Finset ℕ) : Prop where
  each : ∀Y∈claims t C,C⊆outN D V (t.rep Y) ∧ Y.card=r ∧
    (N3 D V (t.rep Y)).card=r-1 ∧ (ball D V (t.rep Y) 3).card=3*r
  ceiling : rowStock t (booked t) C≤2

/-- At width equal to the degree every actual class remaining on the unpaid
cycle has the same shell sizes. The representatives, their head incidence,
and the common stock are retained for the next rule. -/
theorem pure_middle_rows {D V q r target δ cap C A} (free : QFree D V q)
    (reg : OutEq r D V) (t : Selection D V q r 3 (3*r)) (policy : ShellBooking t)
    (ready : RoutingRoom q r V.card target) (mark : RemainingPayer t C δ cap A)
    (width : (exterior D V C).card=r) (size : C.card+1=r) (enough : 2*(r-q+1)<C.card)
    (margin : 4*6<3*C.card+6) (capacity : (2*r-1)*(2*r)<(r-1)*(2*(r+4))+r*14)
    (supply : 4*(r-q+1)<3*(3*q+3-2*r)) : MiddleRows t C := by
  classical
  have hq := ready.cycle.1
  have hr := ready.growth.2.1
  have fit := ready.close
  have ⟨cyclic,med⟩ := remaining_medium_primary free reg t policy ready mark width size enough margin
  have off : C∉shortSwitches t := by
    intro sw; have := (switched_shell_paid free reg t (by omega) hr fit sw).1.width; omega
  have debit := one_omission_total free reg t ready policy off width size med
  have empty : A=∅ := eq_empty_iff_forall_notMem.mpr (fun Z zm=>by
    have := (mark.routed Z zm).2.2.2.2.1.nextSize; omega)
  have due := mark.due
  rw [empty,sum_empty,add_zero] at due
  have limit := due.trans debit
  refine ⟨?_,limit⟩
  intro Y ym
  obtain ⟨key,id⟩ := mem_filter.mp ym
  have kept : Y∉shortSwitches t := fun sw=>off (((policy.secondary Y sw).symm.trans id) ▸ sw)
  have first := id ▸ policy.primary Y key kept (cyclic Y ym)
  have uv := rep_native t key
  have y := rep_key t key
  have low := (mem_filter.mp (mem_filter.mp (t.represents Y key)).1).2
  have eq := le_antisymm low (med Y ym first)
  obtain ⟨_,a,b,c,d,_⟩ := ready.cycle
  have lo := GuardedLayerGrowth.second_floor free (by omega) reg (by omega) (by omega) uv
  have hi := low_third_second free hq reg uv a b c d low
  change (ball D V (t.rep Y) 2).card≤2*r+1 at hi
  have one := card_B1 (free.mono_bound (by omega : 4≤q)) uv
  rw [reg _ uv] at one
  have two := @card_B2 D V (t.rep Y)
  have three := @card_B3 D V (t.rep Y)
  have full : (N2 D V (t.rep Y)).card=r := by
    by_contra neg
    have narrow : (N2 D V (t.rep Y)).card=r-1 := by omega
    have rooted := t.rooted _ (t.assigned _ key)
    have len := t.length _ (t.assigned _ key)
    rw [id] at rooted len
    obtain ⟨rows,paid⟩ := actual_narrow_middle free hq reg uv fit hr a narrow (by omega) capacity first len rooted
    let L := C.filter (fun x=>(outN D (outN D V (t.rep Y)) x).card=1)
    have per x (xm : x∈L) : 3≤surplus (3*r) (ball D V x 3).card := by
      have := paid x (mem_filter.mp xm).1 (mem_filter.mp xm).2
      simp [surplus,show 3*r<(ball D V x 3).card by omega]; omega
    have summed := sum_le_sum per
    simp only [sum_const_nat (fun _ _=>rfl)] at summed
    have sub : ∑v∈L,surplus (3*r) (ball D V v 3).card≤∑v∈C,surplus (3*r) (ball D V v 3).card :=
      sum_le_sum_of_subset (filter_subset _ _)
    have scale K (km : K∈booked t) : omissions D V K r≤r-q := by
      obtain ⟨Z,zk,rfl⟩ := mem_image.mp km; exact t.loss _ (t.assigned _ zk)
    have cap := booked_score_cap free reg (by omega : r-q+2≤q) t scale mark.bookedHere (allowance:=2) (by simpa using limit)
    have om : omissions D V C r=1 := by unfold omissions; rw [width]; omega
    rw [om,pow_one] at cap
    change 3*q+3-2*r≤L.card at rows
    omega
  exact ⟨first,(congrArg card y).symm.trans full,by omega,eq⟩

#print axioms pure_middle_rows
end LeanCH.BR.LowShellCycleSelection
