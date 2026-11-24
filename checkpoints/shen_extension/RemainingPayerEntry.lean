import checkpoints.shen_extension.SimultaneousShellPayments

namespace LeanCH.BR.LowShellCycleSelection
open Finset BRq2 BRq3 BR45 BRsGen ExteriorPacking PhysicalCycleStock CHRuleCatalog

theorem remaining_dimensions {D V q r target g mid top cap C A} {t : Selection D V q r 3 (3*r)}
    (free : QFree D V q) (reg : OutEq r D V) (policy : ShellBooking t)
    (room : PrimaryRoom q r V.card target g mid top cap)
    (due : RemainingPayer t C (V.card-((r-1)+top)) cap A) : C.card=q+1 ∧ r=q+2 := by
  classical
  obtain ⟨Y,ym,kept,first,cy⟩ := first_is_kept policy due.first
  have fit := room.route.close
  have hq := room.route.cycle.1
  have hr := room.route.growth.2.1
  by_cases mv : C∈shortSwitches t
  · have wid := (mem_filter.mp mv).2.1
    have long := t.length _ (t.assigned Y (mem_filter.mp ym).1)
    rw [(mem_filter.mp ym).2] at long
    exact ⟨by omega,by omega⟩
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
    have proper' := proper_primary free reg proper room.route
    exact ⟨proper'.length,proper'.parameters⟩

theorem remaining_orientation {D V q r C A δ cap} {t : Selection D V q r 3 (3*r)}
    (m : RemainingPayer t C δ cap A) (width : (exterior D V C).card=r)
    (size : C.card+1=r) (enough : 2*(r-q+1)<C.card) :
    (∀Y∈claims t C,¬QFree D (outN D V (t.rep Y)) (outN D V (t.rep Y)).card) ∨
    ∃Y∈claims t C,C⊆outN D V (t.rep Y) ∧ (ball D V (t.rep Y) 3).card<3*r := by
  classical
  by_contra! no
  obtain ⟨⟨Z,zm,dag⟩,medium⟩ := no
  exact m.excluded ⟨m.bookedHere,width,size,enough,⟨Z,zm,dag⟩,medium⟩

def RemainingInput (p : Input) (δ cap : ℕ) : Prop :=
  ∃F,(∀u v,F u v=true → p.D u v=true) ∧ OutEq p.s F (range p.n) ∧
    ∃t : Selection F (range p.n) (cutoff p) p.s 3 (3*p.s),
      ShellBooking t ∧ ∃C A,RemainingPayer t C δ cap A ∧ C.card=cutoff p+1 ∧ p.s=cutoff p+2

theorem remaining_from_input {p : Input} {target g mid top cap} (bad : Bad p)
    (room : PrimaryRoom (cutoff p) p.s p.n target g mid top cap)
    (reserve : cap+5<3*(p.s-1)) (afford : 4*(p.s-cutoff p+1)<3*fullRowFloor (cutoff p) p.s) : RemainingInput p (p.n-((p.s-1)+top)) cap := by
  obtain ⟨F,sub,reg⟩ := exists_outEq (fun v (vm : v∈range p.n)=>Compose.FloorSix.out_card bad.degree (mem_range.mp vm))
  have free := qfree_sub sub (qfree_of_noShort bad.loopless bad.missing)
  have onF : PrimaryRoom (cutoff p) p.s (range p.n).card target g mid top cap := by simpa using room
  obtain ⟨hq,a,b,c,d,e,f,h⟩ := room.route.cycle
  obtain ⟨s⟩ := native_selection free hq reg a b c d e f h
  obtain ⟨t,_,policy⟩ := book_short_shells free reg s room.route.cycle room.route.growth.2.1 room.route.close
  obtain ⟨C,A,mark⟩ := remaining_after_partial_routes free reg ⟨0,mem_range.mpr bad.order⟩ t policy onF reserve afford
  have dim := remaining_dimensions free reg policy onF mark
  exact ⟨F,sub,reg,t,policy,C,A,by simpa only [card_range] using mark,dim⟩

structure OnRemainingPayer (p : Input) : Prop where
  on_room : ∀target g mid top cap,PrimaryRoom (cutoff p) p.s p.n target g mid top cap →
    cap+5<3*(p.s-1) → 4*(p.s-cutoff p+1)<3*fullRowFloor (cutoff p) p.s → RemainingInput p (p.n-((p.s-1)+top)) cap

theorem remaining_on_bad {p : Input} (bad : Bad p) : OnRemainingPayer p := ⟨fun _ _ _ _ _=>remaining_from_input bad⟩

attribute [aesop safe forward (immediate := [bad]) (rule_sets := [CHGraphFamilies])] remaining_on_bad
attribute [aesop safe forward (immediate := [bad,room,reserve,afford]) (rule_sets := [CHGraphFamilies])] remaining_from_input
#print axioms remaining_on_bad
#print axioms remaining_from_input
attribute [aesop safe forward (immediate := [m,width,size,enough]) (rule_sets := [CHGraphFamilies])] remaining_orientation
ch_family_split_result remaining_orientation
#print axioms remaining_orientation
end LeanCH.BR.LowShellCycleSelection
