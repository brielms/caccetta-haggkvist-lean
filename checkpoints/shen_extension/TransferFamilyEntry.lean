import checkpoints.shen_extension.RecoveredCyclePayment

namespace LeanCH.BR.LowShellCycleSelection
open Finset BRq2 BRq3 BR45 BRsGen ExteriorPacking PhysicalCycleStock CHRuleCatalog

/-- One concrete debit can be routed with the common-arrival congestion bound.
Its removal leaves at most one unit on the named source. -/
structure RoutedDebit {D V q r} (t : Selection D V q r 3 (3*r)) (C Z : Finset ℕ) (δ : ℕ) : Prop where
  amount : shellDebt D V 3 (3*r) Z≤1
  remaining : netDebt t C-(shellDebt D V 3 (3*r) Z:ℚ)≤1
  paidHere : 2*(r-q+1)<C.card → 1<rowStock t (booked t) C
  arrival : ∃T,StrongTerminal D V r T ∧ WeakArrival D V r δ (fullRowFloor q r) 1 C T

theorem mixed_item {D V q r target g mid top cap C A Z} (free : QFree D V q)
    (reg : OutEq r D V) (t : Selection D V q r 3 (3*r)) (policy : ShellBooking t)
    (room : PrimaryRoom q r V.card target g mid top cap)
    (mark : MixedPayer t C (V.card-((r-1)+top)) cap A)
    (width : (exterior D V C).card=r) (zm : Z∈claims t C)
    (dag : QFree D (outN D V (t.rep Z)) (outN D V (t.rep Z)).card)
    (medium : ∀Y∈claims t C,C⊆outN D V (t.rep Y) → 3*r≤(ball D V (t.rep Y) 3).card)
    (afford : 4*(r-q+1)<3*fullRowFloor q r) : RoutedDebit t C Z (V.card-((r-1)+top)) := by
  have hr := room.route.growth.2.1
  refine ⟨(acyclic_class_debit free reg (by omega) t (mem_filter.mp zm).1 room.route.cycle dag
    (by have := room.route.close; have := room.route.space; omega) room.route.distance).2,?_,?_,
    medium_route free reg t policy room mark width zm dag medium afford⟩
  · exact residual_after_transfer free reg t room.route policy width (by rw [mark.length,mark.degree]) zm dag medium
  · intro enough
    exact stock_after_secondary free reg t room.route zm dag (by rw [mark.length,mark.degree]) width enough (by omega)

def TransferInput (p : Input) (δ cap : ℕ) : Prop :=
  ∃F,(∀u v,F u v=true → p.D u v=true) ∧ OutEq p.s F (range p.n) ∧
    ∃t : Selection F (range p.n) (cutoff p) p.s 3 (3*p.s),ShellBooking t ∧ ∃C A,
    MixedPayer t C δ cap A ∧ ((exterior F (range p.n) C).card=p.s →
      4*(p.s-cutoff p+1)<3*fullRowFloor (cutoff p) p.s →
      ∀Z∈claims t C,QFree F (outN F (range p.n) (t.rep Z)) (outN F (range p.n) (t.rep Z)).card →
      ((∃Y∈claims t C,C⊆outN F (range p.n) (t.rep Y) ∧ (ball F (range p.n) (t.rep Y) 3).card<3*p.s)
        ∨ RoutedDebit t C Z δ))

theorem transfer_from_input {p : Input} {target g mid top cap} (bad : Bad p)
    (room : PrimaryRoom (cutoff p) p.s p.n target g mid top cap)
    (reserve : cap+5<3*(p.s-1)) : TransferInput p (p.n-((p.s-1)+top)) cap := by
  classical
  obtain ⟨F,sub,reg,t,policy,C,A,mark⟩ := mixed_from_input bad room reserve
  refine ⟨F,sub,reg,t,policy,C,A,mark,?_⟩
  intro width afford Z zm dag
  by_cases short : ∃Y∈claims t C,C⊆outN F (range p.n) (t.rep Y) ∧ (ball F (range p.n) (t.rep Y) 3).card<3*p.s
  · exact .inl short
  push Not at short
  right
  have free := qfree_sub sub (qfree_of_noShort bad.loopless bad.missing)
  have onF : PrimaryRoom (cutoff p) p.s (range p.n).card target g mid top cap := by simpa using room
  simpa only [card_range] using mixed_item free reg t policy onF (by simpa only [card_range] using mark)
    width zm dag short afford

structure OnItemizedTransfer (p : Input) : Prop where
  on_room : ∀target g mid top cap,PrimaryRoom (cutoff p) p.s p.n target g mid top cap →
    cap+5<3*(p.s-1) → TransferInput p (p.n-((p.s-1)+top)) cap
theorem transfer_on_bad {p : Input} (bad : Bad p) : OnItemizedTransfer p :=
  ⟨fun _ _ _ _ _=>transfer_from_input bad⟩

theorem transfer_cases {D V q r target g mid top cap C A Z} (free : QFree D V q)
    (reg : OutEq r D V) {t : Selection D V q r 3 (3*r)} (policy : ShellBooking t)
    (room : PrimaryRoom q r V.card target g mid top cap) (mark : MixedPayer t C (V.card-((r-1)+top)) cap A)
    (width : (exterior D V C).card=r) (zm : Z∈claims t C)
    (dag : QFree D (outN D V (t.rep Z)) (outN D V (t.rep Z)).card)
    (afford : 4*(r-q+1)<3*fullRowFloor q r) :
    (∃Y∈claims t C,C⊆outN D V (t.rep Y) ∧ (ball D V (t.rep Y) 3).card<3*r) ∨
      RoutedDebit t C Z (V.card-((r-1)+top)) := by
  classical
  by_cases short : ∃Y∈claims t C,C⊆outN D V (t.rep Y) ∧ (ball D V (t.rep Y) 3).card<3*r
  · exact .inl short
  push Not at short
  exact .inr (mixed_item free reg t policy room mark width zm dag short afford)

attribute [aesop safe forward (immediate := [bad]) (rule_sets := [CHGraphFamilies])] transfer_on_bad
attribute [aesop safe forward (immediate := [bad,room,reserve]) (rule_sets := [CHGraphFamilies])] transfer_from_input
attribute [aesop safe forward (immediate := [free,reg,policy,room,mark,width,zm,dag,afford]) (rule_sets := [CHGraphFamilies])] transfer_cases
ch_family_split_result transfer_cases
#print axioms mixed_item
#print axioms transfer_on_bad
end LeanCH.BR.LowShellCycleSelection
