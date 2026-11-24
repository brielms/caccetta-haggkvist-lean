import checkpoints.shen_extension.MixedOmissionPayment

namespace LeanCH.BR.LowShellCycleSelection
open Finset BRq2 BRq3 BR45 BRsGen ExteriorPacking PhysicalCycleStock CHRuleCatalog

/-- At width r an actual acyclic secondary claimant requires a short
primary claimant on C. A strong terminal has width r−1, so no routed
arrival can subsidize this case. -/
theorem short_needed_on_mixed {D V q r C δ cap A target} (free : QFree D V q) (reg : OutEq r D V)
    {t : Selection D V q r 3 (3*r)} (policy : ShellBooking t) (room : RoutingRoom q r V.card target)
    (mark : MixedPayer t C δ cap A) (width : (exterior D V C).card=r) {Z} (zm : Z∈claims t C)
    (dag : QFree D (outN D V (t.rep Z)) (outN D V (t.rep Z)).card)
    (score : 3*r+2≤4+target) (enough : 4*(r-q+1)<3*(C.card-(r-q))) :
    ∃Y∈claims t C,C⊆outN D V (t.rep Y) ∧ (ball D V (t.rep Y) 3).card<3*r := by
  classical
  by_contra! none
  have hr := room.growth.2.1
  have empty : A=∅ := eq_empty_iff_forall_notMem.mpr (fun T tm=>by
    have opposite := (mark.charges.routed T tm).2.2.2.2.1.nextSize
    omega)
  have due := mark.charges.due
  rw [empty,sum_empty,add_zero] at due
  exact (not_lt_of_ge due) (mixed_medium_paid free reg t room policy width
    (by rw [mark.length,mark.degree]) none zm dag score enough)

def OmissionInput (p : Input) (target δ cap : ℕ) : Prop :=
  ∃F,(∀u v,F u v=true → p.D u v=true) ∧ OutEq p.s F (range p.n) ∧
    ∃t : Selection F (range p.n) (cutoff p) p.s 3 (3*p.s),ShellBooking t ∧ ∃C A,
    MixedPayer t C δ cap A ∧
    ((exterior F (range p.n) C).card=p.s → 3*p.s+2≤4+target →
    4*(p.s-cutoff p+1)<3*(C.card-(p.s-cutoff p)) →
    ∀Z∈claims t C,QFree F (outN F (range p.n) (t.rep Z)) (outN F (range p.n) (t.rep Z)).card →
    ∃Y∈claims t C,C⊆outN F (range p.n) (t.rep Y) ∧ (ball F (range p.n) (t.rep Y) 3).card<3*p.s)

theorem omission_from_input {p : Input} {target g mid top cap} (bad : Bad p)
    (room : PrimaryRoom (cutoff p) p.s p.n target g mid top cap)
    (reserve : cap+5<3*(p.s-1)) : OmissionInput p target (p.n-((p.s-1)+top)) cap := by
  obtain ⟨F,sub,reg,t,policy,C,A,mark⟩ := mixed_from_input bad room reserve
  refine ⟨F,sub,reg,t,policy,C,A,mark,?_⟩
  intro width score enough Z zm dag
  exact short_needed_on_mixed (qfree_sub sub (qfree_of_noShort bad.loopless bad.missing)) reg policy
    (by simpa only [card_range] using room.route) mark width zm dag score enough

structure OnOmissionPayer (p : Input) : Prop where
  on_room : ∀target g mid top cap,PrimaryRoom (cutoff p) p.s p.n target g mid top cap →
    cap+5<3*(p.s-1) → OmissionInput p target (p.n-((p.s-1)+top)) cap

theorem omission_on_bad {p : Input} (bad : Bad p) : OnOmissionPayer p := ⟨fun _ _ _ _ _=>omission_from_input bad⟩

attribute [aesop safe forward (immediate := [bad]) (rule_sets := [CHGraphFamilies])] omission_on_bad
attribute [aesop safe forward (immediate := [bad,room,reserve]) (rule_sets := [CHGraphFamilies])] omission_from_input
attribute [aesop safe forward (immediate := [free,reg,policy,room,mark,width,zm,dag,score,enough]) (rule_sets := [CHGraphFamilies])] short_needed_on_mixed
#print axioms short_needed_on_mixed
#print axioms omission_on_bad
end LeanCH.BR.LowShellCycleSelection
