import checkpoints.shen_extension.OneExtraSecondShell

namespace LeanCH.BR.LowShellCycleSelection
open Finset BRq2 BRq3 BR45 BRsGen ExteriorPacking PhysicalCycleStock CHRuleCatalog
open scoped Classical

/-- The low row, the original cycle, each competing representative, and
its extra second head are chosen on one and the same marked graph. -/
def PricedPrimaryInput (p : Input) (δ cap : ℕ) : Prop :=
  ∃F,(∀u v,F u v=true → p.D u v=true) ∧ OutEq p.s F (range p.n) ∧
    ∃t : Selection F (range p.n) (cutoff p) p.s 3 (3*p.s), ShellBooking t ∧ ∃C,
      RemainingPayer t C δ cap ∅ ∧ C.card=cutoff p+1 ∧ p.s=cutoff p+2 ∧
      CompleteAccount t C ∅ ∧ (∀e∈exterior F (range p.n) C,Rooted F (range p.n) e (exterior F (range p.n) C)) ∧
      (∃a∈C,(ball F (range p.n) a 3).card=3*p.s+1) ∧
      ∀Y∈claims t C,C⊆outN F (range p.n) (t.rep Y) →
        (ball F (range p.n) (t.rep Y) 3).card=3*p.s ∧ (N3 F (range p.n) (t.rep Y)).card=p.s-1 ∧
        ∃b∈Y\exterior F (range p.n) C,Y=insert b (exterior F (range p.n) C)

theorem price_cyclic_primaries {p : Input} {target g mid top δ cap} (bad : Bad p)
    (cyclic : CyclicExteriorInput p δ cap) (ready : RoutingRoom (cutoff p) p.s p.n target)
    (score : ScoreRoom (cutoff p) p.s (p.s-1) g) (step : GrowthRoom (cutoff p) p.s g mid)
    (again : GrowthRoom (cutoff p) p.s mid top)
    (cost : p.n+8<(p.s-1)+top+3*(p.s-1))
    (capacity : (2*p.s-1)*(2*p.s)<(p.s-1)*(2*(p.s+4))+p.s*14) : PricedPrimaryInput p δ cap := by
  obtain ⟨F,sub,reg,t,policy,C,mark,length,degree,account,next⟩ := cyclic
  have free := qfree_sub sub (qfree_of_noShort bad.loopless bad.missing)
  have room : RoutingRoom (cutoff p) p.s (range p.n).card target := by simpa using ready
  have hq := ready.cycle.1
  obtain ⟨a,am,low⟩ := direct_low_cycle_row free reg t policy room mark account (by omega) next score step again
    (by omega) (by rw [card_range]; omega)
  refine ⟨F,sub,reg,t,policy,C,mark,length,degree,account,next,⟨a,am,low⟩,?_⟩
  intro Y ym first
  exact primary_one_extra free reg t policy room account ym first (by omega) (by omega) am low.le next (.inl capacity)

attribute [aesop safe forward (immediate := [bad,cyclic,ready,score,step,again,cost,capacity]) (rule_sets := [CHGraphFamilies])] price_cyclic_primaries
attribute [aesop safe forward (immediate := [free,uv,am,initial,internal,time,seen]) (rule_sets := [CHGraphFamilies])] BankReachTransfer.prefix_return_size
#print axioms price_cyclic_primaries
end LeanCH.BR.LowShellCycleSelection
