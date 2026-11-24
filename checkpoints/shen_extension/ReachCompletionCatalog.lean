import checkpoints.shen_extension.ReachDescentCatalog
import checkpoints.shen_extension.FifthStripLedger
import checkpoints.shen_extension.RegularFirstLayer
import checkpoints.shen_extension.SharedHeadSuppliers
import checkpoints.shen_extension.StrictPairBanks

namespace LeanCH.BR.ReachCompletionCatalog
open Finset BRq2 BRq3 CHRuleCatalog

/-- Every bad input, including an input reached by repair, carries this
order bound at its own cutoff. It uses no minimality of the input. -/
theorem bad_order {p : Input} (bad : Bad p) :
    FifthStripLedger.orderFloor (cutoff p) p.s ≤ p.n := by
  have free := qfree_of_noShort bad.loopless bad.missing
  have rank (v) (vm : v∈range p.n) := Compose.FloorSix.out_card bad.degree (mem_range.mp vm)
  have live : (range p.n).Nonempty := card_pos.mp (by simpa only [card_range] using bad.order)
  simpa only [card_range] using FifthStripLedger.order_floor free rank live

theorem source_order {q r} (X : ShenMinimumOrder.Source q r) :
    FifthStripLedger.orderFloor q r ≤ X.V.card :=
  FifthStripLedger.order_floor X.free X.degree X.nonempty

theorem order_exit {n q r : ℕ} (bound : FifthStripLedger.orderFloor q r ≤ n)
    (small : n < FifthStripLedger.orderFloor q r) : False := (Nat.not_lt_of_ge bound) small

/-- What a bad input must satisfy on the entire strip. This bundles the
implication so replay can carry it even before the cutoff is known. -/
def FifthBudget (n r q : ℕ) : Prop := 9≤r → q+7=2*r → q*r≤n+1

theorem bad_budget {p : Input} (bad : Bad p) : FifthBudget p.n p.s (cutoff p) := by
  intro rank strip
  have free := qfree_of_noShort bad.loopless bad.missing
  have degree (v) (vm : v∈range p.n) := Compose.FloorSix.out_card bad.degree (mem_range.mp vm)
  have live : (range p.n).Nonempty := card_pos.mp (by simpa only [card_range] using bad.order)
  simpa only [card_range] using FifthStripLedger.fifth_order free degree live rank strip

theorem budget_exit {n r q : ℕ} (budget : FifthBudget n r q) (rank : 9≤r)
    (strip : q+7=2*r) (small : n+2≤q*r) : False := by
  have bound := budget rank strip
  omega

theorem literal_fifth_strip {n r q} {D : CH.Digraph} (hn : 0<n) (rank : 9≤r)
    (cut : CH.ceilDiv n r=q) (strip : q+7=2*r) (small : n+2≤q*r)
    (loopless : CH.Loopless D n) (degree : CH.MinOutdegreeAtLeast D n r) :
    CH.HasDirectedCycleAtMost D n (CH.ceilDiv n r) := by
  by_contra missing
  have budget := bad_budget (p := ⟨n,r,D⟩) ⟨hn,by change 0<r; omega,loopless,degree,missing⟩
  change FifthBudget n r (CH.ceilDiv n r) at budget
  exact budget_exit (cut ▸ budget) rank strip small

/-- A literal CH conclusion when the decidable strip bound exceeds the order. -/
theorem literal_below {n r : ℕ} {D : CH.Digraph} (hn : 0<n) (hr : 0<r)
    (loopless : CH.Loopless D n) (degree : CH.MinOutdegreeAtLeast D n r)
    (small : n < FifthStripLedger.orderFloor (CH.ceilDiv n r) r) :
    CH.HasDirectedCycleAtMost D n (CH.ceilDiv n r) := by
  by_contra missing
  exact order_exit (bad_order (p := ⟨n,r,D⟩) ⟨hn,hr,loopless,degree,missing⟩) small

attribute [aesop safe forward (immediate := [free,degree,live]) (rule_sets := [CHGraphFamilies])]
  FifthStripLedger.order_floor
attribute [aesop safe forward (immediate := [bad]) (rule_sets := [CHGraphFamilies])] bad_order
attribute [aesop safe forward (immediate := [X]) (rule_sets := [CHGraphFamilies])] source_order
attribute [aesop safe forward (immediate := [bound,small]) (rule_sets := [CHGraphFamilies])] order_exit
attribute [aesop safe forward (immediate := [bad]) (rule_sets := [CHGraphFamilies])] bad_budget
attribute [aesop safe forward (immediate := [budget,rank,strip,small]) (rule_sets := [CHGraphFamilies])] budget_exit
attribute [aesop safe forward (immediate := [free,degree,live,rank,strip]) (rule_sets := [CHGraphFamilies])]
  FifthStripLedger.fifth_order

attribute [aesop safe forward (immediate := [free,degree,size,pos,hij,fi,fj,arith]) (rule_sets := [CHGraphFamilies])]
  MixedRadiusCompletion.capacity_regime
attribute [aesop safe forward (immediate := [free,degree,size,none,above,law,hq,ht,tq,order,arith,small,hn]) (rule_sets := [CHGraphFamilies])]
  SharedHeadSuppliers.bank_regime
attribute [aesop safe forward (immediate := [free,hq,size,live,floor,tight,arith]) (rule_sets := [CHGraphFamilies])]
  SharedHeadSuppliers.tied_regime
attribute [aesop safe forward (immediate := [free,hq,degree,floor,vv,one,two,hd,d1,low,arith]) (rule_sets := [CHGraphFamilies])]
  RegularFirstLayer.third_floor
attribute [aesop safe forward (immediate := [free,hq,exact,hr,law,ht,t1,none,none',vv,two,paid,third,quota,pos,wide,deep,cap]) (rule_sets := [CHGraphFamilies])]
  RegularFirstLayer.regular_regime
attribute [aesop safe forward (immediate := [free,hq,hr,exact,size,floor2,floor3,hb,regular,count,third,excess,arith]) (rule_sets := [CHGraphFamilies])]
  StrictPairBanks.strict_count_regime
attribute [aesop safe forward (immediate := [lower,free,hr,hr1,vv,one]) (rule_sets := [CHGraphFamilies])]
  StrictPairBanks.regular_of_lower

#print axioms bad_order
#print axioms source_order
#print axioms literal_below
#print axioms literal_fifth_strip
end LeanCH.BR.ReachCompletionCatalog
