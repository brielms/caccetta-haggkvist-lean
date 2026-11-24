import checkpoints.shen_extension.RankedContractionEntry

namespace LeanCH.BR.RankedUnitDescent
open Finset BRq2 BRq3 WeightedSD Closure CHRuleCatalog RankedContractionEntry

/-- In the one-head loss window the strict head budget always buys at
    least the original degree. All parameters are natural numbers. -/
theorem degree_le_threshold {u q r : ℕ} (hq : 0<q) (hr : 0<r) (window : 1+q*r≤u+q) :
    r≤u/q+1 := by
  by_contra! low
  have lt : u/q<r-1 := by omega
  have small := (Nat.div_lt_iff_lt_mul hq).mp lt
  have split : (r-1)*q+q=q*r := calc
    _ = (r-1+1)*q := by rw [Nat.add_mul,Nat.one_mul]
    _ = q*r := by rw [show r-1+1=r by omega,Nat.mul_comm]
  omega

/-- A unit-price repair found even after pruning supplies a physical child
    on the original labels if surviving rows need at most one replacement.
    The catalogue re-enters at that child via apply_proposal and next_bad. -/
@[aesop safe forward (immediate := [bad,law,sub,two,rep,room,noLoss,upper,paid,one]) (rule_sets := [CHGraphFamilies])]
theorem proposal_from_paid {p : Input} (bad : Bad p)
    (law : RankedUnitWindow.WindowLaw (cutoff p) p.s p.D (range p.n)) {W : Finset ℕ} {z : ℕ}
    (sub : W⊆range p.n) (two : 2≤W.card) (rep : z∈W)
    (room : (range p.n\W).card<1+cutoff p*p.s) (noLoss : 1+cutoff p*p.s≤(range p.n\W).card+cutoff p)
    (upper : (range p.n).card≤1+cutoff p*p.s)
    (paid : ∃ E : CH.Digraph,(∀i j,E i j=true → p.D i j=true) ∧ ∃ H⊆range p.n\W,H.Nonempty ∧
      mass (range p.n\W) (fun _=>1)<(cutoff p:ℚ)*mass H (fun _=>1) ∧
      RankedHeadChoices.RowBills (cutoff p) E (range p.n\W) H (fun _=>1) (cutoff p-2))
    (one : ∀i∈range p.n\W,p.s≤(outN p.D (range p.n\W) i).card+1) :
    Proposal p W (FlatPeelReach.interior p.D (range p.n) (range p.n\W) (cutoff p-1)) z := by
  have hq := (remaining_from_run p bad).1
  have needed := (RankedMenuThreshold.criterion law (by omega) sub room noLoss upper).mp paid
  exact bank_proposal bad sub two rep ((degree_le_threshold (by omega) bad.degree_pos noLoss).trans needed) one

/-- An unpaid one-representative deletion identifies one physical row whose
    loss exceeds its spare degree plus the one head a representative can fund. -/
@[aesop safe forward (immediate := [window,sub,two,rich]) (rule_sets := [CHGraphFamilies])]
theorem lost_heads {q r : ℕ} {X : ShenMinimumOrder.Source q r}
    (window : RankedNativeContraction.NativeWindow X) {W : Finset ℕ} (sub : W⊆X.V) (two : 2≤W.card)
    (rich : r≤(FlatPeelReach.interior X.D X.V (X.V\W) (q-1)).card) :
    ∃i∈X.V\W,(outN X.D X.V i).card-r+2≤(outN X.D W i).card := by
  let U := X.V\W
  have fails : ¬∀i∈U,r≤(outN X.D U i).card+1 := fun paid=>(window.cap W sub two paid).not_ge rich
  push Not at fails
  obtain ⟨i,iu,short⟩ := fails
  have quota := X.degree i (mem_sdiff.mp iu).1
  have cover : outN X.D X.V i ⊆ outN X.D U i ∪ outN X.D W i := by
    intro j jj
    obtain ⟨jv,ij⟩ := mem_outN.mp jj
    by_cases cut : j∈W
    · exact mem_union_right _ (mem_outN.mpr ⟨cut,ij⟩)
    · exact mem_union_left _ (mem_outN.mpr ⟨mem_sdiff.mpr ⟨jv,cut⟩,ij⟩)
  have count := (card_le_card cover).trans (card_union_le _ _)
  exact ⟨i,iu,by omega⟩

#print axioms degree_le_threshold
#print axioms proposal_from_paid
#print axioms lost_heads
end LeanCH.BR.RankedUnitDescent
