import checkpoints.shen_extension.WidePrimaryReceipt

namespace LeanCH.BR.LowShellCycleSelection
open Finset BRq2 BRq3 BR45 BRsGen ExteriorPacking PhysicalCycleStock
open scoped Classical

/-- One simultaneous allocation on labelled cycles, with independently chosen
row and column index sets. Equality is allowed except at one physical payer. -/
structure FundedSchedule {D V q r k b} (sel : Selection D V q r k b) where
  payers : Finset (Finset ℕ)
  rooted : ∀T∈payers,∀x∈T,Rooted D V x T
  amount : Finset ℕ → Finset ℕ → ℚ
  nonneg : ∀C∈booked sel,∀T∈payers,0≤amount C T
  demand : ∀C∈booked sel,netDebt sel C≤∑T∈payers,amount C T
  available : ∀T∈payers,(∑C∈booked sel,amount C T)≤rowStock sel payers T
  unused : ∃T∈payers,(∑C∈booked sel,amount C T)<rowStock sel payers T

/-- Exact common-allocation consumer. Both appearances of each payment use
the same physical source, destination and amount. -/
theorem schedule_exit {D V q r k b} (sel : Selection D V q r k b) (free : QFree D V q)
    (hq : 2≤q) (reg : OutEq r D V) (time : k+k≤q)
    (floor : ∀u∈V,b≤(ball D V u k).card+1) (size : V.card≤2*b)
    (paid : Nonempty (FundedSchedule sel)) : False := by
  obtain ⟨f⟩ := paid
  have charged := sum_le_sum f.demand
  rw [sum_comm] at charged
  have remaining := sum_lt_sum f.available f.unused
  exact (not_lt_of_ge (no_global_surplus sel free hq reg time floor size f.rooted)) (charged.trans_lt remaining)

attribute [aesop safe forward (immediate := [paid,free,hq,reg,time,floor,size]) (rule_sets := [CHGraphFamilies])] schedule_exit
/-- Start from a literal bad graph. The only additional input is arithmetic.
The returned thinning and all its physical marks stay on the original labels. -/
theorem marked_from_input {p : CHRuleCatalog.Input} {target g mid top cap} (bad : CHRuleCatalog.Bad p)
    (room : PrimaryRoom (CHRuleCatalog.cutoff p) p.s p.n target g mid top cap) :
    ∃F,(∀a b,F a b=true → p.D a b=true) ∧ OutEq p.s F (range p.n) ∧
      ∃t : Selection F (range p.n) (CHRuleCatalog.cutoff p) p.s 3 (3*p.s),∃C,PrimaryShort t cap C := by
  obtain ⟨F,sub,reg⟩ := exists_outEq (fun v (vm : v∈range p.n)=>Compose.FloorSix.out_card bad.degree (mem_range.mp vm))
  have free := qfree_sub sub (qfree_of_noShort bad.loopless bad.missing)
  exact ⟨F,sub,reg,native_primary free reg ⟨0,mem_range.mpr bad.order⟩ (by simpa only [card_range] using room)⟩

attribute [aesop safe forward (immediate := [bad,room]) (rule_sets := [CHGraphFamilies])] marked_from_input
#print axioms marked_from_input
#print axioms schedule_exit
end LeanCH.BR.LowShellCycleSelection
