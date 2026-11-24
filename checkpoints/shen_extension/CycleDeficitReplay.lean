import checkpoints.shen_extension.WeakBankCompression
import checkpoints.shen_extension.CHFamilyDeclarations

namespace LeanCH.BR.LowShellCycleSelection
open Finset BRq2 BRq3 BR45 BRsGen ExteriorPacking PhysicalCycleStock

def FirstClaim {D V q r k b} (sel : Selection D V q r k b) (C : Finset ℕ) : Prop :=
  ∃Y∈claims sel C,C⊆outN D V (sel.rep Y) ∧ ¬QFree D (outN D V (sel.rep Y)) (outN D V (sel.rep Y)).card

def RoutedClaim {D V q r} (sel : Selection D V q r 3 (3*r)) (C : Finset ℕ) : Prop :=
  ∃Y,claims sel C={Y} ∧ QFree D (outN D V (sel.rep Y)) (outN D V (sel.rep Y)).card ∧ sel.pay Y=C ∧ omissions D V C r≤1 ∧
    let Z := N3 D V (sel.rep Y)
    let B := bankIteration D V Z
    ∃v∈C,Z⊆outN D V v ∧ (ball D V v 3).card=3*r+1 ∧ ∃k,k+2≤q ∧
      (∀j≤k+1,(B j).card=r-1 ∧ ∀x∈B j,Rooted D V x (B j)) ∧
      ∀x∈B k,3*r+2≤(ball D V x 3).card

theorem routed_deficit {D V q r target} (free : QFree D V q) (reg : OutEq r D V)
    (hr : 2≤r) (live : V.Nonempty) (sel : Selection D V q r 3 (3*r))
    (regime : Room q r) (mixed : ShellBankOrders.MixedRoom q r) (size : V.card≤2*(3*r))
    (one : r≤q+2) (fit : r+1<2*(q-1)) (dist : (r-(q+1))*(r-q)+3≤q)
    (guard : ScoreRoom q r (r-1) target) (pay : 3*r<4+target)
    (squeeze : CompressionRoom q r (r-1) (2*(r-1)+1) (3*(r-1)))
    (order : V.card<(q+1)*(r-1)) (margin : 2*(r-q+1)<3*((q+1)-(r-(q+1))*(r-q))) :
    ∃t : Selection D V q r 3 (3*r),t.rep=sel.rep ∧ ∃C∈booked t,shortfall t C (r-q) ∧
      (FirstClaim t C ∨ RoutedClaim t C) := by
  obtain ⟨t,eq,C,cm,bill,alternatives⟩ := marked_unpaid free reg (by omega) live sel regime mixed size one fit dist guard pay
  refine ⟨t,eq,C,cm,bill,?_⟩
  rcases alternatives with first|⟨Y,only,dag,yc,om,_,tiers⟩
  · exact Or.inl first
  have yk : Y∈claims t C := only.symm ▸ mem_singleton_self Y
  have cap : (r-q+1)*2^(omissions D V C r)≤2*(r-q+1) := by
    have two : 2^(omissions D V C r)≤2^1 := Nat.pow_le_pow_right (by decide) om
    have le := Nat.mul_le_mul_left (r-q+1) two
    simpa [Nat.mul_comm] using le
  have bounds := tiers.trans cap
  rw [←yc] at bounds
  have result := weak_row_chain free reg hr t (mem_filter.mp yk).1 dag regime one fit dist guard pay squeeze
    order (2*(r-q+1)) bounds margin
  rw [yc] at result
  exact .inr ⟨Y,only,dag,yc,om,result⟩

/-- Every marked input, before or after descent, can instantiate the deficit
on an exact thinning while preserving its chosen class representatives. -/
structure OnRoutedDeficit (p : CHRuleCatalog.Input) : Prop where
  on_graph : ∀q≤CHRuleCatalog.cutoff p,∀target,
    Room q p.s → ShellBankOrders.MixedRoom q p.s → p.n≤2*(3*p.s) → p.s≤q+2 →
    p.s+1<2*(q-1) → (p.s-(q+1))*(p.s-q)+3≤q →
    ScoreRoom q p.s (p.s-1) target → 3*p.s<4+target →
    CompressionRoom q p.s (p.s-1) (2*(p.s-1)+1) (3*(p.s-1)) →
    p.n<(q+1)*(p.s-1) → 2*(p.s-q+1)<3*((q+1)-(p.s-(q+1))*(p.s-q)) →
    ∀F,(∀a b,F a b=true → p.D a b=true) → OutEq p.s F (range p.n) →
      ∀sel : Selection F (range p.n) q p.s 3 (3*p.s),∃t : Selection F (range p.n) q p.s 3 (3*p.s),
        t.rep=sel.rep ∧ ∃C∈booked t,shortfall t C (p.s-q) ∧ (FirstClaim t C ∨ RoutedClaim t C)

theorem routed_on_bad {p : CHRuleCatalog.Input} (bad : CHRuleCatalog.Bad p) : OnRoutedDeficit p := by
  constructor
  intro q cut target room mixed size one fit dist guard pay squeeze order margin F sub reg sel
  have free := qfree_sub sub ((qfree_of_noShort bad.loopless bad.missing).mono_bound cut)
  have degree := mixed.2.1
  exact routed_deficit free reg (by omega) ⟨0,mem_range.mpr bad.order⟩ sel room mixed (by simpa using size)
    one fit dist guard pay squeeze (by simpa using order) margin

attribute [aesop safe forward (immediate := [bad]) (rule_sets := [CHGraphFamilies])] routed_on_bad


structure RoutingRoom (q r n target : ℕ) : Prop where
  cycle : Room q r
  growth : ShellBankOrders.MixedRoom q r
  small : n≤2*(3*r)
  close : r≤q+2
  space : r+1<2*(q-1)
  distance : (r-(q+1))*(r-q)+3≤q
  score : ScoreRoom q r (r-1) target
  high : 3*r<4+target
  squeeze : CompressionRoom q r (r-1) (2*(r-1)+1) (3*(r-1))
  finite : n<(q+1)*(r-1)
  margin : 2*(r-q+1)<3*((q+1)-(r-(q+1))*(r-q))

/-- Fire once on the graph, quota and horizon. The new selection is output
only; creating it cannot retrigger this producer on the same inputs. -/
theorem native_deficit {D V q r target} (free : QFree D V q) (reg : OutEq r D V)
    (live : V.Nonempty) (ready : RoutingRoom q r V.card target) :
    ∃t : Selection D V q r 3 (3*r),∃C∈booked t,shortfall t C (r-q) ∧
      (FirstClaim t C ∨ RoutedClaim t C) := by
  obtain ⟨hq,a,b,c,d,e,f,g⟩ := ready.cycle
  obtain ⟨sel⟩ := native_selection free hq reg a b c d e f g
  obtain ⟨t,_,cc⟩ := routed_deficit free reg (by have := ready.growth.2.1; omega) live sel
    ready.cycle ready.growth ready.small ready.close ready.space ready.distance ready.score ready.high
    ready.squeeze ready.finite ready.margin
  exact ⟨t,cc⟩

attribute [aesop safe forward (immediate := [free,reg,live,ready]) (rule_sets := [CHGraphFamilies])] native_deficit
ch_family_split_result native_deficit

attribute [aesop safe forward (immediate := [free,hq,sub,distinct,first,slots,wide,time])
  (rule_sets := [CHGraphFamilies])] at_most_one_contact first_cohort_debt

#print axioms native_deficit

#print axioms routed_on_bad
end LeanCH.BR.LowShellCycleSelection
