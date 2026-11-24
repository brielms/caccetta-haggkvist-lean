import checkpoints.shen_extension.ShortestCyclePacking
import checkpoints.shen_extension.RootedCycleLayers
import checkpoints.shen_extension.CoreExchange

namespace LeanCH.BR.Closure.CycleClassFrontier
open Finset BRq2 BRq3 BR45 DeficitLevels BankDescentFrontier CutoffDegreeRank

/-- Properties of the very same source, allowing the cutoff to increase on
a smaller-degree or smaller-order transition. -/
structure LoopConditions {q s} (base : ℕ) (O : Origin q s) : Prop where
  ranked : Ranked base q s O.V.card
  first_arcs : ∀h∈O.V, (inN O.G O.V h).card+q*((outN O.G O.V h).card-s)
    ≤q*(ReturnArcRecurrence.first O.G O.V h q s).card
  cycle : ∀h∈O.V, ∀a∈ReturnArcRecurrence.first O.G O.V h q s, O.G h a=true ∧
    ∃M, ShenCycleSuccessor.Cycle O.G O.V q M ∧ h∈M ∧ a∈M
  core : ∃T⊆O.V, ShortestCyclePeeling.Dense O.G T q (s/(q+1)) ∧
    ∀x∈T,ShortestCycleClasses.carrier O.G T q x=T
  exchanges : ∀d U, U⊆O.V → U.Nonempty → U.card<O.V.card → U.card=q*d →
    ∃B⊆O.V, B.card=U.card ∧ Reach (CoreExchange.Step O.G O.V d) U B ∧
      (∃x∈B,(outN O.G B x).card<d) ∧ (∃y∈O.V\B,d<(outN O.G B y).card) ∧
      ∀x∈B,∀y∈O.V\B,(outN O.G B x).card<d → d<(outN O.G B y).card →
        (inN O.G B y).card<(inN O.G B x).card
  packing : ∃P, ShortestCyclePacking.Packing O.G O.V q P ∧
    (q+1)*s < O.V.card+q*((q+1)*P.card)
  overlap : ∀k, O.V.card≤(q+1)*(s-k) → ∃x∈O.V, ∀Z : Finset ℕ, Z.card≤k →
    ∃M⊆ShortestCycleClasses.carrier O.G O.V q x, M.card=q+1 ∧ OutEq 1 O.G M ∧ Disjoint M Z

theorem from_input {D V base s} (hb : 2≤base) (free : QFree D V base) (live : V.Nonempty)
    (ord : V.card≤base*s) (deg : ∀x∈V,s≤(outN D V x).card) :
    ∃ q d, d+1≤s ∧ ∃ (O : Origin q (d+1)) (st : State), LoopConditions base O ∧
      PackingFrontier.Frontier O st ∧ UnitLoopCapstone.AlternativesWithLoops O st ∧ BankRules O ∧
      ((h : q=3) → DenseArc.FanReturns O.G O.V d ∧ DenseArc.FourEscape (h ▸ O) ∧
                     PackedEscape (h ▸ O) ∧ TriangleRules (h ▸ O)) := by
  obtain ⟨q,d,le,O,st,rank,fr,alt,bank,three⟩ := CutoffDegreeRank.from_input hb free live ord deg
  have hq := hb.trans rank.1
  have budget : O.V.card≤(q+1)*((d+1)-(d+1)/(q+1)) := by
    have div := Nat.mod_add_div (d+1) (q+1)
    have ord := O.order
    rw [Nat.mul_sub,Nat.add_mul q 1 (d+1),Nat.one_mul]
    omega
  exact ⟨q,d,le,O,st,⟨rank,fun _ => ReturnArcRecurrence.at_root O hq,
    fun _ hv _ => ReturnArcRecurrence.cycle_of_first O hq hv,ShortestCyclePeeling.recurrent_core O hb rank budget,
    fun _ _ => CoreExchange.reachable_barrier O hq fr.lower_degrees,ShortestCyclePacking.packed O hb rank,
    fun _ => ShortestCycleClasses.hard_class O hb rank⟩,fr,alt,bank,three⟩

#print axioms from_input
end LeanCH.BR.Closure.CycleClassFrontier
