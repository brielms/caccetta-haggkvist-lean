import checkpoints.shen_extension.PuncturedRootReturns
import checkpoints.shen_extension.FirstArcRecurrence
import checkpoints.shen_extension.DisjointRootFourCycles

namespace LeanCH.BR.Closure.BankDescentFrontier
open Finset BRq2 BRq3 BR45 DeficitLevels CoverBankRecurrence

structure BankRules {q s} (O : Origin q s) : Prop where
  order : ∀ W m d, W⊆O.V → ((d=s ∧ W.card+m<O.V.card) ∨ (d<s ∧ W.card+m≤q*d)) →
    (∀x∈W,d≤(outN O.G W x).card+m) → m≤q*(d-(ReturnBankOrder.exits O.G W q d).card)
  remote : ∀ S H p, S⊆O.V → H⊆O.V\S → (∀a∈S, ∀h∈H,O.G a h=true) →
    S.card=s → p∈O.V\S → q*(s-(H.erase p).card)<s →
    ∃x∈(O.V\S).erase p,(outN O.G O.V x).card=s ∧ O.G x p=true ∧ outN O.G S x=∅
  capacity : ∀ S H, S⊆O.V → H⊆O.V\S → (∀a∈S, ∀h∈H, O.G a h=true) →
    q*(s-H.card)+2≤S.card → let P := parents O.G O.V S s
                            0<P.card ∧ P.card≤q*(s-(S.card-1))
  transfer : ∀ S H, S⊆O.V → H⊆O.V\S → (∀a∈S, ∀h∈H, O.G a h=true) →
    q*(s-H.card)+2≤S.card → S.card=s → 2≤(parents O.G O.V S s).card →
    let P := parents O.G O.V S s
    ∃x∈(O.V\S)\P, (outN O.G O.V x).card=s ∧ P⊆outN O.G O.V x ∧ outN O.G S x=∅
  price : ∀ L : PaidLayerDescent.Layers O.G O.V, ((O.V\L.old)\L.bank).Nonempty →
    (L.old∪L.bank).Nonempty → ∃x∈(O.V\L.old)\L.bank, q*s+1+L.old.card+L.bank.card ≤
      O.V.card+q*L.cost+q*(outN O.G L.bank x).card

structure TriangleRules {s} (O : Origin 3 s) : Prop where
  arc_share : (∑h∈O.V,(outN O.G O.V h).card) ≤ 3*(∑h∈O.V,(RootFirstArcReturns.firstArcs O.G O.V h s).card)
  component : ∀ C, C⊆O.V → C.card<O.V.card → C.Nonempty →
    (∀h∈C, RootFirstArcReturns.firstArcs O.G O.V h s⊆C) →
    ∃h∈C, 3*((outN O.G O.V h).card-s)+3*(((inN O.G O.V h).card+2)/3)+1≤C.card
  middle : ∀h∈O.V, s≤(inN O.G O.V h).card → ∀ T : Finset ℕ, T.Nonempty →
    T⊆O.V\insert h (inN O.G O.V h ∪ outN O.G O.V h) → PuncturedRootReturns.firsts O.G O.V h T=∅ →
    s+T.card+1≤3*(PuncturedRootReturns.overloaded O.G O.V h T ((T.card+1)/2)).card

def PackedEscape {s} (O : Origin 3 s) : Prop :=
  ∃h∈O.V, s≤(inN O.G O.V h).card ∧ DenseArc.UnmatchedTight O.G O.V s h ∧
    DenseArc.FourRoot O.G O.V h ∧ ∃P, DisjointRootFourCycles.Packing O.G O.V h P ∧
    s+14≤30*P.card

theorem recursive_banks {D V q s} (hq : 2≤q) (free : QFree D V q) (live : V.Nonempty)
    (bound : V.card≤q*s) (deg : ∀v∈V, s≤(outN D V v).card) :
    ∃ d, d+1≤s ∧ ∃ (O : Origin q (d+1)) (st : State), PackingFrontier.Frontier O st ∧
      UnitLoopCapstone.AlternativesWithLoops O st ∧ BankRules O ∧
      ((h : q=3) → DenseArc.FanReturns O.G O.V d ∧ DenseArc.FourEscape (h ▸ O) ∧
        PackedEscape (h ▸ O) ∧ TriangleRules (h ▸ O)) := by
  obtain ⟨d,le,O,st,fr,alt,esc⟩ := DenseArc.recursive_escape hq free live bound deg
  refine ⟨d,le,O,st,fr,alt,⟨fun _ _ _ => ReturnBankOrder.order O (by omega) fr.lower_degrees,
    fun _ _ _ => RemoteBankDeletion.external_parent O (by omega),fun _ _ => parent_capacity O hq,fun _ _ => next_parent O hq,
    PaidLayerDescent.price O fr.lower_degrees⟩,?_⟩
  rintro rfl
  obtain ⟨fan,escape⟩ := esc rfl
  obtain ⟨h,hv,high,no,four⟩ := escape.1
  exact ⟨fan,escape,⟨h,hv,high,no,four,DisjointRootFourCycles.high_root O fr.lower_degrees hv high⟩,
    FirstArcRecurrence.arc_share O,fun _ => FirstArcRecurrence.closed_component O fr.lower_degrees,
    fun _ hv high _ => PuncturedRootReturns.majority_count O fr.lower_degrees hv high⟩

#print axioms recursive_banks
end LeanCH.BR.Closure.BankDescentFrontier
