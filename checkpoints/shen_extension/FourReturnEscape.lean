import checkpoints.shen_extension.RecursiveFourReturns
import checkpoints.shen_extension.DistinctUnmatchedRows

namespace LeanCH.BR.Closure.DenseArc
open Finset BRq2 BRq3 BR45 DeficitLevels

def UnmatchedTight (D : CH.Digraph) (V : Finset ℕ) (s y : ℕ) : Prop :=
  ∀ b ∈ V, (outN D V b).card=s → outN D V b≠inN D V y

/-- On the original graph, an above-average column either exceeds the tight
row size or, in the regular case, escapes by the three disjoint banks. -/
theorem high_unmatched {D V s} (safe : QFree D V 3) (ne : V.Nonempty)
    (order : V.card≤3*s) (deg : ∀ x∈V, s≤(outN D V x).card) :
    ∃ y∈V, s≤(inN D V y).card ∧ UnmatchedTight D V s y := by
  classical
  by_cases more : ∃ y∈V, s<(inN D V y).card
  · obtain ⟨y,yv,gt⟩ := more
    exact ⟨y,yv,gt.le,fun b _ tight same => by rw [same] at tight; omega⟩
  have le (y) (yv : y∈V) : (inN D V y).card ≤ s := by
    by_contra! gt; exact more ⟨y,yv,gt⟩
  have e : (∑ y∈V,(outN D V y).card) = ∑ y∈V,(inN D V y).card :=
    Compose.ThinRigid.sum_out_eq_sum_in D V
  have eq := (sum_eq_sum_iff_of_le le).mp (le_antisymm (sum_le_sum le) (e ▸ sum_le_sum deg))
  by_contra none
  have cols (y) (yv : y∈V) : ∃ b∈V, outN D V b=inN D V y := by
    by_contra no
    exact none ⟨y,yv,(eq y yv).ge,fun b bv _ same => no ⟨b,bv,same⟩⟩
  have := ColumnBlockerEscape.all_columns_order safe ne deg cols
  omega

private theorem native_three {d} (O : Origin 3 (d+1)) : 3≤d+1 := by
  have pos := UnitState.origin_degree_pos O
  by_contra! small
  have one : d=1 := by omega
  subst d
  exact HalfLawSupply.no_source_of_halfLaw (s:=2) (by decide) HalfLawSupply.halfLaw_one
    O.free O.ne O.order O.deg

theorem four_at_unmatched {d} (O : Origin 3 (d+1)) (law : OrderLaw 3 d (3*d+1))
    {y} (yv : y∈O.V) (high : d+1≤(inN O.G O.V y).card)
    (no : UnmatchedTight O.G O.V (d+1) y) : FourRoot O.G O.V y := by
  rcases four_or_column O law yv ((native_three O).trans high) high with yes|⟨_,b,bv,t,eq⟩
  · exact yes
  · exact False.elim (no b bv t eq)

/-- At every root of an in-regular source, an unmatched predecessor lies at
distance at most two. Reapplying the repair there yields four-cycle witnesses. -/
theorem near_four {d} (O : Origin 3 (d+1)) (law : OrderLaw 3 d (3*d+1))
    (indeg : ∀y∈O.V, d+1≤(inN O.G O.V y).card) {a} (ha : a∈O.V) :
    ∃ z∈O.V, UnmatchedTight O.G O.V (d+1) z ∧ FourRoot O.G O.V z ∧
      ∃ k, k≤2 ∧ Walk O.G O.V z a k := by
  classical
  have done (z) (zv : z∈O.V) (no : UnmatchedTight O.G O.V (d+1) z)
      (k) (kl : k≤2) (walk : Walk O.G O.V z a k) :
      UnmatchedTight O.G O.V (d+1) z ∧ FourRoot O.G O.V z ∧
        ∃ j, j≤2 ∧ Walk O.G O.V z a j :=
    ⟨no,four_at_unmatched O law zv (indeg z zv) no,k,kl,walk⟩
  by_cases na : UnmatchedTight O.G O.V (d+1) a
  · exact ⟨a,ha,done a ha na 0 (by decide) (.refl _)⟩
  simp only [UnmatchedTight,not_forall,not_not] at na
  obtain ⟨b,bv,_,ab⟩ := na
  by_cases nb : UnmatchedTight O.G O.V (d+1) b
  · obtain ⟨x,hx⟩ := card_pos.mp (show 0<(inN O.G O.V a).card by have := indeg a ha; omega)
    exact ⟨b,bv,done b bv nb 2 le_rfl (.step (mem_inN.mp hx).1
      (mem_outN.mp (ab.symm ▸ hx)).2 (.step ha (mem_inN.mp hx).2 (.refl _)))⟩
  simp only [UnmatchedTight,not_forall,not_not] at nb
  obtain ⟨c,cv,_,bc⟩ := nb
  obtain ⟨_,_,z,hz,no⟩ := ColumnBlockerEscape.local_unmatched O.free O.deg (by omega) O.order
    ha bv cv ab bc (indeg c cv)
  have za := mem_inN.mp (mem_inter.mp hz).1
  exact ⟨z,za.1,done z za.1 (fun w wv _ => no w wv) 1 (by decide) (.step ha za.2 (.refl _))⟩

def FourEscape {d} (O : Origin 3 (d+1)) : Prop :=
  (∃ y∈O.V, d+1≤(inN O.G O.V y).card ∧ UnmatchedTight O.G O.V (d+1) y ∧ FourRoot O.G O.V y) ∧
  ((∀y∈O.V, d+1≤(inN O.G O.V y).card) → ∃u∈O.V, ∃v∈O.V,
    FourRoot O.G O.V u ∧ FourRoot O.G O.V v ∧ outN O.G O.V u≠outN O.G O.V v) ∧
  ((∀y∈O.V, d+1≤(inN O.G O.V y).card) → ∀a∈O.V,
    ∃ z∈O.V, UnmatchedTight O.G O.V (d+1) z ∧ FourRoot O.G O.V z ∧ ∃k, k≤2 ∧ Walk O.G O.V z a k)

theorem four_escape {d} (O : Origin 3 (d+1)) (law : OrderLaw 3 d (3*d+1)) : FourEscape O := by
  obtain ⟨y,yv,high,no⟩ := high_unmatched O.free O.ne O.order O.deg
  refine ⟨⟨y,yv,high,no,four_at_unmatched O law yv high no⟩,?_,fun deg _ ha => near_four O law deg ha⟩
  intro indeg
  obtain ⟨u,uv,v,vv,nu,nv,ne⟩ := ColumnBlockerEscape.distinct_unmatched O.free O.ne O.deg O.order
  exact ⟨u,uv,v,vv,four_at_unmatched O law uv (indeg u uv) (fun w wv _ => nu w wv),
    four_at_unmatched O law vv (indeg v vv) (fun w wv _ => nv w wv),ne⟩

theorem recursive_escape {D V q s} (hq : 2≤q) (free : QFree D V q) (live : V.Nonempty)
    (bound : V.card ≤ q*s) (deg : ∀ v∈V, s ≤ (outN D V v).card) :
    ∃ d, d+1≤s ∧ ∃ (O : Origin q (d+1)) (st : State), PackingFrontier.Frontier O st ∧
      UnitLoopCapstone.AlternativesWithLoops O st ∧
      ((h : q=3) → FanReturns O.G O.V d ∧ FourEscape (h ▸ O)) := by
  obtain ⟨d,le,O,st,fr,alt,fan⟩ := from_candidate hq free live bound deg
  refine ⟨d,le,O,st,fr,alt,?_⟩
  rintro rfl
  exact ⟨fan rfl,four_escape O fr.lower⟩

#print axioms high_unmatched
#print axioms near_four
#print axioms recursive_escape
end LeanCH.BR.Closure.DenseArc
