import checkpoints.shen_extension.DenseArcPayment

namespace LeanCH.BR.Closure.DenseArc
open Finset BRq2 BRq3 BR45 DeficitLevels

/-- y → h → z, with two distinct choices of p completing y → h → z → p → y. -/
def FourHead (D : CH.Digraph) (V : Finset ℕ) (y h : ℕ) : Prop :=
  D y h=true ∧ 2 ≤ ((outN D V h).filter (fun z => 2≤(outN D (inN D V y) z).card)).card

def FourRoot (D : CH.Digraph) (V : Finset ℕ) (y : ℕ) : Prop :=
  ∃ heads ⊆ outN D V y, 2≤heads.card ∧ ∀h∈heads, FourHead D V y h

/-- At every root of at least the native indegree, failure of the four-cycle
rule forces a *whole column* to equal a tight row, at top order. -/
theorem four_or_column {d} (O : Origin 3 (d+1)) (law : OrderLaw 3 d (3*d+1))
    {y} (yv : y∈O.V) (three : 3≤(inN O.G O.V y).card)
    (heavy : d+1≤(inN O.G O.V y).card) :
    FourRoot O.G O.V y ∨ (O.V.card=3*(d+1) ∧ ∃ b∈O.V, (outN O.G O.V b).card=d+1 ∧
      outN O.G O.V b=inN O.G O.V y) := by
  classical
  let I := inN O.G O.V y
  let ℓ := if O.V.card≤3*d+2 then 2 else 3
  have ord := O.order
  have cap (x) (hx : x∈O.V\insert y I) : (outN O.G (insert y I) x).card ≤ I.card := by
    have no : O.G x y≠true := fun e => (mem_sdiff.mp hx).2
      (mem_insert_of_mem (mem_inN.mpr ⟨(mem_sdiff.mp hx).1,e⟩))
    apply card_le_card
    intro p hp
    exact (mem_insert.mp (mem_outN.mp hp).1).resolve_left (fun eq => no (eq ▸ (mem_outN.mp hp).2))
  have bd : O.V.card≤3*d+ℓ := by unfold ℓ; split <;> omega
  have l3 : ℓ≤3 := by unfold ℓ; split <;> omega
  obtain ⟨bad,sub,bc,loads⟩ := payment (K:=I) O.free O.deg law yv (filter_subset _ _) (fun _ hp =>
    (mem_inN.mp hp).2) cap bd l3 (l3.trans three)
  by_cases other : O.V.card=3*(d+1) ∧ ∃ b∈O.V, (outN O.G O.V b).card=d+1 ∧
      outN O.G O.V b=inN O.G O.V y
  · exact Or.inr other
  left
  refine ⟨bad,sub,by have := O.deg y yv; omega,?_⟩
  intro h hh
  obtain ⟨Z,zw,zc,returns⟩ := loads h hh
  refine ⟨(mem_outN.mp (sub hh)).2,?_⟩
  have enough : 2≤Z.card := by have := O.deg h (mem_outN.mp (sub hh)).1; omega
  apply enough.trans (card_le_card ?_)
  intro z hz
  refine mem_filter.mpr ⟨zw hz,?_⟩
  rcases returns z hz with ok | ⟨eq,b,bw,_,tight,full⟩
  · exact ok
  exfalso
  have bv := (mem_sdiff.mp bw).1
  have no : O.G b y≠true := fun e => (mem_sdiff.mp bw).2 (mem_insert_of_mem (mem_inN.mpr ⟨bv,e⟩))
  simp [no] at full
  have allI : outN O.G I b=I := eq_of_subset_of_card_le outN_subset full
  have inc : I ⊆ outN O.G O.V b := by
    intro p pi
    exact mem_outN.mpr ⟨(mem_inN.mp pi).1,(mem_outN.mp (allI.symm ▸ pi)).2⟩
  have size : (outN O.G O.V b).card≤I.card := by rw [tight]; exact heavy
  have same := (eq_of_subset_of_card_le inc size).symm
  have top : O.V.card=3*(d+1) := by unfold ℓ at eq; split at eq <;> omega
  exact other ⟨top,b,bv,tight,same⟩

/-- Root transitions use only original arcs. If every root of X has the
four-cycle return rule and all such steps stay inside X, X has ≥7 labels. -/
theorem closed_four_roots {D V X} (safe : QFree D V 3) (lower : OrderLaw 3 2 7)
    (sub : X⊆V) (live : X.Nonempty) (roots : ∀y∈X, FourRoot D V y)
    (closed : ∀ y∈X, ∀h∈V, FourHead D V y h → h∈X) : 7≤X.card := by
  classical
  let E : CH.Digraph := fun y h => decide (FourHead D V y h)
  have es : QFree E X 3 := qfree_sub (fun y h e => (of_decide_eq_true e : FourHead D V y h).1)
    (safe.mono_set sub)
  apply lower E X es _ live
  intro y yx
  obtain ⟨heads,inside,size,rich⟩ := roots y yx
  apply size.trans (card_le_card ?_)
  intro h hh
  exact mem_outN.mpr ⟨closed y yx h (mem_outN.mp (inside hh)).1 (rich h hh),decide_eq_true (rich h hh)⟩

/-- When every column has a matching row, choosing one representative per
column preserves every ordered adjacency, in both possible truth values. -/
theorem column_map {D : CH.Digraph} {V : Finset ℕ}
    (cols : ∀ y∈V, ∃ b∈V, outN D V b=inN D V y) :
    ∃ f : V → V, (∀ x y : V, D (f x) y=D y x) ∧
      (∀ x y : V, D (f x) (f y)=D x y) ∧
      ∀ x y : V, f x=f y → ∀ z : V, D x z=D y z ∧ D z x=D z y := by
  classical
  choose b inside eq using cols
  let f : V → V := fun x => ⟨b x x.property,inside x x.property⟩
  have flip (x y : V) : D (f x) y=D y x := by
    have iff : D (f x) y=true ↔ D y x=true := by
      change D (b x x.property) y=true ↔ _
      have yy := y.property
      simpa only [mem_outN,mem_inN,yy,true_and] using
        (show y.val∈outN D V (b x x.property) ↔ y.val∈inN D V x by rw [eq x x.property])
    cases a : D (f x) y <;> cases c : D y x <;> simp_all
  have preserve (x y : V) : D (f x) (f y)=D x y := (flip x (f y)).trans (flip y x)
  exact ⟨f,flip,preserve,fun x y same z => ⟨by rw [← preserve x z,same,preserve],
    by rw [← preserve z x,same,preserve]⟩⟩

#print axioms four_or_column
#print axioms closed_four_roots
#print axioms column_map
end LeanCH.BR.Closure.DenseArc
