import checkpoints.shen_extension.RankedLiveSources
import checkpoints.shen_extension.TightCycleSuccessor

namespace LeanCH.BR.RemoteParentPacking
open Finset BRq2 BRq3 BR45

/-- Starts with an actual arc from u. In particular the root counts as
    missed when no positive closed walk of at most q steps exists. -/
noncomputable def missed (D : CH.Digraph) (V : Finset ℕ) (q u : ℕ) :=
  V \ BRsub.ballSet D V (outN D V u) (q-1)

theorem misses_positive {D V q u z} (far : z∈missed D V q u) {k}
    (pos : 0<k) (short : k≤q) (path : Walk D V u z k) : False := by
  cases path with
  | refl => omega
  | @step a b c k bv ab tail =>
    exact (mem_sdiff.mp far).2 (BRsub.mem_ballSet.mpr
      ⟨_,mem_outN.mpr ⟨bv,ab⟩,mem_ball.mpr ⟨(mem_sdiff.mp far).1,k,by omega,tail⟩⟩)

theorem self_missed {D V q u} (hq : 1≤q) (free : QFree D V q) (uv : u∈V) :
    u∈missed D V q u := by
  refine mem_sdiff.mpr ⟨uv,?_⟩
  intro reached
  obtain ⟨v,head,back⟩ := BRsub.mem_ballSet.mp reached
  obtain ⟨_,k,short,p⟩ := mem_ball.mp back
  exact free u (k+1) (by omega) (by omega) (.step (outN_subset head) (mem_outN.mp head).2 p)

/-- The root never runs out of actual predecessors, even if it is the only
    missed target. In the singleton case the older deletion rule suffices. -/
theorem parent {q r} (X : ShenMinimumOrder.Source q r) (hq : 2≤q) (hr : 0<r)
    (law : RemoteHeadRectangle.Law X) {u} (uv : u∈X.V) :
    ∃p∈X.V,X.D p u=true ∧ (outN X.D X.V p).card=r ∧
      missed X.D X.V q u⊆outN X.D X.V p := by
  classical
  let W := missed X.D X.V q u
  have self : u∈W := self_missed (by omega) X.free uv
  by_cases two : 2≤W.card
  · have size := X.degree u uv
    have width : q*(r-(outN X.D X.V u).card)+2≤W.card := by
      simpa [Nat.sub_eq_zero_of_le size] using two
    obtain ⟨p,pp,tight,full⟩ := RankedLiveSources.last_layer hq law outN_subset width
    have pv : p∈X.V := by
      obtain ⟨_,_,hit⟩ := BRsub.mem_ballSet.mp (mem_sdiff.mp pp).1
      exact ball_subset hit
    exact ⟨p,pv,(mem_outN.mp (full self)).2,tight,full⟩
  · obtain ⟨p,pv,pu,tight,_⟩ := ShenCycleSuccessor.fixed_parent X hq hr uv
    have alone : W={u} := (eq_of_subset_of_card_le (singleton_subset_iff.mpr self)
      (by rw [card_singleton]; omega)).symm
    refine ⟨p,pv,pu,tight,?_⟩
    change W⊆_
    rw [alone]
    exact singleton_subset_iff.mpr (mem_outN.mpr ⟨uv,pu⟩)

/-- Choose parents indefinitely, starting at an arbitrary specified vertex. -/
theorem trace {q r} (X : ShenMinimumOrder.Source q r) (hq : 2≤q) (hr : 0<r)
    (law : RemoteHeadRectangle.Law X) {u} (uv : u∈X.V) :
    ∃v : ℕ→ℕ,v 0=u ∧ (∀i,v i∈X.V) ∧ ∀i,X.D (v (i+1)) (v i)=true ∧
      (outN X.D X.V (v (i+1))).card=r ∧ missed X.D X.V q (v i)⊆outN X.D X.V (v (i+1)) := by
  classical
  let pick (b : {w // w∈X.V}) := parent X hq hr law b.property
  let next (b : {w // w∈X.V}) : {w // w∈X.V} :=
    ⟨Classical.choose (pick b),(Classical.choose_spec (pick b)).1⟩
  let chain : ℕ→{w // w∈X.V} := fun i=>Nat.rec ⟨u,uv⟩ (fun _ b=>next b) i
  exact ⟨fun i=>(chain i).val,rfl,fun i=>(chain i).property,
    fun i=>(Classical.choose_spec (pick (chain i))).2⟩

/-- Charge actual target labels to consecutive roots on the same chain. -/
theorem packing {q : ℕ} {D V} {v : ℕ→ℕ} (live : ∀i,v i∈V)
    (edge : ∀i,D (v (i+1)) (v i)=true)
    (cover : ∀i,missed D V q (v i)⊆outN D V (v (i+1))) (start : ℕ) :
    (∑ i∈range (q+1),(missed D V q (v (start+i))).card)≤V.card := by
  classical
  let W (i : ℕ) := missed D V q (v (start+i))
  have route {i z} (hit : z∈W i) (l : ℕ) : Walk D V (v (start+i+l+1)) z (l+1) := by
    induction l with
    | zero => exact .step (outN_subset (cover _ hit)) (mem_outN.mp (cover _ hit)).2 (.refl _)
    | succ k ih => exact .step (live _) (edge _) ih
  have apart {i j} (lt : i<j) (bound : j≤q) : Disjoint (W i) (W j) := by
    refine disjoint_left.mpr (fun z first second=>?_ )
    have len : start+i+(j-i-1)+1=start+j := by omega
    have path := route first (j-i-1)
    rw [len] at path
    exact misses_positive second (by omega) (by omega) path
  have disj : (↑(range (q+1)) : Set ℕ).PairwiseDisjoint W := by
    intro i hi j hj ne
    have bi := mem_range.mp hi
    have bj := mem_range.mp hj
    rcases lt_or_gt_of_ne ne with lt|gt
    · exact apart lt (by omega)
    · exact (apart gt (by omega)).symm
  have sub : (range (q+1)).biUnion W⊆V := by
    intro z contained
    obtain ⟨i,_,hit⟩ := mem_biUnion.mp contained
    exact (mem_sdiff.mp hit).1
  have count := card_le_card sub
  rw [card_biUnion disj] at count
  exact count

#print axioms parent
#print axioms trace
#print axioms packing

/-- Count the actual paid-row incidences left after the disjoint charges.
    Every one of their heads is also reachable from the corresponding child. -/
theorem overlap_budget {q r : ℕ} {D V} {v : ℕ→ℕ} (live : ∀i,v i∈V)
    (steps : ∀i,D (v (i+1)) (v i)=true ∧ (outN D V (v (i+1))).card=r ∧
      missed D V q (v i)⊆outN D V (v (i+1))) (start : ℕ) :
    let B := fun i=>outN D V (v (start+i+1))\missed D V q (v (start+i))
    (q+1)*r≤V.card + ∑ i∈range (q+1),(B i).card := by
  intro B
  let W := fun i=>missed D V q (v (start+i))
  have bound := packing live (fun i=>(steps i).1) (fun i=>(steps i).2.2) start
  change (∑i∈range (q+1),(W i).card)≤V.card at bound
  have split (i : ℕ) : (B i).card+(W i).card=r :=
    (card_sdiff_add_card_eq_card (steps (start+i)).2.2).trans (steps (start+i)).2.1
  have sum : (∑i∈range (q+1),(B i).card)+(∑i∈range (q+1),(W i).card)=(q+1)*r := by
    rw [←sum_add_distrib]
    simp [split]
  omega

theorem detour {D V q u p z} (hq : 1≤q) (zj : z∈outN D V p\missed D V q u) :
    ∃ k,1≤k ∧ k≤q ∧ Walk D V u z k := by
  classical
  have zv := outN_subset (mem_sdiff.mp zj).1
  have seen : z∈BRsub.ballSet D V (outN D V u) (q-1) := by
    by_contra h
    exact (mem_sdiff.mp zj).2 (mem_sdiff.mpr ⟨zv,h⟩)
  obtain ⟨h,uh,reach⟩ := BRsub.mem_ballSet.mp seen
  obtain ⟨_,k,hk,w⟩ := mem_ball.mp reach
  exact ⟨k+1,by omega,by omega,.step (outN_subset uh) (mem_outN.mp uh).2 w⟩

#print axioms overlap_budget
#print axioms detour

/-- The alternate walk from p starts with a different actual edge, and its
    suffix avoids p. It therefore survives removing the charged arc p → z. -/
theorem bypass {D V q u p z} (hq : 1≤q) (free : QFree D V q)
    (uv : u∈V) (pv : p∈V) (pu : D p u=true) (zj : z∈outN D V p\missed D V q u) :
    u≠z ∧ ∃k,1≤k ∧ k≤q ∧ Walk D (V.erase p) u z k := by
  refine ⟨fun eq=>(mem_sdiff.mp zj).2 (eq ▸ self_missed hq free uv),?_⟩
  obtain ⟨k,pos,short,w⟩ := detour hq zj
  rcases w.lastVisit p with old|⟨l,m,_,length,first,last⟩
  · exact ⟨k,pos,short,old⟩
  have nz : z≠p := by
    rintro rfl
    exact loopfree free hq pv (mem_outN.mp (mem_sdiff.mp zj).1).2
  have more : m≠0 := by
    rintro rfl
    cases last
    exact nz rfl
  exact (free p (l+1) (by omega) (by omega) (.step uv pu first)).elim

#print axioms bypass

/-- The largest induced subgraph on U with the requested minimum degree.
    Its union description fixes the physical labels independently of peeling order. -/
noncomputable def core (D : CH.Digraph) (U : Finset ℕ) (t : ℕ) : Finset ℕ := by
  classical
  exact (U.powerset.filter (fun S=>∀i∈S,t≤(outN D S i).card)).biUnion id

theorem core_spec {D U t} :
    core D U t⊆U ∧ (∀i∈core D U t,t≤(outN D (core D U t) i).card) ∧
      ∀S⊆U,(∀i∈S,t≤(outN D S i).card) → S⊆core D U t := by
  classical
  have introS {S : Finset ℕ} (su : S⊆U) (deg : ∀i∈S,t≤(outN D S i).card) : S⊆core D U t :=
    fun i hi=>mem_biUnion.mpr ⟨S,mem_filter.mpr ⟨mem_powerset.mpr su,deg⟩,hi⟩
  refine ⟨?_,?_,fun _ su deg=>introS su deg⟩
  · intro i hi
    obtain ⟨S,law,inS⟩ := mem_biUnion.mp hi
    exact (mem_powerset.mp (mem_filter.mp law).1) inS
  · intro i hi
    obtain ⟨S,law,inS⟩ := mem_biUnion.mp hi
    obtain ⟨inside,deg⟩ := mem_filter.mp law
    have sub := introS (mem_powerset.mp inside) deg
    exact (deg i inS).trans (card_le_card (fun j hj=>mem_outN.mpr ⟨sub (outN_subset hj),(mem_outN.mp hj).2⟩))

/-- Exact test for any seed with the right size. All further deletions are
    allowed; a nonempty core supplies the lower-degree host on the native labels. -/
theorem lower_degree_iff {D V S q t} (free : QFree D V q) (sub : S⊆V)
    (size : V.card-q*t≤S.card) :
    (core D (V\S) t).Nonempty ↔
    ∃U⊆V\S,U.Nonempty ∧ U.card≤q*t ∧ QFree D U q ∧ ∀i∈U,t≤(outN D U i).card := by
  obtain ⟨into,degree,greatest⟩ := core_spec (D:=D) (U:=V\S) (t:=t)
  constructor
  · intro live
    have capacity := card_sdiff_add_card_eq_card sub
    have smaller := card_le_card into
    exact ⟨_,into,live,by omega,free.mono_set (into.trans sdiff_subset),degree⟩
  · rintro ⟨U,us,live,_,_,degree⟩
    exact live.mono (greatest U us degree)

#print axioms lower_degree_iff

/-- The counterexample order buys a full degree of bypass incidences in
    every consecutive window, starting with any chosen native root. -/
theorem every_window {q r} (X : ShenMinimumOrder.Source q r) (hq : 2≤q) (hr : 0<r)
    (order : X.V.card≤q*r) {u} (uv : u∈X.V) :
    ∃v : ℕ→ℕ,v 0=u ∧ (∀i,v i∈X.V) ∧
      (∀i,X.D (v (i+1)) (v i)=true ∧ (outN X.D X.V (v (i+1))).card=r ∧
        missed X.D X.V q (v i)⊆outN X.D X.V (v (i+1))) ∧
      ∀a,r≤∑i∈range (q+1),(outN X.D X.V (v (a+i+1))\missed X.D X.V q (v (a+i))).card := by
  obtain ⟨v,first,live,steps⟩ := trace X hq hr (RemoteHeadRectangle.register X hq) uv
  refine ⟨v,first,live,steps,fun a=>?_⟩
  have bill := overlap_budget live steps a
  dsimp only at bill
  rw [Nat.add_mul,Nat.one_mul] at bill
  omega

#print axioms every_window
end LeanCH.BR.RemoteParentPacking
