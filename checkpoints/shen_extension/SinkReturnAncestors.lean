import checkpoints.shen_extension.ShortCycleBalance

namespace LeanCH.BR.SinkReturnAncestors
open Finset BRq2 BRq3 BR45 BRsGen
abbrev Sink (D : CH.Digraph) (X : Finset ℕ) (s : ℕ) := ∀a∈X,D s a≠true

/-- Every ancestor of every tail returning to the same x uses the same
omission at the specified sink. The union counts each label only once. -/
theorem ancestor_budget {D V X Y q x s k l} (free : QFree D V q) (xv : X⊆V) (yv : Y⊆V)
    (xm : x∈X) (path : Walk D X x s k) (time : k+l+2≤q) :
    Y.filter (fun a=>∃y∈inN D Y x, y∈ball D Y a l) ⊆ Y \ outN D V s := by
  intro a am
  obtain ⟨ay,y,ym,hit⟩ := mem_filter.mp am
  refine mem_sdiff.mpr ⟨ay,?_⟩
  intro sm
  obtain ⟨_,j,le,reach⟩ := mem_ball.mp hit
  have loop := (((path.mono xv).snoc (yv ay) (mem_outN.mp sm).2).append (reach.mono yv)).snoc
    (xv xm) (mem_inN.mp ym).2
  exact free _ _ (by omega) (by omega) loop

theorem sink_budget {D V X Y q x l c} (free : QFree D V q) (xv : X⊆V) (yv : Y⊆V)
    (xm : x∈X) (time : X.card+l+1≤q)
    (budget : ∀s∈X, Sink D X s → (Y \ outN D V s).card≤c) :
    (Y.filter (fun a=>∃y∈inN D Y x, y∈ball D Y a l)).card≤c := by
  obtain ⟨s,sm,stop,k,le,path⟩ := reach_sink_of_card (free.mono_set xv) (by omega) xm
  exact (card_le_card (ancestor_budget free xv yv xm path (by omega))).trans (budget s sm stop)

/-- A single omission forbids every internal parent of a returning row.
Consequently, if every sink in Y must return, Y has no internal arcs. -/
theorem all_sinks {D V X Y q} (free : QFree D V q) (xv : X⊆V) (yv : Y⊆V)
    (time : X.card+2≤q) (size : Y.card≤q)
    (budget : ∀s∈X,Sink D X s → (Y \ outN D V s).card≤1)
    (returns : ∀y∈Y,Sink D Y y → (outN D X y).Nonempty) : ∀a∈Y,Sink D Y a := by
  classical
  let P := Y.filter (fun y=>(inN D Y y).Nonempty)
  have py : P⊆Y := filter_subset _ _
  intro a ay b by' ab
  have bp : b∈P := mem_filter.mpr ⟨by',a,mem_inN.mpr ⟨ay,ab⟩⟩
  obtain ⟨y,yp,stop⟩ := exists_sink (free.mono_set (py.trans yv)) ⟨b,bp⟩ ((card_le_card py).trans size)
  have ys : Sink D Y y := by
    intro v vy yv'
    exact stop v (mem_filter.mpr ⟨vy,y,mem_inN.mpr ⟨py yp,yv'⟩⟩) yv'
  obtain ⟨x,xh⟩ := returns y (py yp) ys
  have yx : y∈inN D Y x := mem_inN.mpr ⟨py yp,(mem_outN.mp xh).2⟩
  obtain ⟨v,vm⟩ := (mem_filter.mp yp).2
  have vY := (mem_inN.mp vm).1
  have vy := (mem_inN.mp vm).2
  have bound := sink_budget (l:=1) free xv yv (outN_subset xh) (by omega) budget
  exact (loopfree free (by omega) (yv (py yp))) ((card_le_one.mp bound v
    (mem_filter.mpr ⟨vY,y,yx,ball_of_adj (py yp) vy⟩) y
    (mem_filter.mpr ⟨py yp,y,yx,self_mem_ball (py yp)⟩)) ▸ vy)

/-- Number of return incidences when every row must spend d of them and
a sink reached from each destination can budget at most c source labels. -/
theorem return_count {D V X Y q d c} (free : QFree D V q) (xv : X⊆V) (yv : Y⊆V)
    (time : X.card+1≤q) (need : ∀y∈Y,d≤(outN D X y).card)
    (budget : ∀s∈X,Sink D X s → (Y \ outN D V s).card≤c) : Y.card*d≤X.card*c := by
  classical
  let R := fun y x=>D y x=true
  have lo (y) (ym : y∈Y) : d≤(X.bipartiteAbove R y).card := need y ym
  have hi x (xm : x∈X) : (Y.bipartiteBelow R x).card≤c := by
    have bound := sink_budget (l:=0) free xv yv xm (by omega) budget
    apply (card_le_card ?_).trans bound
    intro y ym
    exact mem_filter.mpr ⟨(mem_filter.mp ym).1,y,ym,self_mem_ball (mem_filter.mp ym).1⟩
  have a := sum_le_sum lo
  have b := sum_le_sum hi
  rw [sum_const_nat (fun _ _=>rfl)] at a b
  have eq := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (s:=Y) (t:=X) R
  exact a.trans (eq.le.trans b)

theorem one_omission {D V X Y q} (free : QFree D V q) (xv : X⊆V) (yv : Y⊆V)
    (time : X.card+2≤q) (size : Y.card≤q)
    (budget : ∀s∈X,Sink D X s → (Y \ outN D V s).card≤1)
    (returns : ∀y∈Y,Sink D Y y → (outN D X y).Nonempty) : Y.card≤X.card := by
  have sink := all_sinks free xv yv time size budget returns
  simpa using return_count free xv yv (by omega) (d:=1)
    (fun y ym=>card_pos.mpr (returns y ym (sink y ym))) budget

attribute [aesop safe forward (immediate := [free,xv,yv,xm,path,time]) (rule_sets := [CHGraphFamilies])] ancestor_budget
attribute [aesop safe forward (immediate := [free,xv,yv,xm,time,budget]) (rule_sets := [CHGraphFamilies])] sink_budget
attribute [aesop safe forward (immediate := [free,xv,yv,time,size,budget,returns]) (rule_sets := [CHGraphFamilies])] all_sinks one_omission
attribute [aesop safe forward (immediate := [free,xv,yv,time,need,budget]) (rule_sets := [CHGraphFamilies])] return_count
#print axioms ancestor_budget
#print axioms sink_budget
#print axioms all_sinks
#print axioms return_count
#print axioms one_omission
end LeanCH.BR.SinkReturnAncestors
