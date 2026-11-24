import checkpoints.shen_extension.SharedArcSingleCorridor
import checkpoints.shen_extension.SharedArcCompression
import checkpoints.shen_extension.PacketReturnMass
import checkpoints.shen_extension.OneExchange

namespace LeanCH.BR.Closure.SharedArcExchangeReturn
open Finset Matrix BRq2 BRq3 BR45 WeightedSD FiniteCutInverse ShenCycleSuccessor ShortestCycleWeights FirstPacketBarrier
open MarkedCyclePeeling SharedArcBarrier SharedArcComponentExchange
open scoped Matrix

private theorem old_arc {D F M B} {i j} (e : graph D (insert M F) i j=true) :
    graph D (insert B (insert M F)) i j=true := by
  obtain ⟨A,m⟩ := active.mp e
  obtain ⟨am,im,jm,ij⟩ := mem_col.mp m
  exact active.mpr ⟨A,mem_col.mpr ⟨mem_insert_of_mem am,im,jm,ij⟩⟩

/-- On the same host every actual boundary competitor has a compressed
return matrix on at most q coordinates. Every positive-time diagonal
return mass is strictly below one, including sums over branching walks. -/
theorem bounded_returns {q n} (X : Model q n) (small : SmallerSmallRow q X.V.card)
    {F B} (step : Boundary X F B) (stop : ∀M,Boundary X F M → ¬SmallRow q (graph X.D (insert M F)) X.V)
    (M : Finset ℕ) (bm : Boundary X F M) :
    let G := graph X.D (insert B (insert M F))
    let E := graph X.D (insert M F)
    let T : Finset X.V := univ.filter (fun j : X.V => j.val ∈ targets X.D X.V F B)
    T.card≤q ∧ ∃H : Matrix X.V X.V ℝ, CommonInverse (realMatrix q G X.V) H ∧
      let K : Matrix T T ℝ := fun a b => ∑i : X.V,H a i*(realMatrix q G X.V i b-realMatrix q E X.V i b)
      (∀a b,0≤K a b) ∧ (∀t : T→ℝ,PacketCompression.Live t → ∃j,(t ᵥ* K) j<t j) ∧
      ∀b : T,∀m : ℕ,0<m → (K^m) b b<1 := by
  classical
  intro G E T
  obtain ⟨size,H,inv,iff⟩ := SharedArcCompression.competitor X small step (stop B step) M
  refine ⟨size,H,inv,?_⟩
  intro K
  have kn (a b : T) : 0≤K a b := sum_nonneg (fun i _ => mul_nonneg (inv.nonneg _ _)
    (sub_nonneg.mpr (realMatrix_mono_graph (q:=q) (V:=X.V) (fun _ _ _ _ ed => old_arc ed) i b)))
  have escape (t : T→ℝ) (live : PacketCompression.Live t) : ∃j,(t ᵥ* K) j<t j := by
    by_contra! no
    exact stop M bm (iff.mpr ⟨t,live,no⟩)
  refine ⟨kn,escape,fun b m hm => ?_⟩
  by_contra! gain
  obtain ⟨t,live,above⟩ := PacketCompression.returns kn b hm gain
  obtain ⟨j,loss⟩ := escape t live
  exact loss.not_ge (above j)

/-- A whole incidence component obeys the four-entry inequality in the
same inverse H. The exchange may move both endpoints through prior swaps. -/
theorem component {q n} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    {F B} (step : Boundary X F B)
    (least : ∀M,Boundary X F M → (targets X.D X.V F B).card≤(targets X.D X.V F M).card)
    (stop : ∀M,Boundary X F M → ¬SmallRow q (graph X.D (insert M F)) X.V)
    {H : Matrix X.V X.V ℝ} (inv : CommonInverse (realMatrix q (graph X.D (insert B F)) X.V) H)
    {a b u v : X.V} (mark : (a.val,b.val)∈added X.D F B) (fresh : Fresh X F (u.val,v.val))
    (way : Relation.ReflTransGen (neighbor X F) (a.val,b.val) (u.val,v.val)) :
    ((q:ℝ)*H b a-1)*(1+(q:ℝ)*H v u)<(q:ℝ)^2*H b u*H v a := by
  classical
  by_cases same : (a.val,b.val)=(u.val,v.val)
  · have au : a=u := Subtype.ext (congrArg Prod.fst same)
    have bv : b=v := Subtype.ext (congrArg Prod.snd same)
    subst u; subst v; nlinarith
  obtain ⟨out,M,bm,swap⟩ := transport X hq small step least stop mark way
  let G := graph X.D (insert B F)
  have ed : G a b=true := union_arc.mpr (Or.inr mark)
  have absent : ¬G u v=true := by
    intro hit
    rcases union_arc.mp hit with old|m
    · exact Bool.noConfusion (fresh.2.2.2.symm.trans old)
    · exact out (mem_erase.mpr ⟨Ne.symm same,m⟩)
  let J := insertArc G u v
  have native {i j} (hit : J i j=true) : X.D i j=true := by
    by_cases atF : i=(u:ℕ) ∧ j=(v:ℕ)
    · exact atF.1 ▸ atF.2 ▸ fresh.2.2.1
    have old : G i j=true := by simpa [J,insertArc,atF] using hit
    obtain ⟨A,m⟩ := active.mp old
    exact (mem_col.mp m).2.2.2
  have comm : eraseArc J a b=insertArc (eraseArc G a b) u v := by
    funext i j
    by_cases atA : i=(a:ℕ) ∧ j=(b:ℕ)
    · have other : ¬(i=(u:ℕ) ∧ j=(v:ℕ)) := fun e => same (Prod.ext (atA.1.symm.trans e.1) (atA.2.symm.trans e.2))
      simp only [J,insertArc,eraseArc,ite_eq_left atA,ite_eq_right other]
    · simp only [J,insertArc,eraseArc,ite_eq_right atA]
  obtain ⟨w,wn,live,high⟩ := strict_witness_of_not_smallRow (stop B step)
  obtain ⟨x,_,c,ch,xp,_,xm,_,rows,_⟩ := strict_pair_of_proper_smallRow
    (small.induced (PrivateArcEndpoints.graph_free X (insert B F))) live w wn high
  have full : StrictPositiveRows q G X.V := ⟨x,xp,xm,fun i iv => (rows i iv) ▸ ch⟩
  have check := PacketCompression.one_exchange small full inv a b u v ed absent
    (qfree_sub (fun _ _ e => native e) X.free)
  by_contra! cheap
  have paid := check.mpr cheap
  change SmallRow q (eraseArc J a b) X.V at paid
  rw [comm,←graph_swap mark same swap] at paid
  exact stop M bm paid

#print axioms bounded_returns
#print axioms component
end LeanCH.BR.Closure.SharedArcExchangeReturn
