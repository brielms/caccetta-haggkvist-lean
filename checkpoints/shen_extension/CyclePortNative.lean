import checkpoints.shen_extension.CyclePortCollision

namespace LeanCH.BR.Closure.CyclePortNative
open Finset BRq2 BRq3 BR45 BRsub WeightedSD FiniteHorizonHall

private theorem liftWalk {D E : CH.Digraph} {V a b k} (sub : ∀{u v},E u v=true → D u v=true)
    (path : Walk E V a b k) : Walk D V a b k := by
  induction path with
  | refl => exact .refl _
  | step hv edge _ ih => exact .step hv (sub edge) ih

/-- Every matched head is a genuine missing arc from its target in the
ambient graph, even when the family graph uses fewer arcs. -/
theorem missing {D E V q k h} (free : QFree D V q) (sub : ∀{u v},E u v=true → D u v=true)
    (hq : 1≤q) (hv : h∈V) (hit : k∈ball E V h (q-1)) : D k h=false := by
  obtain ⟨_,n,le,path⟩ := mem_ball.mp hit
  cases ed : D k h
  · rfl
  · exact (free k (n+1) (by omega) (by omega) (.step hv ed (liftWalk sub path))).elim

/-- Any actual directed complete rectangle with at least two tails excludes
all its tails from the bounded union of balls. Its weights are the original
source weights, even when some rectangle arcs were absent from E. -/
theorem biclique {E D V q z} {c : ℝ} (hq : 2≤q) (high : 1<c)
    (small : SmallerSmallRow q V.card) (free : QFree D V q)
    (sub : ∀{u v},E u v=true → D u v=true) (unit : realMass V z=1)
    (pos : ∀i∈V,0<z i) (rows : ∀i∈V,realRow q E V z i=c)
    {K O : Finset ℕ} (kv : K⊆V) (two : 2≤K.card) (ov : O⊆V) (on : O.Nonempty)
    (all : ∀k∈K,∀o∈O,D k o=true) : realMass K z+(q:ℝ)*realMass O z<1 := by
  classical
  let B := ballSet E V O (q-1)
  have bs : B⊆V\K := by
    intro k hk
    obtain ⟨o,oh,h⟩ := mem_ballSet.mp hk
    exact mem_sdiff.mpr ⟨(mem_ball.mp h).1,fun ki => (by simpa [missing free sub (by omega : 1≤q) (ov oh) h] using all k ki o oh)⟩
  have room : B.card+1<V.card := by
    have le := card_le_card bs
    have eq := card_sdiff_add_card_eq_card kv
    omega
  have ef : QFree E V q := fun i k pos le path => free i k pos le (liftWalk sub path)
  have growth := ball_growth hq high small ef unit pos rows ov on room
  have comp : realMass B z≤realMass (V\K) z := sum_le_sum_of_subset_of_nonneg bs
    (fun i hi _ => (pos i (mem_sdiff.mp hi).1).le)
  have mass : realMass (V\K) z+realMass K z=1 := (sum_sdiff kv).trans unit
  change (q:ℝ)*realMass O z<realMass B z at growth
  linarith

theorem exact_last_layer {D V q y k h} (free : QFree D V q) (yv : y∈V) (hv : h∈V)
    (ky : D k y=true) (yh : D y h=true) {E} (sub : ∀{u v},E u v=true → D u v=true)
    (hit : k∈ball E V h (q-1)) :
    Walk D V h k (q-1) ∧ ∀n<q-1,¬Walk D V h k n := by
  obtain ⟨_,m,le,path⟩ := mem_ball.mp hit
  have forbid (n) (lt : n<q-1) (short : Walk D V h k n) :=
    free k (n+1+1) (by omega) (by omega) (.step yv ky (.step hv yh short))
  have eq : m=q-1 := le_antisymm le (le_of_not_gt (fun h => forbid m h (liftWalk sub path)))
  exact ⟨eq ▸ liftWalk sub path,forbid⟩

theorem on_source {q n F} (X : ShortestCycleWeights.Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    {x p : ℕ→ℚ} {c : ℚ} (high : 1<c) (xp : ∀i∈X.V,0<x i) (pp : ∀i∈X.V,0<p i)
    (xm : mass X.V x=1) (pm : mass X.V p=1)
    (rows : ∀i∈X.V,WeightedSD.row q (FirstPacketBarrier.graph X.D F) X.V x i=c)
    (cols : ∀i∈X.V,WeightedSD.col q (FirstPacketBarrier.graph X.D F) X.V p i=c) :
    (∀h∈X.V,∀k∈ball (FirstPacketBarrier.graph X.D F) X.V h (q-1),X.D k h=false) ∧
    (∀y∈X.V,∀h∈X.V,∀k∈ball (FirstPacketBarrier.graph X.D F) X.V h (q-1),
      FirstPacketBarrier.graph X.D F k y=true → FirstPacketBarrier.graph X.D F y h=true →
      Walk X.D X.V h k (q-1) ∧ ∀n<q-1,¬Walk X.D X.V h k n) ∧
    ∀K⊆X.V,∀O⊆X.V,(∀k∈K,∀o∈O,X.D k o=true) →
      (2≤K.card → O.Nonempty → mass K x+q*mass O x<1) ∧
      (2≤O.card → K.Nonempty → mass O p+q*mass K p<1) := by
  have sub {u v} (e : FirstPacketBarrier.graph X.D F u v=true) : X.D u v=true := by
    obtain ⟨C,h⟩ := FirstPacketBarrier.active.mp e
    exact (MarkedCyclePeeling.mem_col.mp h).2.2.2
  refine ⟨fun _ hv _ h => missing X.free sub (by omega) hv h,
    fun _ yv _ hv _ hit ky yh => exact_last_layer X.free yv hv (sub ky) (sub yh) sub hit,?_⟩
  intro K kv O ov all
  have cr : 1<(c:ℝ) := by exact_mod_cast high
  constructor
  · intro two live
    have b := biclique (z:=fun i => (x i : ℝ)) hq cr small X.free sub
      (by rw [realMass_rat,xm]; norm_num) (fun i hi => by exact_mod_cast xp i hi)
      (fun i hi => by rw [realRow_rat,rows i hi]) kv two ov live all
    simp only [realMass_rat] at b
    exact_mod_cast b
  · intro two live
    have b := biclique (E:=fun u v => FirstPacketBarrier.graph X.D F v u) (z:=fun i => (p i : ℝ))
      hq cr small X.free.reverse (fun e => sub e)
      (by rw [realMass_rat,pm]; norm_num) (fun i hi => by exact_mod_cast pp i hi)
      (fun i hi => by change realCol q (FirstPacketBarrier.graph X.D F) X.V (fun i => (p i : ℝ)) i=(c:ℝ)
                      rw [realCol_rat,cols i hi]) ov two kv live (fun o ho k hk => all k hk o ho)
    simp only [realMass_rat] at b
    exact_mod_cast b

#print axioms missing
#print axioms biclique
#print axioms exact_last_layer
#print axioms on_source
end LeanCH.BR.Closure.CyclePortNative
