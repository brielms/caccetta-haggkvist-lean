import checkpoints.shen_extension.ReachSlotMatching
namespace LeanCH.BR.PricedReachAssignments
open Finset BRq2 BRq3 BR45 BRsub WeightedSD ReverseReachPayment ReachSlotMatching
open Closure.ShortestCycleWeights Closure.FirstPacketBarrier Closure.MarkedCyclePeeling
open Classical

/-- One rational unit works for all labels and all future choices on this carrier. -/
theorem integer_units (w : ℕ→ℚ) (V : Finset ℕ) (pos : ∀v∈V,0≤w v) :
    ∃d : ℕ,0<d ∧ ∃cap : ℕ→ℕ,∀v∈V,(cap v:ℚ)=d*w v := by
  classical
  induction V using Finset.induction_on with
  | empty => exact ⟨1,by decide,fun _=>0,by simp⟩
  | @insert a S off ih =>
    obtain ⟨d,dp,cap,scale⟩ := ih (fun i is=>pos i (mem_insert_of_mem is))
    have dn := Rat.den_pos (w a)
    have num : ((w a).num.natAbs:ℚ)=(w a).num := by
      have h : ((w a).num.natAbs : ℤ) = (w a).num := Int.natAbs_of_nonneg (Rat.num_nonneg.mpr (pos a (mem_insert_self a S)))
      simpa only [Int.cast_natCast] using congrArg (fun x:ℤ=>(x:ℚ)) h
    refine ⟨d*(w a).den,Nat.mul_pos dp dn,
      fun v=>if v=a then d*(w a).num.natAbs else (w a).den*cap v,?_⟩
    intro v vm
    by_cases at_a : v=a
    · subst v
      simp [Nat.cast_mul,num,mul_assoc,Rat.den_mul_eq_num]
    · have vs := (mem_insert.mp vm).resolve_left at_a
      simp [at_a,scale v vs]
      ring

/-- The original prices are all measured in the same units. The reservation
is one quantum of that scale and can be made at any marked column. -/
def Priced (q : ℕ) (E : CH.Digraph) (V : Finset ℕ) (w : ℕ→ℚ) : Prop :=
  ∃d : ℕ,0<d ∧ ∃cap : ℕ→ℕ,(∀v∈V,(cap v:ℚ)=d*w v) ∧ ReservedAssignments q E V cap

theorem at_prices {q E V w} (law : Expansion q E V w) (pos : ∀v∈V,0<w v) : Priced q E V w := by
  obtain ⟨d,dp,cap,scale⟩ := integer_units w V (fun x xm=>(pos x xm).le)
  have mass_scale (S : Finset ℕ) (sv : S⊆V) :
      mass S (fun v=>(cap v:ℚ)) = d*mass S w := by
    unfold mass
    rw [mul_sum]
    exact sum_congr rfl (fun v vm=>scale v (sv vm))
  have scaled : Expansion q E V (fun v=>(cap v:ℚ)) := by
    intro T tv live room
    have h := mul_lt_mul_of_pos_left (law T tv live room) (show (0:ℚ)<d by exact_mod_cast dp)
    rw [mass_scale T tv,mass_scale (starts E V T (q-1)) (filter_subset _ _)]
    linarith only [show (q:ℚ)*(d*mass T w)=d*(q*mass T w) by ring,h]
  exact ⟨d,dp,cap,scale,fun _ tv room _ spent=>from_expansion scaled tv room spent⟩

/-- Native arcs from every target to every member of H rule out H as starts,
even if the priced retained graph omits any number of native arcs. -/
theorem missed_starts {q E D V T H} (free : QFree D V q) (hq : 1≤q)
    (sub : ∀i j,E i j=true→D i j=true) (hv : H⊆V)
    (feeds : ∀t∈T,∀h∈H,D t h=true) :
    (starts E V T (q-1)).card+H.card≤V.card := by
  have off : starts E V T (q-1)⊆V\H := by
    intro h hm
    obtain ⟨hV,t,tm,ht⟩ := mem_filter.mp hm
    refine mem_sdiff.mpr ⟨hV,?_⟩
    intro hH
    have native : t ∈ ball D V h (q-1) := ball_sub sub ht
    obtain ⟨_,l,bound,walk⟩ := mem_ball.mp native
    exact free t (l+1) (by omega) (by omega) (.step hV (feeds t tm h hH) walk)
  have fit := card_le_card off
  have size := card_sdiff_add_card_eq_card hv
  omega

/-- The physical vertex p belongs to the whole common-parent pool, and every
unit of every member can draw a distinct slot at the same terminal prices. -/
def MarkedPool (q : ℕ) (E D : CH.Digraph) (V : Finset ℕ) (w : ℕ→ℚ)
    (p : ℕ) (H : Finset ℕ) : Prop :=
  let T := commonHeads (fun i j=>D j i) V H
  p∈T ∧ ∃d : ℕ,0<d ∧ ∃cap : ℕ→ℕ,(∀v∈V,(cap v:ℚ)=d*w v) ∧
    ∀reserved : Finset Slot,reserved.card≤1 →
      Assignment E V T (q-1) (fun t=>q*cap t) cap reserved

theorem pool {q E D V w p H} (prices : Priced q E V w) (free : QFree D V q) (hq : 1≤q)
    (sub : ∀i j,E i j=true→D i j=true) (hv : H⊆V) (many : 2≤H.card)
    (pv : p∈V) (feeds : ∀h∈H,D p h=true) : MarkedPool q E D V w p H := by
  let T := commonHeads (fun i j=>D j i) V H
  have tv : T⊆V := filter_subset _ _
  have bound := missed_starts (E:=E) (T:=T) free hq sub hv (fun t tm h hm=>(mem_filter.mp tm).2 h hm)
  obtain ⟨d,dp,cap,scale,hall⟩ := prices
  exact ⟨mem_filter.mpr ⟨pv,feeds⟩,d,dp,cap,scale,hall T tv (by omega)⟩

/-- The other head is supplied by any marked cycle through the feeder which
misses the receiver. No bound on the number of vertices or exact degree. -/
theorem cycle_feeder {q n} (X : Model q n) {E : CH.Digraph} {F : Family} {L : Finset ℕ}
    {w : ℕ→ℚ} (prices : Priced q E X.V w) (hq : 1≤q)
    (sub : ∀i j,E i j=true→X.D i j=true) (boundary : Closure.SharedArcBarrier.Boundary X F L)
    {p z : ℕ} (pl : p∈L) (zv : z∈X.V) (outside : z∉L) (pz : graph X.D F p z=true) :
    ∃y∈outN X.D L p,y≠z ∧ MarkedPool q E X.D X.V w p {z,y} := by
  have cycle := (mem_filter.mp boundary.1).2
  obtain ⟨y,ym⟩ := card_pos.mp (show 0<(outN X.D L p).card by rw [cycle.heads p pl]; decide)
  have ys := mem_outN.mp ym
  have ne : z≠y := fun e=>outside (e ▸ ys.1)
  obtain ⟨A,am⟩ := active.mp pz
  refine ⟨y,ym,Ne.symm ne,pool prices X.free hq sub
    (insert_subset zv (singleton_subset_iff.mpr (cycle.sub ys.1))) (by simp [ne]) (cycle.sub pl) ?_⟩
  intro h hm
  rcases mem_insert.mp hm with rfl | last
  · exact (mem_col.mp am).2.2.2
  · simpa [mem_singleton.mp last] using ys.2

attribute [aesop safe forward (immediate := [law,pos]) (rule_sets := [CHGraphFamilies])] at_prices
attribute [aesop safe forward (immediate := [prices,free,hq,sub,hv,many,pv,feeds]) (rule_sets := [CHGraphFamilies])] pool
/-- On a selected terminal cycle family the required subgraph proof follows
from the definition of its arcs. The feeder may be known in a different old family. -/
def FeederPool (q : ℕ) (E D : CH.Digraph) (V L : Finset ℕ) (w : ℕ→ℚ) (p z : ℕ) : Prop :=
  ∃y∈outN D L p,y≠z ∧ MarkedPool q E D V w p {z,y}

theorem family_feeder {q n} (X : Model q n) {F G : Family} {L : Finset ℕ} {w : ℕ→ℚ}
    (prices : Priced q (graph X.D G) X.V w) (hq : 2≤q)
    (boundary : Closure.SharedArcBarrier.Boundary X F L) {p z : ℕ} (pl : p∈L)
    (zv : z∈X.V) (outside : z∉L) (pz : graph X.D F p z=true) :
    FeederPool q (graph X.D G) X.D X.V L w p z := by
  apply cycle_feeder X prices (by omega) _ boundary pl zv outside pz
  intro i j edge
  obtain ⟨A,am⟩ := active.mp edge
  exact (mem_col.mp am).2.2.2

attribute [aesop safe forward (immediate := [X,prices,hq,boundary,pl,zv,outside,pz]) (rule_sets := [CHGraphFamilies])] family_feeder
#print axioms family_feeder
#print axioms at_prices
#print axioms cycle_feeder
end LeanCH.BR.PricedReachAssignments
