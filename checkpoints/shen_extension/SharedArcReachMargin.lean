import checkpoints.shen_extension.SharedArcFlatArithmetic
import checkpoints.shen_extension.PacketDeletionProfile

namespace LeanCH.BR.Closure.SharedArcReachMargin
open Finset Matrix BRq2 BRq3 BR45 WeightedSD FiniteCutInverse ShortestCycleWeights FirstPacketBarrier MarkedCyclePeeling
open SharedArcBarrier SharedArcComponentExchange
open scoped Matrix

def StrictColumns (q : ℕ) (D : CH.Digraph) (V : Finset ℕ) : Prop :=
  ∃p : V→ℝ,(∀i,0≤p i) ∧ (∑i,p i)=1 ∧ ∀j,(p ᵥ* realMatrix q D V) j<1

/-- Two distinct targets can be missed by different roots. The subgraph
may be any spanning native edit; it need not be a deletion of a single arc. -/
theorem two_targets {q n} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    (E : CH.Digraph) (incl : ∀i j,E i j=true → X.D i j=true)
    (a b : X.V) (diff : a≠b) (ha : ∃s : X.V,(a:ℕ)∉ball E X.V s q)
    (hb : ∃s : X.V,(b:ℕ)∉ball E X.V s q) : StrictColumns q E X.V := by
  classical
  let _ : Nonempty X.V := ⟨a⟩
  let S := WeightedArithmetic.rationalMatrix q (adjacencyMatrix E X.V)
  have sep := FiniteDual.rational_demand_strict_separator (J:=X.V) S (fun _ => 1) 1 (by norm_num)
  obtain ⟨K,inv⟩ := strict_inverse_of_proper_smallRow (small.induced X.free)
    (fun i => (X.weights i:ℚ)) (fun _ _ => Nat.cast_nonneg _) X.strict
  have free := qfree_sub incl X.free
  have impossible : ¬∃w : X.V→ℚ,(∀i,0≤w i) ∧ (∑i,w i)=1 ∧ ∀i,1≤∑j,S i j*w j := by
    rintro ⟨w,wn,wm,wr⟩
    let W := fun i => (w i:ℝ)
    have mass : ∑i,W i=1 := by dsimp [W]; exact_mod_cast wm
    have live : W≠0 := by intro z; rw [z] at mass; simp at mass
    have zero (i : X.V) (hole : ∃s : X.V,(i:ℕ)∉ball E X.V s q) : W i=0 := by
      obtain ⟨s,no⟩ := hole
      have wi : w i=0 := by
        apply le_antisymm _ (wn i)
        by_contra! pos
        apply no
        apply feasible_reach_positive_within hq free small (extendWeight X.V w) _ _ s.property i.property
        · simpa [extendWeight_on] using pos
        · intro k hk; rw [extendWeight_on X.V w ⟨k,hk⟩]; exact wn _
        · intro k hk; rw [mass_extendWeight,wm,row_extendWeight q E X.V w ⟨k,hk⟩]; exact wr _
      simp [W,wi]
    have good (i : X.V) : 0≤(excess (realMatrix q X.D X.V) *ᵥ W) i := by
      rw [mulVec_excess,mass,sub_nonneg]
      have r : (1:ℝ)≤∑j,(S i j:ℝ)*W j := by dsimp [W]; exact_mod_cast wr i
      exact r.trans (sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right
        (realMatrix_mono_graph (q:=q) (fun k _ l _ => incl k l) i j) (by dsimp [W]; exact_mod_cast wn j)))
    obtain ⟨t,ht,_,ray⟩ := InverseOffDiagonal.single_ray inv (fun _ _ ne => InverseOffDiagonal.graph_positive hq inv ne)
      W live good (zero a ha)
    exact (mul_pos ht (InverseOffDiagonal.graph_positive hq inv diff.symm)).ne' ((ray b).symm.trans (zero b hb))
  obtain ⟨p,pn,pm,pc⟩ := sep impossible
  refine ⟨p,pn,pm,fun j => ?_⟩
  have e := pc j
  simp only [Rat.cast_one,one_mul,mul_one,pm] at e
  exact e

/-- Every subthreshold union of stars with two distinct activated tails
has one certificate leaving strict slack in every column. -/
theorem strict_stars {q n} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    {F B} (step : Boundary X F B)
    (least : ∀M,Boundary X F M → (targets X.D X.V F B).card≤(targets X.D X.V F M).card)
    (L R : Finset ℕ) (low : L.card+R.card<(targets X.D X.V F B).card)
    {a b u v : X.V} (f : Fresh X F (a,b)) (g : Fresh X F (u,v)) (different : a≠u)
    (one : (a:ℕ)∈L ∨ (b:ℕ)∈R) (two : (u:ℕ)∈L ∨ (v:ℕ)∈R) :
    StrictColumns q (SharedArcCover.onStars X.D (graph X.D F) L R) X.V := by
  apply two_targets X hq small _ _ a u different
    ⟨b,SharedArcCover.no_return X hq step least L R low f one⟩
    ⟨v,SharedArcCover.no_return X hq step least L R low g two⟩
  intro i j ed
  by_cases hit : i∈L ∨ j∈R
  · simpa [SharedArcCover.onStars,hit] using ed
  have old : graph X.D F i j=true := by simpa [SharedArcCover.onStars,hit] using ed
  obtain ⟨A,m⟩ := active.mp old
  exact (mem_col.mp m).2.2.2


/-- With at least three changed heads, every subthreshold union of native
stars has a strict margin. If only one tail is active, enlarge it to two
whole tail stars and transfer their strict dual back to the smaller edit. -/
theorem every_strict {q n} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    {F B} (step : Boundary X F B)
    (least : ∀M,Boundary X F M → (targets X.D X.V F B).card≤(targets X.D X.V F M).card)
    (large : 3≤(targets X.D X.V F B).card)
    (L R : Finset ℕ) (low : L.card+R.card<(targets X.D X.V F B).card) :
    StrictColumns q (SharedArcCover.onStars X.D (graph X.D F) L R) X.V := by
  classical
  let Miss := SharedArcFlatCut.Missing X F
  let act (e : Miss) := (e.val.1:ℕ)∈L ∨ (e.val.2:ℕ)∈R
  have fresh (e : Miss) : Fresh X F ((e.val.1:ℕ),(e.val.2:ℕ)) :=
    ⟨e.val.1.property,e.val.2.property,e.property⟩
  by_cases two : ∃e g : Miss,act e ∧ act g ∧ e.val.1≠g.val.1
  · obtain ⟨e,g,one,both,ne⟩ := two
    exact strict_stars X hq small step least L R low (fresh e) (fresh g) ne one both
  have cyc : ShenCycleSuccessor.Cycle X.D X.V q B := (mem_filter.mp step.1).2
  have sz : 1<(added X.D F B).card := by rw [count cyc]; omega
  obtain ⟨i,ih,j,jh,ne⟩ := one_lt_card.mp sz
  have sep : i.1≠j.1 := fun h => ne (matching cyc ih jh (Or.inl h))
  let lift (e : ℕ×ℕ) (h : e∈added X.D F B) : Miss :=
    ⟨(⟨e.1,cyc.sub (mem_added.mp h).1⟩,⟨e.2,cyc.sub (mem_added.mp h).2.1⟩),(mem_added.mp h).2.2⟩
  obtain ⟨a,alone⟩ : ∃a : Miss,∀g : Miss,act g → g.val.1=a.val.1 := by
    by_cases any : ∃g : Miss,act g
    · obtain ⟨g,hit⟩ := any
      exact ⟨g,fun e h => by by_contra ne; exact two ⟨e,g,h,hit,ne⟩⟩
    · exact ⟨lift i ih,fun e hit => (any ⟨e,hit⟩).elim⟩
  obtain ⟨b,distinct⟩ : ∃b : Miss,a.val.1≠b.val.1 := by
    by_cases same : a.val.1=(lift i ih).val.1
    · exact ⟨lift j jh,fun h => sep (congrArg Subtype.val (same.symm.trans h))⟩
    · exact ⟨lift i ih,same⟩
  let tails : Finset ℕ := {(a.val.1:ℕ),(b.val.1:ℕ)}
  have size : tails.card + (∅ : Finset ℕ).card < (targets X.D X.V F B).card := by
    have d : (a.val.1:ℕ)≠(b.val.1:ℕ) := fun e => distinct (Subtype.ext e)
    simp [tails,d]; omega
  obtain ⟨p,pn,pm,cols⟩ := strict_stars X hq small step least tails ∅ size (fresh a) (fresh b)
    distinct (by simp [tails]) (by simp [tails])
  have incl : ∀u∈X.V,∀v∈X.V,SharedArcCover.onStars X.D (graph X.D F) L R u v=true →
      SharedArcCover.onStars X.D (graph X.D F) tails ∅ u v=true := by
    intro u uv v vv ed
    have native {h k} (old : graph X.D F h k=true) : X.D h k=true := by
      obtain ⟨A,m⟩ := active.mp old
      exact (mem_col.mp m).2.2.2
    by_cases keep : graph X.D F u v=true
    · simp [SharedArcCover.onStars,keep,native keep]
    · have chosen : u∈L ∨ v∈R := by by_contra h; simp [SharedArcCover.onStars,h,keep] at ed
      have orig : X.D u v=true := by simpa [SharedArcCover.onStars,chosen] using ed
      let e : Miss := ⟨(⟨u,uv⟩,⟨v,vv⟩),orig,Bool.eq_false_iff.mpr keep⟩
      have equ : u=(a.val.1:ℕ) := congrArg Subtype.val (alone e chosen)
      have included : u∈tails := equ ▸ mem_insert_self _ _
      simp [SharedArcCover.onStars,included,orig]
  exact ⟨p,pn,pm,fun j => lt_of_le_of_lt
    (sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (realMatrix_mono_graph incl i j) (pn i))) (cols j)⟩

#print axioms every_strict

#print axioms two_targets
#print axioms strict_stars
end LeanCH.BR.Closure.SharedArcReachMargin
