import checkpoints.shen_extension.SharedArcProductReach

namespace LeanCH.BR.Closure.SharedArcPivotLoopSums
open Finset Matrix BRq2 BRq3 BR45 WeightedSD FiniteCutInverse ShortestCycleWeights
open SharedArcBarrier SharedArcComponentExchange FirstPacketBarrier MarkedCyclePeeling
open scoped Matrix

private theorem triangular {K : Matrix (Fin 2) (Fin 2) ℝ} (nn : ∀i j,0≤K i j) (zero : K 1 0=0) :
    PacketCompression.Feasible K ↔ 1≤K 0 0 ∨ 1≤K 1 1 := by
  constructor
  · rintro ⟨t,⟨tn,v,live⟩,ok⟩
    have left := ok 0
    have right := ok 1
    simp only [vecMul,dotProduct,Fin.sum_univ_two,zero,mul_zero,add_zero] at left right
    by_cases hp : 0<t 0
    · exact Or.inl (by by_contra! h; nlinarith [mul_pos hp (sub_pos.mpr h)])
    · have gone : t 0=0 := le_antisymm (le_of_not_gt hp) (tn 0)
      have hp' : 0<t 1 := by fin_cases v <;> simp_all
      rw [gone,zero_mul,zero_add] at right
      exact Or.inr (by by_contra! h; nlinarith [mul_pos hp' (sub_pos.mpr h)])
  · rintro (h|h)
    · exact PacketCompression.pivot_pays nn 0 h
    · exact PacketCompression.pivot_pays nn 1 h

/-- Two stars meeting at a zero inverse diagonal have no return from the
second intermediate index to the first. Feasibility depends only on
their two diagonal charges, including the equality case. -/
theorem two_sums {V : Type*} [Fintype V] [DecidableEq V] {R S H : Matrix V V ℝ}
    (inv : CommonInverse R H) (a : V) (zero : H a a=0) (u v : V→ℝ)
    (un : ∀j,0≤u j) (vn : ∀i,0≤v i)
    (delta : ∀i j,R i j-S i j=(if i=a then u j else 0)+(if j=a then v i else 0)) :
    (∃p : V→ℝ,PacketCompression.Live p ∧ ∀i,(p ᵥ* excess S) i≤0) ↔
      1≤∑j,u j*H j a ∨ 1≤∑i,H a i*v i := by
  classical
  let L : Matrix V (Fin 2) ℝ := fun i k => if k=0 then (if i=a then 1 else 0) else v i
  let T : Matrix (Fin 2) V ℝ := fun k j => if k=0 then u j else (if j=a then 1 else 0)
  have ln (i j) : 0≤L i j := by dsimp [L]; split_ifs <;> first | exact vn _ | norm_num
  have tn (i j) : 0≤T i j := by dsimp [T]; split_ifs <;> first | exact un _ | norm_num
  have edit : excess S=excess R-L*T := by
    ext i j
    have d := delta i j
    change S i j-1=R i j-1-(∑h : Fin 2,L i h*T h j)
    rw [Fin.sum_univ_two]
    by_cases ia : i=a <;> by_cases ja : j=a <;> simp [L,T,ia,ja] at d ⊢ <;> linarith only [d]
  let K := T*H*L
  have nn i j : 0≤K i j := sum_nonneg fun k _ => mul_nonneg
    (sum_nonneg fun g _ => mul_nonneg (tn i g) (inv.nonneg g k)) (ln k j)
  have col0 (i) : K i 0=(T*H) i a := by
    change (∑j,(T*H) i j*L j 0)=_
    simp [L,mul_ite]
  have row1 (j) : (T*H) 1 j=H a j := by
    change (∑i,T 1 i*H i j)=_
    simp [T,ite_mul]
  have ki : K 1 0=0 := (col0 1).trans ((row1 a).trans zero)
  have out : K 0 0=∑j,u j*H j a := by rw [col0]; rfl
  have inc : K 1 1=∑i,H a i*v i := by
    change (∑i,(T*H) 1 i*L i 1)=_
    simp only [row1]; simp [L]
  rw [PacketCompression.paid_iff inv L T ln tn edit]
  change PacketCompression.Feasible K ↔ _
  rw [triangular nn ki,out,inc]

private theorem graph_dual {q : ℕ} {E : CH.Digraph} {V : Finset ℕ} (live : V.Nonempty) :
    SmallRow q E V ↔ ∃p : V→ℝ,PacketCompression.Live p ∧ ∀i,(p ᵥ* excess (realMatrix q E V)) i≤0 := by
  rw [PacketCompression.normalize]
  constructor
  · intro good
    obtain ⟨p,hp⟩ := realDual_of_smallRow good live
    exact ⟨fun i : V => p i,fun i => hp.nonneg i i.property,by rw [sum_coe_sort]; exact hp.normalized,
      fun i => by rw [realMatrix_col]; exact hp.columns i i.property⟩
  · rintro ⟨p,pn,pm,pc⟩
    apply smallRow_of_realDual (p:=realExtendWeight V p)
    constructor
    · intro j hj; rw [realExtendWeight_on V p ⟨j,hj⟩]; exact pn _
    · rw [realMass_extendWeight]; exact pm
    · intro j hj
      rw [←realMatrix_col q E V _ ⟨j,hj⟩,show (fun i : V => realExtendWeight V p i)=p from
        funext (realExtendWeight_on V p)]
      exact pc _

/-- Every competing attachment of the same terminal family is decided by
one fixed native inverse. The row and column sums are over all missing
native arcs of that competitor at the exceptional vertex. -/
theorem all_competitors {q n} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    {F B} (step : Boundary X F B)
    (least : ∀M,Boundary X F M → (targets X.D X.V F B).card≤(targets X.D X.V F M).card)
    (multi : 1<(targets X.D X.V F B).card) {a b : X.V} (edge : Fresh X F (a,b))
    (no : ¬SharedArcReachMargin.StrictColumns q (insertArc (graph X.D F) a b) X.V) :
    ∃H : Matrix X.V X.V ℝ,CommonInverse (realMatrix q X.D X.V) H ∧ ∀M : Finset ℕ,
      let E := graph X.D (insert M F)
      let loss := realMatrix q X.D X.V-realMatrix q E X.V
      SmallRow q E X.V ↔ 1≤∑j,loss a j*H j a ∨ 1≤∑i,H a i*loss i a := by
  classical
  obtain ⟨H,inv⟩ := strict_inverse_of_proper_smallRow (small.induced X.free)
    (fun i => (X.weights i:ℚ)) (fun _ _ => Nat.cast_nonneg _) X.strict
  have zero := SharedArcPunctureExpansion.zero_diagonal X hq small step least multi edge no inv
  have center := SharedArcPivot.single_center X hq small step least multi edge no
  refine ⟨H,inv,?_⟩
  intro M E loss
  have sub : ∀i∈X.V,∀j∈X.V,E i j=true → X.D i j=true := by
    intro i _ j _ e; obtain ⟨C,m⟩ := active.mp e; exact (mem_col.mp m).2.2.2
  have nn (i j : X.V) : 0≤loss i j := sub_nonneg.mpr (realMatrix_mono_graph sub i j)
  have aa : loss a a=0 := by
    change realMatrix q X.D X.V a a-realMatrix q E X.V a a=_
    rw [realMatrix_added_difference sub]
    simp [loopfree X.free (by omega : 1≤q) a.property]
  rw [graph_dual X.live]
  apply two_sums inv a zero (fun j => loss a j) (fun i => loss i a) (nn a) (fun i => nn i a)
  intro i j
  change loss i j=_
  by_cases ia : i=a
  · subst i; by_cases ja : j=a <;> simp [ja,aa]
  by_cases ja : j=a
  · subst j; simp [ia]
  simp only [ia,ja,ite_false,zero_add]
  change realMatrix q X.D X.V i j-realMatrix q E X.V i j=0
  rw [realMatrix_added_difference sub]
  suffices ¬(X.D i j=true ∧ ¬E i j=true) by simp only [this,ite_false]
  rintro ⟨native,off⟩
  have oldOff : graph X.D F i j=false := Bool.eq_false_iff.mpr (by
    intro e; obtain ⟨C,m⟩ := active.mp e
    obtain ⟨cf,ic,jc,d⟩ := mem_col.mp m
    exact off (active.mpr ⟨C,mem_col.mpr ⟨mem_insert_of_mem cf,ic,jc,d⟩⟩))
  exact (center ⟨(i,j),native,oldOff⟩).elim ia ja

#print axioms two_sums
#print axioms all_competitors

/-- In the exceptional branch either native sum pays the existing
recursive exit, for the actual boundary chosen. -/
theorem progress {q n} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    {F B} (step : Boundary X F B)
    (least : ∀M,Boundary X F M → (targets X.D X.V F B).card≤(targets X.D X.V F M).card)
    (stuck : ¬SmallRow q (graph X.D (insert B F)) X.V)
    (multi : 1<(targets X.D X.V F B).card) {a b : X.V} (edge : Fresh X F (a,b))
    (no : ¬SharedArcReachMargin.StrictColumns q (insertArc (graph X.D F) a b) X.V) :
    ∃H : Matrix X.V X.V ℝ,CommonInverse (realMatrix q X.D X.V) H ∧ ∀M,Boundary X F M →
      let loss := realMatrix q X.D X.V-realMatrix q (graph X.D (insert M F)) X.V
      (SharedArcCompression.winning X F B M ↔ 1≤∑j,loss a j*H j a ∨ 1≤∑i,H a i*loss i a) ∧
      ((1≤∑j,loss a j*H j a ∨ 1≤∑i,H a i*loss i a) →
        ∀J p c,SharedArcPivot.ProgressAt X F B J p c) := by
  obtain ⟨H,inv,eq⟩ := all_competitors X hq small step least multi edge no
  refine ⟨H,inv,?_⟩
  intro M bm loss
  have test := (SharedArcCompression.winning_iff X small step stuck M).trans (eq M)
  exact ⟨test,fun paid _ _ _ => Or.inr ⟨M,bm,test.mpr paid⟩⟩

#print axioms progress
end LeanCH.BR.Closure.SharedArcPivotLoopSums
