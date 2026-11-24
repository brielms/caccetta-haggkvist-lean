import checkpoints.shen_extension.SharedArcPivotPaths

namespace LeanCH.BR.Closure.SharedArcPunctureExpansion
open Finset Matrix BRq2 BRq3 BR45 WeightedSD FiniteCutInverse ShortestCycleWeights
open scoped Matrix

/-- Evaluate both products with the same native inverse at the root.
The diagonal is retained so the identities apply also to ordinary roots. -/
theorem inverse_accounts {q n} (X : Model q n) {H : Matrix X.V X.V ℝ}
    (inv : CommonInverse (realMatrix q X.D X.V) H) (a : X.V) :
    H a a + q*(∑j : X.V,if X.D a j=true then H j a else 0) = (∑j,H j a)+1 ∧
    H a a + q*(∑j : X.V,if X.D j a=true then H a j else 0) = (∑j,H a j)+1 := by
  classical
  have l := congrArg (fun M : Matrix X.V X.V ℝ => M a a) inv.right
  have r := congrArg (fun M : Matrix X.V X.V ℝ => M a a) (mul_eq_one_comm.mp inv.right)
  simp only [mul_apply,excess,realMatrix_entry,sub_mul,add_mul,ite_mul,one_mul,zero_mul,
    sum_sub_distrib,sum_add_distrib,one_apply_eq] at l
  simp only [mul_apply,excess,realMatrix_entry,mul_sub,mul_add,mul_ite,mul_one,mul_zero,
    sum_sub_distrib,sum_add_distrib,one_apply_eq] at r
  simp only [mul_sum,mul_ite,mul_zero]
  constructor
  · simp only [sum_ite_eq,mem_univ,ite_true] at l
    linarith
  · simp only [sum_ite_eq',mem_univ,ite_true,mul_comm (H a _) (q:ℝ)] at r
    linarith

/-- No head-to-parent walk may have length at most q-2. The walk may use
the whole source, so the restriction also holds in every puncture. -/
theorem far_parent {q n} (X : Model q n) (hq : 2≤q) (a h t : X.V)
    (head : X.D a h=true) (parent : X.D t a=true) :
    t.val∉ball X.D X.V h (q-2) := by
  rintro hit
  obtain ⟨_,k,bound,path⟩ := mem_ball.mp hit
  exact X.free a (k+1+1) (by omega) (by omega) (.step h.property head (path.snoc a.property parent))

/-- The row price outside the (q-2)-step reach of all heads pays the
entire mass plus one, less the root diagonal. -/
theorem far_mass {q n} (X : Model q n) (hq : 2≤q) {H : Matrix X.V X.V ℝ}
    (inv : CommonInverse (realMatrix q X.D X.V) H) (a : X.V) :
    let far := univ.filter (fun t : X.V => ∀h : X.V,X.D a h=true → t.val∉ball X.D X.V h (q-2))
    (∑j,H a j)+1 ≤ H a a + q*(∑t∈far,H a t) := by
  classical
  intro far
  rw [←(inverse_accounts X inv a).2]
  apply add_le_add_right
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  rw [show (∑j : X.V,if X.D j a=true then H a j else 0) =
    ∑j∈univ.filter (fun j : X.V => X.D j a=true),H a j by rw [sum_filter]]
  apply sum_le_sum_of_subset_of_nonneg
  · intro t ht
    exact mem_filter.mpr ⟨mem_univ _,fun h ah => far_parent X hq a h t ah (mem_filter.mp ht).2⟩
  · exact fun t _ _ => inv.nonneg a t

#print axioms inverse_accounts
#print axioms far_mass

/-- The exceptional tail has zero diagonal in the native inverse.
The puncture probability vector has surplus at that tail alone. -/
theorem zero_diagonal {q n} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    {F B} (step : SharedArcBarrier.Boundary X F B)
    (least : ∀M,SharedArcBarrier.Boundary X F M →
      (SharedArcBarrier.targets X.D X.V F B).card≤(SharedArcBarrier.targets X.D X.V F M).card)
    (multi : 1<(SharedArcBarrier.targets X.D X.V F B).card) {a b : X.V}
    (tested : SharedArcComponentExchange.Fresh X F (a,b))
    (no : ¬SharedArcReachMargin.StrictColumns q (insertArc (FirstPacketBarrier.graph X.D F) a b) X.V)
    {H : Matrix X.V X.V ℝ} (inv : CommonInverse (realMatrix q X.D X.V) H) : H a a=0 := by
  classical
  obtain ⟨incl,miss⟩ := SharedArcPivot.single_data X hq step least multi tested
  obtain ⟨w,_,wm,wa,rows,_⟩ := SharedArcPivot.one_hole X hq small _ incl a b miss no
  let W (i : X.V) := (w i : ℝ)
  let D := realMatrix q X.D X.V
  let g := excess D *ᵥ W
  have mass : ∑i,W i=1 := by dsimp [W]; exact_mod_cast wm
  have eq (i : X.V) (ne : i≠a) : g i=0 := by
    change (excess D *ᵥ W) i=0
    rw [mulVec_excess,mass,sub_eq_zero]
    have hr := (rows i ne).2
    change (∑j,WeightedArithmetic.rationalMatrix q (adjacencyMatrix X.D X.V) i j*w j)=1 at hr
    change (∑j,((WeightedArithmetic.rationalMatrix q (adjacencyMatrix X.D X.V) i j:ℚ):ℝ)*(w j:ℝ))=1
    exact_mod_cast hr
  have back : H *ᵥ g=W := by
    dsimp only [g,D]
    rw [mulVec_mulVec,mul_eq_one_comm.mp inv.right,one_mulVec]
  have ray (i : X.V) : W i=H i a*g a := by
    rw [←congrFun back i]
    change (∑j,H i j*g j)=_
    apply sum_eq_single a
    · intro j _ ne; rw [eq j ne,mul_zero]
    · simp
  have gn : g a≠0 := by
    intro gz
    simp [fun i => (ray i).trans (by rw [gz,mul_zero])] at mass
  exact (mul_eq_zero.mp ((ray a).symm.trans (by simp [W,wa]))).resolve_right gn

#print axioms zero_diagonal

/-- A failed edit must exhibit a pair of heavy sets separated by q-2
steps, with the source and target measures taken from the same inverse. -/
theorem separated_mass {q n} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    {F B} (step : SharedArcBarrier.Boundary X F B)
    (least : ∀M,SharedArcBarrier.Boundary X F M →
      (SharedArcBarrier.targets X.D X.V F B).card≤(SharedArcBarrier.targets X.D X.V F M).card)
    (multi : 1<(SharedArcBarrier.targets X.D X.V F B).card) {a b : X.V}
    (tested : SharedArcComponentExchange.Fresh X F (a,b))
    (no : ¬SharedArcReachMargin.StrictColumns q (insertArc (FirstPacketBarrier.graph X.D F) a b) X.V) :
    ∃H : Matrix X.V X.V ℝ,CommonInverse (realMatrix q X.D X.V) H ∧ H a a=0 ∧
      q*(∑j : X.V,if X.D a j=true then H j a else 0)=(∑j,H j a)+1 ∧
      (∑j,H a j)+1 ≤ q*(∑t∈univ.filter (fun t : X.V => ∀h : X.V,
        X.D a h=true → t.val∉ball X.D X.V h (q-2)),H a t) := by
  obtain ⟨H,inv⟩ := strict_inverse_of_proper_smallRow (small.induced X.free)
    (fun i => (X.weights i:ℚ)) (fun _ _ => Nat.cast_nonneg _) X.strict
  have diag := zero_diagonal X hq small step least multi tested no inv
  refine ⟨H,inv,diag,?_,?_⟩
  · simpa only [diag,zero_add] using (inverse_accounts X inv a).1
  · simpa only [diag,zero_add] using far_mass X hq inv a

#print axioms separated_mass
end LeanCH.BR.Closure.SharedArcPunctureExpansion
