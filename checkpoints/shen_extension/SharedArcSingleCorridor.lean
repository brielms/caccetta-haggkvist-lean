import checkpoints.shen_extension.SharedArcReachMargin

namespace LeanCH.BR.Closure.SharedArcSingleCorridor
open Finset BRq2 BRq3 BR45 WeightedSD ShortestCycleWeights FirstPacketBarrier MarkedCyclePeeling
open SharedArcBarrier SharedArcComponentExchange

private theorem liftWalk {D J : CH.Digraph} {V x y k} (incl : ∀i j,D i j=true → J i j=true)
    (p : Walk D V x y k) : Walk J V x y k := by
  induction p with
  | refl => exact .refl _
  | step hv uv _ ih => exact .step hv (incl _ _ uv) ih

private theorem splitWalk {E V a b x y k} (p : Walk (insertArc E a b) V x y k) :
    Walk E V x y k ∨ ∃m l,k=m+1+l ∧ Walk E V x a m ∧ Walk (insertArc E a b) V b y l := by
  induction p with
  | refl => exact Or.inl (.refl _)
  | @step i j y k jv ij tail ih =>
    by_cases atArc : i=a ∧ j=b
    · obtain ⟨rfl,rfl⟩ := atArc
      exact Or.inr ⟨0,k,by omega,.refl _,tail⟩
    · have old : E i j=true := by simpa [insertArc,atArc] using ij
      rcases ih with inside|⟨m,l,eq,pre,suf⟩
      · exact Or.inl (.step jv old inside)
      · exact Or.inr ⟨m+1,l,by omega,.step jv old pre,suf⟩

/-- If a one-arc child has no strict subunit dual at a multiple-head
minimum, every native fresh arc with a different tail lies on an actual
length-q geodesic returning from the chosen head to the chosen tail.
Both pieces on either side of that competing arc are entirely old. -/
theorem corridor {q n} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    {F B} (step : Boundary X F B)
    (least : ∀M,Boundary X F M → (targets X.D X.V F B).card≤(targets X.D X.V F M).card)
    (multi : 1<(targets X.D X.V F B).card)
    {a b : X.V} (first : Fresh X F (a,b))
    (survives : ¬SharedArcReachMargin.StrictColumns q (insertArc (graph X.D F) a b) X.V)
    {u v : X.V} (second : Fresh X F (u,v)) (diff : a≠u) :
    ∃l m,l+1+m=q ∧ Walk (graph X.D F) X.V b u l ∧ Walk (graph X.D F) X.V v a m := by
  classical
  let E := graph X.D F
  let J := insertArc E a b
  have old {i j} (ed : E i j=true) : X.D i j=true := by
    obtain ⟨A,h⟩ := active.mp ed
    exact (mem_col.mp h).2.2.2
  have native {i j} (ed : J i j=true) : X.D i j=true := by
    by_cases same : i=(a:ℕ) ∧ j=(b:ℕ)
    · exact same.1 ▸ same.2 ▸ first.2.2.1
    exact old (by simpa [J,insertArc,same] using ed)
  have oldStar (t : ℕ) {i j} (ed : E i j=true) :
      SharedArcCover.onStars X.D E {t} ∅ i j=true := by simp [SharedArcCover.onStars,ed,old ed]
  have hole : (a:ℕ)∉ball J X.V b q := by
    rintro ret
    obtain ⟨_,k,le,path⟩ := mem_ball.mp ret
    apply SharedArcCover.no_return X hq step least {a.val} ∅ (by simpa using multi) first (by simp)
    refine mem_ball.mpr ⟨a.property,k,le,liftWalk ?_ path⟩
    intro i j ed
    by_cases same : i=(a:ℕ) ∧ j=(b:ℕ)
    · obtain ⟨rfl,rfl⟩ := same
      simp [SharedArcCover.onStars,first.2.2.1]
    · exact oldStar a (by simpa [J,insertArc,same] using ed)
  have ret : (u:ℕ)∈ball J X.V v q := by
    by_contra missing
    exact survives (SharedArcReachMargin.two_targets X hq small J (fun _ _ e => native e)
      a u diff ⟨b,hole⟩ ⟨v,missing⟩)
  obtain ⟨_,k,le,path⟩ := mem_ball.mp ret
  have length : k=q := by
    by_contra ne
    exact X.free u (k+1) (by omega) (by omega) (.step v.property second.2.2.1 (liftWalk (fun _ _ e => native e) path))
  rcases splitWalk path with kept|⟨m,l,eq,pre,suf⟩
  · exact (SharedArcCover.no_return X hq step least {u.val} ∅ (by simpa using multi) second (by simp)
      (mem_ball.mpr ⟨u.property,k,le,liftWalk (fun _ _ e => oldStar u e) kept⟩)).elim
  rcases splitWalk suf with finish|⟨z,h,other,twice,_⟩
  · exact ⟨l,m,by omega,finish,pre⟩
  · exact (hole (mem_ball.mpr ⟨a.property,z,by omega,liftWalk (insertArc_mono E a b) twice⟩)).elim

#print axioms corridor
end LeanCH.BR.Closure.SharedArcSingleCorridor
