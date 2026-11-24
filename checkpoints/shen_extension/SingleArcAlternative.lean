import checkpoints.shen_extension.SingleArcReturnProfile

namespace LeanCH.BR.Closure.SingleArcAlternative
open Finset BRq2 BRq3 BR45 ShortestCycleWeights FirstPacketBarrier MarkedCyclePeeling

/-- A short native walk uses the unique new arc at most once. -/
private theorem split {D E : CH.Digraph} {V : Finset ℕ} {q a b i j m : ℕ}
    (free : QFree D V q) (sub : ∀u v,E u v=true → D u v=true)
    (only : ∀u∈V,∀v∈V,D u v=true → E u v=true ∨ (u=a ∧ v=b))
    (w : Walk D V i j m) (iv : i∈V) (len : m≤q) :
    Walk E V i j m ∨ ∃l r, l+1+r=m ∧ Walk E V i a l ∧ Walk E V b j r := by
  induction w with
  | refl => exact Or.inl (.refl _)
  | @step i h j m hv ed rest ih =>
    rcases ih hv (by omega) with old | ⟨l,r,eq,pre,post⟩
    · rcases only i iv h hv ed with keep | ⟨rfl,rfl⟩
      · exact Or.inl (.step hv keep old)
      · exact Or.inr ⟨0,m,by omega,.refl _,old⟩
    · rcases only i iv h hv ed with keep | ⟨rfl,rfl⟩
      · exact Or.inr ⟨l+1,r,by omega,.step hv keep pre,post⟩
      · exact (free i (l+1) (by omega) (by omega) (.step hv ed (walk_sub sub pre))).elim

/-- For a globally unique missing native arc a→b, every other individually
legal old nonedge x→y has old paths y⇝a and b⇝x with total length at most q−2.
Together with the two edits these paths form a prohibited short closed walk. -/
theorem paths {q n} (X : Model q n) (hq : 2≤q) (F : Family)
    (f : SharedArcFlatCut.Missing X F) (single : ∀g : SharedArcFlatCut.Missing X F,g=f)
    (x y : X.V) (different : (x,y)≠f.val) (off : graph X.D F x y=false)
    (legal : x.val∉ball (graph X.D F) X.V y (q-1)) :
    ∃l r, l+r+2≤q ∧ Walk (graph X.D F) X.V y f.val.1 l ∧ Walk (graph X.D F) X.V f.val.2 x r := by
  let E := graph X.D F
  have sub (i j) (ed : E i j=true) : X.D i j=true := (mem_col.mp (active.mp ed).choose_spec).2.2.2
  have only (i) (iv : i∈X.V) (j) (jv : j∈X.V) (ed : X.D i j=true) :
      E i j=true ∨ (i=f.val.1.val ∧ j=f.val.2.val) := by
    by_cases keep : E i j=true
    · exact Or.inl keep
    · let g : SharedArcFlatCut.Missing X F := ⟨(⟨i,iv⟩,⟨j,jv⟩),ed,Bool.eq_false_iff.mpr keep⟩
      exact Or.inr ⟨congrArg (fun z : SharedArcFlatCut.Missing X F => z.val.1.val) (single g),
        congrArg (fun z : SharedArcFlatCut.Missing X F => z.val.2.val) (single g)⟩
  have absent (ed : X.D x y=true) : False := different (congrArg Subtype.val (single ⟨(x,y),ed,off⟩))
  obtain ⟨_,m,short,w⟩ := mem_ball.mp (X.sat y y.property x x.property absent)
  rcases split X.free sub only w y.property (by omega) with old | ⟨l,r,eq,pre,post⟩
  · exact (legal (mem_ball.mpr ⟨x.property,m,short,old⟩)).elim
  · exact ⟨l,r,by omega,pre,post⟩

/-- With one specified native insertion, whether it is the only one is
determined entirely by the old graph and this pair of endpoints. -/
theorem singleton_iff {q n} (X : Model q n) (hq : 2≤q) (F : Family)
    (f : SharedArcFlatCut.Missing X F) :
    (∀g : SharedArcFlatCut.Missing X F,g=f) ↔
      ∀x y : X.V, (x,y)≠f.val → graph X.D F x y=false →
        x.val∉ball (graph X.D F) X.V y (q-1) →
        ∃l r, l+r+2≤q ∧ Walk (graph X.D F) X.V y f.val.1 l ∧ Walk (graph X.D F) X.V f.val.2 x r := by
  refine ⟨paths X hq F f,?_⟩
  intro all g
  by_contra ne
  have sub (i j) (ed : graph X.D F i j=true) : X.D i j=true :=
    (mem_col.mp (active.mp ed).choose_spec).2.2.2
  have legal : g.val.1.val∉ball (graph X.D F) X.V g.val.2 (q-1) := by
    intro mem
    obtain ⟨_,m,bound,path⟩ := mem_ball.mp mem
    exact X.free _ (m+1) (by omega) (by omega) (.step g.val.2.property g.property.1 (walk_sub sub path))
  obtain ⟨l,r,len,pre,post⟩ :=
    all g.val.1 g.val.2 (fun eq => ne (Subtype.ext eq)) g.property.2 legal
  have back : Walk X.D X.V g.val.2 g.val.1 (l+(r+1)) :=
    (walk_sub sub pre).append (.step f.val.2.property f.property.1 (walk_sub sub post))
  exact X.free _ (l+(r+1)+1) (by omega) (by omega) (.step g.val.2.property g.property.1 back)

theorem triangle {q n} (X : Model q n) (three : q=3) (F : Family)
    (f : SharedArcFlatCut.Missing X F) (single : ∀g : SharedArcFlatCut.Missing X F,g=f)
    (x y : X.V) (different : (x,y)≠f.val) (off : graph X.D F x y=false)
    (legal : x.val∉ball (graph X.D F) X.V y (q-1)) :
    x=f.val.2 ∨ y=f.val.1 := by
  obtain ⟨l,r,short,pre,post⟩ := paths X (by omega) F f single x y different off legal
  rcases (by omega : r=0 ∨ l=0) with hr | hl
  · exact Or.inl (Subtype.ext (walk_zero (hr ▸ post)).symm)
  · exact Or.inr (Subtype.ext (walk_zero (hl ▸ pre)))

end LeanCH.BR.Closure.SingleArcAlternative
#print axioms LeanCH.BR.Closure.SingleArcAlternative.paths
#print axioms LeanCH.BR.Closure.SingleArcAlternative.singleton_iff
#print axioms LeanCH.BR.Closure.SingleArcAlternative.triangle
