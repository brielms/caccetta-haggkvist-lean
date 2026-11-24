import checkpoints.shen_extension.SingleArcAlternative
import LeanCH.BR.BRWeightedOutUniformSaturation

namespace LeanCH.BR.Closure.SingleArcModuleBoundary
open Finset BRq2 BRq3 BR45 BRsub WeightedSD ShenPrimeTransition
open ShortestCycleWeights FirstPacketBarrier MarkedCyclePeeling

/-- Every proper nontrivial set whose old rows agree outside it has a
missing native arc leaving it. The incoming version holds separately. -/
theorem crossing {q n} (X : Model q n) (F : Family) {M : Finset ℕ}
    (sub : M⊆X.V) (size : 2≤M.card) (proper : M≠X.V) :
    (OutUniform (graph X.D F) X.V M → ∃g : SharedArcFlatCut.Missing X F, g.val.1.val∈M ∧ g.val.2.val∉M) ∧
    (InUniform (graph X.D F) X.V M → ∃g : SharedArcFlatCut.Missing X F, g.val.2.val∈M ∧ g.val.1.val∉M) := by
  classical
  let E := graph X.D F
  have agree (i j : X.V) (no : ∀g : SharedArcFlatCut.Missing X F,g.val≠(i,j)) :
      X.D i j = E i j := by
    apply Bool.eq_iff_iff.mpr
    constructor
    · intro ed
      by_contra bad
      exact no ⟨(i,j),ed,Bool.eq_false_iff.mpr bad⟩ rfl
    · intro ed
      exact (mem_col.mp (active.mp ed).choose_spec).2.2.2
  have prime := X.prime M sub size proper
  constructor
  · intro old
    by_contra! none
    have edge (i) (im : i∈M) (j) (jv : j∈X.V) (jm : j∉M) : X.D i j = E i j := by
      apply agree ⟨i,sub im⟩ ⟨j,jv⟩
      intro g eq
      have fact := none g
      rw [eq] at fact
      exact jm (fact im)
    have out : OutUniform X.D X.V M := fun i im j jm z zv zm =>
      (edge i im z zv zm).trans ((old i im j jm z zv zm).trans (edge j jm z zv zm).symm)
    exact prime ⟨out,outUniform_inUniform X.free X.sat sub out⟩
  · intro old
    by_contra! none
    have edge (i) (iv : i∈X.V) (im : i∉M) (j) (jm : j∈M) : X.D i j = E i j := by
      apply agree ⟨i,iv⟩ ⟨j,sub jm⟩
      intro g eq
      have fact := none g
      rw [eq] at fact
      exact im (fact jm)
    have inc : InUniform X.D X.V M := fun i im j jm z zv zm =>
      (edge z zv zm i im).trans ((old i im j jm z zv zm).trans (edge z zv zm j jm).symm)
    exact prime ⟨outUniform_inUniform (D:=fun i j => X.D j i) X.free.reverse
      (SerialChain.sat_reverse X.sat) sub inc,inc⟩

theorem at_singleton {q n} (X : Model q n) (F : Family) (f : SharedArcFlatCut.Missing X F)
    (single : ∀g : SharedArcFlatCut.Missing X F,g=f) :
    Prime (graph X.D F) X.V ∧ ∀M⊆X.V,2≤M.card → M≠X.V →
      (OutUniform (graph X.D F) X.V M → f.val.1.val∈M ∧ f.val.2.val∉M) ∧
      (InUniform (graph X.D F) X.V M → f.val.2.val∈M ∧ f.val.1.val∉M) := by
  have sides (M) (sub : M⊆X.V) (size : 2≤M.card) (proper : M≠X.V) := crossing X F sub size proper
  constructor
  · intro M sub size proper modl
    obtain ⟨g,_,head⟩ := (sides M sub size proper).1 modl.1
    obtain ⟨h,inside,_⟩ := (sides M sub size proper).2 modl.2
    exact head ((single h).trans (single g).symm ▸ inside)
  · intro M sub size proper
    constructor
    · intro old; obtain ⟨g,hit⟩ := (sides M sub size proper).1 old; exact single g ▸ hit
    · intro old; obtain ⟨g,hit⟩ := (sides M sub size proper).2 old; exact single g ▸ hit

/-- In the flat branch the existing positive-feasible saturation theorem
excludes even one-sided modules, without global uniqueness of the insertion. -/
theorem on_flat {q n} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    (F : Family) (f : SharedArcFlatCut.Missing X F) {w p : ℕ→ℚ}
    (pos : ∀i∈X.V,0<w i ∧ 0<p i)
    (rows : ∀i∈X.V,mass X.V w≤WeightedSD.row q (graph X.D F) X.V w i)
    (cols : ∀i∈X.V,mass X.V p≤WeightedSD.col q (graph X.D F) X.V p i) :
    ∀M⊆X.V,2≤M.card → M≠X.V →
      ¬OutUniform (graph X.D F) X.V M ∧ ¬InUniform (graph X.D F) X.V M := by
  let E := graph X.D F
  let a := f.val.1
  let b := f.val.2
  have sub (i j) (ed : E i j=true) : X.D i j=true := (mem_col.mp (active.mp ed).choose_spec).2.2.2
  have unsat {D G : CH.Digraph} (free : QFree D X.V q) (x y : X.V)
      (old : ∀i j,G i j=true → D i j=true) (native : D x y=true) (off : G x y=false) : ¬Sat q G X.V := by
    intro sat
    obtain ⟨_,l,len,path⟩ := mem_ball.mp (sat y y.property x x.property (by simp [off]))
    exact free _ (l+1) (by omega) (by omega) (.step y.property native (walk_sub old path))
  intro M mv size proper
  refine ⟨positive_feasible_nonsaturated_out_prime hq small (qfree_sub sub X.free)
    (unsat X.free a b sub f.property.1 f.property.2) w (fun i iv => (pos i iv).1) rows M mv size proper,?_⟩
  exact positive_feasible_nonsaturated_out_prime (D:=fun i j => E j i) hq small (qfree_sub sub X.free).reverse
    (unsat X.free.reverse b a (fun i j => sub j i) f.property.1 f.property.2) p
    (fun i iv => (pos i iv).2) cols M mv size proper

end LeanCH.BR.Closure.SingleArcModuleBoundary
#print axioms LeanCH.BR.Closure.SingleArcModuleBoundary.at_singleton
#print axioms LeanCH.BR.Closure.SingleArcModuleBoundary.on_flat
