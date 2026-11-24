import checkpoints.puncture_law_20261119.HeirRound
import checkpoints.shen_extension.SharedArcPacketReturns
import LeanCH.BR.BRWeightedCritical
import LeanCH.BR.BRNearBoundaryRows
import LeanCH.BR.BRSerialChain

/-! Heir law glue. Co-heir mirror of `sat_of_heirs` (by reversing the graph), heirs from a source
vertex (by `no_incoming_domination`), and the reduction of `FlatLaw` to an heir / co-heir law. -/

set_option linter.style.longLine false

namespace LeanCH.BR.Closure.HeirLaw
open Finset BRq2 BRq3 BR45 WeightedSD ShenCycleSuccessor ShortestCycleWeights FirstPacketBarrier
open MarkedCyclePeeling SharedArcExpansion SharedArcBarrier SharedArcMinimalPacket

/-! ## Item 1. Co-heirs -/

/-- **Co-heir mirror.** Every vertex `b` has a co-heir `k` (an in-neighbour of `b` whose other
out-neighbours are all out-neighbours of `b`), no proper subset of size `≥ 2` is out-uniform, and a
positive unit column law of mass one: then the graph is saturated. -/
theorem sat_of_coheirs {q : ℕ} (hq : 2 ≤ q) {E : CH.Digraph} {V : Finset ℕ}
    (free : QFree E V q)
    {p : ℕ → ℚ} (hp : ∀ i ∈ V, 0 < p i) (pm : mass V p = 1)
    (pc : ∀ i ∈ V, WeightedSD.col q E V p i = 1)
    (noOut : ∀ U ⊆ V, 2 ≤ U.card → U ≠ V → ¬ BRsub.OutUniform E V U)
    (coheirs : ∀ b ∈ V, ∃ k ∈ V, E k b = true ∧ ∀ j ∈ V, j ≠ b → E k j = true → E b j = true) :
    BRsub.Sat q E V := by
  have hrev : BRsub.Sat q (fun x y => E y x) V :=
    HeirRound.sat_of_heirs (E := fun x y => E y x) hq free.reverse hp pm pc noOut coheirs
  exact WeightedSD.SerialChain.sat_reverse (D := fun x y => E y x) hrev

#print axioms sat_of_coheirs

/-! ## Item 2. Heirs from a source vertex -/

/-- If `a → x` and every parent of `x` is `a` or a parent of `a`, then `x` is an heir of `a`. -/
theorem heir_of_source {E : CH.Digraph} {V : Finset ℕ} {a x : ℕ} (hx : x ∈ V)
    (par : ∀ i ∈ V, E i x = true → i = a ∨ E i a = true) (hax : E a x = true) :
    ∃ v ∈ V, E a v = true ∧ ∀ i ∈ V, i ≠ a → E i v = true → E i a = true :=
  ⟨x, hx, hax, fun i hi hia hix => (par i hi hix).resolve_left hia⟩

/-- In a positive feasible host whose proper subsets are self-dual, the in-neighbourhood of `x ≠ a`
cannot sit inside that of `a`; so if every parent of `x` is `a` or a parent of `a`, then `a → x`. -/
theorem arc_of_source {q : ℕ} {E : CH.Digraph} {V : Finset ℕ}
    (hproper : ∀ U ⊆ V, U ≠ V → SelfDual q E U)
    (w : ℕ → ℚ) (hw : ∀ v ∈ V, 0 < w v) (hr : ∀ v ∈ V, mass V w ≤ WeightedSD.row q E V w v)
    {a x : ℕ} (ha : a ∈ V) (hx : x ∈ V) (hne : x ≠ a)
    (par : ∀ i ∈ V, E i x = true → i = a ∨ E i a = true) : E a x = true := by
  by_contra hax
  apply no_incoming_domination hproper w hw hr hx ha hne
  intro v hv hvx
  rcases par v (Finset.mem_of_mem_erase hv) hvx with h | h
  · subst h; exact absurd hvx hax
  · exact h

/-- Flat form: positive unit rows of mass one, and smaller `q`-free instances self-dual. -/
theorem heir_of_source_flat {q : ℕ} {E : CH.Digraph} {V : Finset ℕ}
    (free : QFree E V q) (small : SmallerSelfDual q V.card)
    {w : ℕ → ℚ} (hw : ∀ i ∈ V, 0 < w i) (wm : mass V w = 1)
    (wr : ∀ i ∈ V, WeightedSD.row q E V w i = 1)
    {a x : ℕ} (ha : a ∈ V) (hx : x ∈ V) (hne : x ≠ a)
    (par : ∀ i ∈ V, E i x = true → i = a ∨ E i a = true) :
    ∃ v ∈ V, E a v = true ∧ ∀ i ∈ V, i ≠ a → E i v = true → E i a = true :=
  heir_of_source hx par (arc_of_source (small.induced free) w hw
    (fun v hv => by rw [wm, wr v hv]) ha hx hne par)

#print axioms arc_of_source
#print axioms heir_of_source_flat

/-! ## Item 3. Glue to `FlatLaw` -/

/-- `FlatLaw` premises, with the conclusion replaced by: every vertex has an heir. -/
def HeirLaw {q n} (X : Model q n) : Prop :=
  ∀C F B,Built X.D C F → F⊆family X → support F=X.V → Boundary X F B →
    (targets X.D X.V F B).card=1 →
    (∃w p : ℕ→ℚ,(∀i∈X.V,0<w i ∧ 0<p i) ∧ mass X.V w=1 ∧ mass X.V p=1 ∧
      (∀i∈X.V,WeightedSD.row q (graph X.D F) X.V w i=1) ∧ (∀i∈X.V,WeightedSD.col q (graph X.D F) X.V p i=1)) →
    (∀u∈X.V,∀v∈X.V,v∈ball (graph X.D F) X.V u q) →
    (∀U⊆X.V,2≤U.card → U≠X.V → ¬BRsub.OutUniform (graph X.D F) X.V U) →
    (∀U⊆X.V,2≤U.card → U≠X.V → ¬BRsub.InUniform (graph X.D F) X.V U) →
    ∀a∈X.V,∃v∈X.V,graph X.D F a v=true ∧ ∀i∈X.V,i≠a → graph X.D F i v=true → graph X.D F i a=true

/-- `FlatLaw` premises, with the conclusion replaced by: every vertex has a co-heir. -/
def CoheirLaw {q n} (X : Model q n) : Prop :=
  ∀C F B,Built X.D C F → F⊆family X → support F=X.V → Boundary X F B →
    (targets X.D X.V F B).card=1 →
    (∃w p : ℕ→ℚ,(∀i∈X.V,0<w i ∧ 0<p i) ∧ mass X.V w=1 ∧ mass X.V p=1 ∧
      (∀i∈X.V,WeightedSD.row q (graph X.D F) X.V w i=1) ∧ (∀i∈X.V,WeightedSD.col q (graph X.D F) X.V p i=1)) →
    (∀u∈X.V,∀v∈X.V,v∈ball (graph X.D F) X.V u q) →
    (∀U⊆X.V,2≤U.card → U≠X.V → ¬BRsub.OutUniform (graph X.D F) X.V U) →
    (∀U⊆X.V,2≤U.card → U≠X.V → ¬BRsub.InUniform (graph X.D F) X.V U) →
    ∀b∈X.V,∃k∈X.V,graph X.D F k b=true ∧ ∀j∈X.V,j≠b → graph X.D F k j=true → graph X.D F b j=true

/-- `FlatLaw` premises, with the conclusion: all vertices have heirs, or all have co-heirs. -/
def HeirOrCoheirLaw {q n} (X : Model q n) : Prop :=
  ∀C F B,Built X.D C F → F⊆family X → support F=X.V → Boundary X F B →
    (targets X.D X.V F B).card=1 →
    (∃w p : ℕ→ℚ,(∀i∈X.V,0<w i ∧ 0<p i) ∧ mass X.V w=1 ∧ mass X.V p=1 ∧
      (∀i∈X.V,WeightedSD.row q (graph X.D F) X.V w i=1) ∧ (∀i∈X.V,WeightedSD.col q (graph X.D F) X.V p i=1)) →
    (∀u∈X.V,∀v∈X.V,v∈ball (graph X.D F) X.V u q) →
    (∀U⊆X.V,2≤U.card → U≠X.V → ¬BRsub.OutUniform (graph X.D F) X.V U) →
    (∀U⊆X.V,2≤U.card → U≠X.V → ¬BRsub.InUniform (graph X.D F) X.V U) →
    (∀a∈X.V,∃v∈X.V,graph X.D F a v=true ∧ ∀i∈X.V,i≠a → graph X.D F i v=true → graph X.D F i a=true) ∨
    (∀b∈X.V,∃k∈X.V,graph X.D F k b=true ∧ ∀j∈X.V,j≠b → graph X.D F k j=true → graph X.D F b j=true)

theorem flatLaw_of_heirOrCoheirLaw {q n} (X : Model q n) (hq : 2 ≤ q) (h : HeirOrCoheirLaw X) :
    SharedArcPacketReturns.FlatLaw X := by
  intro C F B built sub supp bd card laws diam noOut noIn
  obtain ⟨w, p, pos, wm, pm, wr, pc⟩ := laws
  rcases h C F B built sub supp bd card ⟨w, p, pos, wm, pm, wr, pc⟩ diam noOut noIn with hh | hc
  · exact HeirRound.sat_of_heirs hq (PrivateArcEndpoints.graph_free X F)
      (fun i hi => (pos i hi).1) wm wr noIn hh
  · exact sat_of_coheirs hq (PrivateArcEndpoints.graph_free X F)
      (fun i hi => (pos i hi).2) pm pc noOut hc

theorem flatLaw_of_heirLaw {q n} (X : Model q n) (hq : 2 ≤ q) (h : HeirLaw X) :
    SharedArcPacketReturns.FlatLaw X :=
  flatLaw_of_heirOrCoheirLaw X hq
    (fun C F B built sub supp bd card laws diam noOut noIn =>
      Or.inl (h C F B built sub supp bd card laws diam noOut noIn))

theorem flatLaw_of_coheirLaw {q n} (X : Model q n) (hq : 2 ≤ q) (h : CoheirLaw X) :
    SharedArcPacketReturns.FlatLaw X :=
  flatLaw_of_heirOrCoheirLaw X hq
    (fun C F B built sub supp bd card laws diam noOut noIn =>
      Or.inr (h C F B built sub supp bd card laws diam noOut noIn))

#print axioms flatLaw_of_heirOrCoheirLaw
#print axioms flatLaw_of_heirLaw
#print axioms flatLaw_of_coheirLaw

end LeanCH.BR.Closure.HeirLaw
