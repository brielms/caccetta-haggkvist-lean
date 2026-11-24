import checkpoints.shen_extension.FeederJoinedComparisons
import checkpoints.shen_extension.GlobalFamilyDual

namespace LeanCH.BR.Closure.FeederPrivateHeadDescent
open Finset BRq2 BRq3 BR45 WeightedSD ShenCycleSuccessor ShortestCycleWeights ShenPrimeTransition

def FirstDifference (D : CH.Digraph) (V : Finset ℕ) (w : ℕ → ℚ) (a b : ℕ) : Prop :=
  w a ≠ w b ∨ ∃ u v i j, Joined D V a b u v ∧ w u = w v ∧
    i ∈ exclusive D V u v ∧ j ∈ exclusive D V v u ∧ w i ≠ w j

/-- An inequality found through joins has a physical first explanation. -/
theorem first_difference {D V a b x y} {w : ℕ → ℚ}
    (path : Joined D V a b x y) (diff : w x ≠ w y) : FirstDifference D V w a b := by
  classical
  induction path with
  | seed => exact Or.inl diff
  | refl => exact (diff rfl).elim
  | symm _ ih => exact ih diff.symm
  | @trans x y z _ _ ih₁ ih₂ =>
    by_cases left : w x = w y
    · exact ih₂ (fun right => diff (left.trans right))
    · exact ih₁ left
  | @heads u v i j parent left right ih =>
    by_cases eq : w u = w v
    · exact Or.inr ⟨u,v,i,j,parent,eq,left,right,diff⟩
    · exact ih eq

/-- The two original seed arcs can derive the same unequal pair, before
choosing any prime or selecting a terminal price discrepancy. -/
def SharedSignature {q n} (X : Model q n) (w π : ℕ → ℚ) (c : ℚ)
    (a b u v : ℕ) : Prop :=
  ∃ i ∈ X.V, ∃ j ∈ X.V, Joined X.D X.V a b i j ∧ Joined X.D X.V u v i j ∧
    w i ≠ w j ∧ FirstDifference X.D X.V w a b ∧ FirstDifference X.D X.V w u v ∧
    ∀ ell, ell.Prime → ell ∣ q → SignatureExit X w π c i j ell

def UniformOn (D : CH.Digraph) (V : Finset ℕ) (w : ℕ → ℚ) : Prop :=
  ∀ i ∈ V, ∀ j ∈ V, w i = w j ∧ (outN D V i).card = (outN D V j).card

theorem two_arc_fork {q n a b u v} (X : Model q n) (hq : 2 ≤ q)
    (small : SmallerSmallRow q X.V.card) {w π c}
    (posw : ∀ i ∈ X.V, 0 < w i) (flat : ∀ i ∈ X.V, WeightedSD.row q X.D X.V w i = c)
    (pos : ∀ i ∈ X.V, 0 < π i) (high : mass X.V π < c)
    (cols : ∀ i ∈ X.V, WeightedSD.col q X.D X.V π i = c)
    (av : a ∈ X.V) (bv : b ∈ X.V) (uv : u ∈ X.V) (vv : v ∈ X.V)
    (first : X.D a b = true) (second : X.D u v = true) :
    SharedSignature X w π c a b u v ∨ UniformOn X.D X.V w := by
  have both (x y) (xv : x ∈ X.V) (yv : y ∈ X.V) (arc : X.D x y = true) :
      ∀ t ∈ X.V, Joined X.D X.V x y x t :=
    joined_arc_spans X hq small pos high cols xv yv (.refl _) .seed arc
  rcases joined_or_regular X hq small posw flat pos high cols (both a b av bv first) with win | reg
  · obtain ⟨i,iv,j,jv,p,neq,finish⟩ := win
    have other := (both u v uv vv second i iv).symm.trans (both u v uv vv second j jv)
    exact Or.inl ⟨i,iv,j,jv,p,other,neq,first_difference p neq,first_difference other neq,finish⟩
  · exact Or.inr reg

/-- Reverse only the physical arcs. Clearing rational prices changes the
integer budget used to present a model and keeps all vertices and arcs labelled. -/
theorem reverse_on_labels {q n} (X : Model q n) (hq : 2 ≤ q)
    (small : SmallerSmallRow q X.V.card) {π c}
    (pos : ∀ i ∈ X.V, 0 < π i) (high : mass X.V π < c)
    (cols : ∀ i ∈ X.V, WeightedSD.col q X.D X.V π i = c) :
    ∃ m, ∃ Y : Model q m, Y.D = (fun u v => X.D v u) ∧ Y.V = X.V := by
  let E : CH.Digraph := fun u v => X.D v u
  have strict (i) (iv : i ∈ X.V) : mass X.V π < WeightedSD.row q E X.V π i := by
    change mass X.V π < WeightedSD.col q X.D X.V π i
    rw [cols i iv]; exact high
  obtain ⟨w,posw,sw⟩ := GlobalFamilyDual.integral_strict pos strict
  have mincard {F U g} (live : U.Nonempty) (free : QFree F U q) (paid : Strict q F U g) :
      X.V.card ≤ U.card := by
    by_contra! less
    exact (small F U less free).no_strict live (fun j => (g j : ℚ)) (fun _ _ => Nat.cast_nonneg _) paid
  have prime : Prime E X.V := fun M sub two proper h => X.prime M sub two proper ⟨h.2,h.1⟩
  have sep : ShenParentIntersection.Separated E X.V X.V := by
    intro t tv r rv ne
    obtain ⟨j,hj⟩ := has_exclusive X hq small pos high cols tv rv ne.symm
    obtain ⟨yes,no⟩ := mem_sdiff.mp hj
    obtain ⟨jv,tj⟩ := mem_outN.mp yes
    exact ⟨j,jv,tj,Bool.eq_false_iff.mpr (fun hit => no (mem_outN.mpr ⟨jv,hit⟩))⟩
  exact ⟨_,⟨E,X.V,X.live,X.free.reverse,SerialChain.sat_reverse X.sat,w,posw,le_rfl,sw,
    fun _ _ _ live free _ _ paid => mincard live free paid,prime,sep⟩,rfl,rfl⟩

/-- At the actual receiver, either its two seed arcs share a signed comparison
in one orientation, or every physical vertex has uniform prices and both degrees
are constant. In the latter case the unit allocation is already strict. -/
theorem at_receiver {q n p t z} (X : Model q n) (hq : 2 ≤ q) (small : SmallerSmallRow q X.V.card)
    {w π c} (posw : ∀ i ∈ X.V, 0 < w i) (highw : mass X.V w < c)
    (flat : ∀ i ∈ X.V, WeightedSD.row q X.D X.V w i = c)
    (pos : ∀ i ∈ X.V, 0 < π i) (high : mass X.V π < c)
    (cols : ∀ i ∈ X.V, WeightedSD.col q X.D X.V π i = c)
    (pv : p ∈ X.V) (tv : t ∈ X.V) (zv : z ∈ X.V) (pz : X.D p z = true) (tz : X.D t z = true) :
    ∃ m, ∃ Y : Model q m, Y.D = (fun u v => X.D v u) ∧ Y.V = X.V ∧
      (SharedSignature X w π c p z t z ∨ SharedSignature Y π w c z p z t ∨
        (UniformOn X.D X.V w ∧ UniformOn (fun u v => X.D v u) X.V π ∧
         ∀ i ∈ X.V, X.V.card ≤ q*(outN X.D X.V i).card)) := by
  obtain ⟨m,Y,graph,carrier⟩ := reverse_on_labels X hq small pos high cols
  refine ⟨m,Y,graph,carrier,?_⟩
  rcases two_arc_fork X hq small posw flat pos high cols pv zv tv zv pz tz with win | left
  · exact Or.inl win
  have flipRow (i) (iv : i ∈ Y.V) : WeightedSD.row q Y.D Y.V π i = c := by
    rw [graph,carrier]; exact cols i (carrier ▸ iv)
  have flipCol (i) (iv : i ∈ Y.V) : WeightedSD.col q Y.D Y.V w i = c := by
    rw [graph,carrier]; exact flat i (carrier ▸ iv)
  rcases two_arc_fork Y hq (carrier ▸ small) (carrier ▸ pos) flipRow (carrier ▸ posw)
    (carrier ▸ highw) flipCol (carrier ▸ zv) (carrier ▸ pv) (carrier ▸ zv) (carrier ▸ tv)
    (graph ▸ pz) (graph ▸ tz) with win | right
  · exact Or.inr (Or.inl win)
  rw [graph,carrier] at right
  refine Or.inr (Or.inr ⟨left,right,?_⟩)
  intro i iv
  have fixed (T : Finset ℕ) (sub : T ⊆ X.V) : mass T w = (T.card : ℚ)*w i := by
    unfold mass
    calc
      _ = ∑ _ ∈ T, w i := sum_congr rfl (fun j hj => (left j (sub hj) i iv).1)
      _ = _ := by simp
  have strict := highw.trans_eq (flat i iv).symm
  rw [WeightedSD.row,outW_eq_mass,fixed _ (fun _ h => (mem_outN.mp h).1),fixed _ Subset.rfl] at strict
  have lift : (X.V.card : ℚ) < 1+(q:ℚ)*(outN X.D X.V i).card := by
    apply lt_of_mul_lt_mul_right (a := w i)
    · convert strict using 1
      ring
    · exact (posw i iv).le
  have natural : X.V.card < 1+q*(outN X.D X.V i).card := by exact_mod_cast lift
  omega

#print axioms first_difference
#print axioms two_arc_fork
#print axioms reverse_on_labels
#print axioms at_receiver
end LeanCH.BR.Closure.FeederPrivateHeadDescent
