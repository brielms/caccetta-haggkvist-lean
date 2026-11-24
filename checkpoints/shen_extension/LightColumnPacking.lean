import checkpoints.shen_extension.ComparableColumnCut

namespace LeanCH.BR.Closure.LightColumnPacking
open Finset BRq2 BRq3 BR45 ShenCycleSuccessor ShortestCycleWeights RootedSplice MandatoryTwoStep

def Adj (D : CH.Digraph) (x y : ℕ) := D x y=true ∨ D y x=true

noncomputable def closedN (D : CH.Digraph) (V : Finset ℕ) (x : ℕ) :=
  insert x (outN D V x ∪ inN D V x)

private theorem heavy_solo {q n} (X : Model q n) {h p x} (pv : p∈X.V)
    (minimum : ∀z∈X.V,X.weights h≤X.weights z) (size : q*(q-1)+1≤X.V.card)
    (one : outN X.D X.V p={x}) : (q-1)*X.weights h<X.weights x := by
  have high := PunctureWeightCoverage.flow_floor X pv minimum size
  simpa only [one,sum_singleton] using high

private theorem single_arc {q n} (X : Model q n) (hq : 2≤q) {x y}
    (xv : x∈X.V) (yv : y∈X.V) (ne : x≠y) (xy : X.D x y=true)
    (comp : Forces X.D X.V q x y ∨ Forces X.D X.V q y x) : outN X.D X.V x={y} := by
  ext z
  constructor
  · intro zx
    obtain ⟨zv,xz⟩ := mem_outN.mp zx
    apply mem_singleton.mpr
    rcases comp with f|f
    · exact sole_head X hq (mem_erase.mpr ⟨ne,xv⟩) zv xy xz (forces_iff.mp f)
    · by_contra zy
      obtain ⟨p,pv,py,pz⟩ := X.separated y yv z zv zy
      obtain rfl := sole_parent X hq (mem_erase.mpr ⟨ne.symm,yv⟩) pv xy py (forces_iff.mp f)
      rw [pz] at xz
      contradiction
  · intro eq
    exact mem_singleton.mp eq ▸ mem_outN.mpr ⟨yv,xy⟩

/-- Any comparable labels below the common global weight threshold have
pairwise disjoint closed neighbourhoods in the underlying undirected graph.
The comparison can run either way, and neither of the two labels has to
be the root providing the weight floor. -/
theorem disjoint_neighbourhoods {q n} (X : Model q n) (hq : 2≤q) {h x y}
    (xv : x∈X.V) (yv : y∈X.V) (ne : x≠y)
    (minimum : ∀z∈X.V,X.weights h≤X.weights z) (size : q*(q-1)+1≤X.V.card)
    (lightx : X.weights x≤(q-1)*X.weights h) (lighty : X.weights y≤(q-1)*X.weights h)
    (comp : Forces X.D X.V q x y ∨ Forces X.D X.V q y x) :
    Disjoint (closedN X.D X.V x) (closedN X.D X.V y) := by
  classical
  have separate : ¬Adj X.D x y := by
    rintro (xy|yx)
    · exact lighty.not_gt (heavy_solo X xv minimum size (single_arc X hq xv yv ne xy comp))
    · exact lightx.not_gt (heavy_solo X yv minimum size (single_arc X hq yv xv ne.symm yx comp.symm))
  have via {u z v} (uv : u∈X.V) (zv : z∈X.V) (vv : v∈X.V)
      (uz : X.D u z=true) (zv' : X.D z v=true) (light : X.weights v≤(q-1)*X.weights h)
      (order : Forces X.D X.V q u v ∨ Forces X.D X.V q v u) : False := by
    rcases order with inc|inc
    · exact light.not_gt (heavy_solo X zv minimum size (unique_corridor X hq uv zv vv uz zv' inc).2)
    · exact light.not_gt (heavy_solo X zv minimum size (unique_incoming X hq uv zv vv uz zv' inc).2)
  have unpack {u z} (hz : z∈closedN X.D X.V u) : z=u ∨ z∈X.V ∧ Adj X.D u z := by
    rcases mem_insert.mp hz with eq|hit
    · exact Or.inl eq
    rcases mem_union.mp hit with a|a
    · exact Or.inr ⟨(mem_outN.mp a).1,Or.inl (mem_outN.mp a).2⟩
    · exact Or.inr ⟨(mem_inN.mp a).1,Or.inr (mem_inN.mp a).2⟩
  apply disjoint_left.mpr
  intro z zx zy
  rcases unpack zx with rfl | ⟨zv,xz|zx⟩
  · rcases unpack zy with rfl|⟨_,yx|xy⟩
    · exact ne rfl
    · exact separate (Or.inr yx)
    · exact separate (Or.inl xy)
  · rcases unpack zy with rfl|⟨_,yz|zy⟩
    · exact separate (Or.inl xz)
    · rcases comp with inc|inc
      · exact ne (ComparableColumnCut.distinct_parents X hq zv xv xz yz inc)
      · exact ne.symm (ComparableColumnCut.distinct_parents X hq zv yv yz xz inc)
    · exact via xv zv yv xz zy lighty comp
  · rcases unpack zy with rfl|⟨_,yz|zy⟩
    · exact separate (Or.inr zx)
    · exact via yv zv xv yz zx lightx comp.symm
    · rcases comp with inc|inc
      · exact ne (ComparableColumnCut.distinct_heads X hq zv xv zx zy inc)
      · exact ne.symm (ComparableColumnCut.distinct_heads X hq zv yv zy zx inc)

/-- Apply the disjoint packing to the actual receiver of a failed puncture. -/
theorem uncovered_far {q n} (X : Model q n) (hq : 2≤q) {h t}
    (hv : h∈X.V) (tw : t∈X.V.erase h) (minimum : ∀z∈X.V,X.weights h≤X.weights z)
    (size : q*(q-1)+1≤X.V.card) (absent : ¬Covered X.D X.V q h t) :
    Disjoint (closedN X.D X.V h) (closedN X.D X.V t) := by
  have cap := ((PunctureReceiverFrontier.classify X hq hv tw minimum size).resolve_left absent).1
  exact disjoint_neighbourhoods X hq hv (mem_of_mem_erase tw) (mem_erase.mp tw).1.symm minimum size
    (Nat.le_mul_of_pos_left _ (by omega)) cap.le (Or.inr (forces_iff.mpr absent))

/-- The disjoint closed neighbourhoods pay all the strict rows on the chain.
The diagonal term gives a strict mass inequality, including at the endpoints. -/
theorem chain_mass {q n} (X : Model q n) (hq : 2≤q) {h K}
    (minimum : ∀z∈X.V,X.weights h≤X.weights z) (size : q*(q-1)+1≤X.V.card)
    (sub : K⊆X.V) (live : K.Nonempty) (light : ∀x∈K,X.weights x≤(q-1)*X.weights h)
    (chain : ∀x∈K,∀y∈K,Forces X.D X.V q x y ∨ Forces X.D X.V q y x) :
    K.card*(∑z∈X.V,X.weights z)+(q-1)*(∑x∈K,X.weights x)<q*(∑z∈X.V,X.weights z) := by
  classical
  let B (x : ℕ) := insert x (outN X.D X.V x)
  have inc (x) : B x⊆closedN X.D X.V x := insert_subset_insert x (subset_union_left (s₂:=inN X.D X.V x))
  have pair : (K : Set ℕ).PairwiseDisjoint B := by
    intro x xk y yk ne
    exact (disjoint_neighbourhoods X hq (sub xk) (sub yk) ne minimum size (light x xk) (light y yk)
      (chain x xk y yk)).mono (inc x) (inc y)
  have ub : K.biUnion B⊆X.V := by
    intro z zs
    obtain ⟨x,xk,zb⟩ := mem_biUnion.mp zs
    rcases mem_insert.mp zb with rfl|zh
    · exact sub xk
    · exact (mem_outN.mp zh).1
  have total := sum_le_sum_of_subset_of_nonneg (f:=X.weights) ub (by intros; omega)
  rw [sum_biUnion pair] at total
  let mass := ∑z∈X.V,X.weights z
  have row (x) (xk : x∈K) : mass+(q-1)*X.weights x < q*(∑z∈B x,X.weights z) := by
    have orig := ShenPrimeTransition.nat_strict.mp X.strict x (sub xk)
    have hx : x∉outN X.D X.V x := fun e => loopfree X.free (by omega) (sub xk) (mem_outN.mp e).2
    have eq : (q-1)*X.weights x+X.weights x=q*X.weights x := by
      rw [←Nat.succ_mul]; congr 1; omega
    have form : ShenPrimeTransition.score q X.D X.V X.weights x =
        X.weights x+q*(∑z∈outN X.D X.V x,X.weights z) := by simp only [ShenPrimeTransition.score,outN,sum_filter]
    rw [form] at orig
    change mass<_ at orig
    simp only [B,sum_insert hx,Nat.mul_add]
    omega
  have allrows := sum_lt_sum_of_nonempty live row
  simp only [sum_add_distrib,sum_const,nsmul_eq_mul,←mul_sum] at allrows
  exact allrows.trans_le (Nat.mul_le_mul_left q total)

#print axioms chain_mass
#print axioms disjoint_neighbourhoods
#print axioms uncovered_far
end LeanCH.BR.Closure.LightColumnPacking
