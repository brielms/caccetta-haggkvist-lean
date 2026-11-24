import checkpoints.shen_extension.DisjointCutCapacity

namespace LeanCH.BR.Closure.OpposedExteriorCapacity
open Finset BRq2 BRq3 BR45 WeightedSD ShenCycleSuccessor ShortestCycleWeights FullCycleTransfer

/-- Retain the mass before conditioning. It is precisely this mass that can
be charged to the original column equalizer. -/
structure Exterior (q : ℕ) (E : CH.Digraph) (V A M : Finset ℕ) (x : ℕ→ℝ) (c : ℝ) (u : ℕ→ℝ) : Prop where
  nonneg : ∀i,0≤u i
  supported : ∀i,i∉V\A → u i=0
  substantial : c-realMass V x ≤ c*realMass (V\A) u
  bill : ∀P : Pairing E A M,
    c-realMass V x ≤ ∑b∈V\A,u b*(c-realRow q E (V\(A\M)) (fun v => x v+P.deposit x v) b)

private theorem extract {q E V A M} (a : Cycle E V q A) (m : Cycle E V q M)
    (small : SmallRow q E (V\(A\M))) {x : ℕ→ℝ} (pos : ∀i∈V,0≤x i)
    {c : ℝ} (rows : ∀i∈V,c≤realRow q E V x i) :
    ∃z, RealDual q E (V\(A\M)) 1 z ∧ Exterior q E V A M x c (maskReal (V\A) z) ∧
    ∀b,maskReal (V\A) z b≤maskReal (V\(A\M)) z b := by
  obtain ⟨z,hz,bill⟩ := PairingPressure.uniform a m small pos rows
  let T := V\A
  let U := V\(A\M)
  have sub : T⊆U := fun _ hi => mem_sdiff.mpr ⟨(mem_sdiff.mp hi).1,fun del =>
    (mem_sdiff.mp hi).2 (mem_sdiff.mp del).1⟩
  let u := maskReal T z
  have onT (b) (bt : b∈T) : u b=z b := by simp [u,maskReal,bt]
  have non (i) : 0≤u i := by
    by_cases h : i∈T
    · rw [onT i h]; exact hz.nonneg i (sub h)
    · simp [u,maskReal,h]
  have massT : realMass T u=realMass T z := sum_congr rfl (fun b hb => onT b hb)
  obtain ⟨P⟩ := exists_pairing a m
  let child := fun i => x i+P.deposit x i
  have childNon (i) (iv : i∈V) : 0≤child i := by
    have dep : 0≤P.deposit x i := by
      apply sum_nonneg
      intro y hy
      split_ifs <;> first | exact pos y (a.sub (mem_sdiff.mp hy).1) | exact le_rfl
    exact add_nonneg (pos i iv) dep
  have rowNon (i) (it : i∈T) : 0≤realRow q E U child i := by
    apply add_nonneg (childNon i (mem_sdiff.mp it).1)
    apply mul_nonneg (Nat.cast_nonneg _)
    apply sum_nonneg
    intro j ju
    split_ifs <;> first | exact childNon j (mem_sdiff.mp ju).1 | exact le_rfl
  have enough := bill P
  have upper : (∑b∈T,z b*(c-realRow q E U child b))≤c*realMass T z := by
    rw [mul_comm c,realMass,sum_mul]
    exact sum_le_sum fun b hb => mul_le_mul_of_nonneg_left (sub_le_self _ (rowNon b hb)) (hz.nonneg b (sub hb))
  refine ⟨z,hz,⟨non,fun i hi => by simp [maskReal,hi],?_,?_⟩,?_⟩
  · change c-realMass V x≤c*realMass T u
    rw [massT]; exact enough.trans upper
  · intro Q
    apply (bill Q).trans_eq
    exact sum_congr rfl fun b hb => by rw [show maskReal (V\A) z b = z b from onT b hb]
  · intro b
    by_cases bt : b∈T
    · change maskReal T z b≤maskReal U z b
      simp [maskReal,bt,sub bt]
    · change maskReal T z b≤maskReal U z b
      by_cases bu : b∈U
      · simpa [maskReal,bt,bu] using hz.nonneg b bu
      · simp [maskReal,bt,bu]

/-- Opposite trials have disjoint omissions. Both full families of pairing
tests can be supplied subject to one common pointwise capacity constraint. -/
theorem paired {q n} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    {F A M x p c} (sub : F⊆FirstPacketBarrier.family X) (af : A∈F) (mf : M∈F) (ne : A≠M)
    (high : 1<c) (pos : ∀z∈X.V,0<x z) (xm : mass X.V x=1) (pm : mass X.V p=1)
    (rows : ∀z∈X.V,WeightedSD.row q (FirstPacketBarrier.graph X.D F) X.V x z=c)
    (cols : ∀z∈X.V,WeightedSD.col q (FirstPacketBarrier.graph X.D F) X.V p z=c) :
    let E := FirstPacketBarrier.graph X.D F
    let w := fun z => (x z : ℝ)
    ∃u v, Exterior q E X.V A M w c u ∧ Exterior q E X.V M A w c v ∧
      ∀b∈X.V,((c:ℝ)-1)*(u b+v b)≤((q:ℝ)-1)*(p b : ℝ) := by
  classical
  intro E w
  have free := PrivateArcEndpoints.graph_free X F
  have actual {C} (cf : C∈F) : Cycle E X.V q C := FirstPacketBarrier.retain_cycle
    (show Cycle X.D X.V q C from (mem_filter.mp (sub cf)).2) cf
  have cut {C T} (cf : C∈F) (tf : T∈F) (diff : C≠T) : SmallRow q E (X.V\(C\T)) := by
    apply small.induced free _ sdiff_subset
    intro all
    apply diff
    apply eq_of_subset_of_card_le _ (by rw [(actual cf).size,(actual tf).size])
    intro z zc
    obtain ⟨_,keep⟩ := mem_sdiff.mp (show z∈X.V\(C\T) by rw [all]; exact (actual cf).sub zc)
    exact by_contra fun no => keep (mem_sdiff.mpr ⟨zc,no⟩)
  have xn (i) (hi : i∈X.V) : 0≤w i := by change (0:ℝ)≤(x i : ℝ); exact_mod_cast (pos i hi).le
  have rr (i) (hi : i∈X.V) : (c:ℝ)≤realRow q E X.V w i := by rw [realRow_rat,rows i hi]
  obtain ⟨m,mu,first,mle⟩ := extract (actual af) (actual mf) (cut af mf ne) xn rr
  obtain ⟨k,ku,second,kle⟩ := extract (actual mf) (actual af) (cut mf af ne.symm) xn rr
  refine ⟨_,_,first,second,fun b bv => ?_⟩
  have cover : X.V⊆(X.V\(A\M))∪(X.V\(M\A)) := by
    intro i iv
    by_cases ia : i∈A
    · exact mem_union_right _ (mem_sdiff.mpr ⟨iv,fun gone => (mem_sdiff.mp gone).2 ia⟩)
    · exact mem_union_left _ (mem_sdiff.mpr ⟨iv,fun gone => ia (mem_sdiff.mp gone).1⟩)
  have raw := DisjointCutCapacity.two_cuts hq free small high pos xm pm rows cols sdiff_subset sdiff_subset cover mu ku b bv
  exact (mul_le_mul_of_nonneg_left (add_le_add (mle b) (kle b)) (sub_nonneg.mpr (by exact_mod_cast high.le))).trans raw

#print axioms paired
end LeanCH.BR.Closure.OpposedExteriorCapacity
