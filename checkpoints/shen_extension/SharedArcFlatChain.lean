import checkpoints.shen_extension.SharedArcFlatCut

namespace LeanCH.BR.Closure.SharedArcFlatChain
open Finset Matrix BRq2 BRq3 BR45 WeightedSD FiniteCutInverse ShortestCycleWeights FirstPacketBarrier MarkedCyclePeeling
open scoped Matrix

/-- D is the full strict matrix and R is its flat parent. Going through
the inverse and then through a missing arc gives a Markov kernel on labels.
Its invariant mass at a label is the old head weight times its incoming
new-arc price. We use unnormalized stationary masses to include zero heads. -/
theorem stationary {I : Type*} [Fintype I] [DecidableEq I]
    {D R K : Matrix I I ℝ} (native : CommonInverse D K) (added : ∀i j,R i j≤D i j)
    (w p : I→ℝ) (pos : ∀i,0<w i ∧ 0<p i) (wm : ∑i,w i=1) (pm : ∑i,p i=1)
    (wr : R *ᵥ w=fun _=>1) (pc : p ᵥ* R=fun _=>1) :
    let U := D-R
    let M := K*U
    let P := fun i j => M i j*w j/w i
    let π := fun i => w i*(p ᵥ* U) i
    (∀i j,0≤P i j) ∧ (∀i,(∑j,P i j)=1) ∧ (∀j,0≤π j) ∧ (∀j,(∑i,π i*P i j)=π j) ∧
    ∀j,0<π j ↔ ∃i,R i j<D i j := by
  intro U M P π
  have u0 (i j) : 0≤U i j := sub_nonneg.mpr (added i j)
  have diff : U=excess D-excess R := by ext i j; change D i j-R i j=(D i j-1)-(R i j-1); ring
  have flat : excess R *ᵥ w=0 := by
    funext i; rw [mulVec_excess,wr,wm]; simp
  have back : p ᵥ* excess R=0 := by
    funext i; rw [vecMul_excess,pc,pm]; simp
  have left := mul_eq_one_comm.mp native.right
  have harmonic : M *ᵥ w=w := by
    change (K*U) *ᵥ w=w
    rw [←Matrix.mulVec_mulVec,diff,Matrix.sub_mulVec,flat,sub_zero,Matrix.mulVec_mulVec,left,Matrix.one_mulVec]
  have dual : (p ᵥ* U) ᵥ* M=p ᵥ* U := by
    change (p ᵥ* U) ᵥ* (K*U)=p ᵥ* U
    rw [←Matrix.vecMul_vecMul]
    congr 1
    rw [diff,Matrix.vecMul_sub,back,sub_zero,Matrix.vecMul_vecMul,native.right,Matrix.vecMul_one]
  have m0 (i j) : 0≤M i j := sum_nonneg (fun k _ => mul_nonneg (native.nonneg i k) (u0 k j))
  have prices (i j) : 0≤p i*U i j := mul_nonneg (pos i).2.le (u0 i j)
  refine ⟨fun i j => div_nonneg (mul_nonneg (m0 i j) (pos j).1.le) (pos i).1.le,?_,?_,?_,?_⟩
  · intro i
    change (∑j,M i j*w j/w i)=1
    rw [←sum_div]
    exact div_eq_one_iff_eq (pos i).1.ne' |>.mpr (congrFun harmonic i)
  · intro j
    exact mul_nonneg (pos j).1.le (sum_nonneg (fun i _ => prices i j))
  · intro j
    have cancel (i) : π i*P i j=((p ᵥ* U) i*M i j)*w j := by
      dsimp [π,P]; field_simp [(pos i).1.ne']
    rw [sum_congr rfl (fun i _ => cancel i),←sum_mul]
    change ((p ᵥ* U) ᵥ* M) j*w j=_
    rw [dual,mul_comm]
  · intro j
    change 0<w j*(∑i,p i*U i j) ↔ _
    rw [mul_pos_iff_of_pos_left (pos j).1,Finset.sum_pos_iff_of_nonneg (fun i _ => prices i j)]
    simp only [mem_univ,true_and]
    exact exists_congr (fun i => by rw [mul_pos_iff_of_pos_left (pos i).2]; exact sub_pos)

/-- The stationary law is evaluated on the actual least-support graph. -/
def StationaryAt {q n} (X : Model q n) (F : Family) (w p : ℕ→ℚ) : Prop :=
    let D := realMatrix q X.D X.V
    let R := realMatrix q (graph X.D F) X.V
    ∃K : Matrix X.V X.V ℝ,CommonInverse D K ∧
      let P := fun (i j : X.V) => (K*(D-R)) i j*(w j:ℝ)/(w i:ℝ)
      let π := fun (i : X.V) => (w i:ℝ)*((fun v : X.V => (p v:ℝ)) ᵥ* (D-R)) i
      (∀i j,0≤P i j) ∧ (∀i,(∑j,P i j)=1) ∧ (∀j,0≤π j) ∧ (∀j,(∑i,π i*P i j)=π j) ∧
      ∀j,0<π j ↔ ∃i,R i j<D i j

theorem on_flat {q n} (X : Model q n) (small : SmallerSmallRow q X.V.card)
    (F : Family) {w p : ℕ→ℚ} (pos : ∀i∈X.V,0<w i ∧ 0<p i)
    (wm : mass X.V w=1) (pm : mass X.V p=1)
    (wr : ∀i∈X.V,WeightedSD.row q (graph X.D F) X.V w i=1)
    (pc : ∀i∈X.V,WeightedSD.col q (graph X.D F) X.V p i=1) :
    StationaryAt X F w p := by
  unfold StationaryAt
  intro D R
  obtain ⟨K,h⟩ := strict_inverse_of_proper_smallRow (small.induced X.free)
    (fun i => (X.weights i : ℚ)) (fun _ _ => Nat.cast_nonneg _) X.strict
  refine ⟨K,h,stationary h (realMatrix_mono_graph ?_) _ _ ?_
    (real_mass_of_rational_probability w wm) (real_mass_of_rational_probability p pm)
    (by simpa using funext (realMatrix_rational_rows w 1 wr)) (by simpa using funext (realMatrix_rational_columns p 1 pc))⟩
  · intro i _ j _ ed
    obtain ⟨A,hit⟩ := active.mp ed
    exact (mem_col.mp hit).2.2.2
  · intro i
    exact ⟨by exact_mod_cast (pos i i.property).1,by exact_mod_cast (pos i i.property).2⟩


/-- A competitor whose old-tensor score exceeds this budget strictly
improves the terminal value. Both endpoints of the candidate may change. -/
def Budget {q n} (X : Model q n) (F : Family) (c : ℚ) (w p : ℕ→ℚ) : Prop :=
  ∀f : SharedArcFlatCut.Missing X F,
    let a := f.val.1
    let b := f.val.2
    let L := (realMatrix q (graph X.D F) X.V)⁻¹
    ((c:ℝ)-1)*(1+(q:ℝ)*L b a)≤(q:ℝ)*c*(p a:ℝ)*(w b:ℝ)

private theorem budget_of_value {c d z t : ℝ} (high : 1<c) (le : c≤d) (pos : 0≤t)
    (eq : (d-1)*z=t*d) : (c-1)*z≤t*c := by
  have id : (d-1)*(t*c-(c-1)*z)=t*(d-c) := by linear_combination -(c-1)*eq
  have fin : 0≤(d-1)*(t*c-(c-1)*z) := id ▸ mul_nonneg pos (sub_nonneg.mpr le)
  exact sub_nonneg.mp (nonneg_of_mul_nonneg_right fin (sub_pos.mpr (high.trans_le le)))

theorem at_terminal {q n} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    {F B} (step : SharedArcBarrier.Boundary X F B)
    (least : ∀M,SharedArcBarrier.Boundary X F M → (SharedArcBarrier.targets X.D X.V F B).card≤(SharedArcBarrier.targets X.D X.V F M).card)
    {H : Matrix X.V X.V ℝ} (inv : CommonInverse (realMatrix q (graph X.D (insert B F)) X.V) H)
    (charge : ∀a b : X.V,(a:ℕ)∈B → (b:ℕ)∈B → X.D a b=true → graph X.D F a b=false → 1≤(q:ℝ)*H b a)
    {c : ℚ} (high : 1<c) (compare : ∀M,SharedArcBarrier.Boundary X F M →
      (SharedArcBarrier.targets X.D X.V F M).card=(SharedArcBarrier.targets X.D X.V F B).card →
      ∃x : ℕ→ℚ,∃d : ℚ,c≤d ∧ mass X.V x=1 ∧ ∀v∈X.V,WeightedSD.row q (graph X.D (insert M F)) X.V x v=d)
    (a b : X.V) (ab : (a:ℕ)∈B) (bb : (b:ℕ)∈B) (ed : X.D a b=true) (off : graph X.D F a b=false)
    (threshold : (q:ℝ)*H b a=1) :
    ∃w p : ℕ→ℚ,(∀i∈X.V,0<w i ∧ 0<p i) ∧ mass X.V w=1 ∧ mass X.V p=1 ∧
      (∀i∈X.V,WeightedSD.row q (graph X.D F) X.V w i=1) ∧ (∀i∈X.V,WeightedSD.col q (graph X.D F) X.V p i=1) ∧
      SharedArcFlatCut.Conditions X F w p ∧ StationaryAt X F w p ∧ Budget X F c w p := by
  obtain ⟨single,_,⟨w,p,wp,wm,pm,wr,pc⟩,_⟩ := SharedArcPacketReturns.exact_parent X hq small step least inv
    charge a b ab bb ed off threshold
  refine ⟨w,p,wp,wm,pm,wr,pc,SharedArcFlatCut.global X hq small F wp wm wr pc,
    on_flat X small F wp wm pm wr pc,?_⟩
  intro f
  obtain ⟨_,_,_,_,d,le,_,_,eq⟩ := SharedArcFlatCut.competitors X hq small F c (fun M bm size => compare M bm
    (by rw [single,card_singleton]; exact size)) wp wm wr pc f
  have hp : (0:ℝ)≤p f.val.1 := by exact_mod_cast (wp _ f.val.1.property).2.le
  have hw : (0:ℝ)≤w f.val.2 := by exact_mod_cast (wp _ f.val.2.property).1.le
  have h := budget_of_value (c:=(c:ℝ)) (d:=(d:ℝ)) (t:=(q:ℝ)*(p f.val.1:ℝ)*(w f.val.2:ℝ))
    (by exact_mod_cast high) (by exact_mod_cast le) (mul_nonneg (mul_nonneg (Nat.cast_nonneg q) hp) hw)
    (by convert eq using 1; ring)
  dsimp only
  convert h using 1; ring

#print axioms at_terminal

#print axioms on_flat
end LeanCH.BR.Closure.SharedArcFlatChain
