import checkpoints.shen_extension.SharedArcComponentExchange
import LeanCH.BR.BRWeightedNativePressureRepair

namespace LeanCH.BR.Closure.SharedArcFlatResponse
open Finset Matrix BRq2 BRq3 BR45 WeightedSD FiniteCutInverse
open ShenCycleSuccessor ShortestCycleWeights FirstPacketBarrier MarkedCyclePeeling SharedArcExpansion SharedArcBarrier
open SharedArcComponentExchange
open scoped Matrix

theorem matrix_unit {q : ℕ} (hq : 2≤q) (E : CH.Digraph) (V : Finset ℕ) :
    IsUnit (realMatrix q E V).det := by
  apply isUnit_iff_ne_zero.mpr
  let A := WeightedArithmetic.rationalMatrix q (adjacencyMatrix E V)
  change ((Rat.castHom ℝ).mapMatrix A).det ≠ 0
  rw [←RingHom.map_det]
  change (A.det : ℝ) ≠ 0
  exact_mod_cast WeightedArithmetic.rational_det_ne_zero hq _

section Linear
variable {I : Type*} [Fintype I] [DecidableEq I]
private def spike (k : I) (c : ℝ) : I → ℝ := fun v => if k=v then c else 0

private theorem row_spike (L : Matrix I I ℝ) (k : I) (c : ℝ) (v : I) :
    (L *ᵥ spike k c) v = L v k*c := by
  simp [Matrix.mulVec,dotProduct,spike,mul_ite]

private theorem col_sum (R L : Matrix I I ℝ) (right : R*L=1) (p : I→ℝ)
    (col : p ᵥ* R = fun _=>1) (k : I) : (∑v,L v k)=p k := by
  have eq := congrArg (fun z => z ᵥ* L) col
  rw [Matrix.vecMul_vecMul,right,Matrix.vecMul_one] at eq
  simpa [Matrix.vecMul,dotProduct] using (congrFun eq k).symm

private theorem changeRow {R S : Matrix I I ℝ} {a b : I} {t : ℝ}
  (edit : ∀i j,S i j-R i j=if i=a ∧ j=b then t else 0) (x : I→ℝ) (i : I) : (S *ᵥ x) i-(R *ᵥ x) i=spike a (t*x b) i := by
  change (∑j,S i j*x j)-(∑j,R i j*x j)=_
  rw [←sum_sub_distrib]
  simp_rw [←sub_mul,edit]
  by_cases h : i=a
  · subst i; simp [spike,ite_mul]
  · simp [spike,h,Ne.symm h]

/-- The same old inverse determines the normalized value of every one-entry extension. -/
theorem response {R S L : Matrix I I ℝ} (right : R*L=1) {a b : I} {t c : ℝ}
    (edit : ∀i j,S i j-R i j=if i=a ∧ j=b then t else 0)
    {w p x : I→ℝ} (old : R *ᵥ w=fun _=>1) (dual : p ᵥ* R=fun _=>1)
    (wm : ∑i,w i=1) (xm : ∑i,x i=1) (rows : S *ᵥ x=fun _=>c) :
    (c-1)*(1+t*L b a)=t*c*p a*w b := by
  have eq : R *ᵥ x = R *ᵥ (fun v => c*w v) - spike a (t*x b) := by
    funext i
    have scale : (R *ᵥ (fun v => c*w v)) i=c := by
      change (∑v,R i v*(c*w v))=_
      simp_rw [mul_left_comm (R i _) c,←mul_sum]
      change c*(R *ᵥ w) i=c
      rw [old,mul_one]
    have diff := changeRow edit x i
    rw [rows] at diff
    simpa only [Pi.sub_apply,scale] using (eq_sub_of_add_eq (show (R *ᵥ x) i+spike a (t*x b) i=c by linarith))
  have left := mul_eq_one_comm.mp right
  have sol := congrArg (fun z => L *ᵥ z) eq
  simp only [Matrix.mulVec_sub,Matrix.mulVec_mulVec,left,Matrix.one_mulVec] at sol
  have point (i : I) : x i=c*w i-L i a*(t*x b) := by
    simpa only [Pi.sub_apply,row_spike] using congrFun sol i
  have sum := Finset.sum_congr (rfl : (univ : Finset I) = univ) (fun i _ => point i)
  rw [xm,sum_sub_distrib,←mul_sum,wm,mul_one,←sum_mul,col_sum R L right p dual] at sum
  linear_combination -(1+t*L b a)*sum + t*p a*(point b)

/-- The tensor column solves the centered system for any one-entry edit,
including edits whose centered inverse has negative entries. -/
theorem rectangle_column {R S L : Matrix I I ℝ} (right : R*L=1)
    {a b : I} {t : ℝ} (edit : ∀i j,S i j-R i j=if i=a ∧ j=b then t else 0)
    {w p : I→ℝ} (old : R *ᵥ w=fun _=>1) (dual : p ᵥ* R=fun _=>1) (wm : ∑i,w i=1) (k : I) :
    excess S *ᵥ (fun v => t*p a*w b*L v k - t*p k*w b*L v a
      + w v*(p k + t*p k*L b a - t*p a*L b k)) = fun i => if k=i then t*p a*w b else 0 := by
  let A := t*p a*w b
  let B := t*p k*w b
  let C := p k+t*p k*L b a-t*p a*L b k
  let z : I→ℝ := fun i => A*L i k-B*L i a+C*w i
  have mass : (∑i,z i)=C := by
    simp only [z,sum_add_distrib,sum_sub_distrib,←mul_sum,col_sum R L right p dual,wm]
    dsimp [A,B]; ring
  have zb : t*z b=B := by dsimp [z,A,B,C]; ring
  have send (i : I) : (R *ᵥ z) i=A*(1:Matrix I I ℝ) i k-B*(1:Matrix I I ℝ) i a+C := by
    change (∑u,R i u*(A*L u k-B*L u a+C*w u))=_
    simp_rw [mul_add,mul_sub,mul_left_comm (R i _) A,mul_left_comm (R i _) B,mul_left_comm (R i _) C]
    rw [sum_add_distrib,sum_sub_distrib,←mul_sum,←mul_sum,←mul_sum]
    change A*(R*L) i k-B*(R*L) i a+C*(R *ᵥ w) i=_
    rw [right,old,mul_one]
  have residual : excess S *ᵥ z = spike k A := by
    funext i
    have change := changeRow edit z i
    rw [zb,send] at change
    rw [mulVec_excess,mass]
    have term (d : ℝ) (u : I) : d*(1:Matrix I I ℝ) i u=spike u d i := by
      by_cases e : i=u
      · subst u; simp [spike]
      · simp [spike,e,Ne.symm e]
    rw [term,term] at change
    linarith
  have col : (fun v => t*p a*w b*L v k - t*p k*w b*L v a
      + w v*(p k + t*p k*L b a - t*p a*L b k))=z := by
    funext v; dsimp [z,A,B,C]; ring
  rw [col]; exact residual

/-- All legally inserted arcs at a flat parent use a common four-index test.
The displayed expression is exactly a positive multiple of an entry of the
child's centered inverse. No sign assumption on the old inverse is used. -/
theorem rectangle_identity {R S L H : Matrix I I ℝ} (right : R*L=1)
    {a b : I} {t : ℝ} (edit : ∀i j,S i j-R i j=if i=a ∧ j=b then t else 0)
    (child : CommonInverse S H) {w p : I→ℝ}
    (old : R *ᵥ w=fun _=>1) (dual : p ᵥ* R=fun _=>1) (wm : ∑i,w i=1) (v k : I) :
    t*p a*w b*L v k - t*p k*w b*L v a
      + w v*(p k + t*p k*L b a - t*p a*L b k) = (t*p a*w b)*H v k := by
  have residual := rectangle_column right edit old dual wm k
  have eq := congrArg (fun u => H *ᵥ u) residual
  rw [Matrix.mulVec_mulVec,mul_eq_one_comm.mp child.right,Matrix.one_mulVec] at eq
  have e := congrFun eq v
  change _=(H *ᵥ spike k (t*p a*w b)) v at e
  rw [row_spike,mul_comm (H v k)] at e
  exact e

end Linear

/-- Strictness of a one-arc extension produces a full boundary cycle of the
original family. The cycle has exactly the prescribed new arc. -/
theorem realize {q n} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    {F} {f : SharedArcComponentExchange.Arc} (fresh : Fresh X F f)
    (bad : ¬SmallRow q (insertArc (graph X.D F) f.1 f.2) X.V) :
    ∃M,Boundary X F M ∧ added X.D F M={f} ∧
      graph X.D (insert M F)=insertArc (graph X.D F) f.1 f.2 := by
  classical
  let E := graph X.D F
  let J := insertArc E f.1 f.2
  obtain ⟨fv,fw,fd,off⟩ := fresh
  have raw {u v} (ed : J u v=true) : X.D u v=true := by
    by_cases same : u=f.1 ∧ v=f.2
    · exact same.1 ▸ same.2 ▸ fd
    have old : E u v=true := by simpa [J,insertArc,same] using ed
    obtain ⟨A,hit⟩ := active.mp old
    exact (mem_col.mp hit).2.2.2
  have safe := qfree_sub (fun _ _ h => raw h) X.free
  obtain ⟨M,cm,im,jm⟩ := SharedArcMinimalPacket.cycle_at_arc hq small safe bad fv fw
    (show J f.1 f.2=true by simp [J,insertArc])
  obtain ⟨cd,kept⟩ := SharedArcMinimalPacket.lift_cycle (by omega : 1≤q) X.free (fun ed => raw ed) cm
  have fm : f∈added X.D F M := mem_added.mpr ⟨im,jm,fd,off⟩
  have only : added X.D F M={f} := by
    apply Subset.antisymm _ (singleton_subset_iff.mpr fm)
    intro g gm
    apply mem_singleton.mpr
    by_contra ne
    have diff : ¬(g.1=f.1 ∧ g.2=f.2) := fun h => ne (Prod.ext h.1 h.2)
    obtain ⟨gu,gv,gd,miss⟩ := mem_added.mp gm
    have old : E g.1 g.2=true := by simpa [J,insertArc,diff] using kept g.1 gu g.2 gv gd
    exact Bool.noConfusion (miss.symm.trans old)
  have has : ∃v∈M,v∉targets X.D X.V F M := by
    by_contra! incl
    have m := card_le_card incl
    rw [←count cd,cd.size,only,card_singleton] at m
    omega
  obtain ⟨v,vm,no⟩ := has
  obtain ⟨u,uh⟩ := card_pos.mp (show 0<(inN X.D M v).card by
    have := cd.incoming v vm; change (inN X.D M v).card=1 at this; omega)
  obtain ⟨um,uv⟩ := mem_inN.mp uh
  have old : E u v=true := by
    by_contra miss
    exact no (mem_filter.mpr ⟨cd.sub vm,vm,u,um,uv,Bool.eq_false_iff.mpr miss⟩)
  obtain ⟨A,hit⟩ := active.mp old
  obtain ⟨af,ua,va,arc⟩ := mem_col.mp hit
  have outside : M∉F := fun h => Bool.noConfusion (off.symm.trans (active.mpr ⟨M,mem_col.mpr ⟨h,im,jm,fd⟩⟩))
  refine ⟨M,⟨mem_filter.mpr ⟨mem_powerset.mpr cd.sub,cd⟩,outside,A,af,
    u,mem_inter.mpr ⟨ua,um⟩,v,mem_inter.mpr ⟨va,vm⟩,arc⟩,only,?_⟩
  funext i j
  apply Bool.eq_iff_iff.mpr
  rw [union_arc,only,mem_singleton]
  by_cases same : i=f.1 ∧ j=f.2
  · simp [insertArc,same]
  · have diff : (i,j)≠f := fun h => same ⟨congrArg Prod.fst h,congrArg Prod.snd h⟩
    simp [insertArc,same,diff]

/-- This test depends only on the parent and the proposed ordered pair.
Every safe insertion must pass for every pair of test labels. -/
noncomputable def test {I : Type*} (L : Matrix I I ℝ) (w p : I→ℝ)
    (t : ℝ) (a b v k : I) : ℝ :=
  t*p a*w b*L v k - t*p k*w b*L v a + w v*(p k+t*p k*L b a-t*p a*L b k)

theorem inverse_test {q : ℕ} (hq : 2≤q) {E : CH.Digraph} {V : Finset ℕ}
    (small : SmallerSmallRow q V.card) (a b : V) (off : E a b=false)
    (safe : QFree (insertArc E a b) V q) {w p : ℕ→ℚ}
    (wp : ∀i∈V,0<w i ∧ 0<p i) (wm : mass V w=1)
    (wr : ∀i∈V,WeightedSD.row q E V w i=1) (pc : ∀i∈V,WeightedSD.col q E V p i=1)
    : ∃H : Matrix V V ℝ, CommonInverse (realMatrix q (insertArc E a b) V) H ∧
      ∀v k : V,test (realMatrix q E V)⁻¹ (fun i : V => (w i : ℝ)) (fun i : V => (p i : ℝ)) q a b v k =
        ((q:ℝ)*(p a:ℝ)*(w b:ℝ))*H v k := by
  let J := insertArc E a b
  have bad : ¬SmallRow q J V := positive_feasible_extension_not_smallRow hq
    (fun i _ j _ h => insertArc_mono E a b i j h) w (fun i hi => (wp i hi).1)
    (fun i hi => by rw [wm,wr i hi]) a.property b.property (by simp [off]) (by simp [J,insertArc])
  obtain ⟨z,zn,_,zh⟩ := strict_witness_of_not_smallRow bad
  obtain ⟨H,inv⟩ := strict_inverse_of_proper_smallRow (small.induced safe) z zn zh
  refine ⟨H,inv,fun v k => ?_⟩
  exact rectangle_identity (Matrix.mul_nonsing_inv _ (matrix_unit hq E V))
    (realMatrix_insert_difference (q:=q) a b (by simp [off])) inv
    (by simpa using funext (realMatrix_rational_rows w 1 wr))
    (by simpa using funext (realMatrix_rational_columns p 1 pc)) (real_mass_of_rational_probability w wm) v k

theorem safe_test {q : ℕ} (hq : 2≤q) {E : CH.Digraph} {V : Finset ℕ}
    (small : SmallerSmallRow q V.card) (a b : V) (off : E a b=false)
    (safe : QFree (insertArc E a b) V q) {w p : ℕ→ℚ}
    (wp : ∀i∈V,0<w i ∧ 0<p i) (wm : mass V w=1)
    (wr : ∀i∈V,WeightedSD.row q E V w i=1) (pc : ∀i∈V,WeightedSD.col q E V p i=1)
    (v k : V) :
    0≤test (realMatrix q E V)⁻¹ (fun i : V => (w i : ℝ)) (fun i : V => (p i : ℝ)) q a b v k := by
  obtain ⟨H,inv,r⟩ := inverse_test hq small a b off safe wp wm wr pc
  rw [r]
  have hp : (0:ℝ)≤p a := by exact_mod_cast (wp a a.property).2.le
  have hw : (0:ℝ)≤w b := by exact_mod_cast (wp b b.property).1.le
  exact mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg q) hp) hw) (inv.nonneg v k)

#print axioms realize
#print axioms response
#print axioms rectangle_identity
#print axioms inverse_test
end LeanCH.BR.Closure.SharedArcFlatResponse
