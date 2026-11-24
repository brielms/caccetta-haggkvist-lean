import checkpoints.shen_extension.SingleArcCyclePrices
import checkpoints.puncture_law_20261119.ClosedSetExit

namespace LeanCH.BR.Closure.SingleArcCyclePivot
open Finset Matrix BRq2 BRq3 BR45 BRsub WeightedSD WeightedArithmetic FiniteCutInverse
open ShortestCycleWeights FirstPacketBarrier MarkedCyclePeeling SharedArcFlatResponse ClosedSetExit ShenCycleSuccessor

/-- The closed-set pivot still carries the full root excess when other
rows have zero excess, provided the weight is positive on its support. -/
theorem feasible_gap {q : ℕ} (hq : 2≤q) {D : CH.Digraph} {V S : Finset ℕ}
    (free : QFree D V q) {v : ℕ} (hv : v∈V) (sub : S⊆V) (off : v∉S)
    (closed : ∀i∈V,i∉S → i≠v → ∀j∈S,D i j=true → D i v=true)
    (pay : SmallRow q D (V \ S)) {u : ℕ→ℚ} (pos : ∀i∈V,0<u i)
    (rows : ∀i∈V,mass V u≤WeightedSD.row q D V u i) :
    WeightedSD.row q D V u v-mass V u ≤
      (q:ℚ)*(∑j∈S,if D v j=true then u j else 0) - ∑j∈S,u j := by
  have vk : v∈V \ S := mem_sdiff.mpr ⟨hv,off⟩
  have total : 0≤∑j∈S,u j := sum_nonneg (fun j hj=>(pos _ (sub hj)).le)
  let z := setTransfer u S v
  have zp (i) (hi : i∈V \ S) : 0<z i := by
    have h := pos i (mem_sdiff.mp hi).1
    dsimp [z,setTransfer]
    split_ifs <;> linarith
  by_contra! bad
  have root : mass (V \ S) z<WeightedSD.row q D (V \ S) z v := by
    rw [show z=setTransfer u S v from rfl,row_setTransfer sub vk,mass_setTransfer sub vk]
    rw [if_pos rfl,if_neg (loopfree free (by omega) hv)]
    linarith
  have allRows (i) (hi : i∈V \ S) : mass (V \ S) z≤WeightedSD.row q D (V \ S) z i := by
    by_cases eq : i=v
    · exact eq ▸ root.le
    have iv := (mem_sdiff.mp hi).1
    have feasible := rows i iv
    rw [show z=setTransfer u S v from rfl,row_setTransfer sub vk,mass_setTransfer sub vk]
    simp only [if_neg eq,add_zero]
    by_cases ed : D i v=true
    · rw [if_pos ed]
      have bound : (∑j∈S,if D i j=true then u j else 0)≤∑j∈S,u j :=
        sum_le_sum (fun j hj=>by split_ifs <;> first | exact le_rfl | exact (pos _ (sub hj)).le)
      linarith only [feasible,mul_le_mul_of_nonneg_left bound (Nat.cast_nonneg q : (0:ℚ)≤q)]
    · rw [if_neg ed,sum_eq_zero (fun j hj=>if_neg (fun h=>ed (closed i iv (mem_sdiff.mp hi).2 eq j hj h)))]
      linarith
  exact root.ne' (positive_feasible_rows_tight_of_smallRow hq pay z zp allRows v vk)

/-- Each reverse-closed set has at least one unit of credit on the
midpoint row of the rational centered inverse of the actual child. -/
theorem inverse_credit {q : ℕ} (hq : 2≤q) {G : CH.Digraph} {V S : Finset ℕ}
    (free : QFree G V q) (small : SmallerSmallRow q V.card)
    {H : Matrix V V ℚ} (inv : SingleArcTensorMerge.center q G V * H=1) (v : V)
    (pos : ∀i,0<H v i) (sub : S⊆V) (ne : S.Nonempty) (off : v.val∉S)
    (closed : ∀i∈V,i∉S → i≠v.val → ∀j∈S,G j i=true → G v i=true) :
    let u := extendWeight V (H v)
    1 ≤ (q:ℚ)*(∑j∈S,if G j v=true then u j else 0) - ∑j∈S,u j := by
  intro u
  have col (j : V) : WeightedSD.col q G V u j-mass V u=(1:Matrix V V ℚ) v j := by
    rw [show u=extendWeight V (H v) from rfl,col_extendWeight q G V _ j,mass_extendWeight]
    have left : H*SingleArcTensorMerge.center q G V=1 := mul_eq_one_comm.mp inv
    have eq := congrFun (congrFun left v) j
    change (∑i,H v i*rationalMatrix q (adjacencyMatrix G V) i j)-∑i,H v i=_
    simpa only [mul_apply,SingleArcTensorMerge.center,mul_sub,mul_one,sum_sub_distrib] using eq
  have proper : V \ S≠V := by
    obtain ⟨j,hj⟩ := ne
    intro eq
    have hjK : j∈V \ S := by rw [eq]; exact sub hj
    exact (mem_sdiff.mp hjK).2 hj
  have up (i) (iv : i∈V) : 0<u i := by
    simpa only [u,extendWeight_on V _ (⟨i,iv⟩ : V)] using pos ⟨i,iv⟩
  have h := feasible_gap (D:=fun x y=>G y x) hq free.reverse v.property sub off closed
    (small.reverse_induced free _ sdiff_subset proper) up (fun i iv=>by
      apply sub_nonneg.mp
      change 0≤WeightedSD.col q G V u (⟨i,iv⟩ : V)-mass V u
      rw [col,one_apply]; split <;> norm_num)
  change WeightedSD.col q G V u v-mass V u≤_ at h
  simpa only [col v,one_apply_eq] using h

/-- Each member of a reverse-closed set has coefficient q−1 when it
enters the root and −1 otherwise. Exterior vertices have coefficient zero. -/
def score (q : ℕ) (G : CH.Digraph) (S : Finset ℕ) (v i : ℕ) : ℚ :=
  if i∈S then (if G i v=true then (q:ℚ) else 0)-1 else 0

private theorem score_sum {q : ℕ} {G : CH.Digraph} {V S : Finset ℕ} (sub : S⊆V)
    (v : ℕ) (p : V→ℚ) :
    (∑i : V,p i*score q G S v i) =
      (q:ℚ)*(∑j∈S,if G j v=true then extendWeight V p j else 0)-∑j∈S,extendWeight V p j := by
  let u := extendWeight V p
  have restrict : (∑i : V,p i*score q G S v i)=∑i∈S,u i*((if G i v=true then (q:ℚ) else 0)-1) := by
    calc
      _ = ∑i∈V,u i*score q G S v i := by
        conv_rhs => rw [←sum_coe_sort]
        exact sum_congr rfl (fun i _=>by rw [show u i=p i from extendWeight_on V p i])
      _ = ∑i∈S,u i*score q G S v i := (sum_subset sub (fun i _ off=>by simp [score,off])).symm
      _ = _ := sum_congr rfl (fun i hi=>by simp [score,hi])
  rw [restrict,mul_sum,←sum_sub_distrib]
  apply sum_congr rfl
  intro i _
  by_cases ed : G i v=true <;> simp [ed,u] <;> ring

/-- A usable graph-only test. If the exterior incidences of an old
cycle dominate a nonnegative multiple of a reverse-closed set score,
then the diagonal is at most minus that multiple times q p(a) w(b). -/
theorem diagonal_bound {q n} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    (F : Family) {w p : ℕ→ℚ} (wp : ∀i∈X.V,0<w i ∧ 0<p i) (wm : mass X.V w=1)
    (wr : ∀i∈X.V,WeightedSD.row q (graph X.D F) X.V w i=1)
    (pc : ∀i∈X.V,WeightedSD.col q (graph X.D F) X.V p i=1)
    (f : SharedArcFlatCut.Missing X F) (v : X.V) {C S : Finset ℕ}
    (cy : Cycle (graph X.D F) X.V q C) (ac : f.val.1.val∈C) (vc : v.val∈C) (bc : f.val.2.val∉C)
    (sub : S⊆X.V) (ne : S.Nonempty) (off : v.val∉S) (alpha : ℝ) (nonneg : 0≤alpha)
    (closed : let G := insertArc (graph X.D F) f.val.1 f.val.2
              ∀i∈X.V,i∉S → i≠v.val → ∀j∈S,G j i=true → G v i=true)
    (cover : let E := graph X.D F
             let G := insertArc E f.val.1 f.val.2
             ∀i : X.V,alpha*(score q G S v i:ℝ)≤SingleArcCyclePrices.exterior q E ⟨f.val.1,ac⟩
               ⟨v,vc⟩ (-(w v:ℝ)/((q:ℝ)*(w f.val.2:ℝ))) i) :
    test (realMatrix q (graph X.D F) X.V)⁻¹ (fun i : X.V=>(w i:ℝ)) (fun i : X.V=>(p i:ℝ))
      q f.val.1 f.val.2 v v ≤ -alpha*((q:ℝ)*(p f.val.1:ℝ)*(w f.val.2:ℝ)) := by
  let E := graph X.D F
  let G := insertArc E f.val.1 f.val.2
  let H := (SingleArcTensorMerge.center q G X.V)⁻¹
  let d := (q:ℝ)*(p f.val.1:ℝ)*(w f.val.2:ℝ)
  let T := test (realMatrix q E X.V)⁻¹ (fun i : X.V=>(w i:ℝ)) (fun i : X.V=>(p i:ℝ)) q f.val.1 f.val.2
  let z (i : X.V) := SingleArcCyclePrices.exterior q E ⟨f.val.1,ac⟩ ⟨v,vc⟩ (-(w v:ℝ)/((q:ℝ)*(w f.val.2:ℝ))) i
  have dp : 0<d := mul_pos (mul_pos (by exact_mod_cast (by omega : 0<q)) (by exact_mod_cast (wp _ f.val.1.property).2))
    (by exact_mod_cast (wp _ f.val.2.property).1)
  obtain ⟨inv,eq⟩ := SingleArcTensorMerge.identify X hq F wp wm wr pc f
  have tp (i : X.V) : 0<T v i := SharedArcFlatArithmetic.positive X hq small F wp wm wr pc f v i
  have hp (i : X.V) : 0<H v i := by
    have h := tp i
    change 0<test _ _ _ _ _ _ _ _ at h
    rw [eq v i] at h
    exact_mod_cast pos_of_mul_pos_right h dp.le
  have free : QFree G X.V q := by
    apply qfree_sub _ X.free
    intro i j ij
    by_cases ab : i=f.val.1.val ∧ j=f.val.2.val
    · exact ab.1 ▸ ab.2 ▸ f.property.1
    have old : E i j=true := by simpa only [G,insertArc,if_neg ab] using ij
    exact (mem_col.mp (active.mp old).choose_spec).2.2.2
  have credit := inverse_credit hq free small inv v hp sub ne off closed
  change 1≤(q:ℚ)*_ - _ at credit
  rw [←score_sum sub v (H v)] at credit
  have realCredit : (1:ℝ)≤∑i : X.V,(H v i:ℝ)*(score q G S v i:ℝ) := by exact_mod_cast credit
  have bound := sum_le_sum (s:=univ) (fun (i : X.V) _=>mul_le_mul_of_nonneg_left (cover i) (tp i).le)
  change (∑i : X.V,T v i*(alpha*(score q G S v i:ℝ)))≤∑i : X.V,T v i*z i at bound
  have factor (i : X.V) : T v i*(alpha*(score q G S v i:ℝ))=
      (alpha*d)*((H v i:ℝ)*(score q G S v i:ℝ)) := by
    change test _ _ _ _ _ _ _ _ * _=_
    rw [eq v i]; dsimp [d,H,G,E]; ring
  simp_rw [factor,←mul_sum] at bound
  have acc := SingleArcCyclePrices.account X hq F wp wm wr pc f v cy.sub ac vc bc
  change T v v= -(∑i : X.V,T v i*z i) at acc
  change T v v≤ -alpha*d
  linarith only [acc,bound,mul_le_mul_of_nonneg_left realCredit (mul_nonneg nonneg dp.le)]

end LeanCH.BR.Closure.SingleArcCyclePivot
#print axioms LeanCH.BR.Closure.SingleArcCyclePivot.feasible_gap
#print axioms LeanCH.BR.Closure.SingleArcCyclePivot.inverse_credit
#print axioms LeanCH.BR.Closure.SingleArcCyclePivot.diagonal_bound
