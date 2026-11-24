import checkpoints.shen_extension.SingleArcCycleSlope

namespace LeanCH.BR.Closure.SingleArcCycleSparse
open Finset Matrix BRq2 BRq3 BR45 WeightedSD FiniteCutInverse ShenCycleSuccessor SingleArcCycleBalance
open SingleArcCyclePrices SingleArcCycleSlope

theorem successor {q E V C} (cy : Cycle E V q C) (i : C) : ∃j : C,E i j=true := by
  obtain ⟨j,hj⟩ := card_pos.mp (show 0<(outN E C i).card by rw [cy.heads i i.property]; decide)
  exact ⟨⟨j,(mem_outN.mp hj).1⟩,(mem_outN.mp hj).2⟩

private theorem predecessor {q E V C} (cy : Cycle E V q C) (j : C) : ∃i : C,E i j=true := by
  have one : (inN E C j).card=1 := cy.incoming j j.property
  obtain ⟨i,hi⟩ := card_pos.mp (show 0<(inN E C j).card by omega)
  exact ⟨⟨i,(mem_inN.mp hi).1⟩,(mem_inN.mp hi).2⟩

private theorem unique {q E V C} (cy : Cycle E V q C) (i j k : C) (ij : E i j=true) (ik : E i k=true) : j=k :=
  Subtype.ext (card_le_one.mp (cy.heads i i.property).le _ (mem_outN.mpr ⟨j.property,ij⟩)
    _ (mem_outN.mpr ⟨k.property,ik⟩))

/-- Only the second cycle successor of v can give a negative price
among one-hit rows missing v. Even that receiver is paid at u=1/q. -/
theorem sparse {q : ℕ} (hq : 2≤q) {E : CH.Digraph} {V C : Finset ℕ} (free : QFree E V q)
    (cy : Cycle E V q C) (a v s r : C) (av : E a v=true) (vs : E v s=true) (sr : E s r=true)
    (x : ℝ) (heavy : 1<((q:ℝ)-1)*x) :
    let z := tiltedPrices q E a v 1 x
    0<score q ∅ z ∧ (∀j : C,j≠v → j≠r → 0<score q {j} z) ∧
    (∀j : C,j≠v → 0<score q {j} z+x) ∧ (∀j : C,j≠s → z j<0) ∧
    z a+(q:ℝ)*z v-∑k,z k= -1 ∧ z v+(q:ℝ)*z s-∑k,z k=1 := by
  intro z
  let Q := (q:ℝ)
  let L := Q-1
  have two : 2≤Q := by dsimp [Q]; exact_mod_cast hq
  have qp : 0<Q := by linarith
  have lp : 0<L := by dsimp [L]; linarith
  change 1<L*x at heavy
  let mean := (∑j,z j)/(Q+1)
  let h (j : C) := z j-mean
  have sumz : ∑j,z j=(Q+1)*mean := by dsimp [mean]; field_simp
  have zv : z v= -x := by simp [z,tiltedPrices]
  have row (i j : C) (ij : E i j=true) : z i+Q*z j-∑k,z k=
      (if i=v then 1 else 0)-(if i=a then 1 else 0) := by
    have eq := exterior_on hq cy a v (-x) i
    have ident (k : C) : prices (realMatrix q E C) a v (-x) k=z k := by
      unfold z tiltedPrices prices
      simp only [neg_one_mul]
      rfl
    have edges (k : C) : E i k=true ↔ k=j := ⟨fun ed=>unique cy i k j ed ij,fun e=>e ▸ ij⟩
    have diag (k : C) : i.val=k.val ↔ k=i := Subtype.ext_iff.symm.trans eq_comm
    simp only [SingleArcCyclePrices.exterior,ident,edges,diag,add_mul,sub_mul,ite_mul,zero_mul,
      one_mul,sum_sub_distrib,sum_add_distrib,sum_ite_eq',mem_univ,ite_true] at eq
    simp only [show (v=i)↔i=v from eq_comm,show (a=i)↔i=a from eq_comm] at eq
    change z i+(q:ℝ)*z j-_=_
    linarith only [eq]
  have recur (i j : C) (ij : E i j=true) : h i+Q*h j=(if i=v then 1 else 0)-(if i=a then 1 else 0) := by
    dsimp [h]; linarith only [sumz,row i j ij]
  have va : v≠a := by rintro rfl; exact loopfree free (by omega) (cy.sub v.property) av
  have as' : a≠s := by rintro rfl; exact free a 2 (by omega) hq (.step (cy.sub v.property) av (.step (cy.sub a.property) vs (.refl _)))
  have atA := recur a v av
  have atV := recur v s vs
  simp only [ite_true,ite_eq_right va,ite_eq_right va.symm,zero_sub,sub_zero] at atA atV
  have envelope (i : C) : L*|h i|≤1 := by
    obtain ⟨k,_,mx⟩ := exists_max_image univ (fun j : C=>|h j|) ⟨i,mem_univ _⟩
    obtain ⟨m,mk⟩ := predecessor cy k
    have lim : |h m+Q*h k|≤1 := by rw [recur m k mk]; split_ifs <;> norm_num
    have tri := abs_sub_le (h m+Q*h k) 0 (h m)
    rw [add_sub_cancel_left,abs_mul,abs_of_pos qp,sub_zero,zero_sub,abs_neg] at tri
    have maxH : L*|h k|≤1 := by dsimp [L]; linarith only [lim,tri,mx m (mem_univ _)]
    exact (mul_le_mul_of_nonneg_left (mx i (mem_univ _)) lp.le).trans maxH
  have upper (i : C) : L*h i≤1 := (mul_le_mul_of_nonneg_left (le_abs_self _) lp.le).trans (envelope i)
  have lower (i : C) : L*(-h i)≤1 := (mul_le_mul_of_nonneg_left (neg_le_abs _) lp.le).trans (envelope i)
  have high : 0≤h s := by
    have hv : h v≤1 := by
      by_contra! big
      have ll : 0≤L-1 := by dsimp [L]; linarith
      nlinarith only [mul_nonneg ll (le_of_lt (zero_lt_one.trans big)),upper v,big]
    by_contra! neg
    linarith only [atV,hv,mul_neg_of_pos_of_neg qp neg]
  have plain (j : C) (jv : j≠v) (js : j≠s) :
      ∃k : C,k≠v ∧ k≠a ∧ h k+Q*h j=0 := by
    obtain ⟨k,kj⟩ := predecessor cy j
    have kv : k≠v := by rintro rfl; exact js (unique cy k j s kj vs)
    have ka : k≠a := by rintro rfl; exact jv (unique cy k j v kj av)
    exact ⟨k,kv,ka,by simpa [kv,ka] using recur k j kj⟩
  have small (j : C) (jv : j≠v) (js : j≠s) : Q^2*L*h j≤1 := by
    obtain ⟨k,kv,_,rec1⟩ := plain j jv js
    by_cases ks : k=s
    · have hj : h j≤0 := by
        rw [ks] at rec1
        exact nonpos_of_mul_nonpos_right (by linarith only [rec1,high] : Q*h j≤0) qp
      exact le_trans (mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (sq_nonneg _) lp.le) hj) zero_le_one
    · obtain ⟨m,_,_,rec2⟩ := plain k kv ks
      have eq : Q^2*h j=h m := by linear_combination Q*rec1-rec2
      nlinarith only [upper m,congrArg (fun z : ℝ=>L*z) eq]
  have noHit : 0<score q ∅ z := by
    have hv : -h v<x := lt_of_mul_lt_mul_left ((lower v).trans_lt heavy) lp.le
    have neg : mean<0 := by dsimp [h] at hv; linarith only [zv,hv]
    unfold score
    rw [sum_empty,mul_zero,zero_sub,sumz]
    exact neg_pos.mpr (mul_neg_of_pos_of_neg (by linarith) neg)
  have singlePrice (k j : C) (kj : E k j=true) (ka : k≠a) :
      score q {j} z=x+h v-h k+(if k=v then 1 else 0) := by
    have eq := row k j kj
    simp only [ite_eq_right ka,sub_zero] at eq
    simp only [score,sum_singleton]; dsimp only [h,Q] at *
    linarith only [eq,zv]
  have limit (k : C) (kv : k≠v) (ks : k≠s) : L*(h k-h v)≤1 := by
    have sm := small k kv ks
    have sa := small a va.symm as'
    have q3 : 0<Q^3 := pow_pos qp _
    apply le_of_mul_le_mul_left (a:=Q^3) _ q3
    have scale := mul_le_mul_of_nonneg_left sm qp.le
    have eq := congrArg (fun u : ℝ=>Q^2*L*u) atA
    dsimp [L] at scale sa eq ⊢
    nlinarith only [scale,sa,eq,mul_nonneg (show 0≤Q-2 by linarith) (show 0≤Q+1 by linarith)]
  refine ⟨noHit,?_,?_,?_,by simpa [va.symm] using row a v av,by simpa [va] using row v s vs⟩
  · intro j jv jr
    obtain ⟨k,kj⟩ := predecessor cy j
    have ka : k≠a := by rintro rfl; exact jv (unique cy k j v kj av)
    have ks : k≠s := by rintro rfl; exact jr (unique cy k j r kj sr)
    rw [singlePrice k j kj ka]
    by_cases kv : k=v
    · have xp : 0<x := pos_of_mul_pos_right (zero_lt_one.trans heavy) lp.le
      simp [kv]; linarith
    · simp only [ite_eq_right kv,add_zero]
      have := lt_of_mul_lt_mul_left ((limit k kv ks).trans_lt heavy) lp.le
      linarith
  · intro j jv
    obtain ⟨k,kj⟩ := predecessor cy j
    have ka : k≠a := by rintro rfl; exact jv (unique cy k j v kj av)
    rw [singlePrice k j kj ka]
    have hv := lt_of_mul_lt_mul_left ((lower v).trans_lt heavy) lp.le
    have hk := lt_of_mul_lt_mul_left ((upper k).trans_lt heavy) lp.le
    split_ifs <;> linarith
  · intro j js
    by_cases jv : j=v
    · rw [jv,zv]
      have xp : 0<x := pos_of_mul_pos_right (zero_lt_one.trans heavy) lp.le
      linarith
    · have bound := lt_of_mul_lt_mul_left ((limit j jv js).trans_lt heavy) lp.le
      dsimp [h] at bound
      linarith only [bound,zv]

end LeanCH.BR.Closure.SingleArcCycleSparse
#print axioms LeanCH.BR.Closure.SingleArcCycleSparse.sparse
