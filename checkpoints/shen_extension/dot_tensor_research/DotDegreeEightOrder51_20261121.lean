
import checkpoints.shen_extension.dot_tensor_research.DotDegreeEightPairCover_20261121
import checkpoints.shen_extension.dot_tensor_research.DotDegreeEightGram_20261121

namespace LeanCH.BR.DotDegreeEight
open Finset BRq2 BRq3 BR45 BRsGen Matrix
open scoped BigOperators
set_option maxHeartbeats 1000000

noncomputable def arcMat (D : CH.Digraph) (V : Finset ℕ) : Matrix V V ℝ :=
  fun i j => if D i j=true then 1 else 0

theorem arcMat_rows {D : CH.Digraph} {V : Finset ℕ} (i : V) :
    (∑ j, arcMat D V i j)=((outN D V i).card : ℝ) := by
  classical
  unfold arcMat
  rw [← Finset.sum_subtype V (fun _ => Iff.rfl) (fun j : ℕ => if D i j=true then (1:ℝ) else 0)]
  simp only [outN,sum_boole]

theorem arcMat_cols {D : CH.Digraph} {V : Finset ℕ} (j : V) :
    (∑ i, arcMat D V i j)=((inN D V j).card : ℝ) := by
  classical
  unfold arcMat
  rw [← Finset.sum_subtype V (fun _ => Iff.rfl) (fun i : ℕ => if D i j=true then (1:ℝ) else 0)]
  simp only [inN,sum_boole]

theorem walk_of_arc_power_ne_zero {D : CH.Digraph} {V : Finset ℕ} (k : ℕ)
    (u v : V) (h : (arcMat D V ^ k) u v ≠ 0) : Walk D V u v k := by
  classical
  induction k generalizing u v with
  | zero =>
    have eq : u=v := by
      by_contra e
      exact h (by simp [e])
    subst v
    exact .refl _
  | succ k ih =>
    rw [pow_succ',Matrix.mul_apply] at h
    obtain ⟨x,_,nz⟩ := exists_ne_zero_of_sum_ne_zero h
    have uv : D u x=true := by
      by_contra n
      apply nz
      simp [arcMat,n]
    have nz' : (arcMat D V ^ k) x v≠0 := by
      intro no
      exact nz (by simp [no])
    exact .step x.property uv (ih x v nz')

theorem trace_zero_of_qfree {D : CH.Digraph} {V : Finset ℕ} {q k : ℕ}
    (hf : QFree D V q) (hp : 0<k) (hk : k≤q) : Matrix.trace (arcMat D V ^ k)=0 := by
  classical
  have z (u : V) : (arcMat D V ^ k) u u=0 := by
    by_contra e
    exact hf u k hp hk (walk_of_arc_power_ne_zero k u u e)
  simp [Matrix.trace, Matrix.diag, z]

theorem order51_q7 {D : CH.Digraph} {V : Finset ℕ}
    (hq : QFree D V 7) (hc : V.card=51) (hm : ∀ v∈V,8≤(outN D V v).card) : False := by
  classical
  obtain ⟨F,sub,ho⟩ := exists_outEq hm
  have hf := qfree_sub sub hq
  have pairs := pair_cover_of_endpoint DotDegreeSeven.endpoint_seven_seven
    (by decide : 0<7) (by decide : 0<7) hf (by simpa using hc) ho
  have ind := diagonal_pair_cover_regular (d:=7) (by simpa using hc) ho pairs
  let A := arcMat F V
  let J : Matrix V V ℝ := fun _ _ => 8/51
  let P := A-J
  let E : Matrix V V ℝ := fun i j => (Aᵀ*A) i j-(if i=j then 7 else 0)-1
  have vn : Fintype.card V=51 := by simpa using hc
  have row (i : V) : (∑ j,A i j)=8 := by
    rw [arcMat_rows,ho i i.property]
    norm_num
  have col (j : V) : (∑ i,A i j)=8 := by
    rw [arcMat_cols,ind j j.property]
    norm_num
  have dia (i : V) : (Aᵀ*A) i i=8 := by
    rw [Matrix.mul_apply]
    simp only [Matrix.transpose_apply]
    calc
      _ = ∑ k,A k i := by
        apply sum_congr rfl
        intro k _
        by_cases e : F k i=true <;> simp [A,arcMat,e]
      _ = 8 := col i
  have es (i j : V) : E i j=E j i := by
    dsimp only [E]
    simp only [Matrix.mul_apply,Matrix.transpose_apply]
    simp [eq_comm,mul_comm]
  have ez (i : V) : E i i=0 := by
    change (Aᵀ*A) i i-(if i=i then 7 else 0)-1=0
    norm_num [dia]
  have en (i j : V) : 0≤E i j := by
    by_cases e : i=j
    · subst j
      rw [ez]
    have ne : i.val≠j.val := fun h => e (Subtype.ext h)
    obtain ⟨k,kv,ki,kj⟩ := pairs i i.property j j.property ne
    let k' : V := ⟨k,kv⟩
    have low : 1≤(Aᵀ*A) i j := by
      rw [Matrix.mul_apply]
      have r : Aᵀ i k' * A k' j=1 := by simp [A,arcMat,k',ki,kj]
      rw [←r]
      apply single_le_sum (f:=fun t=>Aᵀ i t*A t j) ?_ (mem_univ k')
      intro z _
      have nonneg (a b : V) : 0≤A a b := by
        by_cases e : F a b=true <;> simp [A,arcMat,e]
      exact mul_nonneg (nonneg z i) (nonneg z j)
    change 0≤(Aᵀ*A) i j-(if i=j then 7 else 0)-1
    simp only [ite_eq_right e]
    linarith
  have er (i : V) : (∑ j,E i j)=6 := by
    have gr : (∑ j,(Aᵀ*A) i j)=64 := by
      simp only [Matrix.mul_apply,Matrix.transpose_apply]
      rw [sum_comm]
      simp_rw [←mul_sum,row,←sum_mul,col]
      norm_num
    change (∑ j,((Aᵀ*A) i j-(if i=j then 7 else 0)-1))=6
    rw [sum_sub_distrib,sum_sub_distrib,gr]
    norm_num [Finset.sum_ite_eq,hc]
  have gram (i j : V) : (Pᵀ*P) i j=(if i=j then 7 else 0)+E i j-13/51 := by
    have a : (∑ k,A k i * (8/51:ℝ))=64/51 := by rw [←sum_mul,col]; norm_num
    have b : (∑ k,A k j * (8/51:ℝ))=64/51 := by rw [←sum_mul,col]; norm_num
    have c : (∑ _k : V,(8/51:ℝ)*(8/51))=64/51 := by simp [hc] <;> norm_num
    change (∑ k,(A k i-8/51)*(A k j-8/51))=
      (if i=j then 7 else 0)+((∑ k,A k i*A k j)-(if i=j then 7 else 0)-1)-13/51
    simp_rw [sub_mul,mul_sub,Finset.sum_sub_distrib,mul_comm (8/51:ℝ) (A _ _)]
    rw [a,b,c]
    ring
  have f : frob2 P=344 := by
    have diag (i : V) : (∑ k,P k i^2)=7-13/51 := by
      have v := gram i i
      rw [ez] at v
      simpa [Matrix.mul_apply,Matrix.transpose_apply,pow_two] using v
    unfold frob2
    simp_rw [diag]
    simp [hc] <;> norm_num
  have contract (x : V→ℝ) : (∑ i,(P *ᵥ x) i^2)≤13*(∑ i,x i^2) := by
    have t := contract_of_codegrees (b0:=(by norm_num : (0:ℝ)≤13/51))
      en es er gram x
    norm_num at t
    exact t
  have aj : A*J = (8:ℝ) • J := by
    ext i j
    change (∑ k,A i k*(8/51:ℝ))=8*(8/51)
    rw [←sum_mul,row]
  have ja : J*A = (8:ℝ) • J := by
    ext i j
    change (∑ k,(8/51:ℝ)*A k j)=8*(8/51)
    rw [←mul_sum,col]
    ring
  have jj : J*J = (8:ℝ) • J := by
    ext i j
    change (∑ _k : V,(8/51:ℝ)*(8/51))=8*(8/51)
    simp [hc] <;> norm_num
  have pj : P*J=0 := by rw [show P=A-J from rfl,sub_mul,aj,jj,sub_self]
  have jp : J*P=0 := by rw [show P=A-J from rfl,mul_sub,ja,jj,sub_self]
  have hp (k : ℕ) : (P+J)^(k+1)=P^(k+1)+J^(k+1) := by
    induction k with
    | zero => simp
    | succ k ih =>
      simp only [pow_succ' (P+J) (k+1),ih,mul_add,add_mul]
      have z₁ : P * J^(k+1)=0 := by rw [pow_succ',←mul_assoc,pj,zero_mul]
      have z₂ : J * P^(k+1)=0 := by rw [pow_succ',←mul_assoc,jp,zero_mul]
      rw [z₁,z₂,add_zero,zero_add]
      simp only [←pow_succ']
  have jr (k : ℕ) : J^(k+1)=(8:ℝ)^k • J := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ' J (k+1),ih,Matrix.mul_smul,jj,smul_smul,pow_succ]
  have tj : Matrix.trace J=8 := by simp [J,Matrix.trace,Matrix.diag,hc] <;> norm_num
  have ex : A=P+J := by dsimp only [P]; abel
  have t := trace_zero_of_qfree hf (k:=6) (by decide) (by decide)
  change Matrix.trace (A^6)=0 at t
  rw [ex,show 6=5+1 by decide,hp,Matrix.trace_add,jr,Matrix.trace_smul,tj] at t
  have bound := six_moment_bound (by norm_num : (0:ℝ)≤13) contract
  rw [f] at bound
  norm_num at t bound
  linarith

#print axioms order51_q7
end LeanCH.BR.DotDegreeEight


