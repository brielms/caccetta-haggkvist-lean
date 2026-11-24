import LeanCH.BR.BRFiniteThresholdUnit
import LeanCH.BR.BRFiniteUniformInverse

/-! Nonnegative signed integer pressures leave a degree-one or a genuine
single-excess profile. This uses actual arc charges, not an IH. -/
namespace LeanCH.BR.NonnegativePressure
open Finset Matrix FiniteCutInverse ThresholdUnit
open scoped Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem inverse_has_head {q : ℕ} (E : ι → ι → Bool)
    {C H : Matrix ι ι ℝ} (hH : CommonInverse C H)
    (hC : ∀ i j, C i j = (if i=j then 1 else 0)+if E i j=true then (q : ℝ) else 0)
    (i : ι) : ∃ j, E i j=true := by
  by_contra hn
  push Not at hn
  have hh := congrArg (fun M : Matrix ι ι ℝ => M i i) hH.right
  simp [Matrix.mul_apply,excess,hC,hn,sub_mul,sum_sub_distrib,ite_mul] at hh
  have hs := single_le_sum (s := univ) (fun j _ => hH.nonneg j i) (mem_univ i)
  linarith

theorem classify {q : ℕ} (hq : 3 ≤ q) [Nonempty ι]
    (E : ι → ι → Bool) {C H : Matrix ι ι ℝ} (hH : CommonInverse C H)
    (hC : ∀ i j, C i j = (if i=j then 1 else 0)+if E i j=true then (q : ℝ) else 0)
    (hcharge : ∀ i j, E i j=true → 1 ≤ (q : ℝ)*H j i)
    (hpressure : ∀ i, Fintype.card ι ≤ 1+q*(univ.filter (fun j => E i j=true)).card) :
    ((∀ i, (univ.filter (fun j => E i j=true)).card=1) ∧ Fintype.card ι ≤ q) ∨
    ∃ r : ℕ, 1 ≤ r ∧ ∃ h : ι, Fintype.card ι=q*r+1 ∧
      (univ.filter (fun j => E h j=true)).card=r+1 ∧
      (∀ i, i≠h → (univ.filter (fun j => E i j=true)).card=r) ∧
      ∀ i, H i h=1/(q : ℝ) := by
  let n := Fintype.card ι
  let d := fun i => (univ.filter (fun j => E i j=true)).card
  let k : ι → ℤ := fun i => 1+(q : ℤ)*d i-n
  have hnn (i : ι) : 0 ≤ k i := by
    have hi : (n : ℤ) ≤ 1+(q : ℤ)*d i := by exact_mod_cast hpressure i
    dsimp only [k]
    omega
  have hdpos (i : ι) : 1 ≤ d i := by
    obtain ⟨j,hj⟩ := inverse_has_head E hH hC i
    have hp : 0 < (univ.filter (fun j => E i j=true)).card :=
      card_pos.mpr ⟨j,mem_filter.mpr ⟨mem_univ _,hj⟩⟩
    exact hp
  have hrow : excess C *ᵥ (fun _ => (1 : ℝ)) = fun i => (k i : ℝ) := by
    funext i
    simp [Matrix.mulVec,dotProduct,excess,hC,sum_sub_distrib,sum_add_distrib,k,d,n]
    rw [← sum_filter]
    simp [mul_comm]
  have hleft : H * excess C=1 := mul_eq_one_comm.mp hH.right
  have hrec : H *ᵥ (fun i => (k i : ℝ)) = fun _ => 1 := by
    rw [← hrow,Matrix.mulVec_mulVec,hleft,Matrix.one_mulVec]
  have hrec' (i : ι) : ∑ j, H i j*(k j : ℝ)=1 := congrFun hrec i
  have hkn (i : ι) : (0 : ℝ) ≤ k i := by exact_mod_cast hnn i
  have hcap (i : ι) : k i ≤ q := by
    obtain ⟨v,hv⟩ := inverse_has_head E hH hC i
    have hh := single_le_sum (s := univ)
      (fun j _ => mul_nonneg (hH.nonneg v j) (hkn j)) (mem_univ i)
    rw [hrec' v] at hh
    have ha := hcharge i v hv
    have hb := mul_le_mul_of_nonneg_right ha (hkn i)
    have hqR : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    have hbound : (k i : ℝ) ≤ q := by nlinarith
    exact_mod_cast hbound
  by_cases hzero : ∃ z, k z=0
  · right
    obtain ⟨z,hz⟩ := hzero
    let r := d z
    have hn : n=q*r+1 := by
      have hi : (n : ℤ) = (q : ℤ)*r+1 := by dsimp only [k,r] at *; linarith
      exact_mod_cast hi
    have hqd : (0 : ℤ) < q := by exact_mod_cast (show 0 < q by omega)
    have hdegrees (i : ι) : d i=r ∨ d i=r+1 := by
      have hlo := hnn i
      have hhi := hcap i
      have hnZ : (n : ℤ)=(q : ℤ)*r+1 := by exact_mod_cast hn
      dsimp only [k] at hlo hhi
      have hl : (r : ℤ) ≤ d i := by nlinarith
      have hh : (d i : ℤ) ≤ r+1 := by nlinarith
      have hln : r ≤ d i := by exact_mod_cast hl
      have hhn : d i ≤ r+1 := by exact_mod_cast hh
      omega
    have hkcase (i : ι) : k i=0 ∨ k i=q := by
      rcases hdegrees i with he | he <;> dsimp only [k] <;> rw [hn,he] <;> push_cast <;> ring_nf <;> simp
    have hactive : ∃ h, k h=q := by
      by_contra hh
      have hall (i : ι) : k i=0 := (hkcase i).resolve_right (fun he => hh ⟨i,he⟩)
      let i : ι := Classical.choice inferInstance
      have he := hrec' i
      simp only [hall,Int.cast_zero,mul_zero,sum_const_zero] at he
      norm_num at he
    obtain ⟨h,hh⟩ := hactive
    obtain ⟨v,hv⟩ := inverse_has_head E hH hC h
    have hsingle := single_le_sum (s := univ)
      (fun j _ => mul_nonneg (hH.nonneg v j) (hkn j)) (mem_univ h)
    rw [hrec' v,hh] at hsingle
    have hthreshold : (q : ℝ)*H v h=1 := by
      have hc := hcharge h v hv
      push_cast at hsingle
      nlinarith
    let A : Matrix ι ι ℤ := fun i j => if E i j=true then 1 else 0
    have hrep : ∀ i j, C i j=(if i=j then 1 else 0)+(q : ℝ)*(A i j : ℝ) := by
      intro i j
      rw [hC]
      dsimp only [A]
      split_ifs <;> norm_num
    have hp := (integer_exact_threshold (by omega : 2 ≤ q) A hH hrep h v hthreshold).1
    have hpoint (i : ι) : (if i=h then (1 : ℝ) else 0) ≤ H v i*(k i : ℝ) := by
      by_cases hi : i=h
      · subst i; simp only [ite_true,hh,Int.cast_natCast]; nlinarith
      · simp only [hi,ite_false]; exact mul_nonneg (hH.nonneg v i) (hkn i)
    have hsum : (∑ i, if i=h then (1 : ℝ) else 0) = ∑ i, H v i*(k i : ℝ) := by
      rw [hrec' v]
      simp
    have hother (i : ι) (hi : i≠h) : k i=0 := by
      have he := (sum_eq_sum_iff_of_le (fun i _ => hpoint i)).mp hsum i (mem_univ i)
      simp only [hi,ite_false] at he
      have hzR : (k i : ℝ)=0 := by nlinarith [hp i]
      exact_mod_cast hzR
    have hdh : d h=r+1 := by
      rcases hdegrees h with he | he
      · have hk0 : k h=0 := by dsimp [k]; rw [hn,he]; push_cast; ring
        rw [hh] at hk0
        omega
      · exact he
    refine ⟨r,hdpos z,h,hn,hdh,?_,?_⟩
    · intro i hi
      have hk0 := hother i hi
      have hnZ : (n : ℤ)=(q : ℤ)*r+1 := by exact_mod_cast hn
      dsimp only [k] at hk0
      have : (d i : ℤ)=r := by nlinarith
      exact_mod_cast this
    · intro i
      have he := hrec' i
      have hfun : (fun j => (k j : ℝ)) = fun j => if j=h then (q : ℝ) else 0 := by
        funext j
        by_cases hj : j=h
        · subst j; simp [hh]
        · simp [hj,hother j hj]
      simp_rw [congrFun hfun] at he
      simp only [mul_ite,mul_zero,sum_ite_eq',mem_univ,ite_true] at he
      have hq0 : (q : ℝ)≠0 := by exact_mod_cast (show q≠0 by omega)
      apply (eq_div_iff hq0).mpr
      exact he
  · left
    apply UniformInverse.degree_floor_one hq E hH
      (by intro i j; by_cases h : E i j=true <;> simpa [h] using hC i j) hcharge
    intro i
    have hi := hnn i
    have hne : k i≠0 := fun he => hzero ⟨i,he⟩
    have hp : 1 ≤ k i := by omega
    have hh : (n : ℤ) ≤ (q : ℤ)*d i := by dsimp only [k] at hp; omega
    exact_mod_cast hh

end LeanCH.BR.NonnegativePressure
