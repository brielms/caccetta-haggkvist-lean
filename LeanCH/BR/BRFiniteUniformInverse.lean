import LeanCH.BR.BRFiniteInverseDiagonal
import LeanCH.BR.BRFiniteInverseTransport

/-! Integer arc charges exclude regular strict inverse sources of degree
at least two. This structural statement assumes no girth or induction. -/
namespace LeanCH.BR.UniformInverse
open Finset Matrix FiniteCutInverse InverseDiagonal
open scoped Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem diagonal_degree_charge {q : ℕ} (E : ι → ι → Bool)
    {C H : Matrix ι ι ℝ} (hH : CommonInverse C H)
    (hC : ∀ i j, C i j = (if i = j then 1 else 0) + if E i j = true then q else 0)
    (hcharge : ∀ i j, E i j = true → 1 ≤ (q : ℝ)*H j i) (i : ι) :
    (((univ.filter (fun j => E i j = true)).card : ℝ)-1) + H i i ≤ ∑ j, H j i := by
  have hs : ((univ.filter (fun j => E i j = true)).card : ℝ) ≤
      (q : ℝ)*∑ j ∈ univ.filter (fun j => E i j = true), H j i := by
    calc
      _ = ∑ _j ∈ univ.filter (fun j => E i j = true), (1 : ℝ) := by simp
      _ ≤ ∑ j ∈ univ.filter (fun j => E i j = true), (q : ℝ)*H j i :=
        sum_le_sum (fun j hj => hcharge i j (mem_filter.mp hj).2)
      _ = _ := by rw [mul_sum]
  have he := congrArg (fun M : Matrix ι ι ℝ => M i i) hH.right
  have hex : (excess C * H) i i = H i i +
      (q : ℝ)*∑ j ∈ univ.filter (fun j => E i j = true), H j i - ∑ j, H j i := by
    simp [Matrix.mul_apply,excess,hC,sub_mul,add_mul,sum_sub_distrib,
      sum_add_distrib,sum_filter,mul_sum,ite_mul]
  rw [hex] at he
  simp only [Matrix.one_apply,ite_true] at he
  linarith


theorem zero_diagonal_order {q : ℕ} (hq : 2 ≤ q)
    (E : ι → ι → Bool) {C H : Matrix ι ι ℝ} (hH : CommonInverse C H)
    (hC : ∀ i j, C i j = (if i = j then 1 else 0) + if E i j = true then q else 0)
    (u : ι) (hz : H u u = 0) : (Fintype.card ι : ZMod q) = 2 := by
  have hcol : (∑ i, H i u) ≠ 0 := by
    intro hz
    have hall : ∀ i, H i u = 0 := fun i =>
      (sum_eq_zero_iff_of_nonneg (fun j _ => hH.nonneg j u)).mp hz i (mem_univ i)
    have hh := congrArg (fun M : Matrix ι ι ℝ => M u u) hH.right
    simp [Matrix.mul_apply,hall] at hh
  let A : Matrix ι ι ℤ := fun i j => if E i j = true then 1 else 0
  have hB : centeredInteger q A = excess C := by
    ext i j
    simp only [centeredInteger,excess,hC,A]
    split_ifs <;> norm_num
  exact zero_diagonal_card_mod hq A H (by rw [hB]; exact hH.right) u hz hcol

/-- The explicit integral degree floor is sufficient. No equalizer,
looplessness, girth, or induction hypothesis is used. -/
theorem degree_floor_one {q : ℕ} (hq : 3 ≤ q) [Nonempty ι]
    (E : ι → ι → Bool) {C H : Matrix ι ι ℝ} (hH : CommonInverse C H)
    (hC : ∀ i j, C i j = (if i = j then 1 else 0) + if E i j = true then q else 0)
    (hcharge : ∀ i j, E i j = true → 1 ≤ (q : ℝ)*H j i)
    (hfloor : ∀ i, Fintype.card ι ≤ q*(univ.filter (fun j => E i j = true)).card) :
    (∀ i, (univ.filter (fun j => E i j = true)).card = 1) ∧ Fintype.card ι ≤ q := by
  let n := Fintype.card ι
  let d := fun i => (univ.filter (fun j => E i j = true)).card
  let k := fun i => 1+q*d i-n
  have hn : 0 < n := Fintype.card_pos
  have hk (i : ι) : 1 ≤ k i := by
    have hi := hfloor i
    change n ≤ q*d i at hi
    dsimp only [k]
    omega
  have hnk (i : ι) : n+k i = 1+q*d i := by
    have hi := hfloor i
    change n ≤ q*d i at hi
    dsimp only [k]
    omega
  have hdpos (i : ι) : 1 ≤ d i := by
    have hi := hfloor i
    change n ≤ q*d i at hi
    by_contra hh
    have hz : d i = 0 := by omega
    rw [hz,mul_zero] at hi
    omega
  have hrow : excess C *ᵥ (fun _ => (1 : ℝ)) = fun i => (k i : ℝ) := by
    funext i
    have hi : (n : ℝ)+(k i : ℝ) = 1+(q : ℝ)*d i := by exact_mod_cast hnk i
    have he : (excess C *ᵥ (fun _ => (1 : ℝ))) i = 1+(q : ℝ)*d i-n := by
      simp [Matrix.mulVec,dotProduct,excess,hC,sum_sub_distrib,sum_add_distrib,
        d,n]
      rw [← sum_filter]
      simp [mul_comm]
    rw [he]
    linarith
  have hleft : H * excess C = 1 := mul_eq_one_comm.mp hH.right
  have hrecover : H *ᵥ (fun i => (k i : ℝ)) = fun _ => 1 := by
    rw [← hrow,Matrix.mulVec_mulVec,hleft,Matrix.one_mulVec]
  have htotal : ∑ i, (k i : ℝ)*(∑ j, H j i) = n := by
    have he := congrArg (fun f : ι → ℝ => ∑ i, f i) hrecover
    simp only [Matrix.mulVec,dotProduct,sum_const,card_univ,nsmul_eq_mul,mul_one] at he
    rw [sum_comm] at he
    simpa only [← sum_mul,mul_comm] using he
  let b := fun i => (k i : ℝ)*((d i : ℝ)-1+H i i)
  have hb (i : ι) : 0 ≤ b i := by
    have hd : (1 : ℝ) ≤ d i := by exact_mod_cast hdpos i
    dsimp only [b]
    exact mul_nonneg (Nat.cast_nonneg _) (by linarith [hH.nonneg i i])
  have hsum : ∑ i, b i ≤ n := by
    rw [← htotal]
    exact sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left
      (diagonal_degree_charge E hH hC hcharge i) (Nat.cast_nonneg (k i)))
  have hex : ∃ u, d u = 1 := by
    by_contra hh
    have hd2 (i : ι) : 2 ≤ d i := by
      have hi := hdpos i
      have hne : d i ≠ 1 := fun he => hh ⟨i,he⟩
      omega
    have hone (i : ι) : 1 ≤ b i := by
      have hkR : (1 : ℝ) ≤ k i := by exact_mod_cast hk i
      have hdR : (2 : ℝ) ≤ d i := by exact_mod_cast hd2 i
      have hnn := hH.nonneg i i
      dsimp only [b]
      nlinarith [mul_nonneg (sub_nonneg.mpr hkR) (show 0 ≤ (d i : ℝ)-1+H i i by linarith)]
    have heach (i : ι) : b i = 1 := by
      have he : (∑ _i : ι, (1 : ℝ)) = ∑ i, b i := by
        apply le_antisymm (sum_le_sum (fun i _ => hone i))
        simpa only [sum_const,card_univ,nsmul_eq_mul,mul_one] using hsum
      exact ((sum_eq_sum_iff_of_le (fun i _ => hone i)).mp he i (mem_univ i)).symm
    let u : ι := Classical.choice inferInstance
    have hu := heach u
    have hkR : (1 : ℝ) ≤ k u := by exact_mod_cast hk u
    have hdR : (2 : ℝ) ≤ d u := by exact_mod_cast hd2 u
    have hnn := hH.nonneg u u
    change (k u : ℝ)*((d u : ℝ)-1+H u u) = 1 at hu
    have hdle : (d u : ℝ) ≤ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hkR) (show 0 ≤ (d u : ℝ)-1+H u u by linarith)]
    have hdeq : d u = 2 := by exact_mod_cast (le_antisymm hdle hdR)
    have hkeq : k u = 1 := by
      have hkle : (k u : ℝ) ≤ 1 := by nlinarith [mul_nonneg (Nat.cast_nonneg (k u) : (0 : ℝ) ≤ k u) hnn]
      exact_mod_cast (le_antisymm hkle hkR)
    have hzero : H u u = 0 := by rw [hdeq,hkeq] at hu; norm_num at hu; linarith
    have hneq : n = 2*q := by have ht := hnk u; rw [hdeq,hkeq] at ht; omega
    have hmod := zero_diagonal_order (by omega : 2 ≤ q) E hH hC u hzero
    have hz2 : (2 : ZMod q) = 0 := by
      change (n : ZMod q) = 2 at hmod
      rw [hneq] at hmod
      simpa using hmod.symm
    have hdiv : q ∣ 2 := (ZMod.natCast_eq_zero_iff 2 q).mp hz2
    have hle := Nat.le_of_dvd (by omega : 0 < 2) hdiv
    omega
  obtain ⟨u,hu⟩ := hex
  have hnq : n ≤ q := by have hh := hfloor u; change n ≤ q*d u at hh; simpa [hu] using hh
  refine ⟨?_,hnq⟩
  intro i
  by_contra hh
  have hd2 : 2 ≤ d i := by have hp := hdpos i; change d i ≠ 1 at hh; omega
  have hki : q+1 ≤ k i := by
    have he := hnk i
    have hmul : q*2 ≤ q*d i := Nat.mul_le_mul_left q hd2
    omega
  have hbound : b i ≤ n := (single_le_sum (s := univ) (fun j _ => hb j) (mem_univ i)).trans hsum
  have hkR : (q : ℝ)+1 ≤ k i := by exact_mod_cast hki
  have hdR : (2 : ℝ) ≤ d i := by exact_mod_cast hd2
  have hnR : (n : ℝ) ≤ q := by exact_mod_cast hnq
  have hnn := hH.nonneg i i
  dsimp only [b] at hbound
  nlinarith [mul_nonneg (Nat.cast_nonneg (k i) : (0 : ℝ) ≤ k i)
    (show 0 ≤ (d i : ℝ)-2+H i i by linarith)]

/-- Uniform strict rows supply the integral degree floor. -/
theorem uniform_degree_one {q : ℕ} (hq : 3 ≤ q) [Nonempty ι]
    (E : ι → ι → Bool) {C H : Matrix ι ι ℝ} (hH : CommonInverse C H)
    (hC : ∀ i j, C i j = (if i = j then 1 else 0) + if E i j = true then q else 0)
    (hcharge : ∀ i j, E i j = true → 1 ≤ (q : ℝ)*H j i)
    (c : ℝ) (hc : 1 < c)
    (hr : ∀ i, (C *ᵥ (fun _ => 1/(Fintype.card ι : ℝ))) i = c) :
    (∀ i, (univ.filter (fun j => E i j = true)).card = 1) ∧ Fintype.card ι ≤ q := by
  apply degree_floor_one hq E hH hC hcharge
  intro i
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos (α := ι)
  have he : ∑ j, C i j = 1+(q : ℝ)*(univ.filter (fun j => E i j = true)).card := by
    simp [hC,sum_add_distrib]
    rw [← sum_filter]
    simp [mul_comm]
  have hh := hr i
  change (∑ j, C i j*(1/(Fintype.card ι : ℝ))) = c at hh
  rw [← sum_mul,he] at hh
  have hnz := ne_of_gt hn
  have heq : 1+(q : ℝ)*(univ.filter (fun j => E i j = true)).card = c*Fintype.card ι := by
    field_simp at hh
    nlinarith
  have hlt : Fintype.card ι < 1+q*(univ.filter (fun j => E i j = true)).card := by
    have : (Fintype.card ι : ℝ) < 1+(q : ℝ)*(univ.filter (fun j => E i j = true)).card := by nlinarith
    exact_mod_cast this
  omega

end LeanCH.BR.UniformInverse
