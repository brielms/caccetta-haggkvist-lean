import LeanCH.BR.BRFiniteInverseTransport
import LeanCH.BR.BRFiniteInverseComparison
import Mathlib.Tactic.LinearCombination

/-! Signed two-entry equalizer comparison on arbitrary finite real matrices.
Threshold, graph integrality, and positivity enter only in later consumers. -/
namespace LeanCH.BR.ThresholdExchange
open Finset Matrix FiniteCutInverse InverseTransport
open scoped Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def firstCoefficient (H : Matrix ι ι ℝ) (p : ι→ℝ) (β : ℝ) (h t b : ι) : ℝ :=
  p h*(1+β*H b t)-β*p t*H b h

def secondCoefficient (H : Matrix ι ι ℝ) (p : ι→ℝ) (β : ℝ) (h w t : ι) : ℝ :=
  β*p h*H w t+p t*(1-β*H w h)

def price (H : Matrix ι ι ℝ) (a p : ι→ℝ) (β : ℝ) (h w t b : ι) : ℝ :=
  a w*firstCoefficient H p β h t b-a b*secondCoefficient H p β h w t

def thresholdPrice (H : Matrix ι ι ℝ) (a p : ι→ℝ) (β : ℝ) (h w t b : ι) : ℝ :=
  a w*p h*(1+β*H b t)-β*a w*p t*H b h-β*a b*p h*H w t

theorem vecMul_change {C K : Matrix ι ι ℝ} {β : ℝ} {h w t b : ι}
    (hd : ∀ i j,K i j-C i j=(if i=t ∧ j=b then β else 0)-(if i=h ∧ j=w then β else 0))
    (p' : ι→ℝ) (j : ι) :
    (p' ᵥ* K) j-(p' ᵥ* C) j=(if j=b then β*p' t else 0)-(if j=w then β*p' h else 0) := by
  simp only [Matrix.vecMul,dotProduct]
  rw [←sum_sub_distrib]
  simp_rw [←mul_sub,hd,mul_sub]
  rw [sum_sub_distrib]
  by_cases hjb : j=b <;> by_cases hjw : j=w <;> simp_all [mul_comm]

theorem mixed_gain {C K : Matrix ι ι ℝ} {β : ℝ} {h w t b : ι}
    (hd : ∀ i j,K i j-C i j=(if i=t ∧ j=b then β else 0)-(if i=h ∧ j=w then β else 0))
    (a p' : ι→ℝ) (ha : ∑i,a i=1) (hp : ∑i,p' i=1) (c c' : ℝ)
    (hr : ∀i,(C *ᵥ a) i=c) (hc : ∀j,(p' ᵥ* K) j=c') :
    c'-c=β*(p' t*a b-p' h*a w) := by
  rw [mixed_equalizer_gain a p' ha hp c c' hr hc]
  simp_rw [hd,mul_sub,sub_mul]
  simp only [sum_sub_distrib]
  simp [ite_and,mul_ite,ite_mul]
  ring

theorem dual_recovery {C K H : Matrix ι ι ℝ} (hH : centered C*H=1)
    {β : ℝ} {h w t b : ι}
    (hd : ∀ i j,K i j-C i j=(if i=t ∧ j=b then β else 0)-(if i=h ∧ j=w then β else 0))
    (p' : ι→ℝ) (hp : ∑i,p' i=1) (c' : ℝ) (hc : ∀j,(p' ᵥ* K) j=c') (i : ι) :
    p' i=(c'-1)*(∑j,H j i)-β*p' t*H b i+β*p' h*H w i := by
  have hcols (j : ι) : (p' ᵥ* C) j=c'-(if j=b then β*p' t else 0)+(if j=w then β*p' h else 0) := by
    have hh := vecMul_change hd p' j
    rw [hc j] at hh
    linarith
  have he := congrFun (show (p' ᵥ* centered C) ᵥ* H=p' by
    rw [Matrix.vecMul_vecMul,hH,Matrix.vecMul_one]) i
  have hre : p' i=∑j,((p' ᵥ* C) j-1)*H j i := by
    rw [←he]
    change (∑j,(p' ᵥ* centered C) j*H j i)=_
    simp only [centered,Matrix.vecMul,dotProduct,mul_sub,mul_one,sum_sub_distrib,hp]
  rw [hre]
  simp only [hcols,sub_mul,add_mul,sum_sub_distrib,sum_add_distrib,ite_mul,zero_mul]
  simp only [sum_ite_eq',mem_univ,ite_true,one_mul,←mul_sum]
  ring

theorem dual_elimination {C K H : Matrix ι ι ℝ} (hH : centered C*H=1)
    {β : ℝ} {h w t b : ι}
    (hd : ∀ i j,K i j-C i j=(if i=t ∧ j=b then β else 0)-(if i=h ∧ j=w then β else 0))
    (p p' : ι→ℝ) (hp : ∑i,p i=1) (hp' : ∑i,p' i=1) (c c' : ℝ)
    (hc : ∀j,(p ᵥ* C) j=c) (hc' : ∀j,(p' ᵥ* K) j=c') :
    p' t*firstCoefficient H p β h t b=p' h*secondCoefficient H p β h w t := by
  have hd' := dual_recovery hH hd p' hp' c' hc'
  have hm := column_mass hH p hp c hc
  have hcross : p h*(∑j,H j t)=p t*(∑j,H j h) := by
    rw [←hm h,←hm t]
    ring
  unfold firstCoefficient secondCoefficient
  linear_combination p h * hd' t - p t * hd' h + (c'-1) * hcross

theorem price_identity {C K H : Matrix ι ι ℝ} (hH : centered C*H=1)
    {β : ℝ} {h w t b : ι}
    (hd : ∀ i j,K i j-C i j=(if i=t ∧ j=b then β else 0)-(if i=h ∧ j=w then β else 0))
    (a p p' : ι→ℝ) (ha : ∑i,a i=1) (hp : ∑i,p i=1) (hp' : ∑i,p' i=1) (c c' : ℝ)
    (hr : ∀i,(C *ᵥ a) i=c) (hc : ∀j,(p ᵥ* C) j=c) (hc' : ∀j,(p' ᵥ* K) j=c') :
    β*p' t*price H a p β h w t b=secondCoefficient H p β h w t*(c-c') := by
  have he := dual_elimination hH hd p p' hp hp' c c' hc hc'
  have hg := mixed_gain hd a p' ha hp' c c' hr hc'
  unfold price
  linear_combination β*a w*he + secondCoefficient H p β h w t*hg

theorem threshold_price_identity {C K H : Matrix ι ι ℝ} (hH : centered C*H=1)
    {β : ℝ} {h w t b : ι}
    (hd : ∀ i j,K i j-C i j=(if i=t ∧ j=b then β else 0)-(if i=h ∧ j=w then β else 0))
    (ht : β*H w h=1) (a p p' : ι→ℝ)
    (ha : ∑i,a i=1) (hp : ∑i,p i=1) (hp' : ∑i,p' i=1) (c c' : ℝ)
    (hr : ∀i,(C *ᵥ a) i=c) (hc : ∀j,(p ᵥ* C) j=c) (hc' : ∀j,(p' ᵥ* K) j=c') :
    p' t*thresholdPrice H a p β h w t b=H w t*p h*(c-c') := by
  have he := price_identity hH hd a p p' ha hp hp' c c' hr hc hc'
  have hb : β≠0 := by intro hh; simp [hh] at ht
  have hsec : secondCoefficient H p β h w t=β*p h*H w t := by simp [secondCoefficient,ht]
  have hprice : price H a p β h w t b=thresholdPrice H a p β h w t b := by
    rw [price,hsec]
    unfold firstCoefficient thresholdPrice
    ring
  rw [hsec,hprice] at he
  apply (mul_left_cancel₀ hb)
  linear_combination he

end LeanCH.BR.ThresholdExchange
