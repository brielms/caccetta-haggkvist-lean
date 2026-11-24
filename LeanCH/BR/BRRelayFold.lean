import LeanCH.BR.BRRelayFoldRows

/-! Actual full relay surgery with one shared cut, unit-source budgets,
and the smaller-order obstruction. No successful cut is supplied. -/
namespace LeanCH.BR.WeightedSD.RelayFold
open Finset BRq2 BRq3 BR45 BRsub

noncomputable def surplus (D : CH.Digraph) (V : Finset ℕ) (d x : ℕ) := (outN D V x).card-d

def Paid (D : CH.Digraph) (V : Finset ℕ) (d u h t : ℕ)
    (K : Finset (ℕ×ℕ)) (Q : ℕ→Finset ℕ) : Prop :=
  (C D V u h t).card≤2+surplus D V d u ∧
  (∀z∈X1 D V u h t,(cutHeads V K z).card≤1+surplus D V d z) ∧
  (∀r∈R D V u h t,(losses D V u h t r).card≤(Q r).card+surplus D V d r)

namespace Base
variable {D : CH.Digraph} {V : Finset ℕ} {u h t : ℕ} (B : Base D V u h t)
include B
variable {K : Finset (ℕ×ℕ)} {Q : ℕ→Finset ℕ}

theorem boost_mass : mass (V.erase h) (boost t)=(V.card:ℚ) := by
  rw [mass_boost]
  have ht : t∈V.erase h := mem_erase.mpr ⟨B.ht.symm,B.tmem⟩
  rw [if_pos ht]
  exact_mod_cast card_erase_add_one B.hmem

omit B in
theorem boost_positive {x : ℕ} : 0< boost t x := by
  unfold boost
  split_ifs <;> norm_num

omit B in
theorem unit_row_surplus (q d : ℕ) {x : ℕ} (hd : d≤(outN D V x).card) :
    row q D V (fun _=>1) x=1+q*d+q*(surplus D V d x:ℚ) := by
  have he := congrArg (fun n:ℕ=>(n:ℚ)) (Nat.sub_add_cancel hd)
  simp only [Nat.cast_add] at he
  simp only [row,outW_unit,surplus]
  nlinarith

/-- Coefficient-parametric accounting; only the actual surgery geometry uses cutoff three. -/
theorem paid_rows (hK : ValidCuts D V u h t K) (hQ : Selected D V u h t K Q)
    (q d : ℕ) (hd : ∀x∈V,d≤(outN D V x).card) (hp : Paid D V d u h t K Q) :
    ∀x∈V.erase h,1+(q:ℚ)*d≤row q (graph D V u h t K Q) (V.erase h) (boost t) x := by
  classical
  intro x hx
  have hxV := (mem_erase.mp hx).2
  have he := unit_row_surplus q d (hd x hxV)
  have hnq : (0:ℚ)≤q := Nat.cast_nonneg q
  have hns : (0:ℚ)≤surplus D V d x := Nat.cast_nonneg _
  by_cases hx0 : x∈X0 D V u h t
  · rw [B.row_X0 hK q hx0,he]
    exact le_add_of_nonneg_right (mul_nonneg hnq hns)
  by_cases hx1 : x∈X1 D V u h t
  · have hrow := B.row_X1 hK (Q:=Q) q hx1
    have hp' : ((cutHeads V K x).card:ℚ)≤1+surplus D V d x := by exact_mod_cast hp.2.1 x hx1
    have hmul := mul_le_mul_of_nonneg_left hp' hnq
    nlinarith only [hrow,he,hmul]
  by_cases hxu : x=u
  · subst x
    have hrow := B.row_u hK (Q:=Q) q
    have hp' : ((C D V u h t).card:ℚ)≤2+surplus D V d u := by exact_mod_cast hp.1
    have hmul := mul_le_mul_of_nonneg_left hp' hnq
    nlinarith only [hrow,he,hmul]
  by_cases hxR : x∈R D V u h t
  · have hrow := B.row_R hK hQ q hxR
    have hp' : ((losses D V u h t x).card:ℚ)≤(Q x).card+surplus D V d x := by exact_mod_cast hp.2.2 x hxR
    have hmul := mul_le_mul_of_nonneg_left hp' hnq
    nlinarith only [hrow,he,hmul]
  have hrow := B.row_other hK (Q:=Q) q hxu hx0 hx1 hxR
  have hn : D x h=true→D x t=true := by
    intro exh
    by_contra nxt
    have hX : x∈X D V h t := mem_X.mpr ⟨hxV,exh,nxt⟩
    by_cases exu : D x u=true
    · exact hx1 (mem_X1.mpr ⟨hxV,exh,nxt,exu⟩)
    · exact hx0 (mem_X0.mpr ⟨hxV,exh,nxt,exu⟩)
  have hi : (if D x h=true then 1 else 0 : ℚ)≤(if D x t=true then 1 else 0) := by
    by_cases hh : D x h=true
    · simp [hh,hn hh]
    · simp [hh]; split_ifs <;> norm_num
  have hi' := mul_le_mul_of_nonneg_left hi hnq
  have hdiag : (0:ℚ) ≤ if x=t then 1 else 0 := by split_ifs <;> norm_num
  have hs := mul_nonneg hnq hns
  linarith only [hrow,he,hi',hdiag,hs]

/-- An actual shared cut and actual relay targets satisfying the budgets cannot
exist at boundary order under the genuine smaller-order SmallRow hypothesis. -/
theorem no_paid (hsmall : SmallerSmallRow 3 V.card) (d : ℕ)
    (hn : V.card=3*d+1) (hd : ∀x∈V,d≤(outN D V x).card)
    (hK : ValidCuts D V u h t K) (hQ : Selected D V u h t K Q)
    (hp : Paid D V d u h t K Q) : False := by
  have hfeasible : ∀x∈V.erase h,mass (V.erase h) (boost t)≤
      row 3 (graph D V u h t K Q) (V.erase h) (boost t) x := by
    intro x hx
    rw [B.boost_mass,hn]
    simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_one,Nat.cast_ofNat,add_comm] using
      B.paid_rows hK hQ 3 d hd hp x hx
  have horder := hsmall.erased_positive_child_order (by decide : 2≤3) B.hmem
    ⟨t,mem_erase.mpr ⟨B.ht.symm,B.tmem⟩⟩ _ (B.graph_qfree hQ) (boost t)
    (fun _ _=>boost_positive) hfeasible
  rw [hn] at horder
  norm_num only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] at horder
  have h3 : (3:ZMod 3)=0 := by decide
  rw [h3,zero_mul,zero_add] at horder
  exact (by decide : (1:ZMod 3)≠2) horder

end Base
end LeanCH.BR.WeightedSD.RelayFold
