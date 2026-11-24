import checkpoints.shen_extension.TwoCutParentBanks

namespace LeanCH.BR.Closure.TwoCutVariation
open Finset Matrix BRq2 BRq3 BR45 WeightedSD FiniteCutInverse TwoCutParentBanks

def distance {ι : Type*} [Fintype ι] (u v : ι→ℝ) := ∑i,|u i-v i|

theorem triangle {ι : Type*} [Fintype ι] (u v w : ι→ℝ) :
    distance u w ≤ distance u v+distance v w := by
  unfold distance
  rw [←sum_add_distrib]
  exact sum_le_sum (fun i _ => abs_sub_le (u i) (v i) (w i))

/-- Recover the exact cost in ℓ¹ of restricting and renormalizing a law. -/
theorem conditioning {ι : Type*} [Fintype ι] [DecidableEq ι] (T : Finset ι) (u v : ι→ℝ)
    (nn : ∀i,0≤u i) (um : ∑i,u i=1) {d : ℝ} (dm : ∑i∈T,u i=d) (dp : 0<d)
    (onT : ∀i∈T,v i=u i/d) (off : ∀i,i∉T → v i=0) : distance u v=2*(1-d) := by
  have cap : d≤1 := dm ▸ um ▸ sum_le_sum_of_subset_of_nonneg (subset_univ T) (fun i _ _ => nn i)
  have rest := sum_sdiff (subset_univ T) (f:=u)
  rw [dm,um] at rest
  have inside : (∑i∈T,|u i-v i|)=1-d := by
    calc
      _ = ∑i∈T,(u i/d-u i) := sum_congr rfl fun i hi => by
        rw [onT i hi,abs_sub_comm,abs_of_nonneg]
        exact sub_nonneg.mpr ((le_div_iff₀ dp).mpr (by simpa using mul_le_mul_of_nonneg_left cap (nn i)))
      _ = _ := by rw [sum_sub_distrib,←sum_div,dm,div_self dp.ne']
  have outside : (∑i∈univ\T,|u i-v i|) = ∑i∈univ\T,u i :=
    sum_congr rfl fun i hi => by rw [off i (mem_sdiff.mp hi).2,sub_zero,abs_of_nonneg (nn i)]
  have split := sum_sdiff (subset_univ T) (f:=fun i => |u i-v i|)
  rw [inside,outside] at split
  change (∑i,|u i-v i|)=_
  linarith

/-- Opposite exclusive parent banks distinguish the two actual child laws.
This bound is on their entire distributions before conditioning. -/
theorem raw_motion {V : Finset ℕ} {q E M p u v c S T}
    (h : @Coupled V q E M p u v c S T) (un : ∀i,0≤u i) (vn : ∀i,0≤v i) :
    4*(c-1)≤(q:ℝ)*distance u v := by
  classical
  obtain ⟨a,b,s,ap,bp,sn,norm,_,y,_,z,_,_,_,one,two,_,_⟩ := h
  let loss := exclusive E u y z-exclusive E u z y
  let gain := exclusive E v z y-exclusive E v y z
  have l : c-1≤a*((q:ℝ)*loss) := by
    dsimp only [loss]
    nlinarith only [one,mul_nonneg ap.le (un z)]
  have r : c-1≤b*((q:ℝ)*gain) := by
    dsimp only [gain]
    nlinarith only [two,mul_nonneg bp.le (vn y)]
  have dual : loss+gain≤distance u v := by
    dsimp only [loss,gain,exclusive,distance]
    rw [←sum_sub_distrib,←sum_sub_distrib,←sum_add_distrib]
    apply sum_le_sum
    intro i _
    cases E i y <;> cases E i z <;> simp <;>
      linarith only [abs_nonneg (u i-v i),le_abs_self (u i-v i),neg_abs_le (u i-v i)]
  have sumcap : a+b≤1 := by linarith only [norm,sum_nonneg (s:=univ) (fun i _ => sn i)]
  have prodCap : 4*(a*b)≤a+b := by
    nlinarith only [sq_nonneg (a-b),mul_le_mul_of_nonneg_left sumcap (add_nonneg ap.le bp.le)]
  have normNon : 0≤(q:ℝ)*distance u v := mul_nonneg (Nat.cast_nonneg _) (sum_nonneg (fun i _ => abs_nonneg _))
  apply le_of_mul_le_mul_left (a:=a+b) _ (add_pos ap bp)
  nlinarith only [mul_le_mul_of_nonneg_left l bp.le,mul_le_mul_of_nonneg_left r ap.le,
    mul_le_mul_of_nonneg_left dual (mul_nonneg (Nat.cast_nonneg q : (0:ℝ)≤q) (mul_nonneg ap.le bp.le)),
    mul_le_mul_of_nonneg_right prodCap normNon]

#print axioms raw_motion
#print axioms conditioning
end LeanCH.BR.Closure.TwoCutVariation
