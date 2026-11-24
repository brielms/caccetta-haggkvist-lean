import checkpoints.shen_extension.OpposedPairPrices
import checkpoints.shen_extension.PunctureParentFlow

namespace LeanCH.BR.Closure.DisjointCutCapacity
open Finset Matrix BRq2 BRq3 BR45 WeightedSD FiniteCutInverse ShenCycleSuccessor FullCycleTransfer
open scoped Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Test capped combined *excess*, with the source equalizer kept fixed.
Negative columns of one trial may offset positive columns of another. -/
theorem pack {κ : Type*} [Fintype κ] (R H : Matrix ι ι ℝ) (inv : CommonInverse R H)
    (p : ι→ℝ) (pm : ∑b,p b=1) {c : ℝ} (cols : ∀j,(p ᵥ* R) j=c)
    (M : κ→ι→ℝ) (unit : ∀t,∑b,M t b=1) (a : κ→ℝ)
    (space : ∀j,(∑t,a t*(((M t) ᵥ* R) j-1))≤c-1) (b : ι) :
    (∑t,a t*M t b)≤p b := by
  classical
  rw [recovery inv p pm b]
  simp only [cols]
  calc
    _ = ∑t,a t*(∑j,(((M t) ᵥ* R) j-1)*H j b) :=
      sum_congr rfl fun t _ => congrArg (a t * ·) (recovery inv (M t) (unit t) b)
    _ = ∑j, (∑t,a t*(((M t) ᵥ* R) j-1))*H j b := by
      simp only [mul_sum,sum_mul,mul_assoc]
      rw [sum_comm]
    _ ≤ _ := sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (space j) (inv.nonneg j b)

/-- Two independently chosen normalized laws can both be charged against
p on each row when their omitted sets are disjoint. -/
theorem two_cuts {q E V} (hq : 2≤q) (free : QFree E V q)
    (small : SmallerSmallRow q V.card) {x p : ℕ→ℚ} {c : ℚ} (high : 1<c)
    (pos : ∀z∈V,0<x z) (xm : mass V x=1) (pm : mass V p=1)
    (rows : ∀z∈V,WeightedSD.row q E V x z=c) (cols : ∀z∈V,WeightedSD.col q E V p z=c)
    {U W : Finset ℕ} (uv : U⊆V) (wv : W⊆V) (cover : V⊆U∪W)
    {m k} (hu : RealDual q E U 1 m) (hw : RealDual q E W 1 k) (b : ℕ) (bv : b∈V) :
    ((c:ℝ)-1)*(maskReal U m b+maskReal W k b)≤((q:ℝ)-1)*(p b : ℝ) := by
  classical
  let R := realMatrix q E V
  let u := fun i : V => maskReal U m i
  let w := fun i : V => maskReal W k i
  let pv := fun i : V => (p i : ℝ)
  obtain ⟨H,inv⟩ := strict_inverse_of_proper_smallRow (small.induced free) x (fun i hi => (pos i hi).le)
    (fun i hi => by rw [xm,rows i hi]; exact high)
  have cc (j : V) : (pv ᵥ* R) j=(c:ℝ) := realMatrix_rational_columns p c cols j
  have cu := cutCertificate_of_realDual uv hu
  have cw := cutCertificate_of_realDual wv hw
  have cap (S : Finset V) (f : V→ℝ) (cert : CutCertificate R S f) (j : V) :
      (f ᵥ* R) j≤(q:ℝ) := by
    have entry (i : V) : R i j≤(q:ℝ) := by
      change realMatrix q E V i j ≤ _
      rw [realMatrix_entry]
      by_cases ij : i=j
      · subst i
        have no := Bool.eq_false_iff.mpr (loopfree free (by omega) j.property)
        simp [no]; exact_mod_cast (show 1≤q by omega)
      · cases E i j <;> simp [ij]
    calc
      _ ≤ ∑i,f i*(q:ℝ) := sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (entry i) (cert.nonneg i))
      _ = _ := by rw [←sum_mul,cert.mass,one_mul]
  have sumCap (j : V) : (u ᵥ* R) j-1+((w ᵥ* R) j-1)≤(q:ℝ)-1 := by
    rcases mem_union.mp (cover j.property) with ju|jw
    · have low := cu.columns j (by simpa [hostCut] using ju)
      change (u ᵥ* R) j≤1 at low
      linarith only [low,cap _ w cw j]
    · have low := cw.columns j (by simpa [hostCut] using jw)
      change (w ᵥ* R) j≤1 at low
      linarith only [low,cap _ u cu j]
  let i : V := ⟨b,bv⟩
  have ueq := recovery inv u cu.mass i
  have weq := recovery inv w cw.mass i
  have peq := recovery inv pv (real_mass_of_rational_probability p pm) i
  change pv i=∑j,((pv ᵥ* R) j-1)*H j i at peq
  change u i=∑j,((u ᵥ* R) j-1)*H j i at ueq
  change w i=∑j,((w ᵥ* R) j-1)*H j i at weq
  simp only [cc] at peq
  have non : 0≤(c:ℝ)-1 := sub_nonneg.mpr (by exact_mod_cast high.le)
  change ((c:ℝ)-1)*(u i+w i)≤((q:ℝ)-1)*pv i
  rw [ueq,weq,peq,←sum_add_distrib,mul_sum,mul_sum]
  apply sum_le_sum
  intro j _
  nlinarith only [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (sumCap j) non) (inv.nonneg j i)]

#print axioms pack
#print axioms two_cuts
end LeanCH.BR.Closure.DisjointCutCapacity
