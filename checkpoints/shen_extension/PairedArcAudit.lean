import checkpoints.shen_extension.RankedMerge
import LeanCH.BR.BRWeightedStrictAtomFloor

namespace LeanCH.BR.Closure.PairedArcAudit
open Finset BRq2 BRq3 BR45 WeightedSD ShortestCycleWeights

/-- Exact row test for the paired merge deleting the ends of an arc and using
the original flat weights and the surviving heads of its target. -/
theorem rows_iff {q D V} (hq : 2≤q) (free : QFree D V q)
    (small : SmallerSmallRow q V.card) (w : ℕ→ℚ) (pos : ∀i∈V,0<w i)
    {c : ℚ} (high : mass V w<c) (flat : ∀i∈V,WeightedSD.row q D V w i=c)
    {b a : V} (ba : D b a=true) :
    let U := (V.erase a.val).erase b.val
    let H := outN D U a
    let R := BRsub.ballSet D U H (q-2)
    let σ := c-mass V w
    let t := σ+w a-((q:ℚ)-1)*w b
    mass U w < q*mass H w ∧
    ((∀i∈R,mass U w<WeightedSD.row q D U w i ∧ ∀j∈U\R,
        mass U w≤((q:ℚ)-1)*(WeightedSD.row q D U w i-mass U w)+WeightedSD.row q D U w j) ↔
      0<t ∧ (∀j∈U,¬(D j a=true ∧ D j b=true)) ∧
        ((∃j∈U,D j a=true) → ((q:ℚ)-2)*w b≤σ)) := by
  classical
  intro U H R σ t
  have distinct : b.val≠a.val := fun eq => loopfree free (by omega) a.property (eq ▸ ba)
  have bv := mem_erase.mpr ⟨distinct,b.property⟩
  have us : U⊆V := (erase_subset _ _).trans (erase_subset _ _)
  have total (f : ℕ→ℚ) : (∑i∈V,f i)=(∑i∈U,f i)+f b+f a := by
    rw [sum_erase_add _ _ bv,sum_erase_add _ _ a.property]
  have wm : mass V w=mass U w+w b+w a := total w
  have split (i) : WeightedSD.row q D V w i=WeightedSD.row q D U w i+
      q*((if D i b=true then w b else 0)+(if D i a=true then w a else 0)) := by
    unfold WeightedSD.row outW
    rw [total]
    ring
  have qp : (0:ℚ)<q := by exact_mod_cast (show 0<q by omega)
  have coeff : 0≤(q:ℚ)-1 := by
    have : (2:ℚ)≤q := by exact_mod_cast hq
    linarith
  have pb := pos b b.property
  have aa : D a a=false := Bool.eq_false_iff.mpr (loopfree free (by omega) a.property)
  have ab : D a b=false := Bool.eq_false_iff.mpr (fun ed =>
    free b 2 (by decide) hq (.step a.property ba (.step b.property ed (.refl _))))
  constructor
  · have rowA := split a
    rw [flat a a.property,aa,ab] at rowA
    simp only [Bool.false_eq_true,ite_false,add_zero,mul_zero] at rowA
    dsimp [H]
    rw [WeightedSD.row,outW_eq_mass] at rowA
    linarith
  obtain ⟨i,ir,ib,ia,_,least,_⟩ := RankedMerge.arc_pair hq free small w pos
    (b:=b) (a:=a) (fun z zv _ => flat z zv ▸ high) ba
  have iu : i∈U := by obtain ⟨_,_,reach⟩ := BRsub.mem_ballSet.mp ir; exact (mem_ball.mp reach).1
  have inner : WeightedSD.row q D U w i-mass U w=t := by
    have e := split i
    rw [flat i (us iu),ib,ia] at e
    simp only [ite_true,Bool.false_eq_true,ite_false,add_zero] at e
    dsimp [t,σ]
    linarith
  have outside {j} (ju : j∈U) (ja : D j a=true) : j∈U\R := by
    refine mem_sdiff.mpr ⟨ju,?_⟩
    rintro hit
    obtain ⟨h,hh,reach⟩ := BRsub.mem_ballSet.mp hit
    obtain ⟨_,k,hk,p⟩ := mem_ball.mp reach
    have head := mem_outN.mp hh
    exact free a (k+1+1) (by omega) (by omega)
      (.step (us head.1) head.2 ((p.mono us).snoc a.property ja))
  have bill (j) (ju : j∈U) :
      ((q:ℚ)-1)*t+WeightedSD.row q D U w j-mass U w =
      if D j a=true then
        if D j b=true then q*(σ-((q:ℚ)-1)*w b) else q*(σ-((q:ℚ)-2)*w b)
      else if D j b=true then q*t else q*t+q*w b := by
    have e := split j
    rw [flat j (us ju)] at e
    cases eb : D j b <;> cases ea : D j a <;>
      simp only [eb,ea,Bool.false_eq_true,ite_false,ite_true,add_zero,zero_add,mul_zero] at e ⊢ <;>
      dsimp [t,σ] <;> linarith
  have floor := strict_atom_floor_of_proper hq free (small.induced free) w
    (fun z zv => (pos z zv).le) c high (fun z zv => (flat z zv).ge) b b.property
  change σ<((q:ℚ)-1)*w b at floor
  constructor
  · intro pays
    have it := pays i ir
    have nonneg {j} (jb : j∈U\R) : 0≤((q:ℚ)-1)*t+WeightedSD.row q D U w j-mass U w := by
      have e := it.2 j jb
      rw [inner] at e
      linarith
    refine ⟨by linarith [it.1],?_,?_⟩
    · rintro j ju ⟨ja,jb⟩
      have bad := nonneg (outside ju ja)
      rw [bill j ju,ite_eq_left ja,ite_eq_left jb] at bad
      exact (mul_neg_of_pos_of_neg qp (sub_neg.mpr floor)).not_ge bad
    · rintro ⟨j,ju,ja⟩
      have e := nonneg (outside ju ja)
      rw [bill j ju,ite_eq_left ja] at e
      split at e
      · exact False.elim ((mul_neg_of_pos_of_neg qp (sub_neg.mpr floor)).not_ge e)
      · exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left qp).mp e)
  · rintro ⟨positive,clean,threshold⟩ k kr
    have lower : t≤WeightedSD.row q D U w k-mass U w := by linarith [least k kr]
    refine ⟨by linarith,?_⟩
    intro j jr
    have ju := (mem_sdiff.mp jr).1
    have base : 0≤((q:ℚ)-1)*t+WeightedSD.row q D U w j-mass U w := by
      rw [bill j ju]
      by_cases ja : D j a=true
      · rw [ite_eq_left ja,ite_eq_right (fun jb => clean j ju ⟨ja,jb⟩)]
        exact mul_nonneg qp.le (sub_nonneg.mpr (threshold ⟨j,ju,ja⟩))
      · rw [ite_eq_right ja]
        split
        · exact mul_nonneg qp.le positive.le
        · exact add_nonneg (mul_nonneg qp.le positive.le) (mul_nonneg qp.le pb.le)
    linarith only [base,mul_le_mul_of_nonneg_left lower coeff]

#print axioms rows_iff
end LeanCH.BR.Closure.PairedArcAudit
