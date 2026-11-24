import checkpoints.shen_extension.FullFamilySchedule
import LeanCH.BR.BRWeightedDualCoverage

namespace LeanCH.BR.Closure.PairingPressure
open Finset BRq2 BRq3 BR45 WeightedSD ShenCycleSuccessor FullCycleTransfer

/-- Fix the two cycles before choosing the distribution. One distribution on
surviving rows detects every full pairing; the entire positive lower bound
is already due to rows outside the discarded cycle. -/
theorem uniform {q E V A M} (a : Cycle E V q A) (m : Cycle E V q M)
    (small : SmallRow q E (V\(A\M))) {x : ℕ→ℝ} (pos : ∀z∈V,0≤x z)
    {c : ℝ} (rows : ∀z∈V,c≤realRow q E V x z) :
    let U := V\(A\M)
    ∃ p : ℕ→ℝ, RealDual q E U 1 p ∧ ∀ P : Pairing E A M,
      let child := fun v => x v + P.deposit x v
      c-realMass V x ≤ ∑ b∈V\A,p b*(c-realRow q E U child b) := by
  classical
  intro U
  obtain ⟨z,zm⟩ := card_pos.mp (show 0<M.card by rw [m.size]; omega)
  have zu : z∈U := mem_sdiff.mpr ⟨m.sub zm,fun gone => (mem_sdiff.mp gone).2 zm⟩
  obtain ⟨p,hp⟩ := realDual_of_smallRow small ⟨z,zu⟩
  refine ⟨p,hp,?_⟩
  intro P child
  have dep (v) : 0≤P.deposit x v := by
    apply sum_nonneg
    intro y hy
    split_ifs <;> first | exact pos y (a.sub (mem_sdiff.mp hy).1) | exact le_rfl
  have bound := sum_le_sum (s:=U) (fun b bu => mul_le_mul_of_nonneg_left (hp.columns b bu)
    (show 0≤child b from add_nonneg (pos b (mem_sdiff.mp bu).1) (dep b)))
  simp only [mul_one] at bound
  change (∑z∈U,child z * realCol q E U p z) ≤ ∑z∈U,child z at bound
  rw [← real_cross_rows] at bound
  have massEq : (∑b∈U,child b)=realMass V x := P.mass_balance a m x
  rw [massEq] at bound
  have total : c-realMass V x ≤ ∑b∈U,p b*(c-realRow q E U child b) := by
    simp only [mul_sub,sum_sub_distrib,← sum_mul]
    change _ ≤ realMass U p*c-_
    rw [hp.normalized,one_mul]
    linarith
  have kept : V\A⊆U := fun b hb => mem_sdiff.mpr ⟨(mem_sdiff.mp hb).1,
    fun del => (mem_sdiff.mp hb).2 (mem_sdiff.mp del).1⟩
  have nonpos : ∀b∈U\(V\A),p b*(c-realRow q E U child b)≤0 := by
    intro b hb
    obtain ⟨bu,out⟩ := mem_sdiff.mp hb
    have bv := (mem_sdiff.mp bu).1
    have ba : b∈A := by_contra fun no => out (mem_sdiff.mpr ⟨bv,no⟩)
    have bm : b∈M := by_contra fun no => (mem_sdiff.mp bu).2 (mem_sdiff.mpr ⟨ba,no⟩)
    have cover (y) (yd : y∈A\M) (hit : E b y=true) : E b (P.label y)=true := by
      rw [P.label_apply (mem_sdiff.mp yd).1]
      exact P.successor b (mem_inter.mpr ⟨ba,bm⟩) _ hit
    have heads := P.covered_heads a m x (fun y hy => pos y (a.sub (mem_sdiff.mp hy).1)) b cover
    have paid : realRow q E V x b ≤ realRow q E U child b :=
      add_le_add (le_add_of_nonneg_right (dep b)) (mul_le_mul_of_nonneg_left heads (Nat.cast_nonneg q))
    exact mul_nonpos_of_nonneg_of_nonpos (hp.nonneg b bu) (sub_nonpos.mpr ((rows b bv).trans paid))
  have part := sum_sdiff kept (f:=fun b => p b*(c-realRow q E U child b))
  linarith only [total,part,sum_nonpos nonpos]

/-- The exterior rows alone carry a probability law, fixed before choosing
the matching. Its expected child score is at most the original mass. -/
theorem exterior {q E V A M} (a : Cycle E V q A) (m : Cycle E V q M)
    (small : SmallRow q E (V\(A\M))) {x : ℕ→ℝ} (pos : ∀z∈V,0≤x z)
    {c : ℝ} (high : realMass V x<c) (rows : ∀z∈V,c≤realRow q E V x z) :
    ∃ law : ℕ→ℝ, (∀b∈V\A,0≤law b) ∧ realMass (V\A) law=1 ∧
      ∀ P : Pairing E A M, (∑b∈V\A,law b*realRow q E (V\(A\M)) (fun v => x v+P.deposit x v) b) ≤
        realMass V x := by
  classical
  obtain ⟨p,hp,bill⟩ := uniform a m small pos rows
  let T := V\A
  let d := realMass T p
  have sub : T⊆V\(A\M) := fun b hb => mem_sdiff.mpr ⟨(mem_sdiff.mp hb).1,
    fun del => (mem_sdiff.mp hb).2 (mem_sdiff.mp del).1⟩
  have nonneg (b) (bt : b∈T) := hp.nonneg b (sub bt)
  have le : d≤1 := hp.normalized ▸ sum_le_sum_of_subset_of_nonneg sub (fun b bu _ => hp.nonneg b bu)
  have dpos : 0<d := by
    by_contra! fail
    have zero (b) (bt : b∈T) : p b=0 :=
      le_antisymm ((single_le_sum nonneg bt).trans fail) (nonneg b bt)
    obtain ⟨P⟩ := exists_pairing a m
    have tmp := bill P
    have vanish : (∑b∈T,p b*(c-realRow q E (V\(A\M)) (fun v => x v+P.deposit x v) b))=0 :=
      sum_eq_zero (fun b bt => by rw [zero b bt,zero_mul])
    linarith only [tmp,vanish,high]
  refine ⟨fun b => p b/d,fun b bt => div_nonneg (nonneg b bt) dpos.le,?_,?_⟩
  · change (∑b∈T,p b/d)=1
    rw [←sum_div]
    exact div_self dpos.ne'
  · intro P
    let R := fun b => realRow q E (V\(A\M)) (fun v => x v+P.deposit x v) b
    have h := bill P
    change c-realMass V x ≤ ∑b∈T,p b*(c-R b) at h
    simp only [mul_sub,sum_sub_distrib,←sum_mul] at h
    change c-realMass V x ≤ d*c-_ at h
    change (∑b∈T,p b/d*R b)≤realMass V x
    simp only [div_mul_eq_mul_div,←sum_div]
    apply (div_le_iff₀ dpos).mpr
    nlinarith only [h,mul_nonneg (sub_nonneg.mpr le) (sub_nonneg.mpr high.le)]

#print axioms exterior

/-- The concrete supplier in the capstone. It retains the same rational
equalizer and the same two named cycles that are used for the label orbit. -/
theorem on_family {q n} (X : ShortestCycleWeights.Model q n)
    (small : SmallerSmallRow q X.V.card) {F A M x c}
    (sub : F⊆FirstPacketBarrier.family X) (af : A∈F) (mf : M∈F) (diff : A≠M)
    (pos : ∀z∈X.V,0≤x z) (high : mass X.V x<c)
    (rows : ∀z∈X.V,WeightedSD.row q (FirstPacketBarrier.graph X.D F) X.V x z=c) :
    let E := FirstPacketBarrier.graph X.D F
    let w := fun z => (x z : ℝ)
    ∃ law : ℕ→ℝ, (∀b∈X.V\A,0≤law b) ∧ realMass (X.V\A) law=1 ∧
      ∀ P : Pairing E A M, (∑b∈X.V\A,law b*realRow q E (X.V\(A\M)) (fun z => w z+P.deposit w z) b) ≤
        (mass X.V x : ℝ) := by
  classical
  intro E w
  have actual (C) (cf : C∈F) : Cycle E X.V q C := FirstPacketBarrier.retain_cycle
    (show Cycle X.D X.V q C from (mem_filter.mp (sub cf)).2) cf
  have a := actual A af
  have m := actual M mf
  have gone : (A\M).Nonempty := by
    by_contra! empty
    exact diff (eq_of_subset_of_card_le (sdiff_eq_empty_iff_subset.mp empty) (by rw [a.size,m.size]))
  obtain ⟨z,zd⟩ := gone
  have proper : X.V\(A\M)≠X.V := by
    intro eq
    have keep : z∈X.V\(A\M) := by rw [eq]; exact a.sub (mem_sdiff.mp zd).1
    exact (mem_sdiff.mp keep).2 zd
  have cut := small.induced (PrivateArcEndpoints.graph_free X F) _ sdiff_subset proper
  have wt : realMass X.V w=(mass X.V x : ℝ) := realMass_rat _ _
  rw [←wt]
  apply exterior a m cut (c:=(c : ℝ))
  · intro v vv; change (0:ℝ)≤(x v : ℝ); exact_mod_cast pos v vv
  · rw [wt]; exact_mod_cast high
  · intro v vv; rw [realRow_rat,rows v vv]

#print axioms on_family

#print axioms uniform
end LeanCH.BR.Closure.PairingPressure
