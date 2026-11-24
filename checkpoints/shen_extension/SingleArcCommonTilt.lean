import checkpoints.shen_extension.SingleArcCycleSparse
import checkpoints.shen_extension.CycleHitMass

namespace LeanCH.BR.Closure.SingleArcCommonTilt
open Finset BRq2 BRq3 BR45 WeightedSD FiniteCutInverse ShenCycleSuccessor
open SingleArcCycleBalance SingleArcCycleSlope ShortestCycleWeights FirstPacketBarrier MarkedCyclePeeling

def hits (E : CH.Digraph) (C : Finset ℕ) (i : ℕ) : Finset C := univ.filter (fun j=>E i j=true)

/-- The normalized parameter is zero unless an outside vertex hits
only the second successor of v, and that receiver needs a payment. -/
noncomputable def threshold (q : ℕ) (E : CH.Digraph) (V C : Finset ℕ) (a v r : C) (x : ℝ) : ℝ := by
  classical
  exact if ∃i∈V \ C,hits E C i={r} then max 0 (-score q {r} (tiltedPrices q E a v 1 x)/((q:ℝ)*x)) else 0

private theorem scale_iff {q : ℕ} (hq : 2≤q) {E V C} (cy : Cycle E V q C) (a v : C) (av : E a v=true)
    (x t u : ℝ) (t1 : 1≤t) (scale : u*((q:ℝ)+t)=t-1) (N : Finset C) :
    0≤score q N (tiltedPrices q E a v t x) ↔ 0≤score q N (tiltedPrices q E a v 1 x)+u*slope q N v x := by
  have qp : (0:ℝ)<q := by exact_mod_cast (by omega : 0<q)
  have eq := score_change hq cy a v av t x N
  have ratio : ((q:ℝ)+1)*score q N (tiltedPrices q E a v t x)=
      ((q:ℝ)+t)*(score q N (tiltedPrices q E a v 1 x)+u*slope q N v x) := by
    linear_combination eq - slope q N v x * scale
  constructor
  · intro pos
    exact nonneg_of_mul_nonneg_right (ratio ▸ mul_nonneg (by linarith) pos) (by linarith : 0<(q:ℝ)+t)
  · intro pos
    exact nonneg_of_mul_nonneg_right (ratio.symm ▸ mul_nonneg (by linarith) pos) (by linarith : 0<(q:ℝ)+1)

/-- Existence of a common parameter on this cycle is equivalent to
checking the multi-hit rows at one explicitly selected parameter.
The same parameter always pays all zero-hit and one-hit rows. -/
theorem exact_test {q E V C} (hq : 2≤q) (free : QFree E V q) (cy : Cycle E V q C)
    (a v s r : C) (av : E a v=true) (vs : E v s=true) (sr : E s r=true)
    (heir : ∀i∈V \ C,E i v=true → E i a=true) (x : ℝ) (heavy : 1<((q:ℝ)-1)*x) :
    let u := threshold q E V C a v r x
    let t₀ := (1+(q:ℝ)*u)/(1-u)
    let F (i : ℕ) (t : ℝ) := score q (hits E C i) (tiltedPrices q E a v t x)
    0≤u ∧ u<1/(q:ℝ) ∧ 1≤t₀ ∧
      (∀i∈V \ C,(hits E C i).card≤1 → 0≤F i t₀) ∧
      ((∃t : ℝ,1≤t ∧ ∀i∈V \ C,0≤F i t) ↔
        ∀i∈V \ C,2≤(hits E C i).card → 0≤F i t₀) := by
  classical
  intro u t₀ F
  let Q := (q:ℝ)
  let z := tiltedPrices q E a v 1 x
  let b := score q {r} z
  let need := -b/(Q*x)
  have two : 2≤Q := by dsimp [Q]; exact_mod_cast hq
  have qp : 0<Q := by linarith
  have xp : 0<x := pos_of_mul_pos_right (zero_lt_one.trans heavy) (by change 0≤Q-1; linarith)
  have dpos := mul_pos qp xp
  have rv : r≠v := by rintro rfl; exact free r 2 (by omega) hq (.step (cy.sub s.property) vs (.step (cy.sub r.property) sr (.refl _)))
  have va : v≠a := by rintro rfl; exact loopfree free (by omega) (cy.sub v.property) av
  obtain ⟨empty,simple,corr,_,_,_⟩ := SingleArcCycleSparse.sparse hq free cy a v s r av vs sr x heavy
  have need_lt : need<1/Q := by
    have br : 0<b+x := corr r rv
    apply (div_lt_iff₀ dpos).mpr
    have ident : (1/Q)*(Q*x)=x := by field_simp
    linarith only [br,ident]
  let P := ∃i∈V \ C,hits E C i={r}
  have ue : u=if P then max 0 need else 0 := by rfl
  have up : 0≤u := by rw [ue]; split <;> first | exact le_max_left .. | exact le_rfl
  have lt : u<1/Q := by
    rw [ue]; split
    · exact max_lt_iff.mpr ⟨div_pos zero_lt_one qp,need_lt⟩
    · exact div_pos zero_lt_one qp
  have lt1 : u<1 := lt.trans_le ((div_le_iff₀ qp).mpr (by linarith))
  have den : 0<1-u := by linarith
  have t1 : 1≤t₀ := by
    apply (le_div_iff₀ den).mpr
    nlinarith only [up,mul_nonneg qp.le up]
  have scaled : u*(Q+t₀)=t₀-1 := by dsimp [t₀,Q]; field_simp [den.ne']; ring
  have at0 (i : ℕ) : 0≤F i t₀ ↔ 0≤F i 1+u*slope q (hits E C i) v x :=
    scale_iff hq cy a v av x t₀ u t1 scaled _
  have slopeOne (j : C) (jv : j≠v) : slope q {j} v x=Q*x :=
    (signs hq heavy {j} v).2.1 (card_singleton j) (by simpa using jv.symm)
  have sparse (i) (ic : i∈V \ C) (few : (hits E C i).card≤1) : 0≤F i t₀ := by
    apply (at0 i).mpr
    change 0≤score q (hits E C i) z+u*slope q (hits E C i) v x
    by_cases no : hits E C i=∅
    · rw [no]
      exact add_nonneg empty.le (mul_nonneg up ((signs hq heavy ∅ v).1 rfl).le)
    obtain ⟨j,hj⟩ := card_eq_one.mp (by have := card_pos.mpr (nonempty_iff_ne_empty.mpr no); omega : (hits E C i).card=1)
    have jv : j≠v := by
      rintro rfl
      have ij : E i j=true := (mem_filter.mp (hj ▸ mem_singleton_self j : j∈hits E C i)).2
      have ia : a∈hits E C i := mem_filter.mpr ⟨mem_univ _,heir i ic ij⟩
      rw [hj,mem_singleton] at ia
      exact va ia.symm
    rw [hj,slopeOne j jv]
    by_cases jr : j=r
    · subst j
      have pu : P := ⟨i,ic,hj⟩
      have lo : need≤u := by rw [ue,ite_eq_left pu]; exact le_max_right .. 
      have val := (div_le_iff₀ dpos).mp lo
      change 0≤b+u*(Q*x); linarith only [val]
    · exact add_nonneg (simple j jv jr).le (mul_nonneg up dpos.le)
  refine ⟨up,lt,t1,sparse,?_,?_⟩
  · rintro ⟨t,t1',pay⟩
    let y := (t-1)/(Q+t)
    have denom : 0<Q+t := by linarith
    have yp : 0≤y := div_nonneg (sub_nonneg.mpr t1') denom.le
    have yscale : y*(Q+t)=t-1 := div_mul_cancel₀ _ denom.ne'
    have atY (i) (ic : i∈V \ C) : 0≤F i 1+y*slope q (hits E C i) v x :=
      (scale_iff hq cy a v av x t y t1' yscale _).mp (pay i ic)
    have le : u≤y := by
      rw [ue]; split_ifs with needRow
      · obtain ⟨i,ic,hit⟩ := needRow
        have cost := atY i ic
        change 0≤score q (hits E C i) z+y*slope q (hits E C i) v x at cost
        rw [hit,slopeOne r rv] at cost
        apply max_le yp ((div_le_iff₀ dpos).mpr ?_)
        change -b≤y*(Q*x)
        linarith only [cost]
      · exact yp
    intro i ic many
    apply (at0 i).mpr
    have neg := (signs hq heavy (hits E C i) v).2.2 many
    linarith only [atY i ic,mul_le_mul_of_nonpos_right le neg.le]
  · intro dense
    exact ⟨t₀,t1,fun i ic=>by
      by_cases few : (hits E C i).card≤1
      · exact sparse i ic few
      · exact dense i ic (by omega)⟩

end LeanCH.BR.Closure.SingleArcCommonTilt
#print axioms LeanCH.BR.Closure.SingleArcCommonTilt.exact_test
