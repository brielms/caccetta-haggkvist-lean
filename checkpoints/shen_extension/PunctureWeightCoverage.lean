import checkpoints.shen_extension.PunctureBypass
import checkpoints.shen_extension.RootedSplice

namespace LeanCH.BR.Closure.PunctureWeightCoverage
open Finset BRq2 BRq3 BR45 ShenPrimeTransition ShortestCycleWeights RootedSplice

theorem flow_floor {q n} (X : Model q n) {h t k} (tv : t∈X.V)
    (minimum : ∀z∈X.V,X.weights h≤X.weights z) (size : q*k+1≤X.V.card) :
    k*X.weights h < ∑z∈outN X.D X.V t,X.weights z := by
  have e := card_erase_add_one tv
  have count : q*k≤(X.V.erase t).card := by omega
  have low := sum_le_sum (s:=X.V.erase t) (fun z hz => minimum z (mem_of_mem_erase hz))
  simp only [sum_const,nsmul_eq_mul] at low
  have a := (Nat.mul_le_mul_right (X.weights h) count).trans low
  have m := sum_erase_add X.V X.weights tv
  have orig := nat_strict.mp X.strict t tv
  have head : score q X.D X.V X.weights t =
      X.weights t+q*(∑z∈outN X.D X.V t,X.weights z) := by simp only [score,outN,sum_filter]
  rw [head] at orig
  rw [Nat.mul_assoc] at a
  exact Nat.lt_of_mul_lt_mul_left (show q*(k*X.weights h)<_ by omega)

private theorem single_weight {W : Finset ℕ} {w : ℕ→ℕ} {a}
    (one : ∀z∈W,z=a) : (∑z∈W,w z)≤w a := by
  classical
  have sub : W⊆{a} := fun z zw => mem_singleton.mpr (one z zw)
  simpa using sum_le_sum_of_subset_of_nonneg (f:=w) sub (by intros; omega)

theorem parent_covered {q n} (X : Model q n) (hq : 2≤q) {h t}
    (tw : t∈X.V.erase h) (minimum : ∀z∈X.V,X.weights h≤X.weights z)
    (size : q+1≤X.V.card) (th : X.D t h=true) : Covered X.D X.V q h t := by
  by_contra absent
  have a := flow_floor X (mem_of_mem_erase tw) minimum (k:=1) (by simpa using size)
  have b := single_weight (w:=X.weights) (W:=outN X.D X.V t) (a:=h) (fun z zh =>
    sole_head X hq tw (mem_outN.mp zh).1 th (mem_outN.mp zh).2 absent)
  simp only [one_mul] at a
  omega

theorem heavy_covered {q n} (X : Model q n) (hq : 2≤q) {h t}
    (hv : h∈X.V) (tw : t∈X.V.erase h) (minimum : ∀z∈X.V,X.weights h≤X.weights z)
    (size : q*(q-1)+1≤X.V.card) (heavy : (q-1)*X.weights h≤X.weights t) :
    Covered X.D X.V q h t := by
  by_contra absent
  have large := Nat.le_mul_of_pos_right q (show 0<q-1 by omega)
  have th : X.D t h=false := Bool.eq_false_iff.mpr (fun yes =>
    absent (parent_covered X hq tw minimum (by omega) yes))
  have tv := mem_of_mem_erase tw
  have tt := loopfree X.free (by omega : 1≤q) tv
  have same : outN X.D ((X.V.erase h).erase t) t=outN X.D X.V t := by
    ext z
    simp only [mem_outN,mem_erase]
    constructor
    · rintro ⟨⟨_,_,zv⟩,tz⟩
      exact ⟨zv,tz⟩
    · rintro ⟨zv,tz⟩
      exact ⟨⟨(fun e => tt (e ▸ tz)),(fun e => by subst z; simp [th] at tz),zv⟩,tz⟩
  apply PunctureBypass.cannot_pay X hq hv tw absent _ _ heavy
  · intro p pu pt y yh
    exact missing_arc X hq tw (mem_of_mem_erase (mem_of_mem_erase pu))
      (mem_of_mem_erase (mem_of_mem_erase (mem_outN.mp yh).1)) pt (mem_outN.mp yh).2 absent
  · rw [same]
    exact (flow_floor X tv minimum size).le

theorem head_covered {q n} (X : Model q n) (hq : 2≤q) {h t}
    (hv : h∈X.V) (tw : t∈X.V.erase h) (minimum : ∀z∈X.V,X.weights h≤X.weights z)
    (size : q*(q-1)+1≤X.V.card) (ht : X.D h t=true) : Covered X.D X.V q h t := by
  by_contra absent
  have b := single_weight (w:=X.weights) (W:=outN X.D X.V h) (a:=t) (fun z zh => by
    by_contra ne
    obtain ⟨p,pv,pt,pz⟩ := X.separated t (mem_of_mem_erase tw) z (mem_outN.mp zh).1 ne
    obtain rfl := sole_parent X hq tw pv ht pt absent
    have arc := (mem_outN.mp zh).2
    rw [pz] at arc
    contradiction)
  exact absent (heavy_covered X hq hv tw minimum size ((flow_floor X hv minimum size).le.trans b))

#print axioms parent_covered
#print axioms heavy_covered
#print axioms head_covered
end LeanCH.BR.Closure.PunctureWeightCoverage
