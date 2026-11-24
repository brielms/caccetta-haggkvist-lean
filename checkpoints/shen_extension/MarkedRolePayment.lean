import checkpoints.shen_extension.TriangleReachableRoles

namespace LeanCH.BR.Closure.MarkedRolePayment
open Finset BRq2 BRq3 BR45 WeightedSD ShortestCycleWeights PuncturedSquareRoles TriangleReachableRoles

/-- For an unmarked retained column only one positive marked parent in
each root role can contribute. If the three role maxima fit, the only
columns still to pay are the marked ones and the root itself. -/
theorem excludes {n} (X : Model 3 n) {h seed} (hv : h∈X.V)
    (minimum : ∀x∈X.V,X.weights h≤X.weights x) (large : 13≤X.V.card)
    (y : ℕ→ℚ) (m : Role→ℚ) (mn : ∀j,0≤m j) (yn : ∀x∈X.V,0≤y x)
    (live : ∃x∈X.V,0<y x)
    (uses : ∀x∈X.V,0<y x → x∈X.V\{h} ∧ Marked X.D (X.V\{h}) seed x ∧ y x≤m (role X.D h x))
    (spread : 3*(m .head + m .opposite + m .parent)≤mass X.V y)
    (root : 3*inW X.D X.V y h≤mass X.V y)
    (internal : ∀t∈X.V\{h},Marked X.D (X.V\{h}) seed t → col 3 X.D X.V y t≤mass X.V y) : False := by
  classical
  let W := X.V\{h}
  have fair (t) (tv : t∈X.V) : col 3 X.D X.V y t≤mass X.V y := by
    by_cases eq : t=h
    · subst t
      have z : y h=0 := le_antisymm (le_of_not_gt fun pos =>
        (mem_sdiff.mp (uses h hv pos).1).2 (mem_singleton_self h)) (yn h hv)
      simpa [col,z] using root
    have tw : t∈W := mem_sdiff.mpr ⟨tv,by simpa using eq⟩
    by_cases marked : Marked X.D W seed t
    · exact internal t tw marked
    have z : y t=0 := le_antisymm (le_of_not_gt fun pos => marked (uses t tv pos).2.1) (yn t tv)
    let f (j : Role) (x : ℕ) := if X.D x t=true ∧ role X.D h x=j then y x else 0
    have bound (j : Role) : (∑x∈X.V,f j x)≤m j := by
      by_cases existsPos : ∃p∈X.V,X.D p t=true ∧ role X.D h p=j ∧ 0<y p
      · obtain ⟨p,pv,pt,pj,yp⟩ := existsPos
        have only (x) (xv : x∈X.V) (ne : x≠p) : f j x=0 := by
          by_cases yes : X.D x t=true ∧ role X.D h x=j
          · have zero : y x=0 := le_antisymm (le_of_not_gt fun pos => marked
                (propagate X hv minimum large (uses p pv yp).2.1 (uses x xv pos).1 tw
                  ne.symm pt yes.1 (pj.trans yes.2.symm))) (yn x xv)
            simp [f,zero]
          · simp [f,yes]
        rw [sum_eq_single p only (fun no => (no pv).elim)]
        simpa [f,pt,pj] using (uses p pv yp).2.2
      · have none : ∀x∈X.V,f j x=0 := by
          intro x xv
          by_cases yes : X.D x t=true ∧ role X.D h x=j
          · have zero : y x=0 := le_antisymm (le_of_not_gt fun pos => existsPos ⟨x,xv,yes.1,yes.2,pos⟩) (yn x xv)
            simp [f,zero]
          · simp [f,yes]
        rw [sum_eq_zero none]
        exact mn j
    have split : inW X.D X.V y t=(∑x∈X.V,f .head x)+(∑x∈X.V,f .opposite x)+(∑x∈X.V,f .parent x) := by
      simp only [inW,←sum_add_distrib]
      apply sum_congr rfl
      intro x _
      cases e : role X.D h x <;> cases et : X.D x t <;> simp [f,e,et]
    have lim := add_le_add (add_le_add (bound .head) (bound .opposite)) (bound .parent)
    rw [←split] at lim
    change y t+3*inW X.D X.V y t≤_
    rw [z,zero_add]
    linarith
  let w := fun x => (X.weights x : ℚ)
  obtain ⟨x,xv,xp⟩ := live
  have lo := sum_lt_sum (s:=X.V) (f:=fun i => y i*mass X.V w) (g:=fun i => y i*WeightedSD.row 3 X.D X.V w i)
    (fun i iv => mul_le_mul_of_nonneg_left (X.strict i iv).le (yn i iv))
    ⟨x,xv,mul_lt_mul_of_pos_left (X.strict x xv) xp⟩
  rw [←sum_mul,rational_cross_rows] at lo
  have hi := sum_le_sum (s:=X.V) (fun z zv => mul_le_mul_of_nonneg_left (fair z zv) (show 0≤w z from Nat.cast_nonneg _))
  rw [←sum_mul] at hi
  change mass X.V y*mass X.V w<_ at lo
  change _≤mass X.V w*mass X.V y at hi
  rw [mul_comm] at hi
  exact lo.not_ge hi

/-- The explicit remaining supply test on the marked labels. -/
def Supply (D : CH.Digraph) (V : Finset ℕ) (w : ℕ→ℕ) : Prop :=
  ∃h∈V,(∀x∈V,w h≤w x) ∧ 13≤V.card ∧ ∃(seed : Finset ℕ) (y : ℕ→ℚ) (m : Role→ℚ),
    (∀j,0≤m j) ∧ (∀x∈V,0≤y x) ∧ (∃x∈V,0<y x) ∧
    (∀x∈V,0<y x → x∈V\{h} ∧ Marked D (V\{h}) seed x ∧ y x≤m (role D h x)) ∧
    3*(m .head+m .opposite+m .parent)≤mass V y ∧ 3*inW D V y h≤mass V y ∧
    ∀t∈V\{h},Marked D (V\{h}) seed t → col 3 D V y t≤mass V y

theorem for_capstone {q n} (X : Model q n) : q=3 → ¬Supply X.D X.V X.weights := by
  rintro rfl ⟨h,hv,minimum,large,seed,y,m,mn,yn,live,uses,spread,root,internal⟩
  exact excludes X hv minimum large y m mn yn live uses spread root internal

#print axioms for_capstone
#print axioms excludes
end LeanCH.BR.Closure.MarkedRolePayment
