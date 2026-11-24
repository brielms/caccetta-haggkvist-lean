import checkpoints.shen_extension.MandatoryTwoStep

namespace LeanCH.BR.Closure.ComparableColumnCut
open Finset BRq2 BRq3 BR45 ShenPrimeTransition ShenCycleSuccessor ShortestCycleWeights MandatoryTwoStep

/-- If u forces v then a fixed row cannot point to both. The cycle for the
actual arc into u supplies the row that would have two internal heads. -/
theorem distinct_heads {q n} (X : Model q n) (hq : 2≤q) {p u v}
    (pv : p∈X.V) (uv : u∈X.V) (pu : X.D p u=true) (pv' : X.D p v=true)
    (forces : Forces X.D X.V q u v) : u=v := by
  obtain ⟨C,c,pc,uc⟩ := edge_cycle X hq pv uv pu
  exact card_le_one.mp (c.heads p pc).le _ (mem_outN.mpr ⟨uc,pu⟩) _
    (mem_outN.mpr ⟨forces C c uc,pv'⟩)

/-- Deleting any proper nonempty chain of cycle-incidence columns forces a
particular outside parent to lose its unique head in the chain. Its exact
old surplus and the entire deleted mass fit inside q times that head's weight. -/
theorem blocking_parent {q n} (X : Model q n) (hq : 2≤q) {K : Finset ℕ}
    (sub : K⊆X.V) (live : K.Nonempty) (proper : K≠X.V)
    (chain : ∀u∈K,∀v∈K, Forces X.D X.V q u v ∨ Forces X.D X.V q v u) :
    ∃p∈X.V\K,∃x∈K, outN X.D K p={x} ∧
      score q X.D X.V X.weights p+(∑z∈K,X.weights z) ≤ (∑z∈X.V,X.weights z)+q*X.weights x ∧
      (∑z∈K,X.weights z)<q*X.weights x := by
  classical
  let U := X.V\K
  have uu : U⊆X.V := sdiff_subset
  have ulive : U.Nonempty := sdiff_nonempty.mpr (fun back => proper (Subset.antisymm sub back))
  have sm : U.card<X.V.card := by
    have e := card_sdiff_add_card_eq_card sub
    have pos := card_pos.mpr live
    dsimp [U]; omega
  have fail : ¬Strict q X.D U X.weights := fun strict => sm.not_ge
    (X.minimal X.D U X.weights ulive (X.free.mono_set uu) (fun z hz => X.positive z (uu hz))
    ((sum_le_sum_of_subset_of_nonneg uu (by intros; omega)).trans X.bounded) strict)
  rw [nat_strict] at fail
  push Not at fail
  obtain ⟨p,pu,low⟩ := fail
  have pv := uu pu
  have high := nat_strict.mp X.strict p pv
  have mass := sum_sdiff sub (f:=X.weights)
  have tab := sum_sdiff sub (f:=fun z => if X.D p z=true then X.weights z else 0)
  have rows : score q X.D X.V X.weights p=score q X.D U X.weights p+q*(∑z∈outN X.D K p,X.weights z) := by
    simp only [outN,sum_filter,score,U]
    rw [←tab,Nat.mul_add]
    omega
  have bound : score q X.D X.V X.weights p+(∑z∈K,X.weights z)≤(∑z∈X.V,X.weights z)+q*(∑z∈outN X.D K p,X.weights z) := by
    change (∑z∈U,X.weights z)+(∑z∈K,X.weights z)=_ at mass
    omega
  have hot := lt_of_not_ge (show ¬q*(∑z∈outN X.D K p,X.weights z)≤(∑z∈K,X.weights z) by omega)
  have pos : (outN X.D K p).Nonempty := by
    by_contra empty
    rw [not_nonempty_iff_eq_empty.mp empty,sum_empty,Nat.mul_zero] at hot
    omega
  obtain ⟨x,xk⟩ := pos
  obtain ⟨xm,px⟩ := mem_outN.mp xk
  have one : outN X.D K p={x} := by
    ext z
    constructor
    · intro zk
      obtain ⟨zm,pz⟩ := mem_outN.mp zk
      apply mem_singleton.mpr
      rcases chain z zm x xm with f | f
      · exact distinct_heads X hq pv (sub zm) pz px f
      · exact (distinct_heads X hq pv (sub xm) px pz f).symm
    · intro eq
      exact mem_singleton.mp eq ▸ xk
  exact ⟨p,pu,x,xm,one,by simpa [one] using bound,by simpa [one] using hot⟩

/-- Comparable labels cannot share a head either, since each cycle has
only one internal parent at that head. -/
theorem distinct_parents {q n} (X : Model q n) (hq : 2≤q) {p u v}
    (pv : p∈X.V) (uv : u∈X.V) (up : X.D u p=true) (vp : X.D v p=true)
    (forces : Forces X.D X.V q u v) : u=v := by
  obtain ⟨C,c,uc,pc⟩ := edge_cycle X hq uv pv up
  exact card_le_one.mp (c.incoming p pc).le _ (mem_inN.mpr ⟨uc,up⟩) _
    (mem_inN.mpr ⟨forces C c uc,vp⟩)

/-- A chain of distinct labels in the cycle-incidence preorder has at most
q members, counting equal columns as well as strict inclusions. -/
theorem chain_size {q n} (X : Model q n) (hq : 2≤q) {K : Finset ℕ}
    (sub : K⊆X.V)
    (chain : ∀u∈K,∀v∈K, Forces X.D X.V q u v ∨ Forces X.D X.V q v u) : K.card≤q := by
  classical
  by_contra! large
  have nonempty := card_pos.mp (show 0<K.card by omega)
  let M := ∑z∈X.V,X.weights z
  have incoming (z) (zv : z∈X.V) : (inN X.D K z).card≤1 := by
    apply card_le_one.mpr
    intro x xi y yi
    obtain ⟨xk,xz⟩ := mem_inN.mp xi
    obtain ⟨yk,yz⟩ := mem_inN.mp yi
    rcases chain x xk y yk with f|f
    · exact distinct_parents X hq zv (sub xk) xz yz f
    · exact (distinct_parents X hq zv (sub yk) yz xz f).symm
  have table : (∑x∈K,∑z∈X.V,if X.D x z=true then X.weights z else 0)≤M := by
    rw [sum_comm]
    apply sum_le_sum
    intro z zv
    calc
      _ = ∑_x∈inN X.D K z,X.weights z := by simp only [inN,sum_filter]
      _ = (inN X.D K z).card*X.weights z := by simp
      _ ≤ X.weights z := by simpa using Nat.mul_le_mul_right (X.weights z) (incoming z zv)
  have high := sum_lt_sum_of_nonempty nonempty (fun x hx => nat_strict.mp X.strict x (sub hx))
  change (∑_x∈K,M)<_ at high
  simp only [sum_const,nsmul_eq_mul,score,sum_add_distrib,←mul_sum] at high
  have diag : (∑x∈K,X.weights x)≤M := sum_le_sum_of_subset_of_nonneg sub (by intros; omega)
  have upper := Nat.add_le_add diag (Nat.mul_le_mul_left q table)
  have lower := Nat.mul_le_mul_right M (show q+1≤K.card by omega)
  apply lower.not_gt
  calc
    K.card*M < _ := high
    _ ≤ M+q*M := upper
    _ = (q+1)*M := by rw [Nat.succ_mul,Nat.add_comm]

/-- A sequence of failed punctures following descending cycle columns can
visit at most q distinct labels. The bound does not involve the input order. -/
theorem orbit_bound {q n} (X : Model q n) (hq : 2≤q) (f : ℕ→ℕ)
    (inside : ∀i,f i∈X.V) (step : ∀i,Forces X.D X.V q (f (i+1)) (f i)) (length : ℕ) :
    ((range length).image f).card≤q := by
  have follows (i j : ℕ) (order : i≤j) : Forces X.D X.V q (f j) (f i) := by
    induction j, order using Nat.le_induction with
    | base => exact fun _ _ hit => hit
    | succ j _ ih => exact fun C c hit => ih C c (step j C c hit)
  apply chain_size X hq
  · intro v vi
    obtain ⟨i,_,rfl⟩ := mem_image.mp vi
    exact inside i
  · intro v vi w wi
    obtain ⟨i,_,rfl⟩ := mem_image.mp vi
    obtain ⟨j,_,rfl⟩ := mem_image.mp wi
    rcases le_total i j with ord | ord
    · exact Or.inr (follows i j ord)
    · exact Or.inl (follows j i ord)

#print axioms chain_size
#print axioms orbit_bound
#print axioms blocking_parent
end LeanCH.BR.Closure.ComparableColumnCut
