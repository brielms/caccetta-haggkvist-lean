import checkpoints.shen_extension.ShortestCycleFiberModule

namespace LeanCH.BR.Closure.AnchoredExteriorColumn
open Finset BRq2 BRq3 BR45 ShenCycleSuccessor ShenPrimeTransition ShortestCycleWeights

private theorem aggregate (q : ℕ) (D : CH.Digraph) (V A : Finset ℕ) (av : A⊆V) (w : ℕ→ℕ) :
    (∑x∈A,score q D V w x) =
      ∑z∈V,((if z∈A then 1 else 0)+q*(inN D A z).card)*w z := by
  classical
  have tab : (∑x∈A,∑z∈V,if D x z=true then w z else 0)=∑z∈V,(inN D A z).card*w z := by
    rw [sum_comm]
    apply sum_congr rfl
    intro z _
    calc
      _ = ∑_x∈inN D A z,w z := by simp only [inN,sum_filter]
      _ = _ := by simp
  have diag : (∑z∈V,(if z∈A then 1 else 0)*w z)=∑z∈A,w z := by
    simp only [ite_mul,one_mul,zero_mul,←sum_filter]
    congr 1
    ext z
    exact ⟨fun t => (mem_filter.mp t).2,fun t => mem_filter.mpr ⟨av t,t⟩⟩
  simp only [score,sum_add_distrib,←mul_sum,tab,Nat.add_mul,diag,Nat.mul_assoc]

/-- The path and moving cycle balance all their internal columns. Strict
rows in the original graph force a joint overload on an exterior column. -/
theorem exterior_mass {q n} (X : Model q n) (hq : 2≤q) {W P S : Finset ℕ} (wv : W⊆X.V)
    (ps : P.card=q) (dis : Disjoint P S) (cs : Cycle X.D W q S)
    (fits : ∀x∈S,Cycle X.D W q (insert x P)) :
    let E := X.V\(P∪S)
    (q+1)^2*(∑z∈E,X.weights z) <
      q*(∑z∈E,((q+1)*(inN X.D P z).card+(inN X.D S z).card)*X.weights z) := by
  classical
  intro E
  let k := q+1
  have sz := cs.size
  obtain ⟨x0,s0⟩ := card_pos.mp (show 0<S.card by omega)
  have pv : P⊆X.V := fun _ hp => wv ((fits x0 s0).sub (mem_insert_of_mem hp))
  have sv := cs.sub.trans wv
  let K (A : Finset ℕ) (z : ℕ) := (if z∈A then 1 else 0)+q*(inN X.D A z).card
  let load (z : ℕ) := k*K P z+K S z
  have rowSum (A : Finset ℕ) (sub : A⊆X.V) (live : A.Nonempty) :
      A.card*(∑z∈X.V,X.weights z) < ∑z∈X.V,K A z*X.weights z := by
    rw [←aggregate q X.D X.V A sub X.weights]
    simpa using sum_lt_sum_of_nonempty live (fun x hx => nat_strict.mp X.strict x (sub hx))
  have pa := rowSum P pv (card_pos.mp (by omega))
  have sa := rowSum S sv ⟨x0,s0⟩
  have high : k*k*(∑z∈X.V,X.weights z)<∑z∈X.V,load z*X.weights z := by
    have big := Nat.add_lt_add (Nat.mul_lt_mul_of_pos_left pa (show 0<k by dsimp [k]; omega)) sa
    rw [ps,sz] at big
    calc
      _ = k*(q*(∑z∈X.V,X.weights z)) + (q+1)*(∑z∈X.V,X.weights z) := by dsimp [k]; ring
      _ < _ := big
      _ = _ := by simp only [load,Nat.add_mul,Nat.mul_assoc,sum_add_distrib,←mul_sum]
  have count (x) (xs : x∈S) (t) : (inN X.D (insert x P) t).card =
      (inN X.D P t).card+(if X.D x t=true then 1 else 0) := by
    have xp : x∉P := fun h => disjoint_left.mp dis h xs
    by_cases arc : X.D x t=true
    · have xn : x∉inN X.D P t := fun h => xp (mem_inN.mp h).1
      simp only [inN,filter_insert,arc,ite_true]
      exact card_insert_of_notMem xn
    · simp [inN,filter_insert,arc]
  have col (z) (zu : z∈P∪S) : load z=k*k := by
    rcases mem_union.mp zu with zp | zs
    ·
      have each (x) (xs : x∈S) : (inN X.D P z).card+(if X.D x z=true then 1 else 0)=1 := by
        rw [←count x xs z]; exact (fits x xs).incoming z (mem_insert_of_mem zp)
      have tot := sum_congr rfl (s₁:=S) (fun x hx => each x hx)
      simp only [sum_add_distrib,sum_const,nsmul_eq_mul,sum_boole,mul_one] at tot
      change S.card*(inN X.D P z).card+(inN X.D S z).card=S.card at tot
      rw [sz] at tot
      have zs : z∉S := fun h => disjoint_left.mp dis zp h
      simp only [load,K,zp,zs,ite_true,ite_false,zero_add]
      dsimp [k]
      nlinarith only [congrArg (fun m : ℕ => q*m) tot]
    · have zv := sv zs
      have zP : z∉P := fun zp => disjoint_left.mp dis zp zs
      have no : X.D z z=false := Bool.eq_false_iff.mpr (loopfree X.free (by omega) zv)
      have r : (inN X.D (insert z P) z).card=1 := (fits z zs).incoming z (mem_insert_self _ _)
      rw [count z zs z] at r
      simp [no] at r
      have j : (inN X.D S z).card=1 := cs.incoming z zs
      simp only [load,K,zP,zs,ite_false,ite_true,zero_add,r,j,Nat.mul_one]
      dsimp [k]
      nlinarith
  have rest (z) (ze : z∈E) : load z=q*((q+1)*(inN X.D P z).card+(inN X.D S z).card) := by
    have ep : z∉P := fun zp => (mem_sdiff.mp ze).2 (mem_union_left _ zp)
    have es : z∉S := fun zs => (mem_sdiff.mp ze).2 (mem_union_right _ zs)
    simp only [load,K,ep,es,ite_false,zero_add,k]
    ring
  have sub := union_subset pv sv
  have total := sum_sdiff sub (f:=X.weights)
  have byCol := sum_sdiff sub (f:=fun z => load z*X.weights z)
  rw [←total,←byCol,Nat.mul_add] at high
  rw [sum_congr rfl (fun z (hz : z∈P∪S) => congrArg (·*X.weights z) (col z hz)),←mul_sum] at high
  have ext := Nat.lt_of_add_lt_add_right high
  change k*k*(∑z∈E,X.weights z)<∑z∈E,load z*X.weights z at ext
  rw [sum_congr rfl (fun z hz => congrArg (·*X.weights z) (rest z hz))] at ext
  simpa only [pow_two,k,Nat.mul_assoc,←mul_sum] using ext

/-- The path and moving cycle balance all their internal columns. Strict
rows in the original graph force a joint overload on an exterior column. -/
theorem escape {q n} (X : Model q n) (hq : 2≤q) {W P S : Finset ℕ} (wv : W⊆X.V)
    (ps : P.card=q) (dis : Disjoint P S) (cs : Cycle X.D W q S)
    (fits : ∀x∈S,Cycle X.D W q (insert x P)) :
    ∃z∈X.V\(P∪S),q+3 ≤ (q+1)*(inN X.D P z).card+(inN X.D S z).card := by
  classical
  have high := exterior_mass X hq wv ps dis cs fits
  dsimp only at high
  by_contra! fail
  have bound := sum_le_sum (s:=X.V\(P∪S)) (fun z hz =>
    Nat.mul_le_mul_right (X.weights z) (show (q+1)*(inN X.D P z).card+(inN X.D S z).card≤q+2 by
      have := fail z hz; omega))
  rw [←mul_sum] at bound
  have le := Nat.mul_le_mul_left q bound
  have factor : q*(q+2)≤(q+1)^2 := by nlinarith
  exact high.not_ge (le.trans (by rw [←Nat.mul_assoc]; exact Nat.mul_le_mul_right _ factor))

/-- The overload falls outside the *whole* configuration even when every
outside member of the current fixed path is allowed as a payer. The vertex
is in the full original source, so a punctured root remains a possible hit. -/
theorem short_loop_escape {q n} (X : Model q n) (hq : 2≤q) {W} (wv : W⊆X.V)
    (M : ℕ→Finset ℕ) (a u v b : ℕ→ℕ) (closed : M (q+1)=M 0)
    (cycle : ∀i,Cycle X.D W q (M i))
    (move : ∀i,CycleSquareTensor.Shift X.D (M i) (M (i+1)) (a i) (u i) (v i) (b i)) :
    let S := (range (q+1)).image u
    let P := (M 0).erase (u 0)
    ∃z∈X.V\(P∪S),q+3≤(q+1)*(inN X.D P z).card+(inN X.D S z).card ∧
      (2≤(inN X.D P z).card ∨ (inN X.D P z).card=1 ∧ 2≤(inN X.D S z).card) := by
  classical
  intro S P
  have safe := X.free.mono_set wv
  obtain ⟨cs,_,_,_,arcs⟩ := AnchoredShiftFlow.least_period (by omega) safe M a u v b closed cycle move
  have us : u 0∈S := mem_image_of_mem u (mem_range.mpr (by omega))
  obtain ⟨dis,fits⟩ := ShortestCycleFiberModule.slots (by omega) safe (cycle 0) (move 0).aM
    (move 0).uM (move 0).bM cs.sub us arcs
  have ps : P.card=q := by
    have eq := card_erase_add_one (move 0).uM
    change P.card+1=(M 0).card at eq
    rw [(cycle 0).size] at eq
    omega
  obtain ⟨z,zv,too⟩ := escape X hq wv ps dis cs fits
  change q+3≤(q+1)*(inN X.D P z).card+(inN X.D S z).card at too
  refine ⟨z,zv,too,?_⟩
  have bound : (inN X.D S z).card≤q+1 := cs.size ▸ card_le_card (filter_subset _ _)
  by_cases enough : 2≤(inN X.D P z).card
  · exact Or.inl enough
  have one : (inN X.D P z).card=1 := by
    by_contra ne
    have zero : (inN X.D P z).card=0 := by omega
    rw [zero,Nat.mul_zero,zero_add] at too
    omega
  rw [one,Nat.mul_one] at too
  exact Or.inr ⟨one,by omega⟩

#print axioms short_loop_escape
#print axioms escape
end LeanCH.BR.Closure.AnchoredExteriorColumn
