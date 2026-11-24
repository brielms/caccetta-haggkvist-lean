import checkpoints.shen_extension.CycleSquareBalance

namespace LeanCH.BR.Closure.SquareFiberPressure
open Finset BRq2 BRq3 BR45 ShenPrimeTransition ShortestCycleWeights

def heads (D : CH.Digraph) (w : ℕ→ℕ) (S : Finset ℕ) (x : ℕ) :=
  ∑z∈S, if D x z=true then w z else 0

def joint (D : CH.Digraph) (w : ℕ→ℕ) (S : Finset ℕ) (u v : ℕ) (i j : Bool) :=
  ∑z∈S,if D u z=i ∧ D v z=j then w z else 0

/-- An exact two-row incidence identity. The shared and simultaneously
missed masses cannot be recovered from the two row totals separately. -/
theorem cells (D : CH.Digraph) (w : ℕ→ℕ) (S : Finset ℕ) (u v : ℕ) :
    heads D w S u+heads D w S v+joint D w S u v false false =
    (∑z∈S,w z)+joint D w S u v true true := by
  unfold heads joint
  simp only [←sum_add_distrib]
  apply sum_congr rfl
  intro z _
  cases D u z <;> cases D v z <;> simp

private theorem light {n} (X : Model 3 n) {S : Finset ℕ} (sv : S⊆X.V) (live : S.Nonempty)
    (ne : S≠X.V) : ∃u∈S,score 3 X.D S X.weights u ≤ ∑z∈S,X.weights z := by
  by_contra! high
  exact ne (eq_of_subset_of_card_le sv (X.minimal X.D S X.weights live (X.free.mono_set sv)
    (fun _ hx => X.positive _ (sv hx)) ((sum_le_sum_of_subset_of_nonneg sv (by intros; omega)).trans X.bounded)
    (nat_strict.mpr high)))

/-- Light rows in two anticomplete fibers can be selected independently.
Their joint external incidence then obeys a strict mass inequality. -/
theorem pressure {n} (X : Model 3 n) {L R : Finset ℕ} (lv : L⊆X.V) (rv : R⊆X.V)
    (ll : L.Nonempty) (rl : R.Nonempty) (dis : Disjoint L R)
    (clear : ∀u∈L,∀v∈R,X.D u v=false ∧ X.D v u=false) :
    let Z := X.V\(L∪R)
    ∃u∈L,∃v∈R, (∑z∈L∪R,X.weights z)+3*joint X.D X.weights Z u v false false <
      (∑z∈Z,X.weights z)+3*joint X.D X.weights Z u v true true := by
  classical
  intro Z
  obtain ⟨a,al⟩ := ll
  obtain ⟨b,br⟩ := rl
  obtain ⟨u,ul,lo⟩ := light X lv ⟨a,al⟩ (fun eq => disjoint_left.mp dis (eq.symm ▸ rv br) br)
  obtain ⟨v,vr,ro⟩ := light X rv ⟨b,br⟩ (fun eq => disjoint_left.mp dis al (eq.symm ▸ lv al))
  have sub := union_subset lv rv
  have part (f : ℕ→ℕ) : (∑z∈Z,f z)+(∑z∈L,f z)+(∑z∈R,f z)=∑z∈X.V,f z := by
    rw [Nat.add_assoc,←sum_union dis]; exact sum_sdiff sub
  have p0 := part X.weights
  have expand (x) : heads X.D X.weights Z x + heads X.D X.weights L x + heads X.D X.weights R x =
      heads X.D X.weights X.V x := part _
  have e1 := expand u
  have e2 := expand v
  have lr : heads X.D X.weights R u=0 :=
    sum_eq_zero fun z zr => by simp [(clear u ul z zr).1]
  have rr : heads X.D X.weights L v=0 :=
    sum_eq_zero fun z zl => by simp [(clear z zl v vr).2]
  rw [lr] at e1
  rw [rr] at e2
  have high1 := nat_strict.mp X.strict u (lv ul)
  have high2 := nat_strict.mp X.strict v (rv vr)
  change _ < X.weights u + 3*heads X.D X.weights X.V u at high1
  change _ < X.weights v + 3*heads X.D X.weights X.V v at high2
  change X.weights u + 3*heads X.D X.weights L u ≤ _ at lo
  change X.weights v + 3*heads X.D X.weights R v ≤ _ at ro
  have eq := cells X.D X.weights Z u v
  refine ⟨u,ul,v,vr,?_⟩
  rw [sum_union dis]
  omega

def fiber (D : CH.Digraph) (V : Finset ℕ) (a b : ℕ) := outN D V a ∩ inN D V b

/-- The two opposite slots of a directed four-cycle range over a complete
product. The absence of cross arcs lets the two fibers use independent
smaller-support row bounds in the preceding theorem. -/
theorem opposite {n} (X : Model 3 n) {a b} (av : a∈X.V) (bv : b∈X.V)
    (ll : (fiber X.D X.V a b).Nonempty) (rl : (fiber X.D X.V b a).Nonempty) :
    let L := fiber X.D X.V a b
    let R := fiber X.D X.V b a
    let Z := X.V\(L∪R)
    ∃u∈L,∃v∈R, X.D a u=true ∧ X.D u b=true ∧ X.D b v=true ∧ X.D v a=true ∧
      (∑z∈L∪R,X.weights z)+3*joint X.D X.weights Z u v false false <
      (∑z∈Z,X.weights z)+3*joint X.D X.weights Z u v true true := by
  classical
  intro L R Z
  have arcs {x y i} (h : i∈fiber X.D X.V x y) : i∈X.V ∧ X.D x i=true ∧ X.D i y=true :=
    ⟨outN_subset (mem_inter.mp h).1,(mem_outN.mp (mem_inter.mp h).1).2,(mem_inN.mp (mem_inter.mp h).2).2⟩
  have dis : Disjoint L R := disjoint_left.mpr (fun i il ir =>
    digonfree X.free (by decide) av (arcs il).1 (arcs il).2.1 (arcs ir).2.2)
  have clear (u) (ul : u∈L) (v) (vr : v∈R) : X.D u v=false ∧ X.D v u=false := by
    obtain ⟨uw,au,ub⟩ := arcs ul
    obtain ⟨vw,bv',va⟩ := arcs vr
    exact ⟨Bool.eq_false_iff.mpr (fun e => X.free a 3 (by decide) le_rfl
      (.step uw au (.step vw e (.step av va (.refl _))))),
      Bool.eq_false_iff.mpr (fun e => X.free b 3 (by decide) le_rfl
      (.step vw bv' (.step uw e (.step bv ub (.refl _)))))⟩
  obtain ⟨u,ul,v,vr,high⟩ := pressure X (fun _ h => (arcs h).1) (fun _ h => (arcs h).1) ll rl dis clear
  exact ⟨u,ul,v,vr,(arcs ul).2.1,(arcs ul).2.2,(arcs vr).2.1,(arcs vr).2.2,high⟩

#print axioms opposite
end LeanCH.BR.Closure.SquareFiberPressure
