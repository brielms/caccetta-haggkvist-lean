import checkpoints.shen_extension.ShortestCycleWeights

namespace LeanCH.BR.Closure.WeightedOneVertexSplit
open Finset BRq2 BRq3 BR45 ShenPrimeTransition ShortestCycleWeights

def paid (q : ℕ) (D : CH.Digraph) (w : ℕ → ℕ) (B : Finset ℕ) (a : ℕ) : Prop :=
  q*(∑y∈B, if D a y=true then w y else 0) ≤ ∑y∈B,w y

private theorem keep {q D w L B a} (dis : Disjoint L B)
    (high : (∑y∈L∪B,w y)<score q D (L∪B) w a) (low : paid q D w B a) :
    (∑y∈L,w y)<score q D L w a := by
  unfold score at high ⊢
  rw [sum_union dis,sum_union dis,Nat.mul_add] at high
  unfold paid at low
  omega

/-- At the shared vertex the strict row picks a child. The other rows can
each pay for deletion of the opposite side using its actual total mass. -/
theorem split {q D w L B r} (dis : Disjoint L B) (rL : r∉L) (rB : r∉B)
    (loop : D r r=false) (strict : Strict q D (insert r (L∪B)) w)
    (left : ∀a∈L,paid q D w B a) (right : ∀b∈B,paid q D w L b) :
    Strict q D (insert r L) w ∨ Strict q D (insert r B) w := by
  classical
  have one (A K : Finset ℕ) (ra : r∉A) (rk : r∉K) (ak : Disjoint A K)
      (all : Strict q D (insert r (A∪K)) w) (pay : ∀a∈A,paid q D w K a)
      (rich : ¬paid q D w A r) : Strict q D (insert r A) w := by
    apply nat_strict.mpr
    intro a ha
    rcases mem_insert.mp ha with rfl | ha
    · unfold paid at rich
      simp [score,sum_insert,ra,loop]
      omega
    · have h := nat_strict.mp all a (mem_insert_of_mem (mem_union_left _ ha))
      rw [←insert_union] at h
      exact keep (disjoint_insert_left.mpr ⟨rk,ak⟩) h (pay a ha)
  by_cases low : paid q D w L r
  · right
    apply one B L rB rL dis.symm (by simpa only [union_comm B L] using strict) right
    intro both
    have hr := nat_strict.mp strict r (mem_insert_self _ _)
    have rm : r∉L∪B := by simp [rL,rB]
    simp only [score,sum_insert rm,loop,Bool.false_eq_true,ite_false,zero_add,
      sum_union dis,Nat.mul_add] at hr
    unfold paid at low both
    omega
  · exact Or.inl (one L B rL rB dis strict left low)

/-- Every nontrivial split around a vertex of the normalized support has a
specific row spending more than a 1/q share of the opposite side. -/
theorem cross_row {q n} (X : Model q n) (hq : 2≤q) {r L B}
    (whole : insert r (L∪B)=X.V) (dis : Disjoint L B) (rL : r∉L) (rB : r∉B)
    (ll : L.Nonempty) (bl : B.Nonempty) :
    (∃a∈L, ¬paid q X.D X.weights B a) ∨ (∃b∈B, ¬paid q X.D X.weights L b) := by
  classical
  by_contra! both
  have rv := whole ▸ mem_insert_self r (L∪B)
  have loop : X.D r r=false := Bool.eq_false_iff.mpr (loopfree X.free (by omega) rv)
  have closed {U : Finset ℕ} (sub : U⊆X.V) (live : U.Nonempty) (proper : U≠X.V)
      (good : Strict q X.D U X.weights) : False := by
    have low := X.minimal X.D U X.weights live (X.free.mono_set sub)
      (fun x hx => X.positive x (sub hx))
      ((sum_le_sum_of_subset_of_nonneg sub (by intros; omega)).trans X.bounded) good
    exact proper (eq_of_subset_of_card_le sub low)
  have subL : insert r L⊆X.V := whole ▸ insert_subset_insert r (subset_union_left : L⊆L∪B)
  have subB : insert r B⊆X.V := whole ▸ insert_subset_insert r (subset_union_right : B⊆L∪B)
  rcases split dis rL rB loop (whole.symm ▸ X.strict) both.1 both.2 with good | good
  · apply closed subL ⟨r,mem_insert_self _ _⟩ _ good
    obtain ⟨b,hb⟩ := bl
    intro eq
    have v := subB (mem_insert_of_mem hb)
    rw [←eq] at v
    exact (mem_insert.mp v).elim (fun e => rB (e ▸ hb)) (fun hl => disjoint_left.mp dis hl hb)
  · apply closed subB ⟨r,mem_insert_self _ _⟩ _ good
    obtain ⟨a,ha⟩ := ll
    intro eq
    have v := subL (mem_insert_of_mem ha)
    rw [←eq] at v
    exact (mem_insert.mp v).elim (fun e => rL (e ▸ ha)) (fun hb => disjoint_left.mp dis ha hb)

#print axioms split
#print axioms cross_row
end LeanCH.BR.Closure.WeightedOneVertexSplit
