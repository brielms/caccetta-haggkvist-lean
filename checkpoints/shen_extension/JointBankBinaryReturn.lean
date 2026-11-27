import checkpoints.shen_extension.JointBankParentChoice
import checkpoints.shen_extension.dot_tensor_research.DotDegreeEightPairCover_20261121

namespace LeanCH.BR.BypassBankReplay
open Finset BRq2 BRq3 BR45 BypassRepair

/-- With common predecessors, one label reaches an arbitrary set of at most
two to the k labels at exactly k steps. Split the target set into two halves. -/
theorem binary_ancestor {D : CH.Digraph} {V : Finset ℕ} (live : V.Nonempty)
    (pair : ∀ u ∈ V, ∀ v ∈ V, ∃ w ∈ V, D w u = true ∧ D w v = true)
    (k : ℕ) {S : Finset ℕ} (sub : S ⊆ V) (small : S.card ≤ 2^k) :
    ∃ w ∈ V, ∀ a ∈ S, Walk D V w a k := by
  classical
  induction k generalizing S with
  | zero =>
    by_cases has : S.Nonempty
    · obtain ⟨a,ha⟩ := has
      refine ⟨a,sub ha,fun b hb => ?_⟩
      have eq := card_le_one.mp small a ha b hb
      exact eq ▸ (Walk.refl a)
    · obtain ⟨u,uv⟩ := live
      exact ⟨u,uv,fun a ha => False.elim (has ⟨a,ha⟩)⟩
  | succ k ih =>
    obtain ⟨A,as,nA⟩ := exists_subset_card_eq (s:=S) (min_le_right (2^k) S.card)
    have nB := card_sdiff_add_card_eq_card as
    have smallA : A.card ≤ 2^k := nA.le.trans (min_le_left ..)
    have smallB : (S \ A).card ≤ 2^k := by
      rw [pow_succ] at small
      omega
    obtain ⟨x,xv,wx⟩ := ih (as.trans sub) smallA
    obtain ⟨y,yv,wy⟩ := ih (sdiff_subset.trans sub) smallB
    obtain ⟨w,wv,ex,ey⟩ := pair x xv y yv
    refine ⟨w,wv,fun a ha => ?_⟩
    by_cases inA : a∈A
    · exact .step xv ex (wx a inA)
    · exact .step yv ey (wy a (mem_sdiff.mpr ⟨ha,inA⟩))

/-- Every predecessor set meets the predecessor set of every row. A binary
ancestor reaching a whole predecessor set would consequently return to itself. -/
theorem indegree_of_binary_return {D V q} (free : QFree D V q) (live : V.Nonempty)
    (hq : 1 ≤ q)
    (pair : ∀ u ∈ V, ∀ v ∈ V, ∃ w ∈ V, D w u = true ∧ D w v = true)
    {p} (pv : p∈V) : 2^(q-1) < (inN D V p).card := by
  by_contra! small
  obtain ⟨w,wv,walk⟩ := binary_ancestor live pair (q-1) (show inN D V p ⊆ V from fun _ h => (mem_inN.mp h).1) small
  obtain ⟨u,uv,up,uw⟩ := pair p pv w wv
  have cycle := (walk u (mem_inN.mpr ⟨uv,up⟩)).snoc wv uw
  exact free w (q-1+1) (by omega) (by omega) cycle

/-- In the two-label bank band, every indegree and hence the regular
outdegree exceed 2^(q-1). -/
theorem exponential_at_two {q s} (X : ShenMinimumOrder.Source q s) (reg : OutEq s X.D X.V)
    (hq : 2 ≤ q) (hs : 2 ≤ s) (order : X.V.card=q*(s-1)+2) (none : NoHost q (s-1)) :
    (∀ p ∈ X.V, 2^(q-1) < (inN X.D X.V p).card) ∧ 2^(q-1) < s := by
  have ep : DotDegreeSeven.Endpoint q (s-1) :=
    fun D V free live size deg => none D V live size.le free deg
  have cover := DotDegreeEight.pair_cover_of_endpoint ep (by omega) (by omega) X.free order
    (by simpa only [show s-1+1=s by omega] using reg)
  have pair (u) (uv : u∈X.V) (v) (vv : v∈X.V) :
      ∃ w∈X.V,X.D w u=true ∧ X.D w v=true := by
    by_cases eq : u=v
    · subst v
      obtain ⟨w,wv,e,_⟩ := ShenCycleSuccessor.fixed_parent X hq (by omega) uv
      exact ⟨w,wv,e,e⟩
    · exact cover _ uv _ vv eq
  have low (u) (uv : u∈X.V) := indegree_of_binary_return X.free X.nonempty (by omega) pair uv
  refine ⟨low,?_⟩
  have count : (∑ v∈X.V, (outN X.D X.V v).card) = ∑ v∈X.V,(inN X.D X.V v).card :=
    Compose.ThinRigid.sum_out_eq_sum_in X.D X.V
  have bound : (∑ _v∈X.V,(2^(q-1)+1)) ≤ ∑ v∈X.V,(inN X.D X.V v).card :=
    sum_le_sum (fun v vv => low v vv)
  rw [← count,sum_congr rfl (fun u uv => reg u uv)] at bound
  simp only [sum_const,smul_eq_mul] at bound
  exact Nat.le_of_mul_le_mul_left bound (card_pos.mpr X.nonempty)

#print axioms binary_ancestor
#print axioms exponential_at_two
end LeanCH.BR.BypassBankReplay

