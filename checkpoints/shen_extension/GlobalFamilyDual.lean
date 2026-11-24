import checkpoints.shen_extension.NativePaidHeadFork
import LeanCH.BR.BRWeightedArcCore

set_option maxHeartbeats 1000000

namespace LeanCH.BR.Closure.GlobalFamilyDual
open Finset BRq2 BRq3 BR45 WeightedSD ShenPrimeTransition ShenParentIntersection
open ShortestCycleWeights MarkedCyclePeeling FirstPacketBarrier

theorem integral_strict {q D V} {x : ℕ → ℚ} (pos : ∀ i ∈ V, 0 < x i)
    (high : ∀ i ∈ V, mass V x < WeightedSD.row q D V x i) :
    ∃ w : ℕ → ℕ, (∀ i ∈ V, 0 < w i) ∧ Strict q D V w := by
  classical
  let K := ∏ i ∈ V, (x i).den
  let w := fun i => (x i).num.toNat * (∏ j ∈ V.erase i, (x j).den)
  have kpos : 0 < K := prod_pos (fun i _ => (x i).den_pos)
  have scale (i) (hi : i ∈ V) : (w i : ℚ) = K * x i := by
    have numpos : 0 ≤ (x i).num := by
      exact (Rat.num_nonneg.mpr (pos i hi).le)
    have prod := mul_prod_erase V (fun j => (x j).den) hi
    change (↑((x i).num.toNat * _) : ℚ) = (↑(∏ j ∈ V, (x j).den) : ℚ) * x i
    rw [← prod, Nat.cast_mul, Nat.cast_mul, ← Int.cast_natCast, Int.toNat_of_nonneg numpos]
    have h := (div_eq_iff (show ((x i).den : ℚ) ≠ 0 by exact_mod_cast (x i).den_ne_zero)).mp (x i).num_div_den
    linarith only [congrArg (fun t : ℚ => t * (∏ j ∈ V.erase i, (x j).den : ℕ)) h]
  have kp : (0:ℚ)<K := by exact_mod_cast kpos
  refine ⟨w,fun i hi => by exact_mod_cast (scale i hi ▸ mul_pos kp (pos i hi) : (0:ℚ)<w i),?_⟩
  intro i hi
  have m : mass V (fun j => (w j : ℚ)) = K * mass V x := by
    unfold mass
    rw [Finset.mul_sum]
    exact sum_congr rfl scale
  have o : outW D V (fun j => (w j : ℚ)) i = K * outW D V x i := by
    unfold outW
    rw [Finset.mul_sum]
    apply sum_congr rfl
    intro j hj
    split_ifs <;> simp [scale j hj]
  rw [m,WeightedSD.row,scale i hi,o]
  have := mul_lt_mul_of_pos_left (high i hi) kp
  unfold WeightedSD.row at this
  linarith only [this]

private theorem bad_of_strict {q D V w} (live : V.Nonempty) (s : Strict q D V w) : ¬SmallRow q D V := by
  intro h
  obtain ⟨i,hi,low⟩ := h (fun v => (w v : ℚ)) (fun _ _ => Nat.cast_nonneg _) live
  exact (s i hi).not_ge low

/-- Minimize support among all rational violations at this cutoff. The budget of
the resulting integral model is chosen afterwards and can exceed the input order. -/
theorem select {q n} (input : Model q n) (hq : 2 ≤ q) :
    ∃ budget, ∃ X : Model q budget, X.V.card ≤ input.V.card ∧ SmallerSmallRow q X.V.card := by
  classical
  let P (k : ℕ) := ∃ (D : CH.Digraph) (V : Finset ℕ), V.card=k ∧ QFree D V q ∧ ¬SmallRow q D V
  have ex : ∃k,P k := ⟨_,input.D,input.V,rfl,input.free,bad_of_strict input.live input.strict⟩
  obtain ⟨D,V,size,safe,bad⟩ := Nat.find_spec ex
  have small : SmallerSmallRow q V.card := by
    intro E U lt free
    by_contra no
    exact (Nat.find_min' ex (show P U.card from ⟨E,U,rfl,free,no⟩)).not_gt (size ▸ lt)
  obtain ⟨E,extE,ef,sat⟩ := BRsub.exists_satQ safe
  have eb : ¬SmallRow q E V := fun ok => bad (smallRow_of_supergraph extE ok)
  obtain ⟨z,hz,live,high⟩ := strict_witness_of_not_smallRow eb
  obtain ⟨x,_,c,hc,hx,_,hm,_,hr,_⟩ := strict_pair_of_proper_smallRow (small.induced ef) live z hz high
  obtain ⟨w,wp,ws⟩ := integral_strict hx (fun i hi => by rw [hm,hr i hi]; exact hc)
  have mincard {F U v} (hl : U.Nonempty) (hf : QFree F U q) (hs : Strict q F U v) : V.card ≤ U.card := by
    by_contra! lt
    exact bad_of_strict hl hs (small F U lt hf)
  obtain ⟨A⟩ := prime_descent (fun i hi => Bool.eq_false_iff.mpr (loopfree ef (by omega) hi)) live wp ws
  have eq := eq_of_subset_of_card_le A.subset (mincard A.nonempty (ef.mono_set A.subset) A.strict)
  have rigid : Rigid A := by
    intro U sub hl v _ hs _
    rw [eq]
    exact mincard hl (ef.mono_set sub) hs
  refine ⟨_,⟨E,V,live,ef,sat,w,wp,le_rfl,ws,fun _ _ _ hl hf _ _ hs => mincard hl hf hs,
    eq ▸ A.prime,eq ▸ ShenParentIntersection.separated rigid⟩,?_,small⟩
  exact mincard input.live input.free input.strict

/-- Row and column equalizers on the actual union of the retained cycle arcs. -/
theorem on_family {q b} (X : Model q b) (small : SmallerSmallRow q X.V.card) {F}
    (feas : Feasible q b X.D X.V F) :
    ∃ x p : ℕ → ℚ, ∃ c : ℚ, 1<c ∧ (∀ i ∈ X.V,0<x i) ∧ (∀ i ∈ X.V,0<p i) ∧
      mass X.V x=1 ∧ mass X.V p=1 ∧ (∀ i ∈ X.V,WeightedSD.row q (graph X.D F) X.V x i=c) ∧
      (∀ i ∈ X.V,WeightedSD.col q (graph X.D F) X.V p i=c) := by
  obtain ⟨w,_,_,hs⟩ := feas
  exact strict_pair_of_proper_smallRow (small.induced (PrivateArcEndpoints.graph_free X F))
    X.live (fun i => (w i : ℚ)) (fun _ _ => Nat.cast_nonneg _) hs

#print axioms select
#print axioms on_family
end LeanCH.BR.Closure.GlobalFamilyDual
