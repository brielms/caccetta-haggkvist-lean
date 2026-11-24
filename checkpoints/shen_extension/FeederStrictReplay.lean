import checkpoints.shen_extension.FeederRetainedIncidence
import LeanCH.BR.BRWeightedOutUniformContraction

namespace LeanCH.BR.Closure.FeederStrictReplay
open Finset BRq2 BRq3 BR45 WeightedSD FeederPrivateHeadDescent OmittedCycleProgress

/-- One physical arc seeds every pair even after a strict graph has been edited.
Smaller-support contraction supplies the module exclusion directly on that graph. -/
theorem arc_replay {q E V x p c a b} (hq : 2 ≤ q) (free : QFree E V q)
    (small : SmallerSmallRow q V.card) (price : Flat q E V x p c)
    (av : a ∈ V) (bv : b ∈ V) (arc : E a b=true) :
    ∀ i ∈ V, ∀ j ∈ V, Joined E V a b i j := by
  obtain ⟨high,xp,pp,xm,pm,rows,cols⟩ := price
  have strict (i) (iv : i ∈ V) : mass V x < WeightedSD.row q E V x i := by rw [xm,rows i iv]; exact high
  have dual (i) (iv : i ∈ V) : mass V p < WeightedSD.col q E V p i := by rw [pm,cols i iv]; exact high
  have bad : ¬SmallRow q E V := fun h =>
    h.no_strict ⟨a,av⟩ x (fun i iv => (xp i iv).le) strict
  have sep (u) (uv : u ∈ V) (v) (vv : v ∈ V) (ne : u≠v) : (exclusive E V u v).Nonempty := by
    by_contra none
    apply strict_no_outgoing_domination small free p (fun i iv => (pp i iv).le) dual uv vv ne
    intro j jv uj
    by_contra vj
    exact none ⟨j,mem_sdiff.mpr ⟨mem_outN.mpr ⟨mem_of_mem_erase jv,uj⟩,fun e => vj (mem_outN.mp e).2⟩⟩
  have all := comparison_class_spans (fun _ hi => loopfree free (by omega : 1≤q) hi) sep
    (not_smallRow_out_prime small free bad) av bv
    (show FeederPrivateHeadDescent.Joined E V a b a a from .refl a) .seed arc
  intro i iv j jv
  exact (all i iv).symm.trans (all j jv)

private theorem retained {D : CH.Digraph} {F L i j} (edge : FirstPacketBarrier.graph D F i j=true) :
    FirstPacketBarrier.graph D (insert L F) i j=true := by
  obtain ⟨M,hm⟩ := FirstPacketBarrier.active.mp edge
  obtain ⟨mf,im,jm,native⟩ := MarkedCyclePeeling.mem_col.mp hm
  exact FirstPacketBarrier.active.mpr ⟨M,MarkedCyclePeeling.mem_col.mpr ⟨mem_insert_of_mem mf,im,jm,native⟩⟩

theorem at_original {q D V F L x p c a b z} (hq : 2 ≤ q)
    (free : QFree (FirstPacketBarrier.graph D (insert L F)) V q)
    (small : SmallerSmallRow q V.card) (price : Flat q (FirstPacketBarrier.graph D (insert L F)) V x p c)
    (av : a ∈ V) (bv : b ∈ V) (zv : z ∈ V)
    (first : FirstPacketBarrier.graph D F a z=true) (second : FirstPacketBarrier.graph D F b z=true) :
    let E := FirstPacketBarrier.graph D (insert L F)
    let T := fun i j => E j i
    ∀ i ∈ V, ∀ j ∈ V, (Joined E V a z i j ∧ Joined E V b z i j) ∧
      (Joined T V z a i j ∧ Joined T V z b i j) ∧
      (x i ≠ x j → FirstDifference E V x a z ∧ FirstDifference E V x b z) ∧
      (p i ≠ p j → FirstDifference T V p z a ∧ FirstDifference T V p z b) := by
  intro E T i iv j jv
  have reverse : Flat q T V p x c :=
    ⟨price.1,price.2.2.1,price.2.1,price.2.2.2.2.1,price.2.2.2.1,price.2.2.2.2.2.2,price.2.2.2.2.2.1⟩
  have a₁ := arc_replay hq free small price av zv (retained first) i iv j jv
  have a₂ := arc_replay hq free small price bv zv (retained second) i iv j jv
  have b₁ := arc_replay hq free.reverse small reverse zv av (retained first) i iv j jv
  have b₂ := arc_replay hq free.reverse small reverse zv bv (retained second) i iv j jv
  exact ⟨⟨a₁,a₂⟩,⟨b₁,b₂⟩,fun h => ⟨first_difference a₁ h,first_difference a₂ h⟩,
    fun h => ⟨first_difference b₁ h,first_difference b₂ h⟩⟩

#print axioms arc_replay
#print axioms at_original
end LeanCH.BR.Closure.FeederStrictReplay
