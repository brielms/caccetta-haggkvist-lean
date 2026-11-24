import LeanCH.BR.BRWeightedDeletionThreshold

namespace LeanCH.BR.PacketCompression
open Finset Matrix WeightedSD BRq2 BRq3 BR45 FiniteCutInverse
open scoped Matrix

/-- Exact simultaneous replacement test from the original strict graph's
inverse. The incoming arc can change both endpoints. -/
theorem one_exchange {q : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (small : SmallerSmallRow q V.card) (strong : StrictPositiveRows q D V)
    {H : Matrix V V ℝ} (inv : CommonInverse (realMatrix q D V) H)
    (a b u v : V) (old : D a b=true) (fresh : ¬ D u v=true)
    (safe : QFree (insertArc D u v) V q) :
    SmallRow q (eraseArc (insertArc D u v) a b) V ↔
      (q:ℝ)^2 * H b u * H v a ≤ ((q:ℝ)*H b a-1)*(1+(q:ℝ)*H v u) := by
  let G := insertArc D u v
  have sup := strong.mono_graph (fun x _ y _ ed => insertArc_mono D u v x y ed)
  obtain ⟨L,invL⟩ := common_inverse_of_smaller_strict small safe sup
  have diff := realMatrix_insert_difference (q:=q) u v fresh
  have row := single_increment_row inv invL u v (q:ℝ) diff a
  have changeBA := single_increment_identity inv invL u v (q:ℝ) diff b a
  let z : ℝ := 1 + (q:ℝ)*H v u
  have pos : 0 < z := by dsimp [z]; positivity [inv.nonneg v u]
  have identity : z*(H b a-L b a) = (q:ℝ)*H b u*H v a := by
    rw [←row,changeBA]
    dsimp [z]; ring
  have scale : ((q:ℝ)*H b a-1)*z - (q:ℝ)^2*H b u*H v a = z*((q:ℝ)*L b a-1) := by
    linear_combination (q:ℝ)*identity
  rw [deletion_smallRow_iff invL a b (insertArc_mono D u v a b old)]
  change 1 ≤ (q:ℝ)*L b a ↔ (q:ℝ)^2 * H b u * H v a ≤ ((q:ℝ)*H b a-1)*z
  rw [← sub_nonneg (b := (q:ℝ)^2 * H b u * H v a),scale]
  exact ⟨fun h => mul_nonneg pos.le (sub_nonneg.mpr h),
    fun h => sub_nonneg.mp (nonneg_of_mul_nonneg_right h pos)⟩

end LeanCH.BR.PacketCompression

#print axioms LeanCH.BR.PacketCompression.one_exchange

