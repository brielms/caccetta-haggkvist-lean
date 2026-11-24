import checkpoints.shen_extension.TwoHeadRepairReplay
import checkpoints.shen_extension.SharedExitReturn
import checkpoints.pair_tilt_20261119.SwappedParentRoom

namespace LeanCH.BR.Closure.TwoHeadAncestorReplay
open Finset BRq2 BRq3 BR45 WeightedSD TwoHeadRepairReplay LabelledLeakageCapacity

/-- The atom floor for both exits and the diffuse price cap imply the
light-root test in the ancestor rectangle, for every cutoff at least three. -/
private theorem price_room {t c a i u v : ℚ} (three : 3≤t) (high : 1<c)
    (ua : 0≤u) (va : 0≤v) (ac : t^2*a≤1) (ic : t^2*i≤1) (uc : t^2*u≤1)
    (fu : c-1≤(t-1)*u) (fv : c-1≤(t-1)*v) :
    2*t^2*a+2*(t-1)≤2*t^2*c-2*t*(t-1)*(t*(c-1)+c)+(t-1)^2*(t-2)*(c-i)
        +2*t^2*((t-1)*(u+v)+min u v) := by
  have t2 : 2≤t^2 := by nlinarith [sq_nonneg (t-3)]
  have half : i≤1/2 := by
    by_contra! bigger
    nlinarith only [mul_le_mul_of_nonneg_right t2 (show 0 ≤ i by linarith), ic, bigger]
  have scale : t^2*(c-1)≤t-1 := by
    nlinarith only [mul_le_mul_of_nonneg_left fu (sq_nonneg t),
      mul_le_mul_of_nonneg_left uc (show 0 ≤ t-1 by linarith)]
  have bar : 2*(t-3)≤(t-1)*(t-2)/2 := by nlinarith only [sq_nonneg (2*t-7)]
  have debt : 2*t^2*(t-3)*(c-1)≤(t-1)^2*(t-2)*(c-i) := by
    nlinarith only [mul_le_mul_of_nonneg_left scale (show 0 ≤ 2*(t-3) by linarith),
      mul_le_mul_of_nonneg_right bar (show 0 ≤ t-1 by linarith),
      mul_le_mul_of_nonneg_left (show 1/2≤c-i by linarith)
        (mul_nonneg (sq_nonneg (t-1)) (show 0 ≤ t-2 by linarith))]
  have banks : 2*(c-1)≤(t-1)*(u+v)+min u v := by
    nlinarith only [fu,fv,le_min ua va]
  nlinarith only [debt,mul_le_mul_of_nonneg_left banks (by positivity : 0≤2*t^2),ac,
    mul_le_mul_of_nonneg_left high.le (show 0 ≤ t by linarith),three]

def rectangleCap (t c σ i : ℚ) : ℚ :=
  2*t^2*(t-1)*c-2*t^3*σ-2*t*(t-1)*(t*σ+c)+(t-1)^2*(t-2)*(c-i)

theorem inner_room {q E V w c} {s : Seeds q E V w c} (hq : 3≤q)
    (free : QFree E V q) (small : SmallerSmallRow q V.card)
    (wm : mass V w=1) (both : Covered s) :
    ∀D : Finset ℕ,outN E V s.a⊆D → D⊆region q E V s.a →
    2*(q:ℚ)^3*mass (region q E V s.a\D) w+2*((q:ℚ)-1)≤
      rectangleCap q c (c-mass V w) (w s.i) := by
  intro D hd dr
  have X := both.2.2.1
  have floor := strict_atom_floor_of_proper (by omega : 2≤q) free (small.induced free) w
    (fun j jv=>(X.pos j jv).le) c X.high (fun j jv=>(X.flat j jv).ge)
  have price := price_room (t:=(q:ℚ)) (by exact_mod_cast hq) (wm ▸ X.high) (X.pos _ X.z₁v).le (X.pos _ X.z₂v).le
    (s.diffuse _ s.av) (s.diffuse _ (X.rs s.ir)) (s.diffuse _ X.z₁v)
    (wm ▸ (floor _ X.z₁v).le) (wm ▸ (floor _ X.z₂v).le)
  have upper := SwappedParentRoom.inner_parent_room (by omega : 2≤q) X free hd dr
  rw [wm] at upper ⊢
  unfold rectangleCap
  nlinarith only [price,mul_le_mul_of_nonneg_left upper (by positivity : 0≤2*(q:ℚ)^2)]

/-- Any union of inner and exterior labels which beats the swapped-pair
cap needs more than (q-1)/q³ native weight in its exterior labels. -/
theorem exterior_needed {q E V w c} {s : Seeds q E V w c} (hq : 3≤q)
    (free : QFree E V q) (small : SmallerSmallRow q V.card) (wm : mass V w=1) (both : Covered s)
    {D P : Finset ℕ} (hd : outN E V s.a⊆D) (dr : D⊆region q E V s.a) (outside : P⊆V\region q E V s.a)
    (beats : rectangleCap q c (c-mass V w) (w s.i)<2*(q:ℚ)^3*mass ((region q E V s.a\D)∪P) w) :
    (q:ℚ)-1<(q:ℚ)^3*mass P w := by
  have dis : Disjoint (region q E V s.a\D) P :=
    disjoint_left.mpr (fun _ left right=>(mem_sdiff.mp (outside right)).2 (mem_sdiff.mp left).1)
  have add : mass ((region q E V s.a\D)∪P) w=mass (region q E V s.a\D) w+mass P w := sum_union dis
  rw [add] at beats
  nlinarith only [inner_room hq free small wm both D hd dr,beats]

/-- The common root supplies the return to a specified starting row. The
small menu and the two exit labels are identical in the return and row count. -/
theorem short_menu {q E V w c} {s : Seeds q E V w c} (free : QFree E V q) (both : Covered s)
    {P : Finset ℕ} (inside : P⊆V) {b d : ℕ} (start : b∈P) (viaRoot : Walk E V s.a b d)
    (room : d+1+P.card≤q) :
    ∃j∈P,(outN E (P∪{s.x,s.y}) j).card<2 := by
  by_contra! budget
  have X := both.2.2.1
  have xv : s.x∈V := X.z₁v
  have ret : b∈ball E V s.x (d+1) := mem_ball.mpr
    ⟨inside start,d+1,le_rfl,by simpa [Nat.add_comm] using
      (Walk.step s.av (mem_outN.mp (mem_inter.mp both.2.2.2.1).1).2 viaRoot : Walk E V s.x b (d+1))⟩
  exact SATBoundaryPilot.shared_exit_excludes_return free inside
    (insert_subset xv (singleton_subset_iff.mpr X.z₂v)) start (mem_insert_self _ _)
    room (fun j jj=>by rw [card_pair s.ne]; exact budget j jj) ret

#print axioms inner_room
#print axioms exterior_needed
#print axioms short_menu
end LeanCH.BR.Closure.TwoHeadAncestorReplay
