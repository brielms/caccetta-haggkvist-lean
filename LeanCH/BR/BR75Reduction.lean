import LeanCH.BR.BR65
import LeanCH.BR.BRBallFiveResidual

/-! The still-open arbitrary-host Ball(5,5) would supply the next boundary parameter.
No inhabitant of that Ball proposition is asserted. -/

namespace LeanCH.BR.BR75
open BRq2 BRq3 BR45 BRsGen Compose.Boundary

theorem br_seven_five_of_ball_five (hb : Ball 5 5) : BoundaryRegular 7 5 := by
  apply br_of_second_ball_cap (by decide : 2 ≤ 5) (by decide : 5 ≤ 7)
  intro D hf hm u hu
  have hthree : ∀ v ∈ Finset.range (7 * 5 + 1),
      16 ≤ (ball D (Finset.range (7 * 5 + 1)) v 3).card :=
    fun v hv => card_ball_three_ge_sixteen (hf.mono_bound (by decide)) hm hv
  have hfour : ∀ v ∈ Finset.range (7 * 5 + 1),
      21 ≤ (ball D (Finset.range (7 * 5 + 1)) v 4).card :=
    fun v hv => ball_of_min hb (hf.mono_bound (by decide)) hm v hv
  have heq := two_balls_boundary_cards hf (by decide : 3 + 4 ≤ 7)
    hthree hfour (by simp)
  exact BR65.second_ball_cap_of_third (hf.mono_bound (by decide)) hm hu (heq u hu).1.le

/-- The five-profile residual is sufficient, but still unproved. -/
theorem br_seven_five_of_residual (h : FiveBallResidual) : BoundaryRegular 7 5 :=
  br_seven_five_of_ball_five (ball_five_of_residual h)

end LeanCH.BR.BR75
