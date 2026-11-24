import LeanCH.BR.BRThirdBallCap
import LeanCH.BR.BRSecondBallBoundary
import LeanCH.BR.BRForcedOutSaturation
import LeanCH.BR.BRsGenBBall
import LeanCH.BR.BRq4Fold

/-! The closed boundary case (6,5), from exact third balls and a shortest-cycle obstruction. -/

namespace LeanCH.BR.BR65
open BRq2 BRq3 BRq4 BR45 BRsGen BRsub Compose.Boundary

theorem second_ball_cap_of_third {D : CH.Digraph} {V : Finset ℕ} {u : ℕ}
    (hf : QFree D V 6) (hmin : ∀ v ∈ V, 5 ≤ (outN D V v).card)
    (hu : u ∈ V) (hthird : (ball D V u 3).card ≤ 16) :
    (ball D V u 2).card ≤ 11 := by
  apply second_ball_cap_of_third_and_lower_orders (by decide : 4 ≤ 5)
    (by decide : 5 + 1 ≤ 6) ?_ hf hmin hu hthird
  intro d hd hds F U hF hm hn
  rcases (by omega : d = 2 ∨ d = 3 ∨ d = 4) with rfl | rfl | rfl
  · exact corB (by decide) hF hm hn
  · exact dt_size (by decide) (ball_all 6 (by decide)) hF hm hn
  · exact dt_size (by decide) (BRq4.ball_all4 6 (by decide)) hF hm hn

theorem boundary_second_ball_cap {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V 6) (hmin : ∀ v ∈ V, 5 ≤ (outN D V v).card)
    (hV : V.card = 31) : ∀ u ∈ V, (ball D V u 2).card ≤ 11 := by
  have hlo : ∀ u ∈ V, 16 ≤ (ball D V u 3).card :=
    fun u hu => card_ball_three_ge_sixteen (hf.mono_bound (by decide)) hmin hu
  have heq := two_balls_boundary_cards hf (by decide : 3 + 3 ≤ 6) hlo hlo (by omega)
  intro u hu
  exact second_ball_cap_of_third hf hmin hu (heq u hu).1.le

theorem boundary_out_regular {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V 6) (hmin : ∀ v ∈ V, 5 ≤ (outN D V v).card)
    (hV : V.card = 31) : OutEq 5 D V :=
  out_regular_of_second_ball_cap (by decide) (hf.mono_bound (by decide)) hmin
    (boundary_second_ball_cap hf hmin hV)

theorem boundary_saturated {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V 6) (hmin : ∀ v ∈ V, 5 ≤ (outN D V v).card)
    (hV : V.card = 31) : Sat 6 D V :=
  sat_of_forced_out_regular (fun _ hE hmE => boundary_out_regular hE hmE hV) hf hmin

theorem boundary_in_regular {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V 6) (hmin : ∀ v ∈ V, 5 ≤ (outN D V v).card)
    (hV : V.card = 31) : ∀ u ∈ V, (inN D V u).card = 5 :=
  incoming_regular_of_second_ball_cap (by decide) (by decide) hf hmin
    (boundary_saturated hf hmin hV) hV (boundary_second_ball_cap hf hmin hV)

theorem boundary_ball_five {D : CH.Digraph} {V : Finset ℕ} {u : ℕ}
    (hf : QFree D V 6) (hmin : ∀ v ∈ V, 5 ≤ (outN D V v).card)
    (hV : V.card = 31) (hu : u ∈ V) : (ball D V u 5).card = 26 := by
  have hi := boundary_in_regular hf hmin hV u hu
  have hb := card_inN_of_satQ (by decide : 1 ≤ 6) hf (boundary_saturated hf hmin hV) hu
  change (inN D V u).card + (ball D V u 5).card = V.card at hb
  omega

theorem br_six_five : BoundaryRegular 6 5 := by
  apply br_of_second_ball_cap (by decide : 2 ≤ 5) (by decide : 5 ≤ 6)
  intro D hf hm
  exact boundary_second_ball_cap hf hm (by simp)

theorem bball_six_five : BBall 6 5 := by
  intro D hf ho u hu
  have hb := boundary_ball_five hf (fun v hv => (ho v hv).ge) (by simp) hu
  change 26 ≤ (ball D (Finset.range (6 * 5 + 1)) u 5).card
  omega

theorem ball_small_six_five : BallSmall 6 5 := by
  intro D V hf ho hV u hu
  have hm : ∀ v ∈ V, 5 ≤ (outN D V v).card := fun v hv => (ho v hv).ge
  have hlo := card_ge_thirty_one hf hm ⟨u, hu⟩
  have hb := boundary_ball_five hf hm (by omega) hu
  change 26 ≤ (ball D V u 5).card
  omega

end LeanCH.BR.BR65
