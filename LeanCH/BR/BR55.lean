import LeanCH.BR.BR55Structure
import LeanCH.BR.BRSecondBallShift
import LeanCH.BR.BRsGenBBall

/-! Unconditional boundary regularity at (5,5), through equality balls and sink shifts. -/

namespace LeanCH.BR.BR55
open BRq2 BRq3 BR45 BRsGen BRsub Compose.Boundary

theorem incoming_regular_of_profile {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V 5) (hV : V.card = 26) (hp : BoundaryProfile D V) :
    ∀ v ∈ V, (inN D V v).card = 5 :=
  incoming_regular_of_second_ball_cap (by decide) (by decide) hf
    (fun v hv => (hp.out_regular v hv).ge) hp.saturated hV
    (fun v hv => (hp.balls v hv).1.le)

theorem boundary_in_regular {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V 5) (hmin : ∀ v ∈ V, 5 ≤ (outN D V v).card)
    (hV : V.card = 26) : ∀ v ∈ V, (inN D V v).card = 5 :=
  incoming_regular_of_profile hf hV (boundary_profile hf hmin hV)

theorem ball_four_eq_of_profile {D : CH.Digraph} {V : Finset ℕ} {u : ℕ}
    (hf : QFree D V 5) (hV : V.card = 26) (hp : BoundaryProfile D V) (hu : u ∈ V) :
    (ball D V u 4).card = 21 := by
  have hi := incoming_regular_of_profile hf hV hp u hu
  have hb := card_inN_of_satQ (by decide : 1 ≤ 5) hf hp.saturated hu
  change (inN D V u).card + (ball D V u 4).card = V.card at hb
  omega

theorem boundary_ball_four {D : CH.Digraph} {V : Finset ℕ} {u : ℕ}
    (hf : QFree D V 5) (hmin : ∀ v ∈ V, 5 ≤ (outN D V v).card)
    (hV : V.card = 26) (hu : u ∈ V) : (ball D V u 4).card = 21 :=
  ball_four_eq_of_profile hf hV (boundary_profile hf hmin hV) hu

/-- The previously open fourth-layer proposition is now discharged. -/
theorem fourth_layer_growth : FourthLayerGrowth := by
  intro D V hf hV hp u hu
  have hb4 := ball_four_eq_of_profile hf hV hp hu
  have hb3 := (hp.balls u hu).2.1
  have hc := Finset.card_sdiff_add_card_eq_card
    (ball_mono_radius (D := D) (W := V) (u := u) (by decide : 3 ≤ 4))
  omega

/-- BR(5,5), without unproved structural premises. -/
theorem br_five_five : BoundaryRegular 5 5 :=
  boundary_regular_of_fourth_layer fourth_layer_growth

/-- The boundary ball result. This does not assert Ball(5,5) on arbitrary hosts. -/
theorem bball_five_five : BBall 5 5 := by
  intro D hf ho u hu
  have hb := boundary_ball_four hf (fun v hv => (ho v hv).ge)
    (by simp : (Finset.range (5 * 5 + 1)).card = 26) hu
  change 21 ≤ (ball D (Finset.range (5 * 5 + 1)) u 4).card
  omega

end LeanCH.BR.BR55
