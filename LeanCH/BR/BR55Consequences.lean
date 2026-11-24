import LeanCH.BR.BR55
import LeanCH.BR.BRBoundaryDeficiency
import LeanCH.BR.BRq4Fold

/-! Feed the closed (5,5) boundary case into small-host folding and deficiency.
Ball(5,5) on arbitrary hosts is not used. -/

namespace LeanCH.BR.BR55
open BRq2 BRq3 BRq4 BR45 BRsGen

theorem ball_small_five_five : BallSmall 5 5 := by
  intro D V hf ho hV u hu
  have hm : ∀ v ∈ V, 5 ≤ (outN D V v).card := fun v hv => (ho v hv).ge
  have hlo := card_ge_twenty_six hf hm ⟨u, hu⟩
  have hb := boundary_ball_four hf hm (by omega) hu
  change 21 ≤ (ball D V u 4).card
  omega

theorem diameter_five {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V 5) (hmin : ∀ v ∈ V, 5 ≤ (outN D V v).card)
    (hV : V.card ≤ 26) : ∀ v ∈ V, ball D V v 5 = V := by
  intro v hv
  have hlo := card_ge_twenty_six hf hmin ⟨v, hv⟩
  have ho := boundary_out_regular hf hmin (by omega)
  exact diam_small_b (by decide) ball_small_five_five hf ho hV v hv

theorem exit_five {D : CH.Digraph} {V : Finset ℕ} {z r : ℕ}
    (hf : QFree D V 5) (ho : OutEq 5 D V) (hz : z ∈ V) (hr : 1 ≤ r)
    (hcard : (ball D V z 5).card + r ≤ 26) :
    ∃ y ∈ ball D V z 5, r + 2 ≤ (exitN D V (ball D V z 5) z y).card :=
  exit_small (by decide) ball_small_five_five hf ho hz hr hcard

theorem degree_five_deficiency_equality {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V 5) (hmin : ∀ v ∈ V, 1 ≤ (outN D V v).card)
    (heq : V.card + ∑ v ∈ V, (5 - (outN D V v).card) = 26) :
    OutEq 5 D V ∧ V.card = 26 :=
  deficiency_equality_of_forced_regular (by decide)
    (fun _ _ hF hmF hc => boundary_out_regular hF hmF hc) hf hmin heq

theorem degree_five_deficiency_strict {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V 5) (hmin : ∀ v ∈ V, 1 ≤ (outN D V v).card) (hne : V.Nonempty)
    (hsmall : V.card < 26 ∨ ¬ OutEq 5 D V) :
    27 ≤ V.card + ∑ v ∈ V, (5 - (outN D V v).card) :=
  deficiency_strict_of_size_regular (by decide)
    (fun _ _ hF hmF hn => card_ge_twenty_six hF hmF hn)
    (fun _ _ hF hmF hc => boundary_out_regular hF hmF hc) hf hmin hne hsmall

end LeanCH.BR.BR55
