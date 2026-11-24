import LeanCH.BR.BRSecondBallShift
import LeanCH.BR.BRTwoBallEquality
import LeanCH.BR.BRFiveCutoff

/-! A uniform diagonal boundary criterion from complementary lower growth. -/

namespace LeanCH.BR.BRsGen
open BRq2 BRq3 BR45 Compose.Boundary

theorem br_of_complementary_ball_lower {q s : ℕ} (hs : 2 ≤ s) (hsq : s ≤ q)
    (hlower : ∀ D : CH.Digraph, QFree D (Finset.range (q * s + 1)) q →
      (∀ v ∈ Finset.range (q * s + 1), s ≤ (outN D (Finset.range (q * s + 1)) v).card) →
      ∀ v ∈ Finset.range (q * s + 1),
        s * (q - 2) + 1 ≤ (ball D (Finset.range (q * s + 1)) v (q - 2)).card) :
    BoundaryRegular q s := by
  apply br_of_second_ball_cap hs hsq
  intro D hf hmin v hv
  have htwo := fun u hu => card_ball_two_ge_twice hs (hf.mono_bound hsq) hmin (u := u) hu
  have hidentity : 2 * s + s * (q - 2) = q * s := by
    calc
      2 * s + s * (q - 2) = s * ((q - 2) + 2) := by
        rw [Nat.mul_add, Nat.mul_two]
        omega
      _ = s * q := by congr 1; omega
      _ = q * s := Nat.mul_comm _ _
  have hcount : (2 * s + 1) + (s * (q - 2) + 1) =
      (Finset.range (q * s + 1)).card + 1 := by
    rw [Finset.card_range]
    omega
  exact (two_balls_boundary_cards hf (by omega : 2 + (q - 2) ≤ q)
    htwo (hlower D hf hmin) hcount v hv).1.le

/-- Supplied arbitrary-host Ball(q-1,s) closes the next boundary pair in the diagonal regime.
The Ball input is explicit; this theorem does not supply the missing general ball family. -/
theorem br_successor_of_ball {q s : ℕ} (hs : 2 ≤ s) (hsq : s ≤ q)
    (hb : Ball (q - 1) s) : BoundaryRegular q s := by
  apply br_of_complementary_ball_lower hs hsq
  intro D hf hmin v hv
  have hh := ball_of_min hb (hf.mono_bound (Nat.sub_le q 1)) hmin v hv
  have hr : q - 1 - 1 = q - 2 := by omega
  simpa only [hr] using hh

end LeanCH.BR.BRsGen
