import checkpoints.shen_extension.RigidHost
import LeanCH.BR.BRSecondBallShift

/-!
# A second-ball cap closes a rigid host

`rigid_false_of_second_cap`: a rigid host (`RigidHost.Rigid`) in which every vertex has
`|B_2(v)| ≤ 2 s + 1` does not exist. The cap gives `|B_k(v)| ≤ s k + 1` at every radius
(`BRsGen.ball_upper_of_second_ball_cap`, sink shift), so with the rigid floors every root has
its first `i` layers of width `≤ s`, which `narrow_root_false` forbids.

This is the rigid-host counterpart of the in-window boundary-regularity route
(`BRsGen.incoming_regular_of_second_ball_cap`): there the same cap gives in-regularity; here it
closes the host outright, so in-regularity is not needed.
-/

set_option linter.style.longLine false
namespace LeanCH.BR.RigidSecondCap
open Finset BRq2 BRq3 LeanCH.BR.RigidHost
open DotTwoPassShellTransport (layer)

theorem rigid_false_of_second_cap {D : CH.Digraph} {V : Finset ℕ} {q s i : ℕ}
    (R : Rigid D V q s i) (hs : 2 ≤ s) (hsq : s < q) (height : s/2 + i ≤ q) (hi : 1 ≤ i)
    (ne : V.Nonempty)
    (cap : ∀ v ∈ V, (ball D V v 2).card ≤ 2*s + 1) : False := by
  obtain ⟨y, hy⟩ := ne
  have up := LeanCH.BR.BRsGen.ball_upper_of_second_ball_cap hs (R.free.mono_bound hsq.le)
    R.degree cap
  refine narrow_root_false R (by omega) hsq height hi hy (fun j hj hji => ?_)
  have e := ShapeClimbRoot.card_ball_succ (D := D) (V := V) (u := y) (j-1)
  rw [Nat.sub_add_cancel hj] at e
  have h1 := up j y hy
  have h2 := R.floor (j-1) (by omega) y hy
  have h3 : s*j = s*(j-1) + s := by
    rw [← Nat.mul_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel hj]
  omega

/-- The fifth strip (`q = 2 s - 7`, `i = s - 4`, `s ≥ 9`): the side conditions hold. -/
theorem fifth_rigid_false_of_second_cap {D : CH.Digraph} {V : Finset ℕ} {a : ℕ}
    (R : Rigid D V (2*a+7) (a+7) (a+3)) (ne : V.Nonempty)
    (cap : ∀ v ∈ V, (ball D V v 2).card ≤ 2*(a+7) + 1) (ha : 2 ≤ a) : False :=
  rigid_false_of_second_cap R (by omega) (by omega) (by omega) (by omega) ne cap

/-! ### Cap descent in the fifth strip, valid up to radius `s - 7`

The in-window step `BRsGen.half_radius_cap_descent_in_window` needs `q ≥ 2 s - 1`. At
`q = 2 s - 7` the same argument (prefix deficiency with the degree-`s-1` order bound
`(2a+7)(a+6) ≤ |U|`, `ShenThirdStrip.order_to_top`) still closes when the upper radius is
`≤ a = s - 7`. The extremal case of the inequality is a layer of `s - 1` rows after a layer
of `s + 1` rows; it is what fails at the radii `a + 1, a + 2, a + 3`. -/

theorem fifth_cap_descent {a k u : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V (2*a+7)) (hm : ∀ v ∈ V, a+7 ≤ (outN D V v).card) (hu : u ∈ V)
    (hk : k+2 ≤ a) (hinner : (a+7)*k+1 ≤ (ball D V u k).card)
    (hcap : (ball D V u (k+2)).card ≤ (a+7)*(k+2)+1) :
    (ball D V u (k+1)).card ≤ (a+7)*(k+1)+1 := by
  classical
  by_contra hn
  have hc := Finset.card_sdiff_add_card_eq_card
    (ball_mono_radius (D := D) (W := V) (u := u) (by omega : k ≤ k+1))
  have ht := Finset.card_sdiff_add_card_eq_card
    (ball_mono_radius (D := D) (W := V) (u := u) (by omega : k+1 ≤ k+2))
  have e1 : (a+7)*(k+1) = (a+7)*k + (a+7) := by ring
  have e2 : (a+7)*(k+2) = (a+7)*k + 2*(a+7) := by ring
  have htlt : (ball D V u (k + 2) \ ball D V u (k + 1)).card < a+7 := by omega
  have hb := LeanCH.BR.BRsGen.prefix_deficiency_of_size (q := 2*a+7) (d := a+6)
    (n := (2*a+7)*(a+6)) (s := a+7)
    (fun F U hF hmF hne => ShenThirdStrip.order_to_top hF hmF hne) hf hu (by omega) hm
    (by omega) htlt
  have hka : (a+7)*(k+2) ≤ (a+7)*a := Nat.mul_le_mul_left _ hk
  generalize (ball D V u k).card = B0 at *
  generalize (ball D V u (k+1)).card = B1 at *
  generalize (ball D V u (k+2)).card = B2 at *
  generalize (ball D V u (k + 1) \ ball D V u k).card = c at *
  generalize (ball D V u (k + 2) \ ball D V u (k + 1)).card = t at *
  obtain ⟨M, rfl⟩ : ∃ M, B1 = M + 1 := ⟨B1 - 1, by omega⟩
  rw [Nat.add_sub_cancel] at hb
  rcases Nat.eq_zero_or_pos t with h0 | hpos
  · subst h0
    rw [show a + 6 + 0 - (a + 7) = 0 by omega, Nat.mul_zero, Nat.add_zero] at hb
    nlinarith
  · obtain ⟨x, rfl⟩ : ∃ x, t = x + 1 := ⟨t - 1, by omega⟩
    rw [show a + 6 + (x + 1) - (a + 7) = x by omega] at hb
    have hcx : (c + x) * x ≤ (2*a+13) * x := Nat.mul_le_mul_right x (by omega)
    nlinarith [sq_nonneg ((x:ℤ) - a - 6)]

/-- **Three top caps close a fifth-strip rigid host.** If some root `y` has
`|B_r(y)| ≤ s r + 1` at the three radii `r = i-1, i-2, i-3` (`i = a + 3`, `s = a + 7`), the
host does not exist. Equivalently: the layers `i-2, i-1, i` of `y` have suffix sums
`ℓ_i ≥ s`, `ℓ_{i-1} + ℓ_i ≥ 2s`, `ℓ_{i-2} + ℓ_{i-1} + ℓ_i ≥ 3s`. Below radius `i - 3` the caps
follow from `fifth_cap_descent`. -/
theorem fifth_rigid_false_of_top_caps {D : CH.Digraph} {V : Finset ℕ} {a y : ℕ}
    (R : Rigid D V (2*a+7) (a+7) (a+3)) (ha : 2 ≤ a) (hy : y ∈ V)
    (c1 : (ball D V y (a+2)).card ≤ (a+7)*(a+2)+1)
    (c2 : (ball D V y (a+1)).card ≤ (a+7)*(a+1)+1)
    (c3 : (ball D V y a).card ≤ (a+7)*a+1) : False := by
  have low : ∀ n, n + 1 ≤ a → (ball D V y (a-n)).card ≤ (a+7)*(a-n)+1 := by
    intro n
    induction n with
    | zero => intro _; simpa using c3
    | succ n ih =>
      intro hn
      have h := ih (by omega)
      have e : a - n = (a - n - 2) + 2 := by omega
      rw [e] at h
      have d := fifth_cap_descent R.free R.degree hy (by omega)
        (R.floor _ (by omega) y hy) h
      rwa [show a - n - 2 + 1 = a - (n+1) by omega] at d
  have caps : ∀ r, 1 ≤ r → r ≤ a+3 → (ball D V y r).card ≤ (a+7)*r+1 := by
    intro r h1 h2
    rcases (by omega : r ≤ a ∨ r = a+1 ∨ r = a+2 ∨ r = a+3) with h | rfl | rfl | rfl
    · have := low (a - r) (by omega)
      rwa [show a - (a - r) = r by omega] at this
    · exact c2
    · exact c1
    · exact (R.inner y hy).le
  refine narrow_root_false R (by omega) (by omega) (by omega) (by omega) hy (fun j hj hji => ?_)
  have e := ShapeClimbRoot.card_ball_succ (D := D) (V := V) (u := y) (j-1)
  rw [Nat.sub_add_cancel hj] at e
  have h1 := caps j hj hji
  have h2 := R.floor (j-1) (by omega) y hy
  have h3 : (a+7)*j = (a+7)*(j-1) + (a+7) := by
    rw [← Nat.mul_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel hj]
  omega

#print axioms rigid_false_of_second_cap
#print axioms fifth_rigid_false_of_second_cap
#print axioms fifth_cap_descent
#print axioms fifth_rigid_false_of_top_caps
end LeanCH.BR.RigidSecondCap
