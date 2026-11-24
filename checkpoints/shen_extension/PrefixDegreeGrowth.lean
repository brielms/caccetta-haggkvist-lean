import LeanCH.BR.BR96

namespace LeanCH.BR.PrefixDegreeGrowth
open Finset BRq2 BRq3 BR45 BRsGen

/-- A theorem about any carrier of minimum degree d can be reapplied inside
any punctured ball. The child is formed with its actual induced graph. -/
theorem step {D V q a j r d N} (free : QFree D V q) (av : a∈V) (dist : j+1≤q)
    (deg : ∀v∈V,r≤(outN D V v).card)
    (child : ∀(W : Finset ℕ), W.Nonempty → W.card≤N → QFree D W q →
      (∀v∈W,d≤(outN D W v).card) → False)
    (positive : 1<(ball D V a j).card) (small : (ball D V a j).card≤N+1) :
    (ball D V a j).card+r < (ball D V a (j+1)).card+d := by
  let B := ball D V a j
  let W := B.erase a
  have eq : W.card=B.card-1 := card_erase_of_mem (self_mem_ball av)
  have sub : W⊆V := (erase_subset a B).trans ball_subset
  have size := card_sdiff_add_card_eq_card (ball_mono_radius (D:=D) (W:=V) (u:=a) (show j≤j+1 by omega))
  by_contra! fail
  apply child W (card_pos.mp (by dsimp [B] at eq; omega)) (by dsimp [B] at eq; omega) (free.mono_set sub)
  exact minOut_prefix_erase free av dist deg (by omega)

theorem small_rank_step {D V q a j r d} (free : QFree D V q) (av : a∈V) (dist : j+1≤q)
    (deg : ∀v∈V,r≤(outN D V v).card) (hq : 5≤q) (low : 2≤d) (high : d≤5)
    (positive : 1<(ball D V a j).card) (fit : (ball D V a j).card≤q*d+1) :
    (ball D V a j).card+r < (ball D V a (j+1)).card+d :=
  step free av dist deg (fun _ ne size f hm => by
    have := BRq6.lower_order hq low (by omega) f hm ne
    omega) positive fit

/-- Check any arithmetic bound for a pair of successive inclusive ball
sizes. Known small-degree theorems act on the actual earlier ball. -/
theorem raise_floor {D V q a j r lo target} (free : QFree D V q) (av : a∈V)
    (dist : j+1≤q) (deg : ∀v∈V,r≤(outN D V v).card) (hq : 5≤q)
    (start : lo≤(ball D V a j).card) (pos : 1<lo)
    (bounds : ∀m,lo≤m → m<target → ∃d,2≤d ∧ d≤5 ∧ m≤q*d+1 ∧ target+d≤m+r+1) :
    target≤(ball D V a (j+1)).card := by
  by_contra! fail
  have mono := card_le_card (ball_mono_radius (D:=D) (W:=V) (u:=a) (show j≤j+1 by omega))
  obtain ⟨d,low,high,fit,up⟩ := bounds _ start (by omega)
  have := small_rank_step free av dist deg hq low high (by omega) fit
  omega

#print axioms step
#print axioms raise_floor
end LeanCH.BR.PrefixDegreeGrowth
