import checkpoints.shen_extension.LocalBallTransfer
import LeanCH.BR.BRWideFirstFunnel

namespace LeanCH.BR.LocalBallTransfer
open Finset BRq2 BRq3 BR45 BRsGen

/-- On a positive small carrier, a whole k-ball of rows having two heads
spends at least 2k+1 slots from the strict degree-two deficiency budget.
This reaches an actual one-head row when |W| ≤ q+k+1. -/
theorem reach_light_tight {D V W a k q} (free : QFree D V q) (hq : 1≤q) (sub : W⊆V)
    (aw : a∈W) (degree : ∀v∈V,2≤(outN D V v).card)
    (positive : ∀v∈W,0<(outN D W v).card) (size : W.card≤2*q)
    (fit : k≤q) (pressure : W.card≤q+k+1) : ∃b∈ball D W a k,(outN D W b).card=1 := by
  by_contra! none
  have heavy (v) (vm : v∈ball D W a k) : 2≤(outN D W v).card := by
    have := positive v (ball_subset vm)
    have := none v vm
    omega
  obtain ⟨E,hf,paid,stay⟩ := localize free sub aw degree
    (fun v vm=>heavy v (ball_mono_radius (Nat.sub_le k 1) vm))
  have lower := (ball_growth q hq E V hf paid a (sub aw) k fit).trans (card_le_card (stay k le_rfl))
  have cap := small_one_core_high_count hq (free.mono_set sub) positive ⟨a,aw⟩ size ball_subset heavy
  omega

/-- Count physical one-head rows in the same carrier that supplies the
short paths. No independence or disjointness of their paths is needed. -/
theorem light_supply {D W q} (free : QFree D W q) (hq : 1≤q) (live : W.Nonempty)
    (positive : ∀v∈W,0<(outN D W v).card) (size : W.card≤2*q) :
    2*q+2≤W.card+(W.filter (fun v=>(outN D W v).card=1)).card := by
  classical
  let L := W.filter (fun v=>(outN D W v).card=1)
  have heavy (v) (vm : v∈W\L) : 2≤(outN D W v).card := by
    obtain ⟨wv,off⟩ := mem_sdiff.mp vm
    have ne : (outN D W v).card≠1 := fun eq=>off (mem_filter.mpr ⟨wv,eq⟩)
    have := positive v wv
    omega
  have cap := small_one_core_high_count hq free positive live size sdiff_subset heavy
  have part := card_sdiff_add_card_eq_card (filter_subset (fun v=>(outN D W v).card=1) W)
  change (W\L).card+L.card=W.card at part
  change 2*q+2≤W.card+L.card
  omega

#print axioms reach_light_tight
#print axioms light_supply
end LeanCH.BR.LocalBallTransfer
