import checkpoints.shen_extension.SingleExitProfile
import checkpoints.shen_extension.RenewedPrefixWitness

set_option maxRecDepth 16384
set_option maxHeartbeats 12000000

namespace LeanCH.BR.RecursivePrefixBudget.Tests
open BRq2 BRq3 CHRuleCatalog ProjectedQuotaTransfer

example {p c : Input} (parent : Bad p) (child : Child p c) :
    ¬RecursivePrefixBudget.Window c.n c.s (cutoff c) projectionFloor ∧
      ¬SingleExitProfile.Window c.n c.s (cutoff c) projectionFloor ∧
      ¬RenewedPrefixWitness.Window c.n c.s (cutoff c) projectionFloor := by
  replay_ch_typed_families
  exact ⟨by assumption,by assumption,by assumption⟩

/-- Exercise the marked-row and recursive-completion exits through ordinary replay. -/
example {p : Input} {D : CH.Digraph} (parent : Bad p) (child : Child p ⟨43,9,D⟩) : False := by
  replay_ch_typed_families

example {p : Input} {D : CH.Digraph} (parent : Bad p) (child : Child p ⟨86,9,D⟩) : False := by
  replay_ch_typed_families

example {p : Input} {D : CH.Digraph} (parent : Bad p) (child : Child p ⟨76,9,D⟩) : False := by
  replay_ch_typed_families

example {p : Input} {D : CH.Digraph} (parent : Bad p) (child : Child p ⟨87,9,D⟩) : False := by
  replay_ch_typed_families

/-- At the first order beyond the cutoff-ten bound, the same floors force
    exact forward and backward balls at every physical vertex. -/
example {D V} (free : QFree D V 10) (deg : ∀ u∈V, 9≤(outN D V u).card)
    (known : ∀ t, t<9 → BypassRepair.NoHost 10 t) (order : V.card=87) :
    ∀ u∈V, (BRq2.ball D V u 5).card=44 ∧ (BRq3.reverseBall D V u 5).card=44 := by
  obtain ⟨left,right⟩ := result_valid (q:=10) (d:=9) (by decide) (by decide) known
  have score : (result 10 9).left=44 ∧ (result 10 9).right=44 := by decide
  rw [score.1] at left
  rw [score.2] at right
  have sizes := BRq3.two_balls_boundary_cards free (by decide : 5+5≤10)
    (left D V free deg) (right D V free deg) (by omega)
  intro u hu
  exact ⟨(sizes u hu).1,(sizes u hu).2.2⟩

/-- On the next order the surviving roots carry both tight balls on the
    very same labels. -/
example {D V} (free : QFree D V 10) (deg : ∀u∈V, 9≤(outN D V u).card)
    (known : ∀t,t<9 → BypassRepair.NoHost 10 t) (order : V.card=88) :
    44≤(V.filter (fun u=>(ball D V u 4).card=36 ∧ (ball D V u 5).card=44)).card := by
  have bank := library_sound (q:=10) (by decide) 8 (fun t ht=>known t (by omega))
  have floors {k} (fit : k+1≤10) := (layers_sound (q:=10) (r:=9)
    (bank:=library 10 8) (by decide) (fun c hc=>⟨(bank c hc).1,by have := (bank c hc).2; omega,
      known _ (by have := (bank c hc).2; omega)⟩) k fit).1 D V free deg
  have two := floors (k:=2) (by decide)
  have three := floors (k:=3) (by decide)
  have four := floors (k:=4) (by decide)
  have five := floors (k:=5) (by decide)
  have scores : (layers 10 9 (library 10 8) 2).1=19 ∧ (layers 10 9 (library 10 8) 3).1=28 ∧
      (layers 10 9 (library 10 8) 4).1=36 ∧ (layers 10 9 (library 10 8) 5).1=44 := by decide
  rw [scores.1] at two
  rw [scores.2.1] at three
  rw [scores.2.2.1] at four
  rw [scores.2.2.2] at five
  apply RenewedPrefixWitness.half_rows free (by decide : 5+5≤10) order (Finset.filter_subset ..) five
  intro u hu short
  have one := ReachLedger.ball_one free (by decide) hu
  have small := RenewedPrefixWitness.squeeze (k:=1) (s:=5) (lo:=36) (hi:=43) free hu deg
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) two three short.le
    (three u hu) (two u hu) (show 9+1≤(ball D V u 1).card by have := deg u hu; omega)
    (by decide) (by decide)
  exact Finset.mem_filter.mpr ⟨hu,le_antisymm small (four u hu),short⟩

end LeanCH.BR.RecursivePrefixBudget.Tests
