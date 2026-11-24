import checkpoints.shen_extension.DistinctReceiverBudget
import checkpoints.shen_extension.SharedBankOrderTransfer

namespace LeanCH.BR.DistinctReceiverBudget.Tests
open Finset BRq2 BRq3 BR45 CHRuleCatalog

example {p c : Input} (start : Bad p) (edit : Child p c) :
    ¬FifthTransfer c.n c.s (cutoff c) ∧
      ¬SharedBankOrderTransfer.Window c.n c.s (cutoff c) ProjectedQuotaTransfer.projectionFloor := by
  replay_ch_typed_families
  constructor <;> assumption

/-- One historical endpoint checks the symbolic window and its ordinary replay exit. -/
example {p : Input} {D : CH.Digraph} (start : Bad p) (edit : Child p ⟨35,9,D⟩) : False := by
  replay_ch_typed_families

example {D V q i j} {A : Finset ℕ} {next base : ℕ → ℕ} {cost : ℕ}
    (free : QFree D V q) (time : i+j≤q) (senders : A⊆V)
    (arcs : ∀x∈A, next x∈V ∧ D x (next x)=true)
    (floor : ∀x∈V, base x≤score D V i j x)
    (price : ∀x∈A, base (next x)+cost≤score D V i j (next x))
    (overbooked : V.card*(V.card+1) <
      (∑ x∈V, base x) + A.card*cost + (∑ x∈V, (ReachLedger.gap D V i j x).card)) :
    ∃ x∈A, ∃ y∈A, x≠y ∧ next x=next y ∧
      x∈inN D V (next x) ∧ y∈inN D V (next x) := by
  replay_ch_typed_families
  assumption
end LeanCH.BR.DistinctReceiverBudget.Tests

namespace LeanCH.BR.SharedBankOrderTransfer.Tests
open Finset BRq2 BRq3 BR45 BRsGen BypassRepair GuardedLayerGrowth FragmentScoreEquality

/-- Diagnose the remaining radius-two premise in the next paper-covered order. -/
private theorem tight_profile_suffices {D V} (safe : QFree D V 5) (rows : OutEq 9 D V)
    (known : ∀d,d<9 → NoHost 5 d) (order : V.card=43)
    (tight : ∀x∈V, (ball D V x 2).card=18 → 26≤(ball D V x 3).card) : False := by
  have thirdFloor (x) (hx : x∈V) : 26≤(ball D V x 3).card := by
    have lower := second_floor safe (by decide) rows (by decide) (by decide) hx
    by_cases tightHere : (ball D V x 2).card=18
    · exact tight x hx tightHere
    by_cases mid : (ball D V x 2).card=19
    · by_contra! short
      have layer := card_sdiff_add_card_eq_card (ball_mono_radius (D:=D) (W:=V) (u:=x) (by decide : 2≤3))
      have bill := RetainedMixedCapacity.prefix_capacity (a:=1) (i:=2) (j:=3) (r:=9) (t:=3)
        (base:=17) (high:=23) safe hx (by decide) (by decide) (fun v hv=>(rows v hv).ge)
        (by change 3+(ball D V x 3 \ ball D V x 2).card≤9; omega) (fun W free deg y hy=>by
          have a : 7≤(ball D W y 2).card := ball_of_min (BRq3.ball_all 3 (by decide)) (free.mono_bound (by decide)) deg y hy
          have b : 10≤(ball D W y 3).card := ball_of_min (BRq3.ball_all 4 (by decide)) (free.mono_bound (by decide)) deg y hy
          omega) (fun W free deg y hy full=>by
          have a := grow_seed (k:=1) (j:=1) free hy deg full (by decide) (known 3 (by decide)) (by decide) (by decide) (by decide)
          have b := grow_seed (k:=2) (j:=2) free hy deg full (by decide) (known 3 (by decide)) (by decide) (by decide) (by decide)
          change 11≤(ball D W y 2).card at a
          change 12≤(ball D W y 3).card at b
          omega)
      dsimp only at bill
      simp only [card_erase_of_mem (self_mem_ball hx), mid, Nat.reduceSub,
        ReachLedger.ball_one safe (by decide) hx, rows x hx, Nat.reduceAdd, Nat.reduceMul] at bill
      omega
    · apply GuardedProfileBudget.third (b₀:=20) safe rows hx (by omega)
        (K:=range 9) (fun d hd=>known d (mem_range.mp hd))
      decide
  have h := mixed_order safe (by decide) (card_pos.mp (by omega)) rows (by decide) (by decide) thirdFloor (by decide)
  omega
#print axioms tight_profile_suffices
end LeanCH.BR.SharedBankOrderTransfer.Tests
