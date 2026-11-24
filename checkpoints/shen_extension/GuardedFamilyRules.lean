import checkpoints.shen_extension.GuardedMixedOrder
import checkpoints.shen_extension.OneSpareBoundaryForward
import checkpoints.shen_extension.BankReachTransfer
import checkpoints.shen_extension.SharedBankLedger

namespace LeanCH.BR.GuardedFamilyRules
open Finset BRq2 BRq3 BR45 CHRuleCatalog

/-- A finite-order exclusion on arbitrary carriers. Any certified bound of
this type can be replayed at every affordable degree, cutoff and order. -/
structure OrderBound (q d m : ℕ) : Prop where
  live : 0<m
  bound : ∀D V,QFree D V q → V.Nonempty → (∀v∈V,d≤(outN D V v).card) → m<V.card

@[ch_numeric_guard] def Fits (n r cutoff q d m : ℕ) : Prop := q≤cutoff ∧ d≤r ∧ n+d≤m+r

instance {n r cutoff q d m} : Decidable (Fits n r cutoff q d m) := by unfold Fits; infer_instance

@[aesop safe forward (immediate := [source,rule]) (rule_sets := [CHGraphFamilies])]
theorem forbidden {p q d m} (source : Bad p) (rule : OrderBound q d m) :
    ¬Fits p.n p.s (cutoff p) q d m := by
  rintro ⟨cut,le,fit⟩
  let k := min p.n m
  have pos : 0<k := lt_min source.order rule.live
  have within : k≤p.n := min_le_left ..
  have small : k≤m := min_le_right ..
  have loss : d+(p.n-k)≤p.s := by dsimp only [k]; omega
  have deg (v) (vm : v∈range k) : d≤(outN p.D (range k) v).card := by
    let A := outN p.D (range p.n) v
    let B := outN p.D (range k) v
    have sub : B⊆A := outN_mono (range_mono within) v
    have lost : A\B⊆range p.n\range k := by
      intro w wm
      obtain ⟨wa,off⟩ := mem_sdiff.mp wm
      exact mem_sdiff.mpr ⟨outN_subset wa,fun atK=>off (mem_outN.mpr ⟨atK,(mem_outN.mp wa).2⟩)⟩
    have budget := card_le_card lost
    rw [card_sdiff_of_subset (range_mono within),card_range,card_range] at budget
    have count := card_sdiff_add_card_eq_card sub
    have paid : p.s≤A.card := Compose.FloorSix.out_card source.degree ((mem_range.mp vm).trans_le within)
    change d≤B.card
    omega
  have free := ((qfree_of_noShort source.loopless source.missing).mono_bound cut).mono_set (range_mono within)
  have bound := rule.bound _ _ free (nonempty_range_iff.mpr pos.ne') deg
  rw [card_range] at bound
  exact (Nat.not_lt_of_ge small) bound

/-- Historical specialisation. GuardedProfileBudget registers the profile law. -/
theorem guarded_five : OrderBound 5 8 38 :=
  ⟨by decide,fun _ _ free live deg=>GuardedLayerGrowth.order_eight_ge39 free (by decide) live deg⟩

/-- Historical specialisation of the registered OneSpareGrowth window. -/
theorem guarded_four : OrderBound 4 8 32 :=
  ⟨by decide,fun _ _ free live deg=>OneSpareGrowth.above_four_times free (by decide) live deg
    (by decide) (by decide) (by decide)⟩

attribute [aesop safe forward (immediate := [free,hq,uv,reg,two,short,time,room,pressure])
  (rule_sets := [CHGraphFamilies])] GuardedLayerGrowth.no_return GuardedLayerGrowth.guarded_third

attribute [aesop safe forward (immediate := [free,hq,uv,reg,room,two,rank,loss])
  (rule_sets := [CHGraphFamilies])] GuardedLayerGrowth.fragment_budget

attribute [aesop safe forward (immediate := [free,hq,sub,aw,degree,positive,size,fit,pressure])
  (rule_sets := [CHGraphFamilies])] LocalBallTransfer.reach_light_tight
attribute [aesop safe forward (immediate := [free,hq,live,positive,size])
  (rule_sets := [CHGraphFamilies])] LocalBallTransfer.light_supply
attribute [aesop safe forward (immediate := [safe,vv,pos,early,returns])
  (rule_sets := [CHGraphFamilies])] SharedLayerBarrier.barrier
attribute [aesop safe forward (immediate := [safe,hq,uv,vv,ne,reg,us,vs,wu,wv,coversU,coversV])
  (rule_sets := [CHGraphFamilies])] SharedLayerBarrier.shared_full_remote
attribute [aesop safe forward (immediate := [free,hq,pv,qv,apart,native,paid,small,time,pressure])
  (rule_sets := [CHGraphFamilies])] BankReachTransfer.reaches_bank
attribute [aesop safe forward (immediate := [uv,first])
  (rule_sets := [CHGraphFamilies])] BankReachTransfer.shells
attribute [aesop safe forward (immediate := [paid,inT,miss])
  (rule_sets := [CHGraphFamilies])] SharedBankLedger.witness_budget

#print axioms guarded_five
#print axioms guarded_four
#print axioms forbidden
end LeanCH.BR.GuardedFamilyRules
