import checkpoints.shen_extension.PuncturedFragmentBudget

namespace LeanCH.BR.FragmentScoreEquality
open Finset BRq2 BRq3 BR45 BRsGen BypassRepair CHRuleCatalog
open OneSpareGrowth GuardedLayerGrowth GuardedProfileBudget ProjectedQuotaTransfer

def ProfileTests (q r h floor : ℕ) : Prop :=
  ∀b∈Ico (2*r+1) (h+1), Covers q r b (h+1) (range floor) ∨
    ∃d∈range floor,∃k∈Icc 2 (q/2), FragmentTest q r b h r k d

instance {q r h floor} : Decidable (ProfileTests q r h floor) := by
  unfold ProfileTests; infer_instance

/-- Under equality in the summed three-ball budget, the exclusion of
larger two-balls makes every root small. Its actual tall successor
contradicts this on the same graph. -/
theorem flat_excludes {D V q r h floor} (free : QFree D V q) (reg : OutEq r D V)
    (live : V.Nonempty) (known : ∀d,d<floor → NoHost q d) (cut : 3+3≤q)
    (rank : 2≤r) (room : r≤2*q) (total : V.card+1≤2*h) (tall : 3*r≤h+2)
    (lower : ∀v∈V,h≤(ball D V v 3).card) (tests : ProfileTests q r h floor) : False := by
  have equal := MixedFragmentEscape.score_equality free cut (fun _=>2*h)
    (fun v vm=>by have := lower v vm; omega)
    (by simpa only [sum_const_nat (fun _ _=>rfl)] using Nat.mul_le_mul_left V.card total)
  have atThree v (vm : v∈V) : (ball D V v 3).card=h := by have := equal v vm; omega
  have atTwo v (vm : v∈V) : (ball D V v 2).card=2*r := by
    have base := second_floor free (by omega) reg (by omega) room vm
    by_contra! diff
    have weak := card_le_card (ball_mono_radius (D:=D) (W:=V) (u:=v) (by decide : 2≤3))
    have three := atThree v vm
    rcases tests (ball D V v 2).card (mem_Ico.mpr ⟨by omega,by omega⟩) with greater|fragment
    · have := third free reg vm le_rfl (fun t tm=>known t (mem_range.mp tm)) greater
      omega
    · obtain ⟨d,dm,k,_,target⟩ := fragment
      have impossible := prefix_exclusion (i:=1) (k:=k) (d:=d) free vm
        (fun x xm=>(reg x xm).ge) (by omega) (fun t lt=>known t (lt.trans_lt (mem_range.mp dm)))
      change ¬FragmentTest q r (ball D V v 2).card (ball D V v 3).card
        ((ball D V v 1).erase v).card k d at impossible
      rw [three,erase_ball_one_eq_outN free (by omega) vm,reg v vm] at impossible
      exact impossible target
  obtain ⟨v,vm⟩ := live
  have two := atTwo v vm
  have three := atThree v vm
  have y := @card_B2 D V v
  rw [card_B1 (free.mono_bound (by omega : 4≤q)) vm,reg v vm] at y
  have z := @card_B3 D V v
  obtain ⟨a,am,big,_⟩ := tall_successor free (by omega) vm reg rank room (by omega) (by omega)
  exact big.ne' (atTwo a (outN_subset am))

@[ch_numeric_guard] def FlatWindow (n r q floor : ℕ) : Prop :=
  let h := (n+2)/2
  3+3≤q ∧ 2≤r ∧ r≤2*q ∧ 3*r≤h+2 ∧
  Covers q r (2*r) h (range floor) ∧ ProfileTests q r h floor

instance {n r q floor} : Decidable (FlatWindow n r q floor) := by
  unfold FlatWindow; infer_instance

theorem replay_flat {p : Input} {floor} (bad : Bad p) (known : ∀t,t<floor → NoHost (cutoff p) t) :
    ¬FlatWindow p.n p.s (cutoff p) floor := by
  rintro ⟨cut,rank,room,tall,heights,tests⟩
  obtain ⟨D,sub,reg⟩ := exists_outEq (fun v (vm : v∈range p.n)=>Compose.FloorSix.out_card bad.degree (mem_range.mp vm))
  have free := qfree_sub sub (qfree_of_noShort bad.loopless bad.missing)
  apply flat_excludes free reg (nonempty_range_iff.mpr bad.order.ne') known cut rank room _ tall _ tests
  · rw [card_range]; omega
  · intro v vm
    exact third free reg vm (second_floor free (by omega) reg (by omega) room vm)
      (fun t tm=>known t (mem_range.mp tm)) heights

theorem replay_at_completed {p : Input} (bad : Bad p) :
    ¬FlatWindow p.n p.s (cutoff p) projectionFloor := replay_flat bad (available_lower_hosts bad)

attribute [aesop safe forward (immediate := [bad,known]) (rule_sets := [CHGraphFamilies])] replay_flat
attribute [aesop safe forward (immediate := [bad]) (rule_sets := [CHGraphFamilies])] replay_at_completed

#print axioms flat_excludes
#print axioms replay_at_completed
end LeanCH.BR.FragmentScoreEquality