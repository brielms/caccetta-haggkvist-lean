import checkpoints.shen_extension.FlatFragmentReplay
import checkpoints.shen_extension.MixedBankSupply

namespace LeanCH.BR.FragmentScoreEquality
open Finset BRq2 BRq3 BR45 BRsGen BypassRepair GuardedLayerGrowth GuardedProfileBudget
open CHRuleCatalog ProjectedQuotaTransfer

/-- A single root at the third-ball floor has a determined two-ball,
even with larger balls elsewhere on the carrier. -/
theorem floor_root_two {D V q r h floor v} (free : QFree D V q) (reg : OutEq r D V)
    (vm : v∈V) (cut : 4≤q) (pos : 0<r) (room : r≤2*q)
    (known : ∀d,d<floor → NoHost q d) (tests : ProfileTests q r h floor)
    (three : (ball D V v 3).card=h) : (ball D V v 2).card=2*r := by
  have base := second_floor free cut reg pos room vm
  by_contra! diff
  have weak := card_le_card (ball_mono_radius (D:=D) (W:=V) (u:=v) (by decide : 2≤3))
  rcases tests (ball D V v 2).card (mem_Ico.mpr ⟨by omega,by omega⟩) with up|fragment
  · have := third free reg vm le_rfl (fun t tm=>known t (mem_range.mp tm)) up
    omega
  · obtain ⟨d,dm,k,_,target⟩ := fragment
    have exclude := prefix_exclusion (i:=1) (k:=k) (d:=d) free vm
      (fun x xm=>(reg x xm).ge) (by omega) (fun t lt=>known t (lt.trans_lt (mem_range.mp dm)))
    change ¬FragmentTest q r (ball D V v 2).card (ball D V v 3).card
      ((ball D V v 1).erase v).card k d at exclude
    rw [three,erase_ball_one_eq_outN free (by omega) vm,reg v vm] at exclude
    exact exclude target

/-- The two-radius bill can be paid at an odd score even when the
ordinary per-row floor is one unit short. Shared marked heads charge
the missing ordered pairs via the existing bank ledger. -/
theorem head_transfer {D V q r h floor k} (free : QFree D V q) (reg : OutEq r D V)
    (known : ∀d,d<floor → NoHost q d) (tests : ProfileTests q r h floor)
    (cut : 3+3≤q) (rank : 2≤r) (room : r≤2*q) (time : k+3≤q)
    (pressure : r≤q+k+1) (space : 2*r≤3*q+1) (many : 3≤2*q+2-r)
    (size : V.card≤2*h) (width : h+1=3*r ∨ h=3*r)
    (lower : ∀v∈V,h≤(ball D V v 3).card) :
    ∀v∈V,h+1≤(ball D V v 3).card := by
  have paid := MixedBankSupply.paid (i:=3) (j:=3) (base:=2*h+1) free (by omega) reg
    rank time pressure space cut (by omega) many
    (fun x xm=>by have := lower x xm; omega) (by
      intro x xm low
      have eq : (ball D V x 3).card=h := by have := lower x xm; omega
      have two := floor_root_two free reg xm (by omega) (by omega) room known tests eq
      have y := @card_B2 D V x
      rw [card_B1 (free.mono_bound (by omega : 4≤q)) xm,reg x xm] at y
      have z := @card_B3 D V x
      constructor
      · omega
      · rcases width with w|w
        · left; omega
        · right; omega) (by
      intro x xm _ score
      rcases width with w|w <;> omega)
  intro v vm
  have := paid v vm
  omega

@[ch_numeric_guard] def HeadWindow (n r q floor : ℕ) : Prop :=
  let h := (n+1)/2
  6≤q ∧ 2≤r ∧ r≤2*q ∧ r≤2*q-2 ∧ 2*r≤3*q+1 ∧ 3≤2*q+2-r ∧
  (h+1=3*r ∨ h=3*r) ∧ Covers q r (2*r) h (range floor) ∧ ProfileTests q r h floor

instance {n r q floor} : Decidable (HeadWindow n r q floor) := by unfold HeadWindow; infer_instance

theorem on_bad {p : Input} {floor} (bad : Bad p) (known : ∀t,t<floor → NoHost (cutoff p) t) :
    ¬HeadWindow p.n p.s (cutoff p) floor := by
  rintro ⟨cut,rank,room,pressure,space,many,width,heights,tests⟩
  obtain ⟨D,sub,reg⟩ := exists_outEq (fun v (vm : v∈range p.n)=>Compose.FloorSix.out_card bad.degree (mem_range.mp vm))
  have free := qfree_sub sub (qfree_of_noShort bad.loopless bad.missing)
  have tall := head_transfer (k:=cutoff p-3) free reg known tests cut rank room
    (by omega) (by omega) space many (by rw [card_range]; omega) width
    (fun x xm=>third free reg xm (second_floor free (by omega) reg (by omega) room xm)
      (fun t tm=>known t (mem_range.mp tm)) heights)
  have cap := card_ge_of_two_balls (i:=3) (j:=3) free cut tall tall (nonempty_range_iff.mpr bad.order.ne')
  rw [card_range] at cap
  omega

theorem at_completed {p : Input} (bad : Bad p) :
    ¬HeadWindow p.n p.s (cutoff p) projectionFloor := on_bad bad (available_lower_hosts bad)

attribute [aesop safe forward (immediate := [bad,known]) (rule_sets := [CHGraphFamilies])] on_bad
attribute [aesop safe forward (immediate := [bad]) (rule_sets := [CHGraphFamilies])] at_completed
#print axioms floor_root_two
#print axioms head_transfer
#print axioms at_completed
end LeanCH.BR.FragmentScoreEquality