import checkpoints.shen_extension.RecursivePrefixBudget

namespace LeanCH.BR.SingleExitProfile
open Finset BRq2 BRq3 BR45 BypassRepair ParentBankPeel CHRuleCatalog
open FragmentScoreEquality GuardedLayerGrowth GuardedProfileBudget ProjectedQuotaTransfer

/-- A retained quota guarantees two successive increases at a marked high row.
If both are tight, a one-label exit must satisfy the degree-two deficiency law. -/
theorem marked_score {D W q d r y} (free : QFree D W q) (cut : 5≤q)
    (deg : ∀z∈W,d≤(outN D W z).card) (root : y∈W) (full : r≤(outN D W y).card)
    (positive : 0<r) (known : NoHost q d) (room : r+2≤q*d+1) :
    2*r+5+(if 2≤d ∧ r<2*q then 1 else 0) ≤ (ball D W y 2).card+(ball D W y 3).card := by
  have a := grow_seed (k:=1) (j:=1) free root deg full positive known (by omega) (by omega) le_rfl
  have b := grow_seed (k:=2) (j:=2) free root deg full positive known (by omega) room le_rfl
  change r+1+1≤(ball D W y 2).card at a
  change r+2+1≤(ball D W y 3).card at b
  split
  next h =>
    by_contra! small
    have atOne := ReachLedger.ball_one free (by omega) root
    have bill := MixedFragmentEscape.single_exit (k:=1) free root
      (fun z hz=>h.1.trans (deg z hz)) (by omega)
      (by change (ball D W y 2).card≤2*q+1; omega)
      (by change (ball D W y 3).card≤(ball D W y 2).card+1; omega)
    change 2*q+3+(ball D W y 1).card≤2*(ball D W y 2).card at bill
    omega
  next => omega

def Pays (q r b h limit : ℕ) : Prop :=
  ∃d∈Ico 1 limit, r+2≤q*d+1 ∧ d+(h-1-b)≤r ∧
    (b-1)*b < r*(2*r+5+(if 2≤d ∧ r<2*q then 1 else 0))+
      (b-1-r)*(floorTable q d 2+floorTable q d 3+2)

instance {q r b h limit} : Decidable (Pays q r b h limit) := by unfold Pays; infer_instance

theorem prefix_rise {D V q r x h limit} (free : QFree D V q) (cut : 5≤q) (reg : OutEq r D V)
    (root : x∈V) (positive : 0<r) (known : ∀d,d<limit → NoHost q d)
    (paid : Pays q r (ball D V x 2).card h limit) : h≤(ball D V x 3).card := by
  by_contra! short
  obtain ⟨d,dm,room,slots,cost⟩ := paid
  obtain ⟨pos,lt⟩ := mem_Ico.mp dm
  have diff := card_sdiff_add_card_eq_card (ball_mono_radius (D:=D) (W:=V) (u:=x) (by decide : 2≤3))
  have bill := RetainedMixedCapacity.prefix_capacity (a:=1) (i:=2) (j:=3) free root (by omega) (by omega)
    (fun z hz=>(reg z hz).ge)
    (show d+(ball D V x 3 \ ball D V x 2).card≤r by omega)
    (base:=floorTable q d 2+floorTable q d 3+2) (fun W wf wd y hy=>by
      have bounds := floor_table wf wd (fun t ht=>known t (ht.trans lt)) (by omega) pos hy
      have := bounds 2 (by omega)
      have := bounds 3 (by omega)
      omega)
    (fun _ wf wd y hy full=>marked_score wf cut wd hy full positive (known _ lt) room)
  dsimp only at bill
  have sz := card_pos.mpr (show (ball D V x 2).Nonempty from ⟨x,self_mem_ball root⟩)
  simp only [Nat.reduceAdd, card_erase_of_mem (self_mem_ball root), erase_ball_one_eq_outN free (by omega) root,
    reg x root] at bill
  rw [Nat.sub_add_cancel (by omega)] at bill
  omega

def AllProfiles (q r h limit : ℕ) : Prop :=
  ∀ b∈Ico (2*r) h, Pays q r b h limit ∨ Covers q r b h (range limit)
instance {q r h limit} : Decidable (AllProfiles q r h limit) := by unfold AllProfiles; infer_instance

theorem third_floor {D V q r h limit} (free : QFree D V q) (cut : 5≤q) (reg : OutEq r D V)
    (positive : 0<r) (room : r≤2*q) (known : ∀d,d<limit → NoHost q d)
    (profiles : AllProfiles q r h limit) (x) (root : x∈V) : h≤(ball D V x 3).card := by
  have weak := card_le_card (ball_mono_radius (D:=D) (W:=V) (u:=x) (by decide : 2≤3))
  by_contra! low
  have base := second_floor free (by omega) reg positive room root
  rcases profiles _ (mem_Ico.mpr ⟨base,by omega⟩) with paid|covered
  · exact low.not_ge (prefix_rise free cut reg root positive known paid)
  · exact low.not_ge (GuardedProfileBudget.third free reg root le_rfl (fun d hd=>known d (mem_range.mp hd)) covered)

@[ch_numeric_guard] def Window (n r q limit : ℕ) : Prop :=
  5≤q ∧ 2≤r ∧ r≤2*q ∧ AllProfiles q r (neededHeight n r) limit
instance {n r q limit} : Decidable (Window n r q limit) := by unfold Window; infer_instance

theorem excluded {p : Input} {limit} (bad : Bad p) (known : ∀t,t<limit → NoHost (cutoff p) t) :
    ¬Window p.n p.s (cutoff p) limit := by
  rintro ⟨cut,two,room,profiles⟩
  obtain ⟨D,sub,reg⟩ := exists_outEq (fun v (hv : v∈range p.n)=>Compose.FloorSix.out_card bad.degree (mem_range.mp hv))
  have safe := qfree_sub sub (qfree_of_noShort bad.loopless bad.missing)
  have h := height_bills p.n p.s
  have bill := mixed_order safe cut (nonempty_range_iff.mpr bad.order.ne') reg two room
    (third_floor safe cut reg (by omega) room known profiles) h.1
  rw [card_range] at bill
  omega

theorem at_completed {p : Input} (bad : Bad p) : ¬Window p.n p.s (cutoff p) projectionFloor :=
  excluded bad (available_lower_hosts bad)

attribute [aesop safe forward (immediate := [free,cut,deg,root,full,positive,known,room]) (rule_sets := [CHGraphFamilies])] marked_score
attribute [aesop safe forward (immediate := [free,cut,reg,root,positive,known,paid]) (rule_sets := [CHGraphFamilies])] prefix_rise
attribute [aesop safe forward (immediate := [bad,known]) (rule_sets := [CHGraphFamilies])] excluded
attribute [aesop safe forward (immediate := [bad]) (rule_sets := [CHGraphFamilies])] at_completed
#print axioms marked_score
#print axioms prefix_rise
#print axioms at_completed
end LeanCH.BR.SingleExitProfile
