import checkpoints.shen_extension.FragmentTransitionCatalog

namespace LeanCH.BR.FragmentScoreEquality
open Finset BRq2 BRq3 BR45 BRsGen BypassRepair ParentBankPeel CHRuleCatalog ProjectedQuotaTransfer

/-- A good vertex of the power graph overspends an aggregate two-radius
budget. A distinct physical row underspends the proposed double-radius
floor. Both vertices and their scores refer to the same carrier. -/
theorem opposed_rows {D V q k a b} (free : QFree D V q) (live : V.Nonempty)
    (time : k+2*k≤q) (base : ∀v∈V,a≤(ball D V v k).card)
    (budget : V.card+1≤a+b) (gap : b+1<2*a) :
    ∃x∈V,∃y∈V,x≠y ∧ 2*(ball D V x k).card≤(ball D V x (2*k)).card+1 ∧
      (ball D V y (2*k)).card<b := by
  obtain ⟨x,xm,big,_⟩ := power_receiver free live (by omega : 2*k≤q)
  have large := base x xm
  have short : ∃y∈V,(ball D V y (2*k)).card<b := by
    by_contra! every
    have equal := MixedFragmentEscape.score_equality free time (fun _=>a+b)
      (fun v vm=>Nat.add_le_add (base v vm) (every v vm))
      (by simpa only [sum_const_nat (fun _ _=>rfl)] using Nat.mul_le_mul_left V.card budget)
    have := equal x xm
    omega
  obtain ⟨y,ym,cheap⟩ := short
  exact ⟨x,xm,y,ym,fun same=>by subst y; omega,big,cheap⟩

/-- The narrow row has an actual first head set of size r supporting
the lower quota. The second vertex retains the opposite reach score. -/
theorem first_bank {D V q r d} (free : QFree D V q) (live : V.Nonempty)
    (reg : OutEq r D V) (radius : 3≤q) (order : V.card≤3*r)
    (quota : d+V.card≤3*r+2) :
    ∃x∈V,∃y∈V,x≠y ∧ 2*r+1≤(ball D V x 2).card ∧
      (ball D V y 2).card<V.card-r ∧ (outN D V y).card=r ∧
      ∀z∈outN D V y,d≤(outN D (outN D V y) z).card := by
  have first v (vm : v∈V) : (ball D V v 1).card=r+1 := (ReachLedger.ball_one free (by omega) vm).trans (by rw [reg v vm])
  obtain ⟨v,vm⟩ := live
  have enough := card_le_card (ball_subset (D:=D) (W:=V) (u:=v) (k:=1))
  rw [first v vm] at enough
  obtain ⟨x,xm,y,ym,ne,high,low⟩ := opposed_rows (k:=1) (a:=r+1) (b:=V.card-r) free
    ⟨v,vm⟩ (by omega) (fun a am=>(first a am).ge) (by omega) (by omega)
  change 2*(ball D V x 1).card≤(ball D V x 2).card+1 at high
  change (ball D V y 2).card<V.card-r at low
  rw [first x xm] at high
  refine ⟨x,xm,y,ym,ne,by omega,low,reg y ym,?_⟩
  rw [←erase_ball_one_eq_outN free (by omega) ym]
  apply minOut_prefix_erase free ym (by omega : 1+1≤q) (fun w wm=>(reg w wm).ge)
  rw [card_sdiff_of_subset (ball_mono_radius (Nat.le_succ _)),first y ym]
  change d+((ball D V y 2).card-(r+1))≤r
  have := card_le_card (ball_mono_radius (D:=D) (W:=V) (u:=y) (by decide : 1≤2))
  rw [first y ym] at this
  omega

@[ch_numeric_guard] def HeadQuota (n r q floor : ℕ) : Prop :=
  3≤q ∧ n≤3*r ∧ ∃d∈range floor,d+n≤3*r+2 ∧ r≤q*d

instance {n r q floor} : Decidable (HeadQuota n r q floor) := by unfold HeadQuota; infer_instance

theorem head_quota_exit {p : Input} {floor} (bad : Bad p) (known : ∀d,d<floor → NoHost (cutoff p) d) :
    ¬HeadQuota p.n p.s (cutoff p) floor := by
  rintro ⟨cut,order,d,dm,quota,fit⟩
  obtain ⟨D,sub,reg⟩ := exists_outEq (fun v (vm : v∈range p.n)=>Compose.FloorSix.out_card bad.degree (mem_range.mp vm))
  have free := qfree_sub sub (qfree_of_noShort bad.loopless bad.missing)
  obtain ⟨_,_,y,_,_,_,_,size,deg⟩ := first_bank free (nonempty_range_iff.mpr bad.order.ne') reg cut
    (by rwa [card_range]) (by rwa [card_range])
  exact known d (mem_range.mp dm) D _ (card_pos.mp (size ▸ bad.degree_pos)) (size ▸ fit)
    (free.mono_set outN_subset) deg

theorem quota_at_completed {p : Input} (bad : Bad p) :
    ¬HeadQuota p.n p.s (cutoff p) projectionFloor := head_quota_exit bad (available_lower_hosts bad)

attribute [aesop safe forward (immediate := [free,live,time,base,budget,gap]) (rule_sets := [CHGraphFamilies])] opposed_rows
attribute [aesop safe forward (immediate := [free,live,reg,radius,order,quota]) (rule_sets := [CHGraphFamilies])] first_bank
attribute [aesop safe forward (immediate := [bad,known]) (rule_sets := [CHGraphFamilies])] head_quota_exit
attribute [aesop safe forward (immediate := [bad]) (rule_sets := [CHGraphFamilies])] quota_at_completed
#print axioms opposed_rows
#print axioms first_bank
#print axioms quota_at_completed
end LeanCH.BR.FragmentScoreEquality