import checkpoints.shen_extension.AvoidedHeadQuota

namespace LeanCH.BR.AvoidedHeadQuota
open Finset BRq2 BRq3 BR45 BypassRepair CHRuleCatalog FragmentScoreEquality ProjectedQuotaTransfer

/-- A boundary-regular head bank of a narrow root supplies the complete
rectangle on that same row and its actual second shell. -/
theorem boundary_exit {D V q r t a d m} (free : QFree D V q) (live : V.Nonempty)
    (reg : OutEq r D V) (cut : 3≤q) (boundary : Compose.Boundary.BoundaryRegular q t)
    (small : NoHost q a) (none : NoHost q d) (order : V.card≤3*r)
    (low : V.card+t≤3*r+2) (mult : r=q*t+1) (below : t<r)
    (size : r-t≤q*a) (need : m+a≤r+(r-t)+1) (pos : 0<m) (fit : m≤q*d)
    (room : V.card+d≤2*r+m) : False := by
  obtain ⟨_,_,v,vm,_,_,cheap,sz,paid⟩ := first_bank free live reg cut order (d:=t) (by omega)
  let H := outN D V v
  let Y := ball D V v 2 \ ball D V v 1
  have hv : H⊆V := outN_subset
  have hs : H.card=r := sz
  have one := ReachLedger.ball_one free (by omega) vm
  rw [sz] at one
  have inc : ball D V v 1⊆ball D V v 2 := ball_mono_radius (by omega)
  have ys : Y.card=(ball D V v 2).card-(ball D V v 1).card := card_sdiff_of_subset inc
  have grow := card_le_card inc
  have eq := WeightedSD.boundary_regular_out_on_set boundary (free.mono_set hv)
    (fun x xm=>loopfree free (by omega) (hv xm)) (hs.trans mult) paid
  obtain ⟨h,hm⟩ := card_pos.mp (show 0<H.card by omega)
  have head := SharedHeadSuppliers.layer_split free (by omega) vm hm
  change (outN D V h).card≤(outN D H h).card+Y.card at head
  rw [reg h (hv hm),eq h hm] at head
  have shell : Y.card+t=r := by omega
  have rectangle_bank := SharedHeadSuppliers.low_bank free (by omega) reg
    (RootRegularBridge.inRegular_of_boundaryRegular (by omega) boundary) mult vm shell
  apply rectangle (H:=H) (Y:=Y) free cut small none (fun x xm=>(reg x xm).ge) hv
    (sdiff_subset.trans ball_subset) (card_pos.mp (by omega)) (by omega)
    (fun x xm y ym=>(mem_outN.mp ((rectangle_bank x xm).2 ym)).2) (by omega) pos fit (by omega)

/-- Arithmetic projection of the physical rectangle. Both lower quotas
are spendable through the supplied table, and the rectangle producer can
also consume any independently supplied boundary law. -/
@[ch_numeric_guard] def BoundaryWindow (n r q floor : ℕ) : Prop :=
  let t := (r-1)/q
  let a := CH.ceilDiv (r-t) q
  3≤q ∧ 2≤t ∧ ¬WeightedSD.NativePressureRegion q t ∧ r=q*t+1 ∧ t<r ∧
  n≤3*r ∧ n+t≤3*r+2 ∧ a<floor ∧ r-t≤q*a ∧
  ∃d∈range floor, let m:=min (q*d) (r+(r-t)+1-a)
                  0<m ∧ m+a≤r+(r-t)+1 ∧ n+d≤2*r+m

instance {n r q floor} : Decidable (BoundaryWindow n r q floor) := by
  unfold BoundaryWindow WeightedSD.NativePressureRegion
  infer_instance

theorem window_excluded {p : Input} {floor} (bad : Bad p)
    (known : ∀k,k<floor → NoHost (cutoff p) k) : ¬BoundaryWindow p.n p.s (cutoff p) floor := by
  rintro ⟨cut,two,region,mult,below,order,low,am,size,d,dm,pos,need,room⟩
  obtain ⟨E,sub,reg⟩ := exists_outEq (fun v (vm : v∈range p.n)=>Compose.FloorSix.out_card bad.degree (mem_range.mp vm))
  have free := qfree_sub sub (qfree_of_noShort bad.loopless bad.missing)
  apply boundary_exit free (nonempty_range_iff.mpr bad.order.ne') reg cut
    (WeightedSD.boundary_regular_outside_pressure_region cut two region) (known _ am) (known d (mem_range.mp dm))
    (by rwa [card_range]) (by rwa [card_range]) mult below size need pos (min_le_left _ _) (by rwa [card_range])

attribute [aesop safe forward (immediate := [bad,known]) (rule_sets := [CHGraphFamilies])] window_excluded
#print axioms boundary_exit
#print axioms window_excluded
end LeanCH.BR.AvoidedHeadQuota
