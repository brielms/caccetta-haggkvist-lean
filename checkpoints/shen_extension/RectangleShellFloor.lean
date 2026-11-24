import checkpoints.shen_extension.BoundaryRectangleReplay

namespace LeanCH.BR.AvoidedHeadQuota
open Finset BRq2 BRq3 BR45 BypassRepair CHRuleCatalog FragmentScoreEquality ProjectedQuotaTransfer

/-- Strengthen the two-ball floor at every actual row. No cheap root,
fixed order or upper bound by three times the degree is assumed. -/
theorem every_ball {D V q r t a d m} (free : QFree D V q) (reg : OutEq r D V)
    (cut : 3≤q) (boundary : Compose.Boundary.BoundaryRegular q t)
    (above : NoHost q (t+1)) (small : NoHost q a) (none : NoHost q d)
    (mult : r=q*t+1) (below : t<r) (size : r-t≤q*a)
    (need : m+a≤r+(r-t)+1) (pos : 0<m) (fit : m≤q*d) (room : V.card+d≤2*r+m) :
    ∀v∈V,2*r+2≤(ball D V v 2).card+t := by
  intro v vm
  have cap : r≤q*(t+1) := by rw [mult,Nat.mul_add]; omega
  have floor := SharedHeadSuppliers.layer_floor above free (by omega) reg (by omega) cap vm
  by_contra! low
  have shell := SharedHeadSuppliers.low_shell free (by omega) reg vm (by omega : (ball D V v 2).card+t=2*r+1)
  have banks := SharedHeadSuppliers.low_bank free (by omega) reg
    (RootRegularBridge.inRegular_of_boundaryRegular (by omega) boundary) mult vm shell
  apply rectangle (H:=outN D V v) (Y:=ball D V v 2 \ ball D V v 1) free cut small none
    (fun x xm=>(reg x xm).ge) outN_subset (sdiff_subset.trans ball_subset)
    (card_pos.mp (by omega)) (by omega) (fun x xm y ym=>(mem_outN.mp ((banks x xm).2 ym)).2)
    (by omega) pos fit (by rw [reg v vm]; omega)

attribute [aesop safe forward (immediate := [free,reg,cut,boundary,above,small,none,mult,below,size,need,pos,fit,room])
  (rule_sets := [CHGraphFamilies])] every_ball

/-- On the remaining top order the narrow root and its opposite large
row survive on the same carrier. Return the complete interval of possible
sizes, retaining the narrow row's native head set. -/
theorem opposite_profile {D V q r t a d m} (free : QFree D V q) (live : V.Nonempty)
    (reg : OutEq r D V) (cut : 3≤q) (boundary : Compose.Boundary.BoundaryRegular q t)
    (above : NoHost q (t+1)) (small : NoHost q a) (none : NoHost q d)
    (mult : r=q*t+1) (below : t<r) (size : r-t≤q*a)
    (need : m+a≤r+(r-t)+1) (pos : 0<m) (fit : m≤q*d) (room : V.card+d≤2*r+m)
    (order : V.card≤3*r) :
    ∃x∈V,∃y∈V,x≠y ∧ 2*r+1≤(ball D V x 2).card ∧ 2*r+2≤(ball D V y 2).card+t ∧
      (ball D V y 2).card+r<V.card ∧
      ∀h∈outN D V y,2*r+1≤(outN D (outN D V y) h).card+(ball D V y 2).card := by
  have all := every_ball free reg cut boundary above small none mult below size need pos fit room
  obtain ⟨x,xm,y,ym,ne,high,low,_,_⟩ := first_bank (d:=0) free live reg cut order (by omega)
  refine ⟨x,xm,y,ym,ne,high,all y ym,by omega,?_⟩
  intro h hm
  have split := SharedHeadSuppliers.layer_split free (by omega) ym hm
  rw [reg h (mem_outN.mp hm).1,card_sdiff_of_subset (ball_mono_radius (by omega)),
    ReachLedger.ball_one free (by omega) ym,reg y ym] at split
  have inc := card_le_card (ball_mono_radius (D:=D) (W:=V) (u:=y) (by decide : 1≤2))
  rw [ReachLedger.ball_one free (by omega) ym,reg y ym] at inc
  omega

attribute [aesop safe forward (immediate := [free,live,reg,cut,boundary,above,small,none,mult,below,size,need,pos,fit,room,order])
  (rule_sets := [CHGraphFamilies])] opposite_profile
#print axioms every_ball
#print axioms opposite_profile
end LeanCH.BR.AvoidedHeadQuota
