import checkpoints.shen_extension.LastShellRetention

namespace LeanCH.BR.FragmentScoreEquality
open Finset BRq2 BRq3 BR45 BRsGen ParentBankPeel BypassRepair RetainedRadiusLayers

/-- Count three disjoint portions of a punctured three-ball. Middle
rows keep a measured two-ball after the last-step loss and renew
that floor at the smaller quota. Inner rows keep their three-ball
apart from the same outside shell. -/
theorem renewed_three_bill {D V q r u d e s t} (free : QFree D V q) (uv : u∈V)
    (reg : OutEq r D V) (time : 3+3≤q) (pos : 0<d)
    (known : ∀j,j≤d → NoHost q j)
    (two : ∀x∈V,s≤(ball D V x 2).card) (three : ∀x∈V,t≤(ball D V x 3).card)
    (small : (ball D V u 4).card≤(ball D V u 3).card+e)
    (afford : d+e≤r) (seed : 1<s-e) (room : s-e≤q*d+1) :
    let m := (ball D V u 3).card-1
    let a := (ball D V u 2).card-1
    2*((m-a)*(floorTable q d 3+1)+(a-r)*(s-e+1)+r*(t-e))≤m*(m+1) := by
  classical
  let W := (ball D V u 3).erase u
  let A := (ball D V u 2).erase u
  let X := (ball D V u 1).erase u
  have aw : A⊆W := erase_subset_erase _ (ball_mono_radius (by decide : 2≤3))
  have xa : X⊆A := erase_subset_erase _ (ball_mono_radius (by decide : 1≤2))
  have wv : W⊆V := (erase_subset ..).trans ball_subset
  have wf := free.mono_set wv
  have deg : ∀x∈W,d≤(outN D W x).card := by
    apply minOut_prefix_erase free uv (by omega : 3+1≤q) (fun x xm=>(reg x xm).ge)
    rw [card_sdiff_of_subset (ball_mono_radius (Nat.le_succ _))]
    change d+((ball D V u 4).card-(ball D V u 3).card)≤r
    omega
  let f := fun x=>(ball D W x 3).card
  have ordinary x (xm : x∈W) : floorTable q d 3+1≤f x :=
    floor_table wf deg (fun j low=>known j low.le) (by omega) pos xm 3 (by omega)
  have middle x (xm : x∈A) : s-e+1≤f x := by
    have lim := loss_bound (K:=3) (j:=1) free uv xm (by decide) (by omega)
    change (ball D V x 2).card≤(ball D W x 2).card+((ball D V u 4).card-(ball D V u 3).card) at lim
    have start := two x (wv (aw xm))
    exact renew_floor (j:=2) wf (aw xm) deg (known d le_rfl) (by omega) (by omega) seed room
  have inner x (xm : x∈X) : t-e≤f x := by
    have lim := loss_bound (K:=3) (j:=2) free uv xm (by decide) (by omega)
    change (ball D V x 3).card≤f x+((ball D V u 4).card-(ball D V u 3).card) at lim
    have start := three x (wv (aw (xa xm)))
    omega
  have bill := strata aw xa (Subset.refl X) ordinary middle inner inner
  rw [Nat.sub_self,zero_mul,add_zero] at bill
  have cap := RetainedMixedCapacity.weighted_rows wf time
    (score:=fun x=>f x+f x) (fun _ _=>le_rfl)
  rw [sum_add_distrib] at cap
  have total := (Nat.mul_le_mul_left 2 bill).trans (show 2*(∑x∈W,f x)≤W.card*(W.card+1) by omega)
  have xs : X.card=r := by dsimp [X]; rw [erase_ball_one_eq_outN free (by omega) uv,reg u uv]
  have ws : W.card=(ball D V u 3).card-1 := card_erase_of_mem (self_mem_ball uv)
  have asz : A.card=(ball D V u 2).card-1 := card_erase_of_mem (self_mem_ball uv)
  simpa only [xs,ws,asz] using total

#print axioms renewed_three_bill
end LeanCH.BR.FragmentScoreEquality