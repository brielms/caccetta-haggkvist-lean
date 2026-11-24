import checkpoints.shen_extension.RecursivePrefixBudget
import checkpoints.shen_extension.WidePrefixCapacity

namespace LeanCH.BR.RenewedPrefixWitness
open Finset BRq2 BRq3 BR45 BRsGen RetainedRadiusLayers RetainedShellScores
open RetainedMixedCapacity
open CHRuleCatalog BypassRepair ProjectedQuotaTransfer

/-- A retained high ball can grow again inside the fragment. The minimum
    degree here belongs to the fragment, and the marked rows belong to C. -/
theorem renewed_load {D W C q j s seed ordinary d} (free : QFree D W q)
    (rank : ∀x∈W,d≤(outN D W x).card) (inside : C⊆W)
    (base : ∀x∈W,ordinary≤(ball D W x s).card)
    (high : ∀x∈C,seed≤(ball D W x j).card) (dist : j≤s) (time : 2*s≤q)
    (cut : 5≤q) (small : 2≤d) (available : d≤5) (pos : 1<seed)
    (room : seed+(s-j)≤q*d+2) (gain : ordinary≤seed+(s-j)) :
    2*(W.card*ordinary+C.card*(seed+(s-j)-ordinary))≤W.card*(W.card+1) := by
  let row := fun x=>(ball D W x s).card
  have high' x (hx : x∈C) : ordinary+(seed+(s-j)-ordinary)≤row x := by
    have h := iterate free (inside hx) rank cut small available
      (show j+(s-j)≤q by omega) room pos (high x hx)
    simpa only [Nat.add_sub_of_le dist, Nat.add_sub_of_le gain] using h
  have score := increments (f:=row) (j:=0) (k:=0) inside (Subset.rfl : C⊆C) (Subset.rfl : C⊆C)
    base high' (by simpa using high') (by simpa using high')
  have upper := weighted_rows (i:=s) (j:=s) free (by omega) (score:=fun x=>row x+row x) (fun _ _=>le_rfl)
  rw [sum_add_distrib] at upper
  simp only [Nat.mul_zero,Nat.add_zero] at score
  omega

/-- At order twice the floor, at least half the physical rows attain it.
    Such rows may be carried into any larger labelled set S. -/
theorem half_rows {D V q j f} {S : Finset ℕ} (free : QFree D V q)
    (time : j+j≤q) (order : V.card=2*f) (sub : S⊆V)
    (base : ∀x∈V,f≤(ball D V x j).card)
    (mark : ∀x∈V,(ball D V x j).card=f → x∈S) : f≤S.card := by
  let T := V\S
  have tv : T⊆V := sdiff_subset
  have high x (hx : x∈T) : f+1≤(ball D V x j).card := by
    have xv := tv hx
    have lo := base x xv
    have ne := mt (mark x xv) (mem_sdiff.mp hx).2
    omega
  have count := increments (j:=0) (k:=0) tv (Subset.rfl : T⊆T) (Subset.rfl : T⊆T)
    base high (by simpa using high) (by simpa using high)
  have up := weighted_rows (i:=j) (j:=j) free time (score:=fun x=>(ball D V x j).card+(ball D V x j).card)
    (fun _ _=>le_rfl)
  rw [sum_add_distrib] at up
  simp only [Nat.mul_zero,Nat.add_zero,Nat.mul_one] at count
  have size : T.card+S.card=V.card := card_sdiff_add_card_eq_card sub
  rw [order] at count up size
  nlinarith

/-- For each possible prefix size choose a smaller quota, a degree-two
    shell charge, or a renewed degree-three charge on the retained rows. -/
def Room (q r s a b c lo hi : ℕ) : Prop :=
  ∀m∈Icc lo hi,
    (∃d∈Icc 2 5, m≤q*d ∧ hi+d≤m+r) ∨
    (hi+2≤m+r ∧ m*(m+1)<load s r m a b c) ∨
    (hi+3≤m+r ∧ 2*(m*(3*s+1)+c*((3*r+1+(s-3))-(3*s+1)))>m*(m+1))
instance {q r s a b c lo hi} : Decidable (Room q r s a b c lo hi) := by unfold Room; infer_instance

theorem squeeze {D V q r s k u a b c lo hi} (free : QFree D V q) (uv : u∈V)
    (deg : ∀x∈V,r≤(outN D V x).card) (time : k+4≤q) (radii : 2*s≤q)
    (rs : s≤r) (sr : 3≤s) (room : 2*r+s≤2*q+3) (renew : 3*r+1+(s-3)≤q*3+2)
    (second : ∀x∈V,2*r+1≤(ball D V x 2).card) (third : ∀x∈V,3*r+1≤(ball D V x 3).card)
    (tiny : (ball D V u (k+4)).card≤hi+1)
    (ha : a+1≤(ball D V u (k+2)).card) (hb : b+1≤(ball D V u (k+1)).card)
    (hc : c+1≤(ball D V u k).card) (pos : 0<lo) (cost : Room q r s a b c lo hi) :
    (ball D V u (k+3)).card≤lo := by
  classical
  let L := fun j=>(ball D V u j).erase u
  let W := L (k+3)
  have card j : (L j).card+1=(ball D V u j).card := card_erase_add_one (self_mem_ball uv)
  have cw : W.card+1=(ball D V u (k+3)).card := card _
  have ds := card_sdiff_add_card_eq_card (ball_mono_radius (D:=D) (W:=V) (u:=u) (show k+3≤k+4 by omega))
  by_contra! wide
  rcases cost W.card (mem_Icc.mpr ⟨by omega,by omega⟩) with ⟨d,dm,fit,bad⟩|⟨keep,bad⟩|⟨keep,bad⟩
  · have lim := PrefixDegreeGrowth.small_rank_step (j:=k+3) free uv time deg (by omega)
      (mem_Icc.mp dm).1 (mem_Icc.mp dm).2 (by omega) (by omega)
    simp only [Nat.add_assoc,Nat.reduceAdd] at lim
    omega
  · have cap := prefix_load free uv deg time radii rs sr room second third (by omega)
    change load s r W.card (L (k+2)).card (L (k+1)).card (L k).card≤W.card*(W.card+1) at cap
    exact bad.not_ge ((load_mono (by have := card (k+2); omega : a≤(L (k+2)).card)
      (by have := card (k+1); omega : b≤(L (k+1)).card) (by have := card k; omega : c≤(L k).card)).trans cap)
  · have ff := free.mono_set (show W⊆V from (erase_subset _ _).trans ball_subset)
    have rank := minOut_prefix_erase (d:=3) free uv time deg
      (show 3+(ball D V u (k+4)\ball D V u (k+3)).card≤r by omega)
    have base x (xm : x∈W) : 3*s+1≤(ball D W x s).card := by
      have f := ball_of_min (BRq3.ball_all (s+1) (by omega)) (ff.mono_bound (by omega)) rank x xm
      simpa only [Nat.add_sub_cancel] using f
    have high x (xm : x∈L k) : 3*r+1≤(ball D W x 3).card := by
      rw [←retained_ball free uv xm (le_refl (k+3)) (by omega : k+3≤q)]
      exact third x (ball_subset (mem_of_mem_erase xm))
    have lower := renewed_load ff rank (show L k⊆W from erase_subset_erase _ (ball_mono_radius (by omega : k≤k+3)))
      base high sr radii (by omega) (by decide) (by decide) (by omega) renew (by omega)
    have up := Nat.mul_le_mul_right ((3*r+1+(s-3))-(3*s+1)) (show c≤(L k).card by have := card k; omega)
    omega

/-- At the boundary of a symmetric ball count, use the same physical
    witness first at radius two, then in its retained fourth ball. -/
theorem witness_order {D V q r f} (free : QFree D V q) (ne : V.Nonempty)
    (degree : ∀x∈V,r≤(outN D V x).card) (time : 10≤q) (rank : 5≤r)
    (room : 2*r+5≤2*q+3) (renew : 3*r+3≤q*3+2)
    (second : ∀x∈V,2*r+1≤(ball D V x 2).card)
    (third : ∀x∈V,3*r+1≤(ball D V x 3).card)
    (fifth : ∀x∈V,f≤(ball D V x 5).card)
    (cost : Room q r 5 (3*r) (2*r) r (4*r) (f-1)) : 2*f≤V.card := by
  rw [two_mul]
  apply RetainedMixedCapacity.strict_order (i:=5) (j:=5) free ne (by omega) fifth fifth
  intro _ _ _
  obtain ⟨u,hu,tall,_⟩ := FragmentScoreEquality.power_receiver (k:=2) free ne (by omega)
  refine ⟨u,hu,?_⟩
  by_contra! little
  have first := degree u hu
  have firstBall := ReachLedger.ball_one free (by omega : 1≤q) hu
  have fourth := squeeze (k:=1) (s:=5) free hu degree (by omega) (by omega)
    rank (by decide) room (by omega) second third (by simpa using (show (ball D V u 5).card≤f-1+1 by omega))
    (third u hu) (second u hu) (by omega) (by omega) cost
  have := second u hu
  change 2*(ball D V u 2).card≤(ball D V u 4).card+1 at tall
  change (ball D V u 4).card≤4*r at fourth
  omega

private def height (q r k : ℕ) : ℕ :=
  (RecursivePrefixBudget.layers q r (RecursivePrefixBudget.library q (r-1)) k).1

@[ch_numeric_guard] def Window (n r q limit : ℕ) : Prop :=
  10≤q ∧ 5≤r ∧ r≤limit ∧ 2*r+5≤2*q+3 ∧ 3*r+3≤q*3+2 ∧ n≤2*(5*r+1) ∧
    n<2*height q r 5 ∧ 2*r+1≤height q r 2 ∧ 3*r+1≤height q r 3 ∧
    Room q r 5 (3*r) (2*r) r (4*r) (height q r 5-1)
instance {n r q limit} : Decidable (Window n r q limit) := by unfold Window; infer_instance

theorem excluded {p : Input} {limit} (bad : Bad p) (known : ∀t,t<limit → NoHost (cutoff p) t) :
    ¬Window p.n p.s (cutoff p) limit := by
  rintro ⟨time,rank,allowed,room,renew,_,small,two,three,cost⟩
  let q := cutoff p
  have bank := RecursivePrefixBudget.library_sound (q:=q) (by omega : 2≤q) (p.s-1)
    (fun t ht=>known t (by omega))
  have safe := qfree_of_noShort bad.loopless bad.missing
  have deg x (hx : x∈range p.n) := Compose.FloorSix.out_card bad.degree (mem_range.mp hx)
  have floor (k) (fit : k+1≤q) := (RecursivePrefixBudget.layers_sound (q:=q) (r:=p.s)
    (bank:=RecursivePrefixBudget.library q (p.s-1)) (by omega)
    (fun c hc=>⟨(bank c hc).1,by have := (bank c hc).2; omega,known _ (by have := (bank c hc).2; omega)⟩)
    k fit).1 p.D (range p.n) safe deg
  have order := witness_order safe (nonempty_range_iff.mpr bad.order.ne') deg time rank room renew
    (fun x hx=>two.trans (floor 2 (by omega) x hx))
    (fun x hx=>three.trans (floor 3 (by omega) x hx)) (floor 5 (by omega)) cost
  rw [card_range] at order
  exact small.not_ge order

theorem at_completed {p : Input} (bad : Bad p) : ¬Window p.n p.s (cutoff p) projectionFloor :=
  excluded bad (available_lower_hosts bad)

attribute [aesop safe forward (immediate := [free,rank,inside,base,high,dist,time,cut,small,available,pos,room,gain]) (rule_sets := [CHGraphFamilies])] renewed_load
attribute [aesop safe forward (immediate := [free,time,order,sub,base,mark]) (rule_sets := [CHGraphFamilies])] half_rows
attribute [aesop safe forward (immediate := [bad,known]) (rule_sets := [CHGraphFamilies])] excluded
attribute [aesop safe forward (immediate := [bad]) (rule_sets := [CHGraphFamilies])] at_completed
#print axioms at_completed
#print axioms renewed_load
#print axioms squeeze
end LeanCH.BR.RenewedPrefixWitness
