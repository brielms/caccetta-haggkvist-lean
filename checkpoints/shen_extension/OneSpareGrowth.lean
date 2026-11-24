import checkpoints.shen_extension.PrefixDegreeGrowth
import checkpoints.shen_extension.DotClonePairCompletion_20261118

namespace LeanCH.BR.OneSpareGrowth
open Finset BRq2 BRq3 BR45 BRsGen DotClonePairCompletion

/-- A row with d actual heads cannot keep minimum degree two on that set
when d ≤ 2q. Its second layer has at least s−1 distinct labels. -/
theorem second_layer {D V q s a} (free : QFree D V q) (hq : 4≤q) (av : a∈V)
    (hm : ∀v∈V,s≤(outN D V v).card) (positive : 0<(outN D V a).card)
    (room : (outN D V a).card≤2*q) : s≤(N2 D V a).card+1 := by
  by_contra! low
  have rank := minOut_prefix_erase (d:=2) free av (by omega : 1+1≤q) hm
    (show 2+(N2 D V a).card≤s by omega)
  rw [erase_ball_one_eq_outN free (by omega) av] at rank
  have bound := corB (by omega : 1≤q) (free.mono_set (outN_subset : outN D V a⊆V)) rank (card_pos.mp positive)
  omega

/-- At local degree t, unmarked rows use 2t+1 slots. A marked row of
degree d uses d+t. All slots are counted on the same finite carrier. -/
theorem marked_capacity {D W q d t} (free : QFree D W q) (hq : 4≤q)
    (two : 2≤t) (cut : t≤q) (degree : ∀v∈W,t≤(outN D W v).card)
    {H : Finset ℕ} (sub : H⊆W)
    (marked : ∀v∈H,(outN D W v).card=d) (room : d≤2*q) :
    2*(H.card*(d+t)+(W.card-H.card)*(2*t+1))≤W.card*(W.card+1) := by
  have rank (v) (hv : v∈H) : d+t≤(ball D W v 2).card := by
    have big := degree v (sub hv)
    have size := marked v hv
    have floor := second_layer free hq (sub hv) degree (by omega) (by omega)
    rw [card_B2,card_B1 (free.mono_bound hq) (sub hv),size]
    omega
  have all3 v (vm : v∈W\H) : 2*t+1≤(ball D W v 2).card :=
    card_ball_two_ge_twice two (free.mono_bound cut) degree (mem_sdiff.mp vm).1
  have left := sum_le_sum rank
  have right := sum_le_sum all3
  rw [sum_const_nat (fun _ _=>rfl)] at left right
  rw [card_sdiff_of_subset sub] at right
  have sum := sum_sdiff sub (f:=fun v=>(ball D W v 2).card)
  have space := incomparable_reach_identity free (by omega : 2+2≤q)
  omega

theorem high_row_capacity {D W q d} (free : QFree D W q) (hq : 4≤q)
    (min3 : ∀v∈W,3≤(outN D W v).card) {H : Finset ℕ} (sub : H⊆W)
    (marked : ∀v∈H,(outN D W v).card=d) (room : d≤2*q) :
    2*(H.card*(d+3)+(W.card-H.card)*7)≤W.card*(W.card+1) :=
  marked_capacity free hq (by decide) (by omega) min3 sub marked room

/-- The geometric hypothesis is the arithmetic capacity deficit. The proof
has no upper bound on the parameter r except what that deficit entails. -/
theorem third_layer {D V q r a} (free : QFree D V q) (hq : 4≤q) (av : a∈V)
    (reg : OutEq r D V) (room : r≤2*q)
    (short : (N2 D V a).card+1=r)
    (deficit : (r+(r-1))*(r+(r-1)+1)<2*(r*(r+3)+(r-1)*7)) :
    r≤(N3 D V a).card+2 := by
  by_contra! low
  let X := outN D V a
  let W := (ball D V a 2).erase a
  have f4 := free.mono_bound hq
  have wx : X⊆W := by
    rw [show X=(ball D V a 1).erase a from (erase_ball_one_eq_outN free (by omega) av).symm]
    exact erase_subset_erase _ (ball_mono_radius (by decide : 1≤2))
  have wv : W⊆V := (erase_subset a _).trans ball_subset
  have min3 : ∀v∈W,3≤(outN D W v).card :=
    minOut_prefix_erase free av (by omega : 2+1≤q) (fun v hv=>(reg v hv).ge)
      (show 3+(N3 D V a).card≤r by omega)
  have high v (vm : v∈X) : (outN D W v).card=r := by
    have inc := outN_prefix_erase_root free av (by omega : 1+1≤q) (X_B1 vm)
    have same : outN D W v=outN D V v := Subset.antisymm (outN_mono wv _) inc
    rw [same,reg v (outN_subset vm)]
  have core := high_row_capacity (free.mono_set wv) hq min3 wx high room
  have wsize : W.card=r+(r-1) := by
    dsimp [W]
    rw [card_erase_of_mem (self_mem_ball av),card_B2,card_B1 f4 av,reg a av]
    omega
  have xsize : X.card=r := reg a av
  rw [wsize,xsize,show r+(r-1)-r=r-1 by omega] at core
  omega

#print axioms second_layer
#print axioms marked_capacity
#print axioms high_row_capacity
#print axioms third_layer
end LeanCH.BR.OneSpareGrowth
