import checkpoints.shen_extension.MixedBankSupply
namespace LeanCH.BR.MixedShellUniform
open Finset BRq2 BRq3 BR45 BRsGen ShellBankOrders GuardedLayerGrowth FullRowEscape RetainedMixedCapacity
open ConsecutiveShellBanks ExpandedBankRows OneSpareGrowth

theorem two_rank {D V q r x} (free : QFree D V q) (hq : 5≤q) (reg : OutEq r D V) (root : x∈V)
    (hr : 4≤r) (range : r+2≤2*q) (cost : (2*r)*(2*r+1)≤r*(2*r+6)+r*12)
    (width : (ball D V x 2).card=2*r+1) (low : (ball D V x 3).card≤3*r-1) : False := by
  let W := (ball D V x 2).erase x
  let H := outN D V x
  have wh : H⊆W := by
    rw [show H=(ball D V x 1).erase x from (erase_ball_one_eq_outN free (by omega) root).symm]
    exact erase_subset_erase _ (ball_mono_radius (by decide : 1≤2))
  have dw : W.card=2*r := by dsimp [W]; rw [card_erase_of_mem (self_mem_ball root),width,Nat.add_sub_cancel]
  have dh : H.card=r := reg x root
  have lim := card_sdiff_of_subset wh
  have diff := card_sdiff_add_card_eq_card (ball_mono_radius (D:=D) (W:=V) (u:=x) (by decide : 2≤3))
  have rr := minOut_prefix_erase (d:=2) free root (by omega : 2+1≤q) (fun z zm=>(reg z zm).ge)
    (show 2+(ball D V x 3\ball D V x 2).card≤r by omega)
  exact dense_fragment (free.mono_set (show W⊆V from (erase_subset _ _).trans ball_subset)) hq rr wh
    (fun z zm=>(reg z (outN_subset zm)).ge.trans (card_le_card
      (outN_prefix_erase_root free root (by omega : 1+1≤q) (X_B1 zm)))) hr range
    (card_pos.mp (by omega)) (by omega) (by rw [dw,dh,show 2*r-r=r by omega]; exact cost)

theorem three_rank {D V q r x} (free : QFree D V q) (hq : 5≤q) (reg : OutEq r D V)
    (root : x∈V) (hr : 4≤r) (range : r≤3*q) (cost : (2*r+1)*(2*r+2)<r*(r+12)+(r+1)*17)
    (width : (ball D V x 2).card=2*r+2) (low : (ball D V x 3).card≤3*r-1) : False := by
  let H := outN D V x
  let W := (ball D V x 2).erase x
  have wh : H⊆W := by
    rw [show H=(ball D V x 1).erase x from (erase_ball_one_eq_outN free (by omega) root).symm]
    exact erase_subset_erase _ (ball_mono_radius (by decide : 1≤2))
  have dw : W.card=2*r+1 := by dsimp [W]; rw [card_erase_of_mem (self_mem_ball root),width]; omega
  have dh : H.card=r := reg x root
  have wv : W⊆V := (erase_subset _ _).trans ball_subset
  have ff := free.mono_set wv
  have diff := card_sdiff_add_card_eq_card (ball_mono_radius (D:=D) (W:=V) (u:=x) (by decide : 2≤3))
  have rr := minOut_prefix_erase (d:=3) free root (by omega : 2+1≤q) (fun z zm=>(reg z zm).ge)
    (show 3+(ball D V x 3\ball D V x 2).card≤r by omega)
  have b3 z (zm : z∈W) : 10≤(ball D W z 3).card :=
    ball_of_min (BRq3.ball_all 4 (by decide)) (ff.mono_bound (by omega)) rr z zm
  have base z (zm : z∈W) : 17≤(ball D W z 2).card+(ball D W z 3).card := by
    have a : 7≤(ball D W z 2).card := ball_of_min (BRq3.ball_all 3 (by decide)) (ff.mono_bound (by omega)) rr z zm
    have := b3 z zm
    omega
  have high z (zm : z∈H) : r+12≤(ball D W z 2).card+(ball D W z 3).card := by
    have quota := (reg z (outN_subset zm)).ge.trans (card_le_card
      (outN_prefix_erase_root free root (by omega : 1+1≤q) (X_B1 zm)))
    have one := card_B1 (ff.mono_bound (by omega : 4≤q)) (wh zm)
    change r≤(outN D W z).card at quota
    have two := PrefixDegreeGrowth.raise_floor (j:=1) (lo:=r+1) (target:=r+2) ff (wh zm)
      (by omega) rr hq (by omega) (by omega) (fun m lo hi=>⟨3,by decide,by decide,by omega,by omega⟩)
    have := b3 z (wh zm)
    change r+2≤(ball D W z 2).card at two
    omega
  have cap := mixed_capacity ff (by omega : 2+3≤q) wh base high
  rw [dh,dw,show 2*r+1-r=r+1 by omega] at cap
  exact cost.not_ge cap

def Room (q r : ℕ) : Prop :=
  MixedRoom q r ∧ 2*r≤3*q+1 ∧ 3≤2*q+2-r ∧ (2*r+1)*(2*r+2)<r*(r+12)+(r+1)*17
instance (q r) : Decidable (Room q r) := by unfold Room; infer_instance

/-- At exact mixed-ball capacity the actual short roots pay their deficit
with disjoint witnesses or missed pairs. The two remaining unequal profiles
each violate the budget on the very same labels. -/
theorem uniform {D V q r} (free : QFree D V q) (reg : OutEq r D V)
    (size : V.card≤5*r) (room : Room q r) :
    ∀x∈V,(ball D V x 2).card=2*r+1 ∧ (ball D V x 3).card=3*r := by
  obtain ⟨mixed,space,many,cost⟩ := room
  have all3 x (xm : x∈V) := mixed_third free mixed reg xm
  obtain ⟨hq,hr,reach,_,_,_,cap⟩ := mixed
  have f4 : 4≤q := by omega
  have all2 x (xm : x∈V) := second_floor free f4 reg (by omega : 0<r) (by omega) xm
  have sum := MixedBankSupply.paid (k:=q-3) (i:=2) (j:=3) (base:=5*r+1)
    free hq reg (by omega) (by omega) (by omega) space (by omega) (by omega) many
    (fun x xm=>by have := all2 x xm; have := all3 x xm; omega) (by
      intro x xm low
      have a := all2 x xm
      have b := all3 x xm
      have one := card_B1 (free.mono_bound f4) xm
      rw [reg x xm] at one
      have cx := @card_B2 D V x
      have cz := @card_B3 D V x
      have bad := two_rank free hq reg xm hr (by omega) cap
      by_cases eq : (ball D V x 2).card=2*r
      · exact ⟨by omega,by omega⟩
      · exact (bad (by omega) (by omega)).elim)
    (fun _ _ _ _=>by omega)
  have eq : (∑_x∈V,(5*r+1))=∑x∈V,((ball D V x 2).card+(ball D V x 3).card) := by
    apply le_antisymm (sum_le_sum sum)
    rw [sum_const_nat (fun _ _=>rfl)]
    exact (Nat.le_add_left _ _).trans ((remote_capacity free (by omega : 2+3≤q)).trans
      (Nat.mul_le_mul_left _ (by omega)))
  have flat := (sum_eq_sum_iff_of_le sum).mp eq
  intro x xm
  have total := flat x xm
  have sec := all2 x xm
  have third := all3 x xm
  by_cases low : (ball D V x 2).card=2*r
  · have one := card_B1 (free.mono_bound f4) xm
    rw [reg x xm] at one
    have sh := @card_B2 D V x
    have ys : (N2 D V x).card+1=r := by omega
    let X := outN D V x
    have dx : X.card=r := reg x xm
    have pos z (zm : z∈X) := internal_positive free f4 xm reg ys zm
    have supply := LocalBallTransfer.light_supply (free.mono_set (show X⊆V from outN_subset))
      (by omega) (card_pos.mp (by omega : 0<X.card)) pos (by omega)
    obtain ⟨w,wm⟩ := card_pos.mp (show 0<(X.filter (fun w=>(outN D X w).card=1)).card by omega)
    obtain ⟨wx,single⟩ := mem_filter.mp wm
    have b := full_row_credit (j:=2) free xm wx (by decide) (by omega) pos
      (sends_layer free f4 xm reg ys wx single)
    simp only [Nat.reduceAdd] at b
    have := flat w (outN_subset wx)
    have := all3 w (outN_subset wx)
    omega
  have impossible := three_rank free hq reg xm hr (by omega) cost
  by_cases high : (ball D V x 2).card=2*r+2
  · exact (impossible high (by omega)).elim
  exact ⟨by omega,by omega⟩

attribute [aesop safe forward (immediate := [free,hq,reg,root,hr,range,cost,width,low]) (rule_sets := [CHGraphFamilies])] two_rank
attribute [aesop safe forward (immediate := [free,hq,reg,root,hr,range,cost,width,low]) (rule_sets := [CHGraphFamilies])] three_rank
attribute [aesop safe forward (immediate := [free,reg,size,room]) (rule_sets := [CHGraphFamilies])] uniform
#print axioms two_rank
#print axioms three_rank
#print axioms uniform
end LeanCH.BR.MixedShellUniform
