import checkpoints.shen_extension.UniformProfileCapacity
namespace LeanCH.BR.SymmetricUniformProfile
open Finset BRq2 BRq3 BR45 BRsGen RetainedLayerCapacity GuardedLayerGrowth ConsecutiveShellBanks

/-- At equality in the equal-radius capacity estimate, the labelled short
roots cannot spend any missing pair without paying their full deficit. -/
theorem third {D V q r} (free : QFree D V q) (reg : OutEq r D V)
    (room : SymmetricRoom r q) (reach : r+2≤2*q) (size : V.card+1≤6*r) :
    ∀x∈V,(ball D V x 3).card=3*r := by
  have hq := room.1
  have hr := room.2.1
  have shape x (xm : x∈V) := symmetric_shape free reg xm room
  have paid := paid_shells (i:=3) (j:=3) (k:=q-3) (base:=6*r) free reg (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) size
    (fun x xm=>by have := (shape x xm).1; omega) (fun x xm low=>by
      have := (shape x xm).1
      have two := (shape x xm).2 (by omega)
      have one := card_B1 (free.mono_bound (by omega : 4≤q)) xm
      rw [reg x xm] at one
      have a := @card_B2 D V x
      have b := @card_B3 D V x
      exact ⟨by omega,by omega⟩)
    (fun _ _ _ large=>by omega)
  have eq : (∑_x∈V,(6*r))=∑x∈V,((ball D V x 3).card+(ball D V x 3).card) := by
    apply le_antisymm (sum_le_sum paid)
    rw [sum_const_nat (fun _ _=>rfl)]
    exact (Nat.le_add_left _ _).trans ((remote_capacity free (by omega : 3+3≤q)).trans (Nat.mul_le_mul_left _ size))
  intro x xm
  have := (sum_eq_sum_iff_of_le paid).mp eq x xm
  omega

/-- If the first two layers have one more label than twice the native
degree, the full rows have a large third ball even on the punctured
carrier. The symmetric capacity then excludes that size. -/
theorem thick {D V q r x} (free : QFree D V q) (reg : OutEq r D V) (root : x∈V)
    (hq : 6≤q) (wide : r+2≤2*q)
    (budget : (2*r+1)*(2*r+2)<r*(2*(r+4))+(r+1)*14)
    (two : (ball D V x 2).card=2*r+2) (three : (ball D V x 3).card=3*r) : False := by
  let W := (ball D V x 2).erase x
  let H := outN D V x
  have wh : H⊆W := by
    rw [show H=(ball D V x 1).erase x from (erase_ball_one_eq_outN free (by omega) root).symm]
    exact erase_subset_erase _ (ball_mono_radius (by decide : 1≤2))
  have wv : W⊆V := (erase_subset _ _).trans ball_subset
  have ff := free.mono_set wv
  have dw : W.card=2*r+1 := by dsimp [W]; rw [card_erase_of_mem (self_mem_ball root),two]; omega
  have dh : H.card=r := reg x root
  have diff := card_sdiff_add_card_eq_card (ball_mono_radius (D:=D) (W:=V) (u:=x) (by decide : 2≤3))
  have paid := minOut_prefix_erase (d:=2) free root (by omega : 2+1≤q) (fun a am=>(reg a am).ge)
    (show 2+(ball D V x 3\ball D V x 2).card≤r by omega)
  have base a (am : a∈W) : 14≤(ball D W a 3).card+(ball D W a 3).card := by
    have := ball_growth q (by omega) D W ff paid a am 3 (by omega)
    omega
  have high a (am : a∈H) : 2*(r+4)≤(ball D W a 3).card+(ball D W a 3).card := by
    have := FullRowEscape.high_third ff (by omega) paid (wh am) ((reg a (outN_subset am)).ge.trans
      (card_le_card (outN_prefix_erase_root free root (by omega : 1+1≤q) (X_B1 am)))) wide
    omega
  have cap := RetainedMixedCapacity.mixed_capacity ff (by omega : 3+3≤q) wh base high
  rw [dw,dh,show 2*r+1-r=r+1 by omega] at cap
  exact budget.not_ge cap

def Capacity (q r : ℕ) : Prop := SymmetricRoom r q ∧ r+2≤2*q ∧
  2*r+3≤3*q+1 ∧ 3*r≤4*q+1 ∧ (2*r+1)*(2*r+2)<r*(2*(r+4))+(r+1)*14
instance (q r) : Decidable (Capacity q r) := by unfold Capacity; infer_instance

theorem uniform {D V q r} (free : QFree D V q) (reg : OutEq r D V)
    (room : Capacity q r) (size : V.card+1≤6*r) :
    ∀x∈V,(ball D V x 2).card=2*r+1 ∧ (ball D V x 3).card=3*r := by
  obtain ⟨sym,wide,fit3,fit4,budget⟩ := room
  have flat := third free reg sym wide size
  have hq := sym.1
  have hr := sym.2.1
  intro x xm
  refine ⟨?_,flat x xm⟩
  have low := second_floor free (by omega : 4≤q) reg (by omega : 0<r) (by omega) xm
  have fixed := flat x xm
  by_cases small : (ball D V x 2).card=2*r
  · have first := card_B1 (free.mono_bound (by omega : 4≤q)) xm
    rw [reg x xm] at first
    have a := @card_B2 D V x
    have b := @card_B3 D V x
    have lows := MixedBankSupply.marked_rows (k:=q-3) free (by omega) xm reg (by omega)
      (by omega) (by omega) (by omega) (.inr (by omega)) (by omega)
    obtain ⟨many,good⟩ := lows
    obtain ⟨v,vm⟩ := card_pos.mp (show 0<((outN D V x).filter (fun v=>(outN D (outN D V x) v).card=1)).card by omega)
    have := (good v vm).2
    have := flat v (outN_subset (mem_filter.mp vm).1)
    omega
  have no := thick free reg xm hq wide budget
  by_cases next : (ball D V x 2).card=2*r+2
  · exact (no next fixed).elim
  by_contra ne
  have mono := card_le_card (ball_mono_radius (D:=D) (W:=V) (u:=x) (by decide : 2≤3))
  have raise d (dl : 2≤d) (du : d≤5) (fits : (ball D V x 2).card≤q*d+1) : (ball D V x 2).card+r<(ball D V x 3).card+d :=
    PrefixDegreeGrowth.small_rank_step (j:=2) free xm (by omega) (fun v vm=>(reg v vm).ge) (by omega) dl du (by omega) fits
  by_cases fits : (ball D V x 2).card≤3*q+1
  · have := raise 3 (by decide) (by decide) (by omega)
    omega
  · have := raise 4 (by decide) (by decide) (by omega)
    omega

theorem order {D V q r d} (free : QFree D V q) (live : V.Nonempty) (degree : ∀x∈V,r≤(outN D V x).card)
    (room : Capacity q r) (fit : UniformProfileCapacity.Fits q r d) : 6*r≤V.card := by
  by_contra! small
  obtain ⟨F,sub,reg⟩ := exists_outEq degree
  have ff := qfree_sub sub free
  exact UniformProfileCapacity.excluded ff live reg fit (uniform ff reg room (by omega))

attribute [aesop safe forward (immediate := [free,reg,room,reach,size]) (rule_sets := [CHGraphFamilies])] third
attribute [aesop safe forward (immediate := [free,reg,root,hq,wide,budget,two,three]) (rule_sets := [CHGraphFamilies])] thick
attribute [aesop safe forward (immediate := [free,reg,room,size]) (rule_sets := [CHGraphFamilies])] uniform
attribute [aesop safe forward (immediate := [free,live,degree,room,fit]) (rule_sets := [CHGraphFamilies])] order
#print axioms third
#print axioms thick
#print axioms uniform
#print axioms order
end LeanCH.BR.SymmetricUniformProfile
