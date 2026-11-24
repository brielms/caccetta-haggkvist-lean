import checkpoints.shen_extension.ConsecutiveShellBanks
import checkpoints.shen_extension.FullRowEscape

namespace LeanCH.BR.ShellBankOrders
open Finset BRq2 BRq3 BR45 BRsGen RetainedLayerCapacity RetainedMixedCapacity
open ConsecutiveShellBanks FullRowEscape GuardedLayerGrowth

/-- A profile with two consecutive almost-full banks. -/
private theorem layers {D V q r u} (free : QFree D V q) (cut : 4≤q) (reg : OutEq r D V)
    (uv : u∈V) (first : (ball D V u 2).card=2*r) (last : (ball D V u 3).card=3*r-1)
    (hr : 2≤r) : (N2 D V u).card+1=r ∧ (N3 D V u).card+1=r := by
  have b1 := card_B1 (free.mono_bound cut) uv
  have b2 := @card_B2 D V u
  have b3 := @card_B3 D V u
  have d := reg u uv
  omega

/-- A symbolic lower bound when the three- and three-step relation
saturates. The same short roots support the full-row and missing-pair bills. -/
theorem symmetric_improved {D V q r} (free : QFree D V q) (room : SymmetricRoom r q)
    (reach : r≤2*q-2) (live : V.Nonempty) (degree : ∀v∈V,r≤(outN D V v).card) :
    6*r-1≤V.card := by
  obtain ⟨F,sub,reg⟩ := exists_outEq degree
  have ff := qfree_sub sub free
  have shapes x (xm : x∈V) := symmetric_shape ff reg xm room
  have hq := room.1
  have hr := room.2.1
  by_contra! small
  have paid := paid_shells (i:=3) (j:=3) (k:=q-3) (base:=6*r) ff reg (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (fun x xm=> by have := (shapes x xm).1; omega)
    (fun x xm low=>by
      have a := (shapes x xm).1
      have b : (ball F V x 3).card=3*r-1 := by omega
      exact layers ff (by omega) reg xm ((shapes x xm).2 b.le) b (by omega))
    (fun _ _ _ high=>by omega)
  have bound := card_ge_of_two_balls ff (by omega : 3+3≤q)
    (fun x xm=>(show 3*r≤(ball F V x 3).card by have := paid x xm; omega))
    (fun x xm=>(show 3*r≤(ball F V x 3).card by have := paid x xm; omega)) live
  omega

/-- These inequalities pay for a rank-three fragment in the short
prefix and a rank-two fragment at equality. They depend only on the
parameters and can be checked independently of the labels. -/
def MixedRoom (q r : ℕ) : Prop :=
  5≤q ∧ 4≤r ∧ r≤2*q-2 ∧ 2*r+2≤4*q+1 ∧ 3*r≤5*q+2 ∧
    (2*r)*(2*r+1)<2*(r*(r+3)+r*7) ∧
    (2*r)*(2*r+1)≤r*(2*r+6)+r*12

instance (q r) : Decidable (MixedRoom q r) := by unfold MixedRoom; infer_instance

theorem mixed_third {D V q r v} (free : QFree D V q) (room : MixedRoom q r)
    (reg : OutEq r D V) (root : v∈V) : 3*r-1≤(ball D V v 3).card := by
  obtain ⟨hq,hr,reach,ran4,ran5,capacity,_⟩ := room
  have deg x (xm : x∈V) := (reg x xm).ge
  have sec := second_floor free (by omega : 4≤q) reg (by omega : 0<r) (by omega) root
  have bn := card_B1 (free.mono_bound (by omega : 4≤q)) root
  have dr := reg v root
  by_contra! small
  by_cases low : (ball D V v 2).card=2*r
  · have shape := low
    rw [card_B2,bn,dr] at shape
    have next := guarded_third (k:=q-2) free (by omega) root reg (by omega) (by omega)
      (by omega) (by omega) (by omega)
    rw [card_B3,low] at small
    omega
  by_cases mid : (ball D V v 2).card=2*r+1
  · have next := @card_B3 D V v
    have bound := fragment_budget (t:=3) free (by omega) root reg (by omega) (by decide)
      (by omega) (by omega)
    dsimp only at bound
    rw [card_erase_of_mem (self_mem_ball root),mid,Nat.add_sub_cancel,show 2*r-r=r by omega] at bound
    omega
  have grow := PrefixDegreeGrowth.raise_floor (j:=2) (lo:=2*r+2) (target:=3*r-1) free root
    (by omega) deg hq (by omega) (by omega) (by
      intro m lo hi
      by_cases fit : m≤4*q+1
      · exact ⟨4,by decide,by decide,by omega,by omega⟩
      · exact ⟨5,by decide,by decide,by omega,by omega⟩)
  change 3*r-1≤(ball D V v 3).card at grow
  omega

theorem mixed_order {D V q r} (free : QFree D V q) (room : MixedRoom q r)
    (live : V.Nonempty) (degree : ∀v∈V,r≤(outN D V v).card) : 5*r≤V.card := by
  obtain ⟨F,sub,reg⟩ := exists_outEq degree
  have ff := qfree_sub sub free
  have deg x (xm : x∈V) := (reg x xm).ge
  have third x (xm : x∈V) := mixed_third ff room reg xm
  obtain ⟨hq,hr,reach,ran4,ran5,mid,cap⟩ := room
  have f4 : 4≤q := by omega
  have sec x (xm : x∈V) := second_floor ff f4 reg (by omega : 0<r) (by omega) xm
  by_contra! small
  have paid := paid_shells (i:=2) (j:=3) (k:=q-3) (base:=5*r) ff reg f4 (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega)
    (fun x xm=>by have := sec x xm; have := third x xm; omega)
    (fun x xm low=>by
      have := sec x xm
      have := third x xm
      exact layers ff f4 reg xm (by omega) (by omega) (by omega))
    (fun _ _ a b=>by omega)
  have lower := sum_le_sum paid
  have bound := remote_capacity ff (by omega : 2+3≤q)
  have eq : (∑_x∈V,5*r)=∑x∈V, ((ball F V x 2).card+(ball F V x 3).card) := by
    apply le_antisymm lower
    rw [sum_const_nat (fun _ _=>rfl)]
    exact (Nat.le_add_left _ _).trans (bound.trans (Nat.mul_le_mul_left _ (by omega)))
  have flat := (sum_eq_sum_iff_of_le paid).mp eq
  have low x (xm : x∈V) : (ball F V x 2).card=2*r := by
    have sum := flat x xm
    have floor := third x xm
    have secx := sec x xm
    by_contra ne
    have size : (ball F V x 2).card=2*r+1 := by omega
    let W := (ball F V x 2).erase x
    let H := outN F V x
    have wh : H⊆W := by
      rw [show H=(ball F V x 1).erase x from (erase_ball_one_eq_outN ff (by omega) xm).symm]
      exact erase_subset_erase _ (ball_mono_radius (by decide : 1≤2))
    have dw : W.card=2*r := by dsimp [W]; rw [card_erase_of_mem (self_mem_ball xm),size,Nat.add_sub_cancel]
    have dh : H.card=r := reg x xm
    have lim := card_sdiff_of_subset wh
    have diff := card_sdiff_add_card_eq_card (ball_mono_radius (D:=F) (W:=V) (u:=x) (by decide : 2≤3))
    have rr := minOut_prefix_erase (d:=2) ff xm (by omega : 2+1≤q) deg
      (show 2+(ball F V x 3 \ ball F V x 2).card≤r by omega)
    exact dense_fragment (ff.mono_set (show W⊆V from (erase_subset _ _).trans ball_subset)) hq
      rr wh (fun z zm=>(deg z (outN_subset zm)).trans (card_le_card
        (outN_prefix_erase_root ff xm (by omega : 1+1≤q) (X_B1 zm)))) hr (by omega)
      (card_pos.mp (by omega)) (by omega) (by rw [dw,dh,show 2*r-r=r by omega]; exact cap)
  obtain ⟨u,um⟩ := live
  have small2 := low u um
  have s := small2
  rw [card_B2,card_B1 (ff.mono_bound f4) um,reg u um] at s
  have t := third u um
  rw [card_B3,small2] at t
  obtain ⟨v,vm,big,_⟩ := OneSpareGrowth.tall_successor ff f4 um reg (by omega) (by omega) (by omega) (by omega)
  exact (Nat.ne_of_gt big) (low v (outN_subset vm))

attribute [aesop safe forward (immediate := [free,room,reg,root]) (rule_sets := [CHGraphFamilies])] mixed_third

#print axioms symmetric_improved
#print axioms mixed_third
#print axioms mixed_order

end LeanCH.BR.ShellBankOrders

