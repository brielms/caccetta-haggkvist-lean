import checkpoints.shen_extension.GuardedLayerGrowth
import LeanCH.BR.BRTwoBallEquality

namespace LeanCH.BR.GuardedLayerGrowth
open Finset BRq2 BRq3 BR45 BRsGen OneSpareGrowth

theorem second_floor {D V q r v} (free : QFree D V q) (hq : 4≤q) (reg : OutEq r D V)
    (pos : 0<r) (room : r≤2*q) (vm : v∈V) : 2*r≤(ball D V v 2).card := by
  have count := reg v vm
  have lower := second_layer free hq vm (fun w wm=>(reg w wm).ge) (by omega) (by omega)
  rw [card_B2,card_B1 (free.mono_bound hq) vm,count]
  omega

/-- An extra label at the shared two-ball boundary. If the mixed
two/three-ball budget is tight, every second ball is minimal. The
one-spare successor at any root has a strictly larger second ball. -/
theorem mixed_order {D V q r h} (free : QFree D V q) (hq : 5≤q) (live : V.Nonempty)
    (reg : OutEq r D V) (two : 2≤r) (room : r≤2*q)
    (floor : ∀v∈V,h≤(ball D V v 3).card) (paid : 3*r≤h+2) : 2*r+h≤V.card := by
  have f4 : 4≤q := by omega
  have sec v (vm : v∈V) := second_floor free f4 reg (by omega : 0<r) room vm
  have lim := card_ge_of_two_balls free (by omega : 2+3≤q) sec floor live
  by_contra! low
  have exactBalls := two_balls_boundary_cards free (by omega : 2+3≤q) sec floor (by omega)
  obtain ⟨a,av⟩ := live
  have minA := (exactBalls a av).1
  have num := minA
  rw [card_B2,card_B1 (free.mono_bound f4) av,reg a av] at num
  have last := floor a av
  rw [card_B3,minA] at last
  obtain ⟨w,wm,tall,_⟩ := tall_successor free f4 av reg two room (by omega) (by omega)
  exact (Nat.ne_of_gt tall) (exactBalls w (outN_subset wm)).1

/-- Here only the arithmetic thresholds are specialized. The returning
row, the retained degree-three fragment and the mixed endpoint are generic. -/
theorem third_floor_eight {D V q a} (free : QFree D V q) (hq : 5≤q) (av : a∈V)
    (reg : OutEq 8 D V) : 23≤(ball D V a 3).card := by
  have f4 : 4≤q := by omega
  have room : 8≤2*q := by omega
  have sec := second_floor free f4 reg (by decide : 0<8) room av
  have sum := @card_B3 D V a
  by_contra! low
  have mono := card_le_card (ball_mono_radius (D:=D) (W:=V) (u:=a) (by decide : 2≤3))
  by_cases short : (ball D V a 2).card=16
  · have sh := short
    rw [card_B2,card_B1 (free.mono_bound f4) av,reg a av] at sh
    have bank := guarded_third (k:=3) free f4 av reg (by decide) (by omega)
      (by omega) room (by decide)
    omega
  by_cases next : (ball D V a 2).card=17
  · have cap := fragment_budget (t:=3) free f4 av reg room (by decide) (by omega) (by omega)
    have size : ((ball D V a 2).erase a).card=16 := by
      rw [card_erase_of_mem (self_mem_ball av),next]
    dsimp only at cap
    rw [size] at cap
    omega
  have deg v (vm : v∈V) := (reg v vm).ge
  by_cases small : (ball D V a 2).card≤21
  · have step := PrefixDegreeGrowth.small_rank_step (j:=2) (d:=4) free av
      (by omega) deg hq (by decide) (by decide) (by omega) (by omega)
    change (ball D V a 2).card+8<(ball D V a 3).card+4 at step
    omega
  · have step := PrefixDegreeGrowth.small_rank_step (j:=2) (d:=5) free av
      (by omega) deg hq (by decide) (by decide) (by omega) (by omega)
    change (ball D V a 2).card+8<(ball D V a 3).card+5 at step
    omega

theorem order_eight_ge39 {D V q} (free : QFree D V q) (hq : 5≤q) (live : V.Nonempty)
    (degree : ∀v∈V,8≤(outN D V v).card) : 39≤V.card := by
  obtain ⟨F,sub,reg⟩ := exists_outEq degree
  have hf := qfree_sub sub free
  exact mixed_order hf hq live reg (by decide) (by omega) (fun _ vm=>third_floor_eight hf hq vm reg) (by decide)

#print axioms mixed_order
#print axioms third_floor_eight
#print axioms order_eight_ge39
end LeanCH.BR.GuardedLayerGrowth
