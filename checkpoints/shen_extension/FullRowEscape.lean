import checkpoints.shen_extension.RetainedLayerOrders

namespace LeanCH.BR.FullRowEscape
open Finset BRq2 BRq3 BR45 BRsGen RetainedMixedCapacity

/-- In a minimum-two fragment, a row with r heads has a large third
ball. A singleton outer layer leaves all first heads heavy on the same
punctured carrier, so the degree-two deficiency budget applies there. -/
theorem high_third {D W q r x} (free : QFree D W q) (hq : 4≤q) (paid : ∀u∈W,2≤(outN D W u).card)
    (xw : x∈W) (high : r≤(outN D W x).card) (room : r+2≤2*q) :
    r+4 ≤ (ball D W x 3).card := by
  by_contra! low
  let K := (ball D W x 2).erase x
  let H := outN D W x
  have hs : H⊆K := by
    rw [show H=(ball D W x 1).erase x from (erase_ball_one_eq_outN free (by omega) xw).symm]
    exact erase_subset_erase _ (ball_mono_radius (by decide : 1≤2))
  have ff := free.mono_set (show K⊆W from (erase_subset _ _).trans ball_subset)
  have size := card_erase_add_one (a:=x) (self_mem_ball (D:=D) (k:=2) xw)
  change K.card+1=_ at size
  have mono := card_le_card (ball_mono_radius (D:=D) (W:=W) (u:=x) (by decide : 2≤3))
  have first := card_B1 (free.mono_bound hq) xw
  have second := @card_B2 D W x
  have oneTwo := card_le_card (ball_mono_radius (D:=D) (W:=W) (u:=x) (by decide : 1≤2))
  have diff := card_sdiff_add_card_eq_card (ball_mono_radius (D:=D) (W:=W) (u:=x) (by decide : 2≤3))
  have lowerHead := paid x xw
  have kn : K.Nonempty := card_pos.mp (by omega : 0<K.card)
  by_cases store : (ball D W x 2).card=(ball D W x 3).card
  · have rank := minOut_prefix_erase (d:=2) free xw (by omega : 2+1≤q) paid
      (show 2+(ball D W x 3 \ ball D W x 2).card≤2 by omega)
    have cap := corB (by omega : 1≤q) ff rank kn
    omega
  have sec := OneSpareGrowth.second_layer free hq xw paid (by omega) (by omega)
  have min1 := minOut_prefix_erase (d:=1) free xw (by omega : 2+1≤q) paid
    (show 1+(ball D W x 3 \ ball D W x 2).card≤2 by omega)
  have cap := small_one_core_high_count (by omega : 1≤q) ff min1 kn (by omega) hs
    (fun y ym=> (paid y (outN_subset ym)).trans (card_le_card
      (outN_prefix_erase_root free xw (by omega : 1+1≤q) (X_B1 ym))))
  change 2*q+2+(outN D W x).card≤2*K.card at cap
  omega

/-- An equality in a mixed row budget leaves the unmarked rows closed
whenever a single head in H would improve a row's score. The resulting
minimum-degree fragment is on the actual complement W minus H. -/
theorem complement_paid {D W H q i j low high d} (free : QFree D W q) (time : i+j≤q)
    (sub : H⊆W) (degree : ∀u∈W,d≤(outN D W u).card)
    (ordinary : ∀x∈W\H,low≤(ball D W x i).card+(ball D W x j).card)
    (marked : ∀x∈H,high≤(ball D W x i).card+(ball D W x j).card)
    (raises : ∀x∈W\H, ∀y∈H,D x y=true → low<(ball D W x i).card+(ball D W x j).card)
    (full : W.card*(W.card+1)≤H.card*high+(W.card-H.card)*low) :
    ∀x∈W\H,d≤(outN D (W\H) x).card := by
  classical
  let score := fun x=>(ball D W x i).card+(ball D W x j).card
  have a := sum_le_sum ordinary
  have b := sum_le_sum marked
  rw [sum_const_nat (fun _ _=>rfl),card_sdiff_of_subset sub] at a
  rw [sum_const_nat (fun _ _=>rfl)] at b
  have cap := weighted_rows free time (score:=score) (fun _ _=>le_rfl)
  have part := sum_sdiff sub (f:=score)
  change _ ≤ ∑x∈W\H,score x at a
  change _ ≤ ∑x∈H,score x at b
  have eq : (∑_x∈W\H,low)=∑x∈W\H,score x := by
    rw [sum_const_nat (fun _ _=>rfl),card_sdiff_of_subset sub]
    omega
  have row := (sum_eq_sum_iff_of_le ordinary).mp eq
  intro x xm
  apply (degree x (mem_sdiff.mp xm).1).trans (card_le_card ?_)
  intro y ym
  obtain ⟨yw,arc⟩ := mem_outN.mp ym
  exact mem_outN.mpr ⟨mem_sdiff.mpr ⟨yw,fun yh=>(Nat.ne_of_lt (raises x xm y yh arc)) (row x xm)⟩,arc⟩

/-- A dense set H of full rows exhausts (or exceeds) the (2,3) budget.
Equality would trap the actual complementary rows in a minimum-two
fragment too small for the cutoff. -/
theorem dense_fragment {D W q r} {H : Finset ℕ} (free : QFree D W q) (hq : 5≤q)
    (deg : ∀x∈W,2≤(outN D W x).card) (sub : H⊆W) (full : ∀x∈H,r≤(outN D W x).card)
    (high : 4≤r) (room : r+2≤2*q) (live : (W\H).Nonempty) (small : (W\H).card≤2*q)
    (cost : W.card*(W.card+1)≤H.card*(2*r+6)+(W.card-H.card)*12) : False := by
  have baseline x (xm : x∈W) := ball_growth q (by omega) D W free deg x xm
  have loose x (xm : x∈W\H) := baseline x (mem_sdiff.mp xm).1
  have low x (xm : x∈W\H) : 12≤(ball D W x 2).card+(ball D W x 3).card := by
    have := loose x xm 2 (by omega)
    have := loose x xm 3 (by omega)
    omega
  have marked x (xm : x∈H) : 2*r+6≤(ball D W x 2).card+(ball D W x 3).card := by
    have three := high_third free (by omega) deg (sub xm) (full x xm) room
    have first := card_B1 (free.mono_bound (by omega : 4≤q)) (sub xm)
    have second := @card_B2 D W x
    have large := full x xm
    by_cases many : 2*q < (outN D W x).card
    · omega
    have := OneSpareGrowth.second_layer free (by omega : 4≤q) (sub xm) deg (by omega) (by omega)
    omega
  have raises x (xm : x∈W\H) y (ym : y∈H) (arc : D x y=true) :
      12<(ball D W x 2).card+(ball D W x 3).card := by
    have g := forward_gain (j:=1) free (by omega) (mem_sdiff.mp xm).1 (mem_outN.mpr ⟨sub ym,arc⟩)
    have hb := card_B1 (free.mono_bound (by omega : 4≤q)) (sub ym)
    have := loose x xm 3 (by omega)
    have := full y ym
    change (ball D W y 1).card+1≤(ball D W x 2).card at g
    omega
  have trapped := complement_paid free (by omega : 2+3≤q) sub deg low marked raises cost
  have bound := corB (by omega : 1≤q) (free.mono_set (sdiff_subset (s:=W) (t:=H))) trapped live
  omega

attribute [aesop safe forward (immediate := [free,hq,deg,sub,full,high,room,live,small,cost])
  (rule_sets := [CHGraphFamilies])] dense_fragment


attribute [aesop safe forward (immediate := [free,hq,paid,xw,high,room])
  (rule_sets := [CHGraphFamilies])] high_third
attribute [aesop safe forward (immediate := [free,time,sub,degree,ordinary,marked,raises,full])
  (rule_sets := [CHGraphFamilies])] complement_paid

#print axioms high_third
#print axioms complement_paid
#print axioms dense_fragment
end LeanCH.BR.FullRowEscape

