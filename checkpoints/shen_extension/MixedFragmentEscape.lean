import checkpoints.shen_extension.LightRowRadius
import checkpoints.shen_extension.GuardedMixedOrder
import checkpoints.shen_extension.CHForwardCatalog

namespace LeanCH.BR.MixedFragmentEscape
open Finset BRq2 BRq3 BR45 BRsGen

/-- On a degree-two carrier, if a ball has at most one exit label in its
next shell, the previous ball gives full rows in the punctured carrier.
The rank-two deficiency theorem bounds all such plateaux at once. -/
@[aesop safe forward (immediate := [free,uv,degree,time,room,exitCap]) (rule_sets := [CHGraphFamilies])]
theorem single_exit {D V q u k} (free : QFree D V q) (uv : u∈V)
    (degree : ∀v∈V,2≤(outN D V v).card) (time : k+2≤q)
    (room : (ball D V u (k+1)).card≤2*q+1)
    (exitCap : (ball D V u (k+2)).card≤(ball D V u (k+1)).card+1) :
    2*q+3+(ball D V u k).card≤2*(ball D V u (k+1)).card := by
  let W := (ball D V u (k+1)).erase u
  let H := (ball D V u k).erase u
  have wv : W⊆V := (erase_subset ..).trans ball_subset
  have sub : H⊆W := erase_subset_erase _ (ball_mono_radius (Nat.le_succ k))
  have ws : W.card+1=(ball D V u (k+1)).card := card_erase_add_one (self_mem_ball uv)
  have hs : H.card+1=(ball D V u k).card := card_erase_add_one (self_mem_ball uv)
  have few : 1+(ball D V u (k+1+1)\ball D V u (k+1)).card≤2 := by
    rw [card_sdiff_of_subset (ball_mono_radius (Nat.le_succ _))]
    change (ball D V u (k+1).succ).card≤(ball D V u (k+1)).card+1 at exitCap
    omega
  have paid := minOut_prefix_erase free uv time degree few
  have big (a) (am : a∈H) : 2≤(outN D W a).card :=
    (degree a (ball_subset (mem_of_mem_erase am))).trans (card_le_card
      (outN_prefix_erase_root free uv (by omega : k+1≤q) (mem_of_mem_erase am)))
  have atOne : (outN D V u).card≤W.card := by
    rw [←erase_ball_one_eq_outN free (by omega : 1≤q) uv]
    exact card_le_card (erase_subset_erase _ (ball_mono_radius (by omega : 1≤k+1)))
  have := degree u uv
  have cap := small_one_core_high_count (by omega : 1≤q) (free.mono_set wv)
    paid (card_pos.mp (by omega)) (by omega) sub big
  omega

/-- Complementary radii give a budget for *different* scores on each
physical row. At equality all of the individual scores are forced. -/
@[aesop safe forward (immediate := [free,time,lower,budget]) (rule_sets := [CHGraphFamilies])]
theorem score_equality {D W q i j} (free : QFree D W q) (time : i+j≤q)
    (f : ℕ→ℕ) (lower : ∀v∈W,f v≤(ball D W v i).card+(ball D W v j).card)
    (budget : W.card*(W.card+1)≤∑v∈W,f v) :
    ∀v∈W,(ball D W v i).card+(ball D W v j).card=f v := by
  classical
  have sum := sum_le_sum (fun v (_ : v∈W)=>reverseBall_add_ball_le (v:=v) free time)
  rw [sum_add_distrib,sum_reverseBall_eq_sum_ball,sum_const_nat (fun _ _=>rfl)] at sum
  have floor := sum_le_sum lower
  have tight : (∑v∈W,f v)=∑v∈W,((ball D W v i).card+(ball D W v j).card) := by
    apply le_antisymm floor
    rw [sum_add_distrib]
    omega
  exact fun v vm=>((sum_eq_sum_iff_of_le lower).mp tight v vm).symm

#print axioms single_exit
#print axioms score_equality
end LeanCH.BR.MixedFragmentEscape
