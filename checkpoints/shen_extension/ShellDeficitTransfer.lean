import checkpoints.shen_extension.LoneReturnedHeadReplay

namespace LeanCH.BR.FragmentScoreEquality
open Finset BRq2 BRq3 BR45 BRsGen

/-- The labels gained between two radii consume the original pair budget
once for each root that actually gains them. Both radii remain free. -/
theorem shell_budget {D U q i j} (free : QFree D U q) (radii : i≤j) (time : j+j≤q) :
    (∑v∈U,((ball D U v i).card+(ball D U v j).card))+
    (∑v∈U,(ball D U v j\ball D U v i).card)≤U.card*(U.card+1) := by
  classical
  have total := ReachLedger.ledger (D:=D) (V:=U) free time
  have eqn : (∑v∈U,((ball D U v i).card+(ball D U v j).card))+
      (∑v∈U,(ball D U v j\ball D U v i).card)=
      (∑v∈U,(ball D U v j).card)+(∑v∈U,(ball D U v j).card) := by
    rw [←sum_add_distrib,←sum_add_distrib]
    apply sum_congr rfl
    intro v _
    have h := card_sdiff_add_card_eq_card (ball_mono_radius (D:=D) (W:=U) (u:=v) radii)
    omega
  omega

/-- A strict expansion at one specified root forces a cheap mixed row
on the same carrier. The two rows can coincide. -/
@[aesop safe forward (immediate := [free,radii,time,vm,growth]) (rule_sets := [CHGraphFamilies])]
theorem cheap_from_growth {D U q i j v} (free : QFree D U q) (radii : i≤j)
    (time : j+j≤q) (vm : v∈U) (growth : (ball D U v i).card<(ball D U v j).card) :
    ∃u∈U,(ball D U u i).card+(ball D U u j).card<U.card+1 := by
  classical
  by_contra no
  have low (w) (wm : w∈U) : U.card+1≤(ball D U w i).card+(ball D U w j).card :=
    Nat.le_of_not_gt (fun h=>no ⟨w,wm,h⟩)
  have tight := MixedFragmentEscape.score_equality free time (fun _=>U.card+1)
    (fun w wm=> (low w wm).trans (Nat.add_le_add_right (card_le_card (ball_mono_radius radii)) _))
    (by simp only [sum_const_nat (fun _ _=>rfl),le_refl])
  have := tight v vm
  have := low v vm
  omega

/-- Every positive-quota carrier with four available steps supplies a
cheap row, even after restriction to an arbitrary retained set. -/
theorem cheap_on_positive {D U q} (free : QFree D U q) (time : 4≤q)
    (live : U.Nonempty) (positive : ∀z∈U,0<(outN D U z).card) :
    ∃v∈U,(outN D U v).card+(ball D U v 2).card<U.card := by
  obtain ⟨z,zm,good,_⟩ := power_receiver (k:=1) free live (by omega)
  have one := ReachLedger.ball_one free (by omega) zm
  have pos := positive z zm
  obtain ⟨v,vm,cheap⟩ := cheap_from_growth free (by decide : 1≤2) time zm
    (by change 2*(ball D U z 1).card≤(ball D U z 2).card+1 at good; omega)
  have := ReachLedger.ball_one free (by omega) vm
  exact ⟨v,vm,by omega⟩

attribute [aesop safe forward (immediate := [free,time,live,positive]) (rule_sets := [CHGraphFamilies])] cheap_on_positive

#print axioms shell_budget
#print axioms cheap_from_growth
#print axioms cheap_on_positive
end LeanCH.BR.FragmentScoreEquality
