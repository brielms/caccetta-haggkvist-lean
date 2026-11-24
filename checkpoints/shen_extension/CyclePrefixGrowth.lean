import checkpoints.shen_extension.FullRowsOnShortestCycle

namespace LeanCH.BR.FullRowsOnShortestCycle
open Finset BRq2 BRq3 BR45 BRsGen

/-- A small punctured prefix with at least four interior rows cannot
lose less than the whole native quota at its outer boundary. -/
theorem prefix_growth {D V q r k u} (free : QFree D V q) (uv : u∈V)
    (degree : ∀x∈V,r≤(outN D V x).card) (hr : 2≤r) (hq : 2≤q) (fit : r≤q+1)
    (time : k+2≤q) (many : 4≤((ball D V u k).erase u).card)
    (last : (ball D V u (k+1)\ball D V u k).card≤q)
    (room : ((ball D V u (k+1)).erase u).card≤q+r) :
    r≤(ball D V u (k+2)\ball D V u (k+1)).card := by
  let W := (ball D V u (k+1)).erase u
  let H := (ball D V u k).erase u
  have sub : H⊆W := erase_subset_erase u (ball_mono_radius (by omega))
  have wv : W⊆V := (erase_subset _ _).trans ball_subset
  have eq : W\H=ball D V u (k+1)\ball D V u k := by
    ext a
    simp only [W,H,mem_sdiff,mem_erase]
    have inside := self_mem_ball (D:=D) (k:=k) uv
    grind
  by_contra! small
  have pos := minOut_prefix_erase (d:=1) free uv time degree (show
    1+(ball D V u (k+2)\ball D V u (k+1)).card≤r by omega)
  have bound := at_most_three (free.mono_set wv) hq sub pos
    (fun x (xm : x∈H)=>(degree x (wv (sub xm))).trans (card_le_card
      (outN_prefix_erase_root free uv (by omega : k+1≤q) (mem_of_mem_erase xm)))) hr fit
    (eq ▸ last) room
  change 4≤H.card at many
  omega

/-- Specialize only the *radius* of the prefix. The allowed earlier
shell size, cutoff, and degree are still independent parameters. -/
theorem third_layer {D V q r u} (free : QFree D V q) (uv : u∈V)
    (degree : ∀x∈V,r≤(outN D V x).card) (hr : 4≤r) (hq : 4≤q) (fit : r≤q+1)
    (room : (ball D V u 2).card≤q+r+1) : r≤(N3 D V u).card := by
  have one := card_B1 (free.mono_bound hq) uv
  have two := @card_B2 D V u
  have du := degree u uv
  apply prefix_growth (k:=1) free uv degree (by omega) (by omega) fit (by omega)
  · rw [erase_ball_one_eq_outN free (by omega) uv]
    omega
  · change (N2 D V u).card≤q
    omega
  · rw [card_erase_of_mem (self_mem_ball uv)]
    change (ball D V u 2).card-1≤q+r
    omega

attribute [aesop safe forward (immediate := [free,uv,degree,hr,hq,fit,time,many,last,room])
  (rule_sets := [CHGraphFamilies])] prefix_growth
attribute [aesop safe forward (immediate := [free,uv,degree,hr,hq,fit,room])
  (rule_sets := [CHGraphFamilies])] third_layer
#print axioms prefix_growth
#print axioms third_layer
end LeanCH.BR.FullRowsOnShortestCycle
