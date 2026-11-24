import checkpoints.shen_extension.FirstCyclePrefixPrice

namespace LeanCH.BR.LowShellCycleSelection
open Finset BRq2 BRq3 BR45 BRsGen ExteriorPacking PhysicalCycleStock
open scoped Classical

/-- The physical parent of an extra first head contributes a whole reverse
ball of improved rows. The base score and the extra label use one prefix. -/
theorem short_first_scores {D V q r u C} (free : QFree D V q) (hq : 4≤q) (reg : OutEq r D V)
    (uv : u∈V) (hr : 4≤r) (fit : r≤q+2) (first : C⊆outN D V u)
    (len : q<C.card) (roots : ∀v∈C,Rooted D V v C)
    (two : (N2 D V u).card=r-1) (three : (N3 D V u).card=r-1)
    (four : r≤(ball D V u 4\ball D V u 3).card) (wide : (N2 D V u).card<(exterior D V C).card) :
    (∀v∈C,3*r+2≤(ball D V v 3).card) ∧
    ∃w∈outN D V u, w∉C ∧ ∃a∈C,D a w=true ∧
      let B := ball (fun x y=>D y x) C a 2
      3≤B.card ∧ B⊆C ∧ ∀v∈B,3*r+3≤(ball D V v 3).card := by
  classical
  let Y := N2 D V u
  let E := exterior D V C
  have base := actual_first_price free hq reg uv hr fit first len roots two three
  have b1 := card_B1 (free.mono_bound hq) uv
  rw [reg _ uv] at b1
  have b2 := @card_B2 D V u
  have b3 := @card_B3 D V u
  have b4 := card_sdiff_add_card_eq_card (ball_mono_radius (D:=D) (W:=V) (u:=u) (by decide : 3≤4))
  have cv := first.trans (outN_subset : outN D V u⊆V)
  have inner v (vm : v∈C) := ball_one_growth (free.mono_set cv) (fun a am=>((roots a am).one a am).ge) vm 3 (by omega)
  have normal v (vm : v∈C) := base v vm (ball D C v 3) (ball_subset.trans first) (ShellCycleSupply.lift_ball cv)
  refine ⟨fun v vm=>by have := inner v vm; have := normal v vm; omega,?_⟩
  obtain ⟨w,we,wy⟩ := not_subset.mp (show ¬E⊆Y from fun h=>wide.not_ge (card_le_card h))
  obtain ⟨hit,wc⟩ := mem_sdiff.mp we
  obtain ⟨a,am,aw⟩ := mem_biUnion.mp hit
  have wx := (mem_union.mp (headX (free.mono_bound hq) uv (first am) (outN_subset aw) (mem_outN.mp aw).2)).resolve_right wy
  refine ⟨w,wx,wc,a,am,(mem_outN.mp aw).2,?_,ball_subset,?_⟩
  · exact ball_one_growth (free.reverse.mono_set cv) (reverse_positive (by omega) roots) am 2 (by omega)
  intro v vb
  have vm := ball_subset vb
  obtain ⟨_,j,near,path⟩ := mem_ball.mp vb
  have reach : w∈ball D V v 3 := mem_ball.mpr ⟨outN_subset aw,j+1,by omega,
    ((path.reverse_of_mem am).mono cv).snoc (outN_subset aw) (mem_outN.mp aw).2⟩
  have bound := base v vm (insert w (ball D C v 3)) (insert_subset wx (ball_subset.trans first))
    (insert_subset reach (ShellCycleSupply.lift_ball cv))
  rw [card_insert_of_notMem (fun m=>wc (ball_subset m))] at bound
  have := inner v vm
  omega

/-- Booked stock at an arbitrary score scale when every actual row uses at
most f distinct cycle successors. Keep the exponent of the specific cycle. -/
theorem stock_times_capacity {D V q r k b C f} (t : Selection D V q r k b)
    (cm : C∈booked t) (turn : ∀v∈C,(turns D (booked t) v).card≤f) :
    (∑v∈C,(surplus b (ball D V v k).card:ℚ))≤
      rowStock t (booked t) C*(f*2^omissions D V C r:ℕ) := by
  classical
  by_cases nn : C.Nonempty
  · obtain ⟨v,vm⟩ := nn
    have nz a (am : a∈C) : 0<(turns D (booked t) a).card :=
      card_pos.mpr ⟨_,mem_image_of_mem _ (mem_filter.mpr ⟨cm,am⟩)⟩
    have fpos := (nz v vm).trans_le (turn v vm)
    let L := f*2^omissions D V C r
    have lpos : 0<(L:ℚ) := by dsimp [L]; positivity
    apply (div_le_iff₀ lpos).mp
    rw [sum_div]
    apply sum_le_sum
    intro a am
    unfold share
    rw [←div_eq_mul_one_div,div_div]
    have positive := nz a am
    apply div_le_div_of_nonneg_left (by positivity) (by positivity) 
    dsimp [L]
    push_cast
    gcongr
    exact_mod_cast turn a am
  · simp [not_nonempty_iff_eq_empty.mp nn,rowStock]

#print axioms short_first_scores
#print axioms stock_times_capacity
end LeanCH.BR.LowShellCycleSelection
