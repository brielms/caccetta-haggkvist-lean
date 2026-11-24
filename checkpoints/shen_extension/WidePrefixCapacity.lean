import checkpoints.shen_extension.RetainedShellScores
namespace LeanCH.BR.WidePrefixCapacity
open Finset BRq2 BRq3 BR45 BRsGen RetainedShellScores RetainedRadiusLayers RetainedMixedCapacity

/-- Sufficient numerical conditions on the retained rows of a prefix.
The first test invokes a smaller degree, the second and third count
reachable ordered pairs in that same prefix. All radii and degrees in
the cost and both ends of the order range are inputs. -/
def Room (q r s a b c lo hi : ℕ) : Prop :=
  ∀m∈Icc lo hi,
    (∃d∈Icc 2 5,m≤q*d ∧ hi+d≤m+r) ∨
    (hi+2≤m+r ∧ m*(m+1)<load s r m a b c) ∨
    (hi+3≤m+r ∧ m*(m+1)<m*(6*s+2)+c*(6*r-6*s))

instance (q r s a b c lo hi) : Decidable (Room q r s a b c lo hi) := by
  unfold Room
  infer_instance

theorem squeeze {D V q r s k u a b c lo hi} (free : QFree D V q) (uv : u∈V)
    (deg : ∀x∈V,r≤(outN D V x).card) (time : k+4≤q) (radii : 2*s≤q)
    (rs : s≤r) (sr : 3≤s) (room : 2*r+s≤2*q+3)
    (second : ∀x∈V,2*r+1≤(ball D V x 2).card) (third : ∀x∈V,3*r+1≤(ball D V x 3).card)
    (tiny : (ball D V u (k+4)).card≤hi+1)
    (ha : a+1≤(ball D V u (k+2)).card) (hb : b+1≤(ball D V u (k+1)).card)
    (hc : c+1≤(ball D V u k).card) (pos : 0<lo) (cost : Room q r s a b c lo hi) :
    (ball D V u (k+3)).card≤lo := by
  classical
  let L := fun j=>(ball D V u j).erase u
  let W := L (k+3)
  have card i : (L i).card+1=(ball D V u i).card := card_erase_add_one (self_mem_ball uv)
  have cw : W.card+1=(ball D V u (k+3)).card := card _
  have ca := card (k+2)
  have cb := card (k+1)
  have cc := card k
  have ds := card_sdiff_add_card_eq_card (ball_mono_radius (D:=D) (W:=V) (u:=u) (show k+3≤k+4 by omega))
  have nest : L k⊆W := erase_subset_erase _ (ball_mono_radius (by omega : k≤k+3))
  have ff := free.mono_set (show W⊆V from (erase_subset _ _).trans ball_subset)
  by_contra! wide
  rcases cost W.card (mem_Icc.mpr ⟨by omega,by omega⟩) with ⟨d,dm,fit,bad⟩ | ⟨fit,bad⟩ | ⟨fit,bad⟩
  · have lim := PrefixDegreeGrowth.small_rank_step (j:=k+3) free uv time deg (by omega)
      (mem_Icc.mp dm).1 (mem_Icc.mp dm).2 (by omega) (by omega)
    simp only [Nat.reduceAdd, Nat.add_assoc] at lim
    omega
  · have cap := prefix_load free uv deg time radii rs sr room second third (by omega)
    change load s r W.card (L (k+2)).card (L (k+1)).card (L k).card≤W.card*(W.card+1) at cap
    exact bad.not_ge ((load_mono (by omega : a≤(L (k+2)).card) (by omega : b≤(L (k+1)).card)
      (by omega : c≤(L k).card)).trans cap)
  · have three := minOut_prefix_erase (d:=3) free uv time deg
      (show 3+(ball D V u (k+4)\ball D V u (k+3)).card≤r by omega)
    let f := fun x=>(ball D W x s).card+(ball D W x s).card
    have base (x) (xm : x∈W) : 6*s+2≤f x := by
      have h := ball_of_min (BRq3.ball_all (s+1) (by omega)) (ff.mono_bound (by omega)) three x xm
      simp only [Nat.add_sub_cancel] at h
      dsimp only [f]
      omega
    have high x (xm : x∈L k) : 6*s+2+(6*r-6*s)≤f x := by
      have h := two_scores free uv xm (by omega : k+3≤k+3) (by omega) sr sr
      have h3 := third x (ball_subset (mem_of_mem_erase xm))
      change 2*(ball D V x 3).card≤f x at h
      omega
    have raw := increments (j:=0) (k:=0) (f:=f) nest (Subset.rfl : L k⊆L k) (Subset.rfl : L k⊆L k)
      base high (by simpa only [Nat.add_zero] using high) (by simpa only [Nat.add_zero] using high)
    have upper := weighted_rows (i:=s) (j:=s) ff (by omega) (score:=f) (fun _ _=>le_rfl)
    have better := Nat.mul_le_mul_right (6*r-6*s) (show c≤(L k).card by omega)
    simp only [Nat.mul_zero,Nat.add_zero] at raw
    omega

/-- At cutoffs above the degree, a small third ball has a full third
layer. A larger second ball would already expand by the degree-two or
degree-three theorem on that punctured carrier. -/
theorem short_third {D V q r u} (free : QFree D V q) (uv : u∈V)
    (deg : ∀x∈V,r≤(outN D V x).card) (hr : 4≤r) (time : r+2≤q)
    (short : (ball D V u 3).card≤3*r+2) : r≤(N3 D V u).card := by
  apply FullRowsOnShortestCycle.third_layer free uv deg hr (by omega) (by omega)
  by_contra! big
  have ds := card_sdiff_add_card_eq_card (ball_mono_radius (D:=D) (W:=V) (u:=u) (by decide : 2≤3))
  by_cases fit : (ball D V u 2).card≤2*q+1
  · have lim := PrefixDegreeGrowth.small_rank_step (j:=2) (d:=2) free uv (by omega) deg (by omega)
      (by decide) (by decide) (by omega) (by omega)
    simp only [Nat.reduceAdd] at lim
    omega
  · have lim := PrefixDegreeGrowth.small_rank_step (j:=2) (d:=3) free uv (by omega) deg (by omega)
      (by decide) (by decide) (by omega) (by omega)
    simp only [Nat.reduceAdd] at lim
    omega

theorem third_floor {D V q r u} (free : QFree D V q) (uv : u∈V)
    (deg : ∀x∈V,r≤(outN D V x).card) (hr : 4≤r) (time : r+2≤q) :
    3*r+1≤(ball D V u 3).card := by
  by_contra! low
  have step := short_third free uv deg hr time (by omega)
  have prev := card_ball_two_ge_twice (by omega : 2≤r) (free.mono_bound (by omega)) deg uv
  have sum := @card_B3 D V u
  omega

attribute [aesop safe forward (immediate := [free,uv,deg,time,radii,rs,sr,room,second,third,tiny,ha,hb,hc,pos,cost])
  (rule_sets := [CHGraphFamilies])] squeeze
attribute [aesop safe forward (immediate := [free,uv,deg,hr,time,short]) (rule_sets := [CHGraphFamilies])] short_third
attribute [aesop safe forward (immediate := [free,uv,deg,hr,time]) (rule_sets := [CHGraphFamilies])] third_floor
#print axioms squeeze
#print axioms short_third
#print axioms third_floor
end LeanCH.BR.WidePrefixCapacity
