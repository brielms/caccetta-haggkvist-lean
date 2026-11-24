import checkpoints.shen_extension.RetainedMixedCapacity

namespace LeanCH.BR.RetainedRadiusLayers
open Finset BRq2 BRq3 BR45 BRsGen RetainedMixedCapacity

/-- Every vertex on the suffix stays inside the same punctured prefix. -/
theorem retained_walk {D V q v x y i j K} (free : QFree D V q) (root : v∈V)
    (start : x∈(ball D V v i).erase v) (suffix : Walk D V x y j)
    (within : i+j≤K) (time : K≤q) : Walk D ((ball D V v K).erase v) x y j ∧
      y∈(ball D V v K).erase v := by
  induction suffix generalizing i with
  | refl =>
    exact ⟨.refl _,erase_subset_erase v (ball_mono_radius (by omega : i≤K)) start⟩
  | @step a b c l bv ab _ ih =>
    have next := outN_prefix_erase_root free root (by omega : i+1≤q) (mem_of_mem_erase start)
      (mem_outN.mpr ⟨bv,ab⟩)
    have nb := outN_subset next
    obtain ⟨tail,last⟩ := ih nb (by omega)
    exact ⟨.step (erase_subset_erase v (ball_mono_radius (by omega : i+1≤K)) nb) ab tail,last⟩

theorem retained_ball {D V q v x i j K} (free : QFree D V q) (root : v∈V)
    (start : x∈(ball D V v i).erase v) (within : i+j≤K) (time : K≤q) :
    ball D V x j = ball D ((ball D V v K).erase v) x j := by
  ext y
  constructor
  · intro hit
    obtain ⟨_,l,ll,path⟩ := mem_ball.mp hit
    obtain ⟨inside,last⟩ := retained_walk free root start path (by omega : i+l≤K) time
    exact mem_ball.mpr ⟨last,l,ll,inside⟩
  · intro hit
    obtain ⟨ym,l,ll,path⟩ := mem_ball.mp hit
    have sub : (ball D V v K).erase v ⊆ V := (erase_subset _ _).trans ball_subset
    exact mem_ball.mpr ⟨sub ym,l,ll,path.mono sub⟩

/-- Add a score increment on a named subset. This can be iterated on as many
    labelled layers as the available bounds justify. -/
theorem add_layer {V H : Finset ℕ} {f g : ℕ→ℕ} {c : ℕ} (sub : H⊆V)
    (base : ∀x∈V,f x≤g x) (extra : ∀x∈H,f x+c≤g x) :
    (∑ x∈V,f x)+H.card*c ≤ ∑ x∈V,g x := by
  have on := sum_le_sum extra
  rw [sum_add_distrib,sum_const_nat (fun _ _=>rfl)] at on
  have off := sum_le_sum (s:=V\H) (fun x hx=>base x (mem_sdiff.mp hx).1)
  have := sum_sdiff sub (f:=f)
  have := sum_sdiff sub (f:=g)
  omega

/-- Sum ordered strata with their actual sizes, vertices included only once. -/
theorem strata {W A B C : Finset ℕ} {f : ℕ→ℕ} {a b c d : ℕ}
    (aw : A⊆W) (ba : B⊆A) (cb : C⊆B)
    (s0 : ∀x∈W,a≤f x) (s1 : ∀x∈A,b≤f x)
    (s2 : ∀x∈B,c≤f x) (s3 : ∀x∈C,d≤f x) :
    (W.card-A.card)*a+(A.card-B.card)*b+(B.card-C.card)*c+C.card*d ≤ ∑x∈W,f x := by
  have h0 := sum_le_sum (s:=W\A) (fun x hx=>s0 x (mem_sdiff.mp hx).1)
  have h1 := sum_le_sum (s:=A\B) (fun x hx=>s1 x (mem_sdiff.mp hx).1)
  have h2 := sum_le_sum (s:=B\C) (fun x hx=>s2 x (mem_sdiff.mp hx).1)
  have h3 := sum_le_sum s3
  rw [sum_const_nat (fun _ _=>rfl),card_sdiff_of_subset aw] at h0
  rw [sum_const_nat (fun _ _=>rfl),card_sdiff_of_subset ba] at h1
  rw [sum_const_nat (fun _ _=>rfl),card_sdiff_of_subset cb] at h2
  rw [sum_const_nat (fun _ _=>rfl)] at h3
  have := sum_sdiff aw (f:=f)
  have := sum_sdiff ba (f:=f)
  have := sum_sdiff cb (f:=f)
  omega

private theorem step2 {D V q x j k} (free : QFree D V q) (hq : 9≤q)
    (rank : ∀x∈V,2≤(outN D V x).card) (xm : x∈V) (time : j+1≤q)
    (start : k≤(ball D V x j).card) (lo : 1<k) (hi : k≤2*q+1) :
    k+1≤(ball D V x (j+1)).card := by
  apply PrefixDegreeGrowth.raise_floor free xm time rank (by omega) start lo
  intro m low high
  exact ⟨2,by decide,by decide,by omega,by omega⟩

private theorem scored2 {D V q x} (free : QFree D V q) (hq : 9≤q)
    (rank : ∀x∈V,2≤(outN D V x).card) (xm : x∈V) :
    let score := (ball D V x 4).card+(ball D V x 5).card
    20≤score ∧ (8≤(outN D V x).card → 27≤score) ∧ (17≤(ball D V x 2).card → 39≤score) := by
  dsimp only
  constructor
  · have grow := ball_growth q (by omega) D V free rank x xm
    have a := grow 4 (by omega)
    have b := grow 5 (by omega)
    omega
  constructor
  · intro high
    have b3 := high_row_ball_three_min (by decide : 2≤2) (by decide : 2*2≤7+1)
      (free.mono_bound (by omega : 7≤q)) rank xm high
    have b4 := step2 free hq rank xm (by omega : 3+1≤q) (by simpa using b3 : 12≤_)
      (by decide) (by omega)
    have b5 := step2 free hq rank xm (by omega : 4+1≤q) (by simpa using b4 : 13≤_)
      (by decide) (by omega)
    simp only [Nat.reduceAdd] at *
    omega
  · intro b2
    have b3 := step2 free hq rank xm (by omega : 2+1≤q) b2 (by decide) (by omega)
    have b4 := step2 free hq rank xm (by omega : 3+1≤q) (by simpa using b3 : 18≤_)
      (by decide) (by omega)
    have b5 := step2 free hq rank xm (by omega : 4+1≤q) (by simpa using b4 : 19≤_)
      (by decide) (by omega)
    simp only [Nat.reduceAdd] at *
    omega

/-- A row at depth i in the punctured K-ball retains its ambient j-ball
and therefore pays that size at both larger radii on the smaller host. -/
theorem two_scores {D V q v i j K x a b} (free : QFree D V q) (root : v∈V)
    (xm : x∈(ball D V v i).erase v) (cut : i+j≤K) (time : K≤q)
    (left : j≤a) (right : j≤b) :
    let W := (ball D V v K).erase v
    2*(ball D V x j).card ≤ (ball D W x a).card+(ball D W x b).card := by
  dsimp only
  rw [retained_ball free root xm cut time]
  have := card_le_card (ball_mono_radius (D:=D) (W:=(ball D V v K).erase v) (u:=x) left)
  have := card_le_card (ball_mono_radius (D:=D) (W:=(ball D V v K).erase v) (u:=x) right)
  omega

theorem fifth40 {D V q v} (free : QFree D V q) (hq : 9≤q) (root : v∈V)
    (degree : ∀x∈V,8≤(outN D V x).card) : 40≤(ball D V v 5).card := by
  classical
  let layer := fun i => (ball D V v i).erase v
  let W := layer 4
  let score := fun x => (ball D W x 4).card+(ball D W x 5).card
  have card (i) : (layer i).card+1=(ball D V v i).card := card_erase_add_one (self_mem_ball root)
  have nest {i j : ℕ} (ij : i≤j) : layer i⊆layer j := erase_subset_erase v (ball_mono_radius ij)
  have wv : W⊆V := (erase_subset _ _).trans ball_subset
  have ff := free.mono_set wv
  have b4 := fourth_floor free hq root degree
  have b3 := DiagonalEight.three25 (free.mono_bound (by omega : 8≤q)) degree root
  have b2 := card_ball_two_ge_twice (by decide : 2≤8) (free.mono_bound (by omega)) degree root
  have b1 := card_B1 (free.mono_bound (by omega : 4≤q)) root
  have dv := degree v root
  have l1 := card 1
  have l2 := card 2
  have l3 := card 3
  have wc : W.card+1=(ball D V v 4).card := card 4
  have near (x) (xm : x∈layer 1) : 50≤score x := by
    have strong := DiagonalEight.three25 (free.mono_bound (by omega : 8≤q)) degree
      (ball_subset (mem_of_mem_erase xm))
    have both := two_scores free root xm (by decide : 1+3≤4) (by omega) (by decide : 3≤4) (by decide : 3≤5)
    change 2*(ball D V x 3).card≤score x at both
    omega
  have cap := weighted_rows (i:=4) (j:=5) ff (by omega) (score:=score) (fun _ _=>le_rfl)
  by_contra! low
  have diff := card_sdiff_add_card_eq_card (ball_mono_radius (D:=D) (W:=V) (u:=v) (by decide : 4≤5))
  by_cases small : W.card=32
  · have rank := minOut_prefix_erase (d:=2) free root (by omega : 4+1≤q) degree
      (show 2+(ball D V v 5 \ ball D V v 4).card≤8 by omega)
    have localScores x (xm : x∈W) := scored2 ff hq rank xm
    have high (x) (xm : x∈layer 3) : 27≤score x := by
      exact (localScores x (nest (by decide : 3≤4) xm)).2.1
        ((degree x (ball_subset (mem_of_mem_erase xm))).trans
          (card_le_card (outN_prefix_erase_root free root (by omega : 3+1≤q) (mem_of_mem_erase xm))))
    have mid (x) (xm : x∈layer 2) : 39≤score x := by
      apply (localScores x (nest (by decide : 2≤4) xm)).2.2
      have native := card_ball_two_ge_twice (by decide : 2≤8) (free.mono_bound (by omega)) degree
        (ball_subset (mem_of_mem_erase xm))
      rwa [←retained_ball free root xm (by decide : 2+2≤4) (by omega : 4≤q)]
    have A : layer 3⊆W := nest (by decide)
    have B : layer 2⊆layer 3 := nest (by decide)
    have C : layer 1⊆layer 2 := nest (by decide)
    have sum := strata (f:=score) A B C (fun x xm=>(localScores x xm).1) high mid near
    have := card_le_card A
    have := card_le_card B
    have := card_le_card C
    rw [small] at cap sum
    omega
  by_cases middle : W.card=33
  · have rank := minOut_prefix_erase (d:=3) free root (by omega : 4+1≤q) degree
      (show 3+(ball D V v 5 \ ball D V v 4).card≤8 by omega)
    have base (x) (xm : x∈W) : 29≤score x := by
      have a := ball_of_min (BRq3.ball_all 5 (by decide)) (ff.mono_bound (by omega)) rank x xm
      have b := ball_of_min (BRq3.ball_all 6 (by decide)) (ff.mono_bound (by omega)) rank x xm
      change 13≤(ball D W x 4).card at a
      change 16≤(ball D W x 5).card at b
      dsimp only [score]
      omega
    have sum := mixed_capacity (i:=4) (j:=5) ff (by omega) (nest (by decide : 1≤4)) base near
    change (layer 1).card*50+(W.card-(layer 1).card)*29≤W.card*(W.card+1) at sum
    rw [middle] at sum
    omega
  have mono := card_le_card (ball_mono_radius (D:=D) (W:=V) (u:=v) (by decide : 4≤5))
  by_cases low4 : (ball D V v 4).card≤37
  · have step := PrefixDegreeGrowth.small_rank_step (j:=4) (d:=4) free root (by omega) degree
      (by omega) (by decide) (by decide) (by omega) (by omega)
    change (ball D V v 4).card+8<(ball D V v 5).card+4 at step
    omega
  · have step := PrefixDegreeGrowth.small_rank_step (j:=4) (d:=5) free root (by omega) degree
      (by omega) (by decide) (by decide) (by omega) (by omega)
    change (ball D V v 4).card+8<(ball D V v 5).card+5 at step
    omega

theorem order_floor {D W q} (free : QFree D W q) (hq : 9≤q) (live : W.Nonempty)
    (degree : ∀x∈W,8≤(outN D W x).card) : 72≤W.card := by
  have := card_ge_of_two_balls free (by omega : 4+5≤q)
    (fun _ root=>fourth_floor free hq root degree) (fun _ root=>fifth40 free hq root degree) live
  omega

@[aesop safe forward (immediate := [source]) (rule_sets := [CHGraphFamilies])]
theorem direct_window {p : CHRuleCatalog.Input} (source : CHRuleCatalog.Bad p) :
    9≤CHRuleCatalog.cutoff p → 8≤p.s → 71+p.s<p.n+8 := by
  have bound : GuardedFamilyRules.OrderBound 9 8 71 :=
    ⟨by decide,fun _ _ ff live degree => order_floor ff (by decide) live degree⟩
  intro hq degree
  by_contra! size
  exact GuardedFamilyRules.forbidden source bound ⟨hq,degree,size⟩

attribute [aesop safe forward (immediate := [free,root,start,within,time]) (rule_sets := [CHGraphFamilies])] retained_ball
attribute [aesop safe forward (immediate := [free,root,xm,cut,time,left,right]) (rule_sets := [CHGraphFamilies])] two_scores
attribute [aesop safe forward (immediate := [aw,ba,cb,s0,s1,s2,s3]) (rule_sets := [CHGraphFamilies])] strata
attribute [aesop safe forward (immediate := [sub,base,extra]) (rule_sets := [CHGraphFamilies])] add_layer

#print axioms direct_window
#print axioms retained_ball
#print axioms strata
#print axioms fifth40
#print axioms order_floor
end LeanCH.BR.RetainedRadiusLayers
