import checkpoints.shen_extension.CommonParentReplay

/-! # Paired-merge exit: indicator tilts, exterior cuts and non-arc common parents

Three statements for every cutoff `q`, all phrased on the actual carrier `U`, heads `H`,
inner ball `R = B_{q-2}(H)` and a selected head set `T`.

* `layered_sink`, `meet_cover_void`, `cover_card`: pure q-freeness. A set of at most `q-1`
  heads cannot both meet `H` and receive an arc from every inner row. Any set receiving an
  arc from every inner row has at least `q-1` elements.
* `tilt_pays`: a nonnegative tilt with strictly positive slopes pays the paired merge after
  the exterior vertices of zero tilt are cut. The cut is `CommonParentReplay.Edge.cut`; it keeps
  `H`, the inner ball and every selected head of positive tilt.
* `nonarc_pays`, `nonarc_common_parent`: the paired-arc row test of `PairedArcAudit.rows_iff`
  needs no arc. Every non-out-neighbour `x` of `a` that is light and below the rise of `a`
  shares a parent with `a` on a least source. -/
namespace LeanCH.BR.Closure.PairTilt
open Finset BRq2 BRq3 BR45 WeightedSD ShortestCycleWeights

/-- A set of at most `q-1-d` vertices containing a vertex within `d` steps of the heads
contains an inner vertex (within `q-2` steps) with no out-neighbour in the set. -/
theorem layered_sink {q d : ℕ} {D : CH.Digraph} {U H T : Finset ℕ} (free : QFree D U q)
    (ts : T⊆U) {t : ℕ} (tt : t∈T) (near : t∈BRsub.ballSet D U H d) (size : d+T.card+1≤q) :
    ∃r∈T,r∈BRsub.ballSet D U H (q-2) ∧ ∀z∈T,D r z=false := by
  classical
  by_contra! hcon
  have next (r) (rt : r∈T) (rr : r∈BRsub.ballSet D U H (q-2)) : ∃z∈T,D r z=true := by
    obtain ⟨z,zt,hz⟩ := hcon r rt rr
    exact ⟨z,zt,by simpa using hz⟩
  let nx : ℕ → ℕ := fun r => if h : ∃z∈T,D r z=true then h.choose else r
  have hnx (r) (rt : r∈T) (rr : r∈BRsub.ballSet D U H (q-2)) : nx r∈T ∧ D r (nx r)=true := by
    have h := next r rt rr
    simp only [nx,dite_cond_eq_true (eq_true h)]
    exact h.choose_spec
  have inner (r) (k) (bound : k≤q-2) (rr : r∈BRsub.ballSet D U H k) : r∈BRsub.ballSet D U H (q-2) := by
    obtain ⟨h,hh,hit⟩ := BRsub.mem_ballSet.mp rr
    exact BRsub.mem_ballSet.mpr ⟨h,hh,ball_mono_radius bound hit⟩
  have hs (i) (bound : i≤T.card) : nx^[i] t∈T ∧ nx^[i] t∈BRsub.ballSet D U H (d+i) := by
    induction i with
    | zero => exact ⟨tt,by simpa using near⟩
    | succ i ih =>
      obtain ⟨it,ir⟩ := ih (by omega)
      obtain ⟨nt,arc⟩ := hnx _ it (inner _ _ (by omega) ir)
      rw [Function.iterate_succ_apply']
      refine ⟨nt,?_⟩
      obtain ⟨h,hh,hit⟩ := BRsub.mem_ballSet.mp ir
      exact BRsub.mem_ballSet.mpr ⟨h,hh,by
        rw [show d+(i+1)=d+i+1 by omega]; exact ball_step hit (ts nt) arc⟩
  have hw (i l) (bound : i+l≤T.card) : Walk D U (nx^[i] t) (nx^[i+l] t) l := by
    induction l with
    | zero => exact .refl _
    | succ l ih =>
      have e : nx^[i+(l+1)] t=nx (nx^[i+l] t) := by
        rw [← Nat.add_assoc,Function.iterate_succ_apply']
      obtain ⟨it,ir⟩ := hs (i+l) (by omega)
      obtain ⟨nt,arc⟩ := hnx _ it (inner _ _ (by omega) ir)
      rw [e]
      exact (ih (by omega)).snoc (ts nt) arc
  obtain ⟨i,hi,j,hj,hij,heq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (s := Finset.range (T.card+1)) (t := T) (f := fun i => nx^[i] t) (by simp)
    (by intro i hi; exact (hs i (by simpa [Nat.lt_succ_iff] using hi)).1)
  have heq' : nx^[i] t=nx^[j] t := heq
  simp only [Finset.mem_range] at hi hj
  rcases Nat.lt_or_gt_of_ne hij with h|h
  · have w := hw i (j-i) (by omega)
    rw [Nat.add_sub_cancel' h.le,← heq'] at w
    exact free _ (j-i) (by omega) (by omega) w
  · have w := hw j (i-j) (by omega)
    rw [Nat.add_sub_cancel' h.le,heq'] at w
    exact free _ (i-j) (by omega) (by omega) w

/-- The bridge premise "T meets H and every inner row points into T" is empty for every
set of at most q-1 heads, in every q-free graph. -/
theorem meet_cover_void {q : ℕ} {D : CH.Digraph} {U H T : Finset ℕ} (free : QFree D U q)
    (ts : T⊆U) (size : T.card+1≤q) (meet : (T∩H).Nonempty)
    (cover : ∀r∈BRsub.ballSet D U H (q-2),∃k∈T,D r k=true) : False := by
  obtain ⟨t,th⟩ := meet
  obtain ⟨tt,hh⟩ := mem_inter.mp th
  have near : t∈BRsub.ballSet D U H 0 := BRsub.mem_ballSet.mpr ⟨t,hh,self_mem_ball (ts tt)⟩
  obtain ⟨r,rt,rr,miss⟩ := layered_sink free ts tt near (by omega)
  obtain ⟨k,kt,hit⟩ := cover r rr
  exact Bool.noConfusion ((miss k kt).symm.trans hit)

/-- A covering head set lies at least `q-|T|` steps from the distinguished heads. -/
theorem cover_far {q d : ℕ} {D : CH.Digraph} {U H T : Finset ℕ} (free : QFree D U q)
    (ts : T⊆U) (cover : ∀r∈BRsub.ballSet D U H (q-2),∃k∈T,D r k=true)
    (size : d+T.card+1≤q) : ∀t∈T,t∉BRsub.ballSet D U H d := by
  intro t tt near
  obtain ⟨r,rt,rr,miss⟩ := layered_sink free ts tt near size
  obtain ⟨k,kt,hit⟩ := cover r rr
  exact Bool.noConfusion ((miss k kt).symm.trans hit)

/-- Every set receiving an arc from every inner row has at least `q-1` elements. -/
theorem cover_card {q : ℕ} {D : CH.Digraph} {U H T : Finset ℕ} (free : QFree D U q)
    (hs : H⊆U) (live : H.Nonempty) (ts : T⊆U)
    (cover : ∀r∈BRsub.ballSet D U H (q-2),∃k∈T,D r k=true) : q≤T.card+1 := by
  by_contra! low
  obtain ⟨h,hh⟩ := live
  have hr : h∈BRsub.ballSet D U H (q-2) := BRsub.mem_ballSet.mpr ⟨h,hh,self_mem_ball (hs hh)⟩
  obtain ⟨k,kt,hit⟩ := cover h hr
  have near : k∈BRsub.ballSet D U H 1 := BRsub.mem_ballSet.mpr
    ⟨h,hh,by simpa using ball_step (self_mem_ball (k:=0) (hs hh)) (ts kt) hit⟩
  exact cover_far free ts cover (by omega) k kt near

/-! ## Tilting and cutting -/

theorem mass_comb (U : Finset ℕ) (u y : ℕ→ℚ) (t : ℚ) :
    mass U (fun v => u v+t*y v)=mass U u+t*mass U y := by
  simp only [mass,sum_add_distrib,mul_sum]

theorem row_comb (q : ℕ) (E : CH.Digraph) (U : Finset ℕ) (u y : ℕ→ℚ) (t : ℚ) (i : ℕ) :
    WeightedSD.row q E U (fun v => u v+t*y v) i=WeightedSD.row q E U u i+t*WeightedSD.row q E U y i := by
  have o : outW E U (fun v => u v+t*y v) i=outW E U u i+t*outW E U y i := by
    unfold outW
    rw [mul_sum,← sum_add_distrib]
    apply sum_congr rfl
    intro v _
    split <;> ring
  simp only [WeightedSD.row,o]
  ring

/-- Deleting vertices of zero tilt changes neither the tilted mass nor any tilted row. -/
theorem cut_zero (q : ℕ) (E : CH.Digraph) {W X : Finset ℕ} {y : ℕ→ℚ} (xs : X⊆W)
    (zero : ∀v∈X,y v=0) :
    mass (W\X) y=mass W y ∧ ∀i,WeightedSD.row q E (W\X) y i=WeightedSD.row q E W y i := by
  have drop (f : ℕ→ℚ) (fz : ∀v∈X,f v=0) : (∑v∈W\X,f v)=∑v∈W,f v := by
    rw [← sum_sdiff xs (f:=f),sum_eq_zero fz,add_zero]
  refine ⟨drop y zero,fun i => ?_⟩
  unfold WeightedSD.row outW
  congr 2
  exact drop (fun v => if E i v=true then y v else 0) (fun v vx => by simp [zero v vx])

/-- A nonnegative tilt whose heavy, inner and paired slopes are strictly positive pays the
paired merge on the same heads and the same inner ball, after the exterior vertices of zero
tilt are cut. The weights are `1 + t*y` for an explicit large `t`. -/
theorem tilt_pays {q : ℕ} {D : CH.Digraph} {V : Finset ℕ} (hq : 1≤q) (W H : Finset ℕ)
    (E : CH.Digraph) (y : ℕ→ℚ) (inside : W⊆V) (room : W.card+1<V.card)
    (sub : ∀i j,E i j=true → D i j=true) (heads : H⊆W) (live : H.Nonempty)
    (nonneg : ∀v∈W,0≤y v) (heavy : mass W y<q*mass H y)
    (inner : ∀i∈BRsub.ballSet E W H (q-2),mass W y<WeightedSD.row q E W y i)
    (pair : ∀i∈BRsub.ballSet E W H (q-2),∀j∈W\BRsub.ballSet E W H (q-2),0<y j →
      mass W y<((q:ℚ)-1)*(WeightedSD.row q E W y i-mass W y)+WeightedSD.row q E W y j) :
    RankedMerge.PairPays q D V := by
  classical
  set R := BRsub.ballSet E W H (q-2) with hR
  set X := (W\R).filter (fun v => y v≤0) with hX
  have xs : X⊆W\R := filter_subset _ _
  have xw : X⊆W := xs.trans sdiff_subset
  have zero (v) (vx : v∈X) : y v=0 := le_antisymm (mem_filter.mp vx).2 (nonneg v (xw vx))
  set W' := W\X with hW'
  have same : BRsub.ballSet E W' H (q-2)=R := RankedMerge.ball_delete xs
  obtain ⟨hmass,hrow⟩ : mass W' y=mass W y ∧ ∀i,WeightedSD.row q E W' y i=WeightedSD.row q E W y i :=
    cut_zero q E xw zero
  have rw' : R⊆W' := by
    intro r rr
    have rw : r∈W := by
      obtain ⟨h,_,hit⟩ := BRsub.mem_ballSet.mp rr
      exact (mem_ball.mp hit).1
    exact mem_sdiff.mpr ⟨rw,fun rx => (mem_sdiff.mp (xs rx)).2 rr⟩
  have heads' : H⊆W' := fun h hh => rw' (BRsub.mem_ballSet.mpr ⟨h,hh,self_mem_ball (heads hh)⟩)
  have survivor (j) (jw : j∈W'\R) : 0<y j := by
    obtain ⟨jw',jr⟩ := mem_sdiff.mp jw
    obtain ⟨jw,jx⟩ := mem_sdiff.mp jw'
    by_contra! le
    exact jx (mem_filter.mpr ⟨mem_sdiff.mpr ⟨jw,jr⟩,le⟩)
  have ww : W'⊆W := sdiff_subset
  -- slopes, read on the original carrier
  let sh : ℚ := (q:ℚ)*mass H y-mass W y
  let si : ℕ → ℚ := fun i => WeightedSD.row q E W y i-mass W y
  let sp : ℕ×ℕ → ℚ := fun p => ((q:ℚ)-1)*si p.1+si p.2
  have shp : 0<sh := by simp only [sh]; linarith
  have sip (i) (ir : i∈R) : 0<si i := sub_pos.mpr (inner i ir)
  have spp (p) (pp : p∈R ×ˢ (W'\R)) : 0<sp p := by
    obtain ⟨ir,jr⟩ := mem_product.mp pp
    have e := pair p.1 ir p.2 (mem_sdiff.mpr ⟨ww (mem_sdiff.mp jr).1,(mem_sdiff.mp jr).2⟩)
      (survivor p.2 jr)
    simp only [sp,si]
    linarith
  let N : ℚ := (q:ℚ)*W'.card+1
  have Np : 0<N := by positivity
  let t : ℚ := N/sh+(∑i∈R,N/si i)+∑p∈R ×ˢ (W'\R),N/sp p
  have A : 0≤∑i∈R,N/si i := sum_nonneg (fun i ir => (div_pos Np (sip i ir)).le)
  have B : 0≤∑p∈R ×ˢ (W'\R),N/sp p := sum_nonneg (fun p pp => (div_pos Np (spp p pp)).le)
  have C : 0≤N/sh := (div_pos Np shp).le
  have tpos : 0≤t := by simp only [t]; linarith
  have big (s : ℚ) (sp0 : 0<s) (le : N/s≤t) : N≤t*s := by
    rw [div_le_iff₀ sp0] at le; exact le
  have th : N≤t*sh := big sh shp (by simp only [t]; linarith)
  have ti (i) (ir : i∈R) : N≤t*si i := big _ (sip i ir) (by
    have := single_le_sum (fun j jr => (div_pos Np (sip j jr)).le) ir
    simp only [t]; linarith)
  have tp (p) (pp : p∈R ×ˢ (W'\R)) : N≤t*sp p := big _ (spp p pp) (by
    have := single_le_sum (fun j jr => (div_pos Np (spp j jr)).le) pp
    simp only [t]; linarith)
  -- weights 1 + t*y on the cut carrier
  let z : ℕ → ℚ := fun v => 1+t*y v
  have zp (v) (vw : v∈W') : 0<z v := by
    have := mul_nonneg tpos (nonneg v (ww vw)); simp only [z]; linarith
  have m1 : mass W' (fun _ : ℕ => (1:ℚ))=W'.card := by simp [mass]
  have mh1 : 0≤mass H (fun _ : ℕ => (1:ℚ)) := mass_nonneg (fun _ _ => zero_le_one)
  have r1 (v) : 0≤WeightedSD.row q E W' (fun _ : ℕ => (1:ℚ)) v := by
    unfold WeightedSD.row outW
    exact add_nonneg zero_le_one (mul_nonneg (Nat.cast_nonneg _)
      (sum_nonneg (fun _ _ => by split <;> norm_num)))
  have mz : mass W' z=W'.card+t*mass W y := by
    have h := mass_comb W' (fun _ => (1:ℚ)) y t
    rw [m1,hmass] at h
    exact h
  have rz (v) : WeightedSD.row q E W' z v=
      WeightedSD.row q E W' (fun _ : ℕ => (1:ℚ)) v+t*WeightedSD.row q E W y v := by
    have h := row_comb q E W' (fun _ => (1:ℚ)) y t v
    rw [hrow] at h
    exact h
  have hz : mass H z=mass H (fun _ : ℕ => (1:ℚ))+t*mass H y := mass_comb H (fun _ => (1:ℚ)) y t
  have qq : (1:ℚ)≤q := by exact_mod_cast hq
  have q1 : (0:ℚ)≤(q:ℚ)-1 := by linarith
  have cq : (0:ℚ)≤W'.card := Nat.cast_nonneg _
  have c1 : (W'.card:ℚ)≤q*W'.card := le_mul_of_one_le_left cq qq
  have ex (v) : -(W'.card:ℚ)+t*si v≤WeightedSD.row q E W' z v-mass W' z := by
    rw [rz,mz]; simp only [si]; linarith [r1 v]
  refine ⟨W',ww.trans inside,by have := card_le_card ww; omega,E,sub,H,heads',live,z,zp,?_,?_⟩
  · rw [mz,hz]
    simp only [sh,N] at th
    have c2 : 0≤(q:ℚ)*mass H (fun _ : ℕ => (1:ℚ)) := mul_nonneg (Nat.cast_nonneg q) mh1
    linarith
  · intro i hi
    rw [same] at hi
    have ei := ex i
    have hti := ti i hi
    simp only [N] at hti
    refine ⟨by linarith,?_⟩
    intro j hj
    rw [same] at hj
    have ej := ex j
    have pj := tp (i,j) (mem_product.mpr ⟨hi,hj⟩)
    simp only [sp,N] at pj
    have m1' := mul_le_mul_of_nonneg_left ei q1
    linarith

/-- On a least source no such tilt exists. -/
theorem no_tilt {q : ℕ} {D : CH.Digraph} {V : Finset ℕ} (hq : 2≤q) (free : QFree D V q)
    (small : SmallerSmallRow q V.card) (W H : Finset ℕ) (E : CH.Digraph) (y : ℕ→ℚ)
    (inside : W⊆V) (room : W.card+1<V.card) (sub : ∀i j,E i j=true → D i j=true)
    (heads : H⊆W) (live : H.Nonempty) (nonneg : ∀v∈W,0≤y v) (heavy : mass W y<q*mass H y)
    (inner : ∀i∈BRsub.ballSet E W H (q-2),mass W y<WeightedSD.row q E W y i)
    (pair : ∀i∈BRsub.ballSet E W H (q-2),∀j∈W\BRsub.ballSet E W H (q-2),0<y j →
      mass W y<((q:ℚ)-1)*(WeightedSD.row q E W y i-mass W y)+WeightedSD.row q E W y j) : False :=
  RankedMerge.no_pair hq free small
    (tilt_pays (by omega) W H E y inside room sub heads live nonneg heavy inner pair)

/-- The cut used by `tilt_pays` is one replay move: it removes exterior vertices only and
keeps every selected head that lies in the inner ball or carries positive tilt. -/
theorem tilt_cut_edge {q : ℕ} {E : CH.Digraph} {W H K : Finset ℕ} {y w : ℕ→ℚ}
    (live : ((W\CommonParentReplay.ball q E H W).filter (fun v => y v≤0)).Nonempty)
    (keep : ∀k∈K,k∈W ∧ (k∈CommonParentReplay.ball q E H W ∨ 0<y k)) :
    CommonParentReplay.Edge q E H ⟨W,K,w⟩
      ⟨W\(W\CommonParentReplay.ball q E H W).filter (fun v => y v≤0),K,w⟩ := by
  refine .cut live (filter_subset _ _) ?_
  intro k kk
  obtain ⟨kw,side⟩ := keep k kk
  refine mem_sdiff.mpr ⟨kw,fun kx => ?_⟩
  obtain ⟨kd,kl⟩ := mem_filter.mp kx
  rcases side with kr|kp
  · exact (mem_sdiff.mp kd).2 kr
  · linarith

/-! ## The paired row test at a non-arc -/

/-- `PairedArcAudit.rows_iff` (sufficiency) without the arc. Delete `a` and any vertex `x`
that `a` does not point to. A light `x` below the rise of `a` pays the paired merge on the
original weights unless `a` and `x` have a common parent. -/
theorem nonarc_pays {q : ℕ} {D E : CH.Digraph} {V : Finset ℕ} (hq : 2≤q) (free : QFree E V q)
    (sub : ∀i j,E i j=true → D i j=true) (w : ℕ→ℚ) (pos : ∀i∈V,0<w i) {g : ℚ} (gp : 0≤g)
    (floor : ∀i∈V,mass V w+g≤WeightedSD.row q E V w i)
    {a x : ℕ} (av : a∈V) (xv : x∈V) (ne : x≠a) (miss : E a x=false)
    (light : ((q:ℚ)-2)*w x≤g) (rise : ((q:ℚ)-1)*w x<w a+g)
    (orphan : ∀j∈V,E j a=true → E j x=false) : RankedMerge.PairPays q D V := by
  classical
  let U := (V.erase a).erase x
  let H := outN E U a
  let R := BRsub.ballSet E U H (q-2)
  have xu : x∈V.erase a := mem_erase.mpr ⟨ne,xv⟩
  have us : U⊆V := (erase_subset _ _).trans (erase_subset _ _)
  have total (f : ℕ→ℚ) : (∑i∈V,f i)=(∑i∈U,f i)+f x+f a := by
    rw [sum_erase_add _ _ xu,sum_erase_add _ _ av]
  have wm : mass V w=mass U w+w x+w a := total w
  have split (i) : WeightedSD.row q E V w i=WeightedSD.row q E U w i+
      q*((if E i x=true then w x else 0)+(if E i a=true then w a else 0)) := by
    unfold WeightedSD.row outW
    rw [total]
    ring
  have qp : (0:ℚ)<q := by exact_mod_cast (show 0<q by omega)
  have q2 : (2:ℚ)≤q := by exact_mod_cast hq
  have px := pos x xv
  have pa := pos a av
  have aa : E a a=false := Bool.eq_false_iff.mpr (loopfree free (by omega) av)
  have room : U.card+1<V.card := by
    have c1 := card_erase_add_one av
    have c2 := card_erase_add_one xu
    dsimp only [U]; omega
  -- a inner row never returns to a
  have ia (i) (ir : i∈R) : E i a=false := by
    apply Bool.eq_false_iff.mpr
    intro back
    obtain ⟨h,hh,reach⟩ := BRsub.mem_ballSet.mp ir
    obtain ⟨_,k,hk,p⟩ := mem_ball.mp reach
    have head := mem_outN.mp hh
    exact free a (k+1+1) (by omega) (by omega)
      (.step (us head.1) head.2 ((p.mono us).snoc av back))
  have heavy : mass U w<q*mass H w := by
    have e := split a
    rw [miss,aa] at e
    simp only [Bool.false_eq_true,ite_false,add_zero,mul_zero] at e
    have f := floor a av
    rw [e,WeightedSD.row,outW_eq_mass] at f
    dsimp [H]
    linarith
  have live : H.Nonempty := by
    by_contra! empty
    rw [empty,show mass ∅ w=0 by simp [mass],mul_zero] at heavy
    exact heavy.not_ge (mass_nonneg (fun r ru => (pos r (us ru)).le))
  -- inner rows: excess at least g + w a - (q-1) w x
  have low (i) (ir : i∈R) : g+w a-((q:ℚ)-1)*w x≤WeightedSD.row q E U w i-mass U w := by
    have iu : i∈U := by obtain ⟨_,_,reach⟩ := BRsub.mem_ballSet.mp ir; exact (mem_ball.mp reach).1
    have e := split i
    rw [ia i ir] at e
    have f := floor i (us iu)
    have cap : (if E i x=true then w x else 0)≤w x := by split <;> linarith
    have capq := mul_le_mul_of_nonneg_left cap qp.le
    simp only [Bool.false_eq_true,ite_false,add_zero] at e
    linarith
  refine ⟨U,us,room,E,sub,H,outN_subset,live,w,fun i iu => pos i (us iu),heavy,?_⟩
  intro i ir
  have li := low i ir
  refine ⟨by linarith,?_⟩
  intro j jr
  have ju := (mem_sdiff.mp jr).1
  have e := split j
  have f := floor j (us ju)
  have coeff : (0:ℚ)≤(q:ℚ)-1 := by linarith
  have scaled := mul_le_mul_of_nonneg_left li coeff
  have lq := mul_le_mul_of_nonneg_left light qp.le
  have rq := mul_lt_mul_of_pos_left rise qp
  have aq := mul_pos qp pa
  cases ea : E j a <;> cases ex : E j x <;> simp only [ea,ex,Bool.false_eq_true,ite_false,
    ite_true,add_zero,zero_add,mul_zero] at e
  · linarith
  · linarith
  · linarith
  · exact absurd ex (by rw [orphan j (us ju) ea]; decide)

/-- On a least source every light non-out-neighbour below the rise of `a` shares a parent
with `a`. The arc case is `RankedMerge.common_parent`. -/
theorem nonarc_common_parent {q : ℕ} {D E : CH.Digraph} {V : Finset ℕ} (hq : 2≤q)
    (native : QFree D V q) (small : SmallerSmallRow q V.card) (free : QFree E V q)
    (sub : ∀i j,E i j=true → D i j=true) (w : ℕ→ℚ) (pos : ∀i∈V,0<w i) {g : ℚ} (gp : 0≤g)
    (floor : ∀i∈V,mass V w+g≤WeightedSD.row q E V w i)
    {a x : ℕ} (av : a∈V) (xv : x∈V) (ne : x≠a) (miss : E a x=false)
    (light : ((q:ℚ)-2)*w x≤g) (rise : ((q:ℚ)-1)*w x<w a+g) :
    ∃j∈V,E j a=true ∧ E j x=true := by
  by_contra! none
  exact RankedMerge.no_pair hq native small (nonarc_pays hq free sub w pos gp floor av xv ne miss
    light rise (fun j jv ja => Bool.eq_false_iff.mpr (none j jv ja)))

/-- At a covered endpoint (every inner row points into the `q-1` selected heads) no selected
head is an out-neighbour of the deleted root. On a least source each light selected head
below the rise of the root therefore shares a parent with the root. -/
theorem endpoint_parents {q : ℕ} {D E : CH.Digraph} {V U T : Finset ℕ} (hq : 2≤q)
    (native : QFree D V q) (small : SmallerSmallRow q V.card) (free : QFree E V q)
    (sub : ∀i j,E i j=true → D i j=true) (w : ℕ→ℚ) (pos : ∀i∈V,0<w i) {g : ℚ} (gp : 0≤g)
    (floor : ∀i∈V,mass V w+g≤WeightedSD.row q E V w i)
    {a : ℕ} (av : a∈V) (us : U⊆V) (ua : a∉U) (ts : T⊆U) (size : T.card+1≤q)
    (cover : ∀r∈BRsub.ballSet E U (outN E U a) (q-2),∃k∈T,E r k=true) :
    ∀t∈T,((q:ℚ)-2)*w t≤g → ((q:ℚ)-1)*w t<w a+g → ∃j∈V,E j a=true ∧ E j t=true := by
  intro t tt light rise
  have miss : E a t=false := by
    apply Bool.eq_false_iff.mpr
    intro hit
    exact meet_cover_void (free.mono_set us) ts size
      ⟨t,mem_inter.mpr ⟨tt,mem_outN.mpr ⟨ts tt,hit⟩⟩⟩ cover
  exact nonarc_common_parent hq native small free sub w pos gp floor av (us (ts tt))
    (fun eq => ua (eq ▸ ts tt)) miss light rise

#print axioms layered_sink
#print axioms endpoint_parents
#print axioms meet_cover_void
#print axioms cover_card
#print axioms tilt_pays
#print axioms no_tilt
#print axioms tilt_cut_edge
#print axioms nonarc_pays
#print axioms nonarc_common_parent
end LeanCH.BR.Closure.PairTilt
