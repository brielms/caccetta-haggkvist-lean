import checkpoints.shen_extension.dot_tensor_research.DotDegreeSevenQ5Charges_20261121
import checkpoints.shen_extension.dot_tensor_research.DotDegreeSevenQ5EndpointSeam_20261121
import checkpoints.shen_extension.dot_tensor_research.DotDegreeSevenQ5BankPropagation_20261121
import LeanCH.BR.BRRegionCycle
import LeanCH.BR.BRFiniteWalk

namespace LeanCH.BR.DotDegreeSevenLow
open Finset BRq2 BRq3 BR45 BRsGen

private theorem suffix_of_walk {D : CH.Digraph} {V : Finset ℕ} {a t m k : ℕ}
    (hf : QFree D V 5) (ha : a∈V) (w : Walk D V a t m)
    (hk : k≤m) (k5 : k≤5) :
    ∃ P⊆V, P.card=k+1 ∧ ∀ z∈P, ∃ j≤k, Walk D V z t j := by
  classical
  obtain ⟨f,f0,ft,he⟩ := w.toFun
  let g i := f (m-k+i)
  let P := (range (k+1)).image g
  have pos (i) (hi : i≤m) : f i∈V := by
    cases i with
    | zero => simpa only [f0] using ha
    | succ i => exact (he i (by omega)).1
  refine ⟨P,?_,?_,?_⟩
  · intro z hz
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hz
    exact pos _ (by simp at hi; omega)
  · rw [card_image_of_injOn,card_range]
    intro i hi j hj eq
    simp only [coe_range, Set.mem_Iio] at hi hj
    change f (m-k+i)=f (m-k+j) at eq
    by_contra ne
    rcases Nat.lt_or_gt_of_ne ne with lt|lt
    · have ww := walk_between he (show m-k+i≤m-k+j by omega) (show m-k+j≤m by omega)
      rw [←eq] at ww
      exact hf _ _ (by omega) (by omega) ww
    · have ww := walk_between he (show m-k+j≤m-k+i by omega) (show m-k+i≤m by omega)
      rw [eq] at ww
      exact hf _ _ (by omega) (by omega) ww
  · intro z hz
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hz
    have h := mem_range.mp hi
    refine ⟨m-(m-k+i),by omega,?_⟩
    rw [←ft]
    exact walk_between he (by omega) (by omega)

/-- A sink that is reachable from every first-layer vertex is impossible
at the saturated mixed endpoint. -/
theorem endpoint_no_reachable_sink {D : CH.Digraph} {V : Finset ℕ} {u a : ℕ}
    (hf : QFree D V 5) (ho : OutEq 7 D V) (n : V.card=35)
    (noLow : ∀ v∈V, 15≤(ball D V v 2).card) (hu : u∈V)
    (ha : a∈outN D V u)
    (sink : ∀ z∈outN D V u, D a z≠true)
    (reach : ∀ z∈outN D V u, ∃ j, Walk D (outN D V u) z a j) :
    False := by
  classical
  let A := outN D V u
  let B := ball D V u 2 \ ball D V u 1
  let T := ball D V u 3 \ ball D V u 2
  have av : A⊆V := fun _ x => (mem_outN.mp x).1
  have bv : B⊆V := sdiff_subset.trans ball_subset
  have tv : T⊆V := sdiff_subset.trans ball_subset
  have a7 : A.card=7 := ho u hu
  have b1 : (ball D V u 1).card=8 := by rw [card_B1 (hf.mono_bound (by decide : 4≤5)) hu,ho u hu]
  have a1 : A⊆ball D V u 1 := fun _ h => (mem_ball_one hu).mpr (Or.inr h)
  have a2 := a1.trans (ball_mono_radius (by decide : 1≤2))
  have a3 := a2.trans (ball_mono_radius (by decide : 2≤3))
  have f3 (v) (hv : v∈V) : 21≤(ball D V v 3).card := by
    have h := floor_three20 hf (fun w hw => (ho w hw).ge) hv
    by_contra! lt
    have e : (ball D V v 3).card=20 := by omega
    have g := tight_three_only_tight_two hf ho hv e
    have k := noLow v hv
    omega
  have sizes := two_balls_boundary_cards hf (by decide : 2+3≤5) noLow f3 (by omega : 15+21=V.card+1)
  have b7 : B.card=7 := by
    have h := card_sdiff_add_card_eq_card (ball_mono_radius (D:=D) (W:=V) (u:=u) (by decide : 1≤2))
    have j := (sizes u hu).1
    change B.card+(ball D V u 1).card=(ball D V u 2).card at h
    omega
  have t6 : T.card=6 := by
    have h := card_sdiff_add_card_eq_card (ball_mono_radius (D:=D) (W:=V) (u:=u) (by decide : 2≤3))
    have j := sizes u hu
    change T.card+(ball D V u 2).card=(ball D V u 3).card at h
    omega
  have adj (x y : ℕ) (hy : y∈V) (e : D x y=true) : Walk D V x y 1 :=
    .step hy e (.refl y)
  have ua (x) (hx : x∈A) : Walk D V u x 1 :=
    adj u x (av hx) (mem_outN.mp hx).2
  have sink_row (x) (hx : x∈A) (sinkx : ∀ z∈A,D x z≠true) : outN D V x=B := by
    have sub : outN D V x⊆B := by
      intro z hz
      obtain ⟨zv,xz⟩ := mem_outN.mp hz
      refine mem_sdiff.mpr ⟨ball_step (a1 hx) zv xz,?_⟩
      intro m
      rcases (mem_ball_one hu).mp m with e|m
      · subst z
        exact hf u 2 (by decide) (by decide) ((ua x hx).append (adj x u hu xz))
      · exact sinkx z m xz
    exact eq_of_subset_of_card_le sub (by rw [b7,ho x (av hx)])
  have ar := sink_row a ha sink
  have bpa (b) (hb : b∈B) : Walk D V a b 1 :=
    adj a b (bv hb) (mem_outN.mp (ar.symm ▸ hb)).2
  have bpt : ∀ t∈T, ∃ b∈B,D b t=true := by
    intro t ht
    obtain ⟨t3,tn⟩ := mem_sdiff.mp ht
    obtain ⟨b,b2,bt⟩ := ball_succ_pred hu t3 tn
    exact ⟨b,mem_sdiff.mpr ⟨b2,fun m => tn (ball_step m (tv ht) bt)⟩,bt⟩
  have B2a : B⊆ball D V a 2 := fun b hb => mem_ball.mpr ⟨bv hb,1,by decide,bpa b hb⟩
  have T2a : T⊆ball D V a 2 := by
    intro t ht
    obtain ⟨b,hb,bt⟩ := bpt t ht
    exact mem_ball.mpr ⟨tv ht,2,by decide,(bpa b hb).append (adj b t (tv ht) bt)⟩
  have noBa (b) (hb : b∈B) : D b a≠true := fun e =>
    hf a 2 (by decide) (by decide) ((bpa b hb).append (adj b a (av ha) e))
  have noBu (b) (hb : b∈B) : D b u≠true := by
    intro e
    obtain ⟨_,j,j2,w⟩ := mem_ball.mp (mem_sdiff.mp hb).1
    exact hf u (j+1) (by omega) (by omega) (w.append (adj b u hu e))
  let S := insert a (B∪T)
  have as : a∉B∪T := by
    intro m
    rcases mem_union.mp m with m|m
    · exact (mem_sdiff.mp m).2 (a1 ha)
    · exact (mem_sdiff.mp m).2 (a2 ha)
  have btD : Disjoint B T := disjoint_left.mpr (fun _ hb ht =>
    (mem_sdiff.mp ht).2 (mem_sdiff.mp hb).1)
  have s14 : S.card=14 := by
    rw [card_insert_of_notMem as,card_union_of_disjoint btD,b7,t6]
  have ssub : S⊆ball D V a 2 :=
    insert_subset (self_mem_ball (av ha)) (union_subset B2a T2a)
  have sone : (ball D V a 2 \ S).card=1 := by
    have eq := card_sdiff_add_card_eq_card ssub
    have h := (sizes a (av ha)).1
    omega
  obtain ⟨p,hp⟩ := card_eq_one.mp sone
  have p2 : p∈ball D V a 2 := (mem_sdiff.mp (hp.symm ▸ mem_singleton_self p)).1
  have pS : p∉S := (mem_sdiff.mp (hp.symm ▸ mem_singleton_self p)).2
  have pne : p≠a := fun e => pS (e ▸ mem_insert_self a _)
  have pn1 : p∉ball D V a 1 := by
    intro m
    rcases (mem_ball_one (av ha)).mp m with e|m
    · exact pne e
    · rw [ar] at m
      exact pS (mem_insert_of_mem (mem_union_left _ m))
  obtain ⟨b,b1a,bp⟩ := ball_succ_pred (av ha) p2 pn1
  obtain ba|hb := (mem_ball_one (av ha)).mp b1a
  · subst b
    have pb : p∈outN D V a := mem_outN.mpr ⟨ball_subset p2,bp⟩
    rw [ar] at pb
    exact pS (mem_insert_of_mem (mem_union_left _ pb))
  rw [ar] at hb
  have pA : p∈A := by
    have p3 := ball_step (mem_sdiff.mp hb).1 (ball_subset p2) bp
    have p2u : p∈ball D V u 2 := by
      by_contra e
      exact pS (mem_insert_of_mem (mem_union_right _ (mem_sdiff.mpr ⟨p3,e⟩)))
    have p1u : p∈ball D V u 1 := by
      by_contra e
      exact pS (mem_insert_of_mem (mem_union_left _ (mem_sdiff.mpr ⟨p2u,e⟩)))
    rcases (mem_ball_one hu).mp p1u with e|pA
    · exact (noBu b hb (e ▸ bp)).elim
    · exact pA
  have restrictB (x) (hx : x∈B) : outN D V x⊆insert p (B∪T) := by
    intro z hz
    obtain ⟨zv,xz⟩ := mem_outN.mp hz
    have z2 := ball_step (ball_of_adj (bv hx) (mem_outN.mp (ar.symm ▸ hx)).2) zv xz
    by_cases zS : z∈S
    · rcases mem_insert.mp zS with rfl|m
      · exact (noBa x hx xz).elim
      · exact mem_insert_of_mem m
    · have m : z∈ball D V a 2 \ S := mem_sdiff.mpr ⟨z2,zS⟩
      rw [hp] at m
      exact mem_insert.mpr (Or.inl (mem_singleton.mp m))
  obtain ⟨j,w⟩ := reach p pA
  have j4 : 4≤j := by
    by_contra! j4
    exact hf a (1+1+j) (by omega) (by omega)
      (((bpa b hb).append (adj b p (av pA) bp)).append (w.mono av))
  obtain ⟨P,pA',pc,paths⟩ := suffix_of_walk (hf.mono_set av) pA w (k:=2) (by omega) (by decide)
  have a_cap : (outN D V p ∩ A).card≤3 := by
    have dis : Disjoint (insert p P) (outN D V p ∩ A) := disjoint_left.mpr (by
      intro z zz zn
      have pe := (mem_outN.mp (mem_inter.mp zn).1).2
      rcases mem_insert.mp zz with e|zz
      · exact hf p 1 (by decide) (by decide) (adj p p (av pA) (e ▸ pe))
      · obtain ⟨k,hk,wk⟩ := paths z zz
        exact hf p (1+k+1+1) (by omega) (by omega)
          ((((adj p z (av (pA' zz)) pe).append (wk.mono av)).append (bpa b hb)).append
          (adj b p (av pA) bp)))
    have pin : p∉P := by
      intro pp
      obtain ⟨k,hk,wk⟩ := paths p pp
      exact hf a (1+1+k) (by omega) (by omega)
        (((bpa b hb).append (adj b p (av pA) bp)).append (wk.mono av))
    have c := card_le_card (union_subset (insert_subset pA pA') (inter_subset_right : outN D V p∩A⊆A))
    rw [card_union_of_disjoint dis,card_insert_of_notMem pin,pc,a7] at c
    omega
  have ap_support : outN D V p⊆A∪B := by
    intro z hz
    obtain ⟨zv,pz⟩ := mem_outN.mp hz
    have b2 := ball_step (a1 pA) zv pz
    by_cases z1 : z∈ball D V u 1
    · rcases (mem_ball_one hu).mp z1 with e|m
      · exact (hf u 2 (by decide) (by decide) ((ua p pA).append (adj p u hu (e ▸ pz)))).elim
      · exact mem_union_left _ m
    · exact mem_union_right _ (mem_sdiff.mpr ⟨b2,z1⟩)
  let H := outN D V p ∩ B
  have h4 : 4≤H.card := by
    have e : outN D V p=(outN D V p∩A)∪H := by
      ext z
      constructor
      · intro m
        rcases mem_union.mp (ap_support m) with l|r
        · exact mem_union_left _ (mem_inter.mpr ⟨m,l⟩)
        · exact mem_union_right _ (mem_inter.mpr ⟨m,r⟩)
      · intro m
        rcases mem_union.mp m with m|m <;> exact (mem_inter.mp m).1
    have c := card_union_le (outN D V p∩A) H
    rw [←e,ho p (av pA)] at c
    omega
  have pred_block (y) (hy : y∈B) (yp : D y p=true) {F : Finset ℕ}
      (sub : F⊆B) (F4 : 4≤F.card) (paths : ∀ z∈F, ∃ k≤3,Walk D B z y k) : False := by
    have dis : Disjoint F H := disjoint_left.mpr (by
      intro z zf zh
      obtain ⟨k,hk,wk⟩ := paths z zf
      have pz := (mem_outN.mp (mem_inter.mp zh).1).2
      exact hf p (1+k+1) (by omega) (by omega)
        (((adj p z (bv (sub zf)) pz).append (wk.mono bv)).append (adj y p (av pA) yp)))
    have d := card_le_card (union_subset sub (inter_subset_right : H⊆B))
    rw [card_union_of_disjoint dis,b7] at d
    omega
  have y_sink_p (y) (hy : y∈B) (hs : ∀ z∈B,D y z≠true) : D y p=true := by
    have sub : outN D V y⊆insert p T := by
      intro z hz
      rcases mem_insert.mp (restrictB y hy hz) with rfl|m
      · exact mem_insert_self _ _
      · rcases mem_union.mp m with m|m
        · exact (hs z m (mem_outN.mp hz).2).elim
        · exact mem_insert_of_mem m
    have pT : p∉T := fun h => (mem_sdiff.mp h).2 (a2 pA)
    have eq := eq_of_subset_of_card_le sub (by rw [card_insert_of_notMem pT,t6,ho y (bv hy)])
    exact (mem_outN.mp (eq.symm ▸ mem_insert_self p T)).2

  have cyc : ∃ m y, 0<m ∧ m≤7 ∧ Walk D B y y m := by
    by_contra! h
    have free : QFree D B 7 := fun y m pos up w => h m y pos up w
    obtain ⟨y,hy,ys,_,_,_⟩ := reach_sink_of_card free (by omega : B.card≤7) hb
    have lone : ∀ z∈B, (∀ x∈B,D z x≠true) → z=y := by
      intro z hz zs
      by_contra ne
      have all (v) (hv : v∈B) (vs : ∀ x∈B,D v x≠true) : outN D V v=insert p T := by
        have sub : outN D V v⊆insert p T := by
          intro x hx
          rcases mem_insert.mp (restrictB v hv hx) with rfl|m
          · exact mem_insert_self _ _
          · rcases mem_union.mp m with m|m
            · exact (vs x m (mem_outN.mp hx).2).elim
            · exact mem_insert_of_mem m
        have pt : p∉T := fun m => (mem_sdiff.mp m).2 (a2 pA)
        exact eq_of_subset_of_card_le sub (by rw [card_insert_of_notMem pt,t6,ho v (bv hv)])
      exact saturated_mixed_endpoint_no_twins hf ho n noLow (bv hz) (bv hy) ne
        ((all z hz zs).trans (all y hy ys).symm)
    obtain ⟨z,hz⟩ := card_pos.mp (show 0<H.card by omega)
    have zb := (mem_inter.mp hz).2
    obtain ⟨t,ht,ts,k,_,w⟩ := reach_sink_of_card free (by omega : B.card≤7) zb
    rw [lone t ht ts] at w
    have yp := y_sink_p y hy ys
    have k4 : 4≤k := by
      by_contra! k4
      exact hf p (1+k+1) (by omega) (by omega)
        (((adj p z (bv zb) (mem_outN.mp (mem_inter.mp hz).1).2).append
        (w.mono bv)).append (adj y p (av pA) yp))
    obtain ⟨F,sub,fc,paths⟩ := suffix_of_walk (hf.mono_set bv) zb w (k:=3) (by omega) (by decide)
    exact pred_block y hy yp sub (by omega) paths
  obtain ⟨m,x,mpos,m7,w⟩ := cyc
  obtain ⟨q,M,q5,_,mB,mc,cyc1,cycIn,le⟩ :=
    WeightedSD.region_closed_walk_shortest_support (by decide : 1≤5) (hf.mono_set bv) mpos w
  have mV := mB.trans bv
  have back (y) (hy : y∈M) (k : ℕ) : ∃ x∈M, Walk D M x y k := by
    induction k generalizing y with
    | zero => exact ⟨y,hy,.refl y⟩
    | succ k ih =>
      obtain ⟨z,hz⟩ := card_pos.mp (by rw [cycIn y hy]; decide : 0<(inN D M y).card)
      obtain ⟨t,ht,w⟩ := ih z (mem_inN.mp hz).1
      exact ⟨t,ht,w.snoc hy (mem_inN.mp hz).2⟩
  have noP (y) (hy : y∈M) : D y p≠true := by
    intro yp
    obtain ⟨z,hz,w⟩ := back y hy 3
    obtain ⟨F,sub,fc,paths⟩ := suffix_of_walk (hf.mono_set mV) hz w (k:=3) (by decide) (by decide)
    exact pred_block y (mB hy) yp (sub.trans mB) (by omega)
      (fun x hx => let ⟨k,hk,wk⟩ := paths x hx; ⟨k,hk,wk.mono mB⟩)
  have bnot : b∉M := fun hbM => noP b hbM bp
  have bm : B=insert b M := by
    apply (eq_of_subset_of_card_le (insert_subset hb mB) _).symm
    rw [card_insert_of_notMem bnot,b7]
    omega
  have m6 : M.card=6 := by
    have eq := congrArg Finset.card bm
    rw [b7,card_insert_of_notMem bnot] at eq
    omega
  have hM : H⊆M := by
    intro z hz
    have zn := mem_inter.mp hz
    have zp := (mem_outN.mp zn.1).2
    have zb := zn.2
    rw [bm] at zb
    rcases mem_insert.mp zb with e|m
    · exact (hf p 2 (by decide) (by decide) ((adj p b (bv hb) (e ▸ zp)).append (adj b p (av pA) bp))).elim
    · exact m
  have noB (y) (hy : y∈M) : D y b≠true := by
    intro yb
    obtain ⟨z,hz,w⟩ := back y hy 2
    obtain ⟨F,sub,fc,paths⟩ := suffix_of_walk (hf.mono_set mV) hz w (k:=2) (by decide) (by decide)
    have dis : Disjoint F H := disjoint_left.mpr (by
      intro v vf vh
      obtain ⟨k,hk,wk⟩ := paths v vf
      have pv := (mem_outN.mp (mem_inter.mp vh).1).2
      exact hf p (1+k+1+1) (by omega) (by omega)
        ((((adj p v (mV (sub vf)) pv).append (wk.mono mV)).append (adj y b (bv hb) yb)).append
          (adj b p (av pA) bp)))
    have h := card_le_card (union_subset sub hM)
    rw [card_union_of_disjoint dis,fc,m6] at h
    omega
  have keep (y) (hy : y∈M) : outN D V y⊆M∪T := by
    intro z hz
    rcases mem_insert.mp (restrictB y (mB hy) hz) with e|m
    · exact (noP y hy (e ▸ (mem_outN.mp hz).2)).elim
    rcases mem_union.mp m with m|m
    · rw [bm] at m
      rcases mem_insert.mp m with e|m
      · exact (noB y hy (e ▸ (mem_outN.mp hz).2)).elim
      · exact mem_union_left _ m
    · exact mem_union_right _ m
  have dis := btD.mono_left mB
  apply no_spill_bank_at35 hf ho (by omega) (fun y hy => (sizes y hy).1.le)
  refine ⟨mV,tv,m6,t6,dis,cyc1,keep,?_⟩
  intro y hy z hz
  have row : outN D (M∪T) y=outN D V y := by
    ext w
    simp only [mem_outN]
    exact ⟨fun h => ⟨union_subset mV tv h.1,h.2⟩,
      fun h => ⟨keep y hy (mem_outN.mpr h),h.2⟩⟩
  have count := card_outN_union (D:=D) (x:=y) dis
  rw [row,ho y (mV hy),cyc1 y hy] at count
  have eq : outN D T y=T := eq_of_subset_of_card_le outN_subset (by omega)
  exact (mem_outN.mp (eq.symm ▸ hz)).2

theorem endpoint_first_layer_not_acyclic {D : CH.Digraph} {V : Finset ℕ} {u : ℕ}
    (hf : QFree D V 5) (ho : OutEq 7 D V) (n : V.card=35)
    (noLow : ∀ v∈V, 15≤(ball D V v 2).card) (hu : u∈V)
    (acyc : QFree D (outN D V u) 7) : False := by
  let A := outN D V u
  have hA : A.card=7 := ho u hu
  obtain ⟨z,hz⟩ := card_pos.mp (show 0<A.card by omega)
  obtain ⟨a,ha,asink,_,_,_⟩ := reach_sink_of_card acyc hA.le hz
  apply endpoint_no_reachable_sink hf ho n noLow hu ha asink
  intro x hx
  obtain ⟨b,hb,bsink,k,_,wk⟩ := reach_sink_of_card acyc hA.le hx
  have rows (y) (hy : y∈A) (sink : ∀ z∈A,D y z≠true) :
      outN D V y=SecondBank D V u := by
    have sub : outN D V y⊆SecondBank D V u := by
      intro w hw
      obtain ⟨wv,yw⟩ := mem_outN.mp hw
      refine mem_sdiff.mpr ⟨ball_step ((mem_ball_one hu).mpr (Or.inr hy)) wv yw,?_⟩
      intro m
      rcases (mem_ball_one hu).mp m with e|m
      · subst w
        exact hf u 2 (by decide) (by decide)
          (.step (mem_outN.mp hy).1 (mem_outN.mp hy).2 (.step hu yw (.refl u)))
      · exact sink w m yw
    have cap : (ball D V u 2).card≤15 := by
      have floor (v) (hv : v∈V) : 21≤(ball D V v 3).card := by
        have h := floor_three20 hf (fun w hw => (ho w hw).ge) hv
        by_contra! lt
        have e : (ball D V v 3).card=20 := by omega
        have g := tight_three_only_tight_two hf ho hv e
        have k := noLow v hv
        omega
      exact (two_balls_boundary_cards hf (by decide : 2+3≤5) noLow floor
        (by omega : 15+21=V.card+1) u hu).1.le
    have diff := card_sdiff_add_card_eq_card (ball_mono_radius (D:=D) (W:=V) (u:=u) (by decide : 1≤2))
    have one : (ball D V u 1).card=8 := by
      rw [card_B1 (hf.mono_bound (by decide : 4≤5)) hu,ho u hu]
    apply eq_of_subset_of_card_le sub
    rw [ho y (mem_outN.mp hy).1]
    unfold SecondBank
    omega
  have eq : b=a := by
    by_contra e
    exact saturated_mixed_endpoint_no_twins hf ho n noLow (mem_outN.mp hb).1
      (mem_outN.mp ha).1 e ((rows b hb bsink).trans (rows a ha asink).symm)
  exact ⟨k,eq ▸ wk⟩

#print axioms endpoint_no_reachable_sink
#print axioms endpoint_first_layer_not_acyclic
end LeanCH.BR.DotDegreeSevenLow
