import checkpoints.shen_extension.CyclicFirstLayer
import checkpoints.shen_extension.dot_tensor_research.DotDegreeSevenQ7EndpointProfileTraits_20261121

namespace LeanCH.BR.ProfileSinkReturns
open Finset BRq2 BRq3 BR45 BRsGen

/-- All eligible sinks and the actual omissions belong to the same digraph. -/
theorem omitted {D V X Y s r} (sink : ∀v∈X,D s v≠true)
    (confined : outN D V s⊆X∪Y) (row : (outN D V s).card=r) (width : Y.card=r+1) :
    ∃b∈Y, outN D V s=Y.erase b := by
  classical
  have sub : outN D V s⊆Y := by
    intro v vm
    exact (mem_union.mp (confined vm)).resolve_left (fun vx=>sink v vx (mem_outN.mp vm).2)
  have size : (Y\outN D V s).card=1 := by rw [card_sdiff_of_subset sub,width,row]; omega
  obtain ⟨b,eq⟩ := card_eq_one.mp size
  have off := mem_sdiff.mp (eq.symm ▸ mem_singleton_self b : b∈Y\outN D V s)
  refine ⟨b,off.1,eq_of_subset_of_card_le (fun v vm=>mem_erase.mpr ⟨fun e=>off.2 (e ▸ vm),sub vm⟩) ?_⟩
  rw [card_erase_of_mem off.1,width,row]
  omega

/-- Bound the number of distinct actual first-layer recipients of a two-step
return, after paying for the labels in the other two layers. -/
theorem return_count {D V X Y Z s} (sv : s∈V) (row : outN D V s⊆Y)
    (menu : ∀y∈outN D V s,outN D V y⊆X∪(Y∪Z)) :
    (ball D V s 2).card ≤ 1+(Y∪Z).card+
      (X∩((outN D V s).biUnion (outN D V))).card := by
  classical
  let T := X∩((outN D V s).biUnion (outN D V))
  have sub : ball D V s 2 ⊆ insert s ((Y∪Z)∪T) := by
    intro v vm
    by_cases one : v∈ball D V s 1
    · rcases (mem_ball_one sv).mp one with e|h
      · exact mem_insert.mpr (.inl e)
      · exact mem_insert_of_mem (mem_union_left _ (mem_union_left _ (row h)))
    obtain ⟨y,ym,yv⟩ := ball_succ_pred sv vm one
    rcases (mem_ball_one sv).mp ym with e|h
    · subst y
      exact (one (ball_of_adj (ball_subset vm) yv)).elim
    have dest := mem_outN.mpr ⟨ball_subset vm,yv⟩
    rcases mem_union.mp (menu y h dest) with vx|other
    · exact mem_insert_of_mem (mem_union_right _ (mem_inter.mpr ⟨vx,mem_biUnion.mpr ⟨y,h,dest⟩⟩))
    · exact mem_insert_of_mem (mem_union_left _ other)
  have bound := card_le_card sub
  have ins := card_insert_le s ((Y∪Z)∪T)
  have un := card_union_le (Y∪Z) T
  change _ ≤ 1+_+T.card
  omega

def Flat (D : CH.Digraph) (V : Finset ℕ) (r : ℕ) : Prop :=
  ∀u∈V,(ball D V u 2).card=2*r+2 ∧ (ball D V u 3).card=3*r+1 ∧ (ball D V u 4).card=4*r

theorem layers {D V q r u} (free : QFree D V q) (hq : 4≤q) (reg : OutEq r D V)
    (flat : Flat D V r) (uv : u∈V) :
    (N2 D V u).card=r+1 ∧ (N3 D V u).card+1=r ∧ (ball D V u 4\ball D V u 3).card+1=r := by
  obtain ⟨b,c,d⟩ := flat u uv
  have a := card_B1 (free.mono_bound hq) uv
  have t := reg u uv
  have h := @card_B2 D V u
  have j := @card_B3 D V u
  rw [card_sdiff_of_subset (ball_mono_radius (by decide : 3≤4)),c,d]
  omega

structure SinksAt (D : CH.Digraph) (V : Finset ℕ) (u : ℕ) : Prop where
  acyclic : QFree D (outN D V u) (outN D V u).card
  reachable : ∀x∈outN D V u, ∃s∈outN D V u,(∀v∈outN D V u,D s v≠true) ∧
    ∃k,k<(outN D V u).card ∧ Walk D (outN D V u) x s k
  at_sink : ∀s∈outN D V u,(∀v∈outN D V u,D s v≠true) →
    ∃b∈N2 D V u,outN D V s=(N2 D V u).erase b ∧ QFree D ((N2 D V u).erase b) ((N2 D V u).erase b).card ∧
      ∃y∈(N2 D V u).erase b, ∃t∈outN D V u,D y t=true

theorem sinks_at {D V q r} (free : QFree D V q) (hq : 4≤q) (hr : 7≤r) (fit : r≤q+1)
    (reg : OutEq r D V) (flat : Flat D V r) {u} (uv : u∈V) : SinksAt D V u := by
  classical
  have ac x (xv : x∈V) := CyclicFirstLayer.acyclic free hq hr fit reg xv
    (layers free hq reg flat xv).1 (layers free hq reg flat xv).2.1 (layers free hq reg flat xv).2.2
    (fun y ym=>(flat y (outN_subset ym)).2.1.le)
  refine ⟨ac u uv,fun _ xm=>reach_sink_of_card (ac u uv) le_rfl xm,?_⟩
  intro s sm sink
  have sv := outN_subset sm
  obtain ⟨b,bm,eq⟩ := omitted sink (fun _ m=>headX (free.mono_bound hq) uv sm (outN_subset m) (mem_outN.mp m).2)
    (reg s sv) (layers free hq reg flat uv).1
  refine ⟨b,bm,eq,eq ▸ ac s sv,?_⟩
  have ys : outN D V s⊆N2 D V u := eq ▸ erase_subset .. 
  have bound := return_count (X:=outN D V u) (Z:=N3 D V u) sv ys (fun y ym v vm=>by
    rcases headY (free.mono_bound hq) uv (ys ym) (outN_subset vm) (mem_outN.mp vm).2 with early|late
    · rcases mem_union.mp early with x|w
      · exact mem_union_left _ x
      · exact mem_union_right _ (mem_union_left _ w)
    · exact mem_union_right _ (mem_union_right _ late))
  have widths := layers free hq reg flat uv
  have union := card_union_le (N2 D V u) (N3 D V u)
  have size := (flat s sv).1
  obtain ⟨t,tm⟩ := card_pos.mp (show 0<(outN D V u ∩ (outN D V s).biUnion (outN D V)).card by omega)
  obtain ⟨tX,heads⟩ := mem_inter.mp tm
  obtain ⟨y,ym,yt⟩ := mem_biUnion.mp heads
  exact ⟨y,eq ▸ ym,t,tX,(mem_outN.mp yt).2⟩

theorem separated {D V q i j a b} (free : QFree D V q) (time : i+j≤q)
    (left : ∀x∈V,a≤(ball D V x i).card) (right : ∀x∈V,b≤(ball D V x j).card)
    (tight : a+b=V.card+1) {s t} (sm : s∈V) (tm : t∈V) (diff : s≠t) :
    outN D V s ≠ outN D V t := by
  by_cases reach : t∈ball D V s i
  · exact DotDegreeSevenQ7.distinct_rows_of_reach free diff (by omega) reach
  · have rev : t∈reverseBall D V s j := by
      rw [two_balls_boundary_complement free time left right tight sm]
      exact mem_union_left _ (mem_sdiff.mpr ⟨tm,reach⟩)
    exact fun eq=>DotDegreeSevenQ7.distinct_rows_of_reach free diff.symm (by omega) (mem_filter.mp rev).2 eq.symm

/-- A second-layer sink that misses X exposes the entire outside bank.
The returned t is the only possible first-layer destination for every
return from this same row of heads. -/
theorem exclusive_return {D V q r u s b y} (free : QFree D V q) (hq : 4≤q)
    (reg : OutEq r D V) (flat : Flat D V r) (uv : u∈V) (sm : s∈outN D V u)
    (bm : b∈N2 D V u) (eq : outN D V s=(N2 D V u).erase b) (ym : y∈outN D V s)
    (sink : ∀v∈outN D V s,D y v≠true) (miss : ∀v∈outN D V u,D y v≠true)
    {t v} (vm : v∈outN D V s) (tm : t∈outN D V u) (vt : D v t=true) :
    t≠s ∧ (∀a∈outN D V s, ∀x∈outN D V u,D a x=true → x=t) ∧
      (∀x∈outN D V u,D t x≠true) := by
  classical
  let X := outN D V u
  let Y := N2 D V u
  let Z := N3 D V u
  let W := ball D V u 4 \ ball D V u 3
  have sv := outN_subset sm
  have tv := outN_subset tm
  have yY := (mem_erase.mp (eq ▸ ym)).2
  have w := layers free hq reg flat uv

  have by2 := (mem_N2.mp bm).1
  have bz : b∉Z := fun h=>(mem_N3.mp h).2 by2
  have yz : Disjoint Y Z := disjoint_left.mpr (fun _ a c=>(mem_N3.mp c).2 (mem_N2.mp a).1)
  have home : outN D V y⊆insert b Z := by
    intro a am
    have ar := (mem_outN.mp am).2
    rcases headY (free.mono_bound hq) uv yY (outN_subset am) ar with early|late
    · rcases mem_union.mp early with x|ay
      · exact (miss a x ar).elim
      · by_cases e : a=b
        · exact mem_insert.mpr (.inl e)
        · exact (sink a (eq.symm ▸ mem_erase.mpr ⟨e,ay⟩) ar).elim
    · exact mem_insert_of_mem late
  have full := eq_of_subset_of_card_le home (by rw [card_insert_of_notMem bz,reg y (outN_subset ym)]; exact w.2.1.le)
  have covered : Y∪Z⊆ball D V s 2 := by
    intro a am
    have via (h : a∈insert b Z) := ball_step (X_B1 ym) (outN_subset (full.symm ▸ h)) (mem_outN.mp (full.symm ▸ h)).2
    rcases mem_union.mp am with ay|az
    · by_cases ab : a=b
      · exact via (mem_insert.mpr (.inl ab))
      · exact ball_mono_radius (by decide : 1≤2) (X_B1 (eq.symm ▸ mem_erase.mpr ⟨ab,ay⟩))
    · exact via (mem_insert_of_mem az)
  have hit := ball_step (X_B1 vm) tv vt
  have ts : t≠s := fun e=>by
    subst t
    exact no_back_arc free sv (X_B1 vm) (by omega) vt
  have first : X⊆ball D V u 1 := fun _ x=>X_B1 x
  have xSep : Disjoint X (Y∪Z) := disjoint_left.mpr (fun a ax az=>by
    rcases mem_union.mp az with ay|az
    · exact (mem_N2.mp ay).2 (first ax)
    · exact (mem_N3.mp az).2 (ball_mono_radius (by decide : 1≤2) (first ax)))
  let A := insert s (Y∪Z)
  have cardA : A.card=2*r+1 := by
    change (insert s (Y∪Z)).card=_
    rw [card_insert_of_notMem (disjoint_left.mp xSep sm),card_union_of_disjoint yz]
    change (N2 D V u).card + (N3 D V u).card + 1=_
    omega
  have part : A⊆ball D V s 2 := insert_subset (self_mem_ball sv) covered
  have off : t∉A := fun h=>(mem_insert.mp h).elim ts (disjoint_left.mp xSep tm)
  have pair : insert t A=ball D V s 2 := eq_of_subset_of_card_le (insert_subset hit part) (by
    rw [card_insert_of_notMem off,cardA,(flat s sv).1])
  have unique (x) (xx : x∈X) (xb : x∈ball D V s 2) (ne : x≠s) : x=t := by
    rcases mem_insert.mp (pair.symm ▸ xb) with e|rest
    · exact e
    · exact ((mem_insert.mp rest).elim ne (disjoint_left.mp xSep xx)).elim
  refine ⟨ts,fun a am x xx arc=>unique x xx (ball_step (X_B1 am) (outN_subset xx) arc)
    (fun e=>by subst x; exact no_back_arc free sv (X_B1 am) (by omega) arc),?_⟩
  have W3 : W⊆ball D V s 3 := by
    intro a aw
    obtain ⟨z,zm,za⟩ := ball_succ_pred uv (mem_sdiff.mp aw).1 (mem_sdiff.mp aw).2
    have late : z∈Z := mem_N3.mpr ⟨zm,fun early=>(mem_sdiff.mp aw).2
      (ball_step early (ball_subset (mem_sdiff.mp aw).1) za)⟩
    exact ball_step (covered (mem_union_right _ late)) (ball_subset (mem_sdiff.mp aw).1) za
  have early : ball D V s 2⊆ball D V u 3 := by
    intro a am
    obtain ⟨av,k,le,path⟩ := mem_ball.mp am
    exact mem_ball.mpr ⟨av,k+1,by omega,.step sv (mem_outN.mp sm).2 path⟩
  have sep : Disjoint (ball D V s 2) W := disjoint_left.mpr (fun _ h m=>(mem_sdiff.mp m).2 (early h))
  have exhausted := eq_of_subset_of_card_le (union_subset (ball_mono_radius (D:=D) (W:=V) (u:=s) (by decide : 2≤3)) W3) (by
    rw [card_union_of_disjoint sep,(flat s sv).1,(flat s sv).2.1]
    change _ ≤ 2*r+2 + (ball D V u 4 \ ball D V u 3).card
    omega)
  intro x xx arc
  have arr := ball_step hit (outN_subset xx) arc
  rcases mem_union.mp (exhausted.symm ▸ arr) with inner|far
  · by_cases xs : x=s
    · subst x
      exact no_back_arc free sv hit (by omega) arc
    · exact loopfree free (by omega) tv (unique x xx inner xs ▸ arc)
  · exact (mem_sdiff.mp far).2 (ball_mono_radius (by decide : 1≤3) (first xx))

/-- Two families of return tails covering Y cannot both be routed to the
same sink t. Only the actual return arcs and the outside quota are used. -/
theorem no_shared_destination {D V X Y Z H J q r t b}
    (free : QFree D V q) (time : 3≤q) (tv : t∈V) (bv : b∈V)
    (row : outN D V t=Y.erase b) (acyclic : QFree D (Y.erase b) (Y.erase b).card)
    (nonempty : (Y.erase b).Nonempty) (yv : Y⊆V)
    (turn : ∃a∈Y,D a t=true)
    (cover : Y⊆H∪J)
    (first : ∀a∈H,∀x∈X,D a x=true → x=t)
    (second : ∀a∈J,∀x∈X,D a x=true → x=t)
    (menu : ∀a∈Y,outN D V a⊆X∪(Y∪Z)) (degree : ∀a∈Y,r≤(outN D V a).card)
    (slots : Z.card<r) : False := by
  obtain ⟨a,ay,atx⟩ := turn
  have bt : D b t=true := by
    by_cases ab : a=b
    · exact ab ▸ atx
    · have ta := (mem_outN.mp (row.symm ▸ mem_erase.mpr ⟨ab,ay⟩)).2
      exact (free t 2 (by decide) (by omega) (.step (yv ay) ta (.step tv atx (.refl _)))).elim
  obtain ⟨w,wm,sink⟩ := BRq3.exists_sink acyclic nonempty le_rfl
  have wy := (mem_erase.mp wm).2
  have tw := (mem_outN.mp (row.symm ▸ wm)).2
  have sub : outN D V w⊆Z := by
    intro x xm
    have arc := (mem_outN.mp xm).2
    rcases mem_union.mp (menu w wy xm) with xx|rest
    · have eq : x=t := (mem_union.mp (cover wy)).elim
        (fun h=>first w h x xx arc) (fun h=>second w h x xx arc)
      subst x
      exact (free t 2 (by decide) (by omega) (.step (yv wy) tw (.step tv arc (.refl _)))).elim
    · rcases mem_union.mp rest with xy|xz
      · by_cases xb : x=b
        · subst x
          exact (free t 3 (by decide) time (.step (yv wy) tw (.step bv arc (.step tv bt (.refl _))))).elim
        · exact (sink x (mem_erase.mpr ⟨xb,xy⟩) arc).elim
      · exact xz
  exact (Nat.not_lt_of_ge ((degree w wy).trans (card_le_card sub))) slots

def Sink (D : CH.Digraph) (X : Finset ℕ) (s : ℕ) := ∀v∈X,D s v≠true

def Deflects (D : CH.Digraph) (V X : Finset ℕ) (s : ℕ) : Prop :=
  ∃y∈outN D V s,Sink D (outN D V s) y ∧ ∀x∈X,D y x≠true

/-- A relation between physical labels, including the existing two arcs
that witness this destination and every competitor on the same head bank. -/
def Routed (D : CH.Digraph) (V X : Finset ℕ) (s t : ℕ) : Prop :=
  (∃y∈outN D V s,D y t=true) ∧ ∀a∈outN D V s,∀x∈X,D a x=true → x=t

theorem route_exists {D V q r u s} (free : QFree D V q) (hq : 4≤q) (hr : 7≤r) (fit : r≤q+1)
    (reg : OutEq r D V) (flat : Flat D V r) (uv : u∈V) (sm : s∈outN D V u)
    (sink : Sink D (outN D V u) s) (deflect : Deflects D V (outN D V u) s) :
    ∃t∈outN D V u,t≠s ∧ Sink D (outN D V u) t ∧ Routed D V (outN D V u) s t := by
  obtain ⟨b,bm,eq,_,v,vm,t,tm,vt⟩ := (sinks_at free hq hr fit reg flat uv).at_sink s sm sink
  obtain ⟨y,ym,sy,my⟩ := deflect
  have orig : v∈outN D V s := eq.symm ▸ vm
  obtain ⟨diff,unique,st⟩ := exclusive_return free hq reg flat uv sm bm eq ym sy my orig tm vt
  exact ⟨t,tm,diff,st,⟨v,orig,vt⟩,unique⟩

theorem route_separates {D V q r u s v t} (free : QFree D V q) (hq : 4≤q) (hr : 7≤r) (fit : r≤q+1)
    (reg : OutEq r D V) (flat : Flat D V r) (uv : u∈V)
    (sm : s∈outN D V u) (vm : v∈outN D V u) (tm : t∈outN D V u)
    (ss : Sink D (outN D V u) s) (vs : Sink D (outN D V u) v) (ts : Sink D (outN D V u) t)
    (sr : Routed D V (outN D V u) s t) (vr : Routed D V (outN D V u) v t) :
    outN D V s=outN D V v := by
  have all := sinks_at free hq hr fit reg flat uv
  obtain ⟨b,bm,bt,acyclic,_⟩ := all.at_sink t tm ts
  obtain ⟨a,am,sa,_⟩ := all.at_sink s sm ss
  obtain ⟨c,cm,vc,_⟩ := all.at_sink v vm vs
  by_contra different
  have diff : a≠c := fun e=>different (sa.trans (e ▸ vc.symm))
  obtain ⟨y,ym,yt⟩ := sr.1
  have enough : ((N2 D V u).erase b).Nonempty := by
    apply card_pos.mp
    rw [←bt,reg t (outN_subset tm)]
    omega
  apply no_shared_destination free (by omega) (outN_subset tm) (N2_subV bm) bt acyclic enough
    (fun _ m=>N2_subV m) ⟨y,(mem_erase.mp (sa ▸ ym)).2,yt⟩ _ sr.2 vr.2
    (Z:=N3 D V u) _ (fun x xm=>(reg x (N2_subV xm)).ge) (by have := (layers free hq reg flat uv).2.1; omega)
  · intro x xm
    rw [sa,vc]
    by_cases xa : x=a
    · exact mem_union_right _ (mem_erase.mpr ⟨xa ▸ diff,xm⟩)
    · exact mem_union_left _ (mem_erase.mpr ⟨xa,xm⟩)
  · intro a ay x xm
    rcases headY (free.mono_bound hq) uv ay (outN_subset xm) (mem_outN.mp xm).2 with h|h
    · rcases mem_union.mp h with l|r
      · exact mem_union_left _ l
      · exact mem_union_right _ (mem_union_left _ r)
    · exact mem_union_right _ (mem_union_right _ h)

/-- A sink receiving an arc from the second layer cannot itself deflect.
Its omitted label would simultaneously receive a head of its own row
and return to the sink, closing a triangle. -/
theorem destination_stays {D V q r u t b a} (free : QFree D V q) (hq : 4≤q)
    (reg : OutEq r D V) (uv : u∈V) (tm : t∈outN D V u) (bm : b∈N2 D V u)
    (row : outN D V t=(N2 D V u).erase b) (az : a∈N2 D V u) (atx : D a t=true)
    (slots : (N3 D V u).card<r) : ¬Deflects D V (outN D V u) t := by
  rintro ⟨y,ym,sink,miss⟩
  have tv := outN_subset tm
  have yy := (mem_erase.mp (row ▸ ym)).2
  have bt : D b t=true := by
    by_cases e : a=b
    · exact e ▸ atx
    · have ta := (mem_outN.mp (row.symm ▸ mem_erase.mpr ⟨e,az⟩)).2
      exact (free t 2 (by decide) (by omega) (.step (N2_subV az) ta (.step tv atx (.refl _)))).elim
  have sub : outN D V y⊆N3 D V u := by
    intro z zm
    have arc := (mem_outN.mp zm).2
    rcases headY (free.mono_bound hq) uv yy (outN_subset zm) arc with early|late
    · rcases mem_union.mp early with first|second
      · exact (miss z first arc).elim
      · by_cases e : z=b
        · subst z
          exact (free t 3 (by decide) (by omega) (.step (outN_subset ym) (mem_outN.mp ym).2
            (.step (N2_subV bm) arc (.step tv bt (.refl _))))).elim
        · exact (sink z (row.symm ▸ mem_erase.mpr ⟨e,second⟩) arc).elim
    · exact late
  have lim := card_le_card sub
  rw [reg y (outN_subset ym)] at lim
  omega

structure Routing (D : CH.Digraph) (V : Finset ℕ) (u : ℕ) : Prop where
  layers : SinksAt D V u
  send : ∀s∈outN D V u,Sink D (outN D V u) s → Deflects D V (outN D V u) s →
    ∃t∈outN D V u,Sink D (outN D V u) t ∧ ¬Deflects D V (outN D V u) t ∧ Routed D V (outN D V u) s t
  injective : ∀s∈outN D V u,∀v∈outN D V u,∀t∈outN D V u,
    Sink D (outN D V u) s → Sink D (outN D V u) v → Sink D (outN D V u) t →
    Routed D V (outN D V u) s t → Routed D V (outN D V u) v t → s=v

theorem routing {D V q r u} (free : QFree D V q) (hq : 4≤q) (hr : 7≤r) (fit : r≤q+1)
    (reg : OutEq r D V) (flat : Flat D V r) (uv : u∈V)
    (distinct : ∀s∈V,∀v∈V,s≠v → outN D V s≠outN D V v) : Routing D V u := by
  have all := sinks_at free hq hr fit reg flat uv
  refine ⟨all,?_,?_⟩
  · intro s sm sink d
    obtain ⟨t,tm,_,ts,route⟩ := route_exists free hq hr fit reg flat uv sm sink d
    obtain ⟨b,bm,bt,_⟩ := all.at_sink t tm ts
    obtain ⟨a,am,atx⟩ := route.1
    have ay := (mem_union.mp (headX (free.mono_bound hq) uv sm (outN_subset am) (mem_outN.mp am).2)).resolve_left
      (fun ax=>sink a ax (mem_outN.mp am).2)
    exact ⟨t,tm,ts,destination_stays free hq reg uv tm bm bt ay atx (by have := (layers free hq reg flat uv).2.1; omega),route⟩
  · intro s sm v vm t tm ss vs ts sr vr
    by_contra ne
    exact distinct _ (outN_subset sm) _ (outN_subset vm) ne (route_separates free hq hr fit reg flat uv sm vm tm ss vs ts sr vr)

structure OnFamily (p : CHRuleCatalog.Input) : Prop where
  on_graph : ∀{q},q≤CHRuleCatalog.cutoff p → 7≤q → 7≤p.s → p.s≤q+1 →
    RetainedLayerCapacity.FourthRoom p.s → MixedBankScore.Capacity p.s → MixedBankProfile.Room p.s → EqualMixedShells.Room p.s →
    p.n≤7*p.s → ∀F,(∀a b,F a b=true → p.D a b=true) → OutEq p.s F (range p.n) →
      ∀u∈range p.n,Routing F (range p.n) u

theorem native {p : CHRuleCatalog.Input} (bad : CHRuleCatalog.Bad p) (profile : EqualMixedShells.OnFamily p) :
    OnFamily p := by
  constructor
  intro q cut hq hr fit prev cap more room size F sub reg u uv
  have free := qfree_sub sub ((qfree_of_noShort bad.loopless bad.missing).mono_bound cut)
  have flat := profile.on_graph cut hq hr fit prev cap more room size F sub reg
  have left := fun x (xm : x∈range p.n)=>(flat x xm).2.1.ge
  have right := fun x (xm : x∈range p.n)=>(flat x xm).2.2.ge
  have time : 3+4≤q := by omega
  have lower := card_ge_of_two_balls free time left right ⟨u,uv⟩
  rw [card_range] at lower
  exact routing free (by omega) hr fit reg flat uv (fun _ sm _ vm ne=>separated free time left right (by rw [card_range]; omega) sm vm ne)

attribute [aesop safe forward (immediate := [bad,profile]) (rule_sets := [CHGraphFamilies])] native
attribute [aesop safe forward (immediate := [free,hq,hr,fit,reg,flat,uv,distinct]) (rule_sets := [CHGraphFamilies])] routing
attribute [aesop safe forward (immediate := [free,hq,hr,fit,reg,flat,uv]) (rule_sets := [CHGraphFamilies])] sinks_at
attribute [aesop safe forward (immediate := [sv,row,menu]) (rule_sets := [CHGraphFamilies])] return_count
#print axioms native
#print axioms destination_stays
#print axioms routing
#print axioms route_separates
#print axioms route_exists
#print axioms exclusive_return
#print axioms sinks_at
#print axioms separated
end LeanCH.BR.ProfileSinkReturns
