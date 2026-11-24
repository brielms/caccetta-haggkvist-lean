import checkpoints.shen_extension.dot_tensor_research.DotDegreeSevenQ7EndpointProfileActive_20261121

namespace LeanCH.BR.DotDegreeSevenQ7
open Finset BRq2 BRq3 BR45

set_option maxHeartbeats 2000000 in
/-- Close the last endpoint profile using the labeled two-basin return frame. -/
theorem paired_profile_impossible {D : CH.Digraph} {V : Finset ℕ} {u : ℕ}
    (hf : QFree D V 7) (ho : OutEq 7 D V) (hu : u∈V)
    (b3 : ∀ x∈V, (ball D V x 3).card=22)
    (b4 : ∀ x∈V, (ball D V x 4).card=28)
    (noTwin : ∀ s∈V, ∀ t∈V, outN D V s = outN D V t → s=t) : False := by
  classical
  obtain ⟨F⟩ := native_active_basins hf ho hu b3 b4 noTwin
  let A := outN D V u
  let B := ball D V u 2 \ ball D V u 1
  let T := ball D V u 3 \ ball D V u 2
  let W := ball D V u 4 \ ball D V u 3
  let k := F.missing
  let P (s : ℕ) := A.filter (ExclusiveBasin D A s)
  let R (s : ℕ) := (P s).filter (fun x => D (k s) x=true)
  let IsA := fun s => IsSinkOn D A s
  let IsR := fun s => (R s).Nonempty
  let Ret := fun s t => ∀ b∈B, ∀ x∈A, D b x=true →
    (b=k s ∧ ExclusiveBasin D A s x) ∨ (b=k t ∧ ExclusiveBasin D A t x)
  have AV : A⊆V := fun _ h => (mem_outN.mp h).1
  have A1 : A⊆ball D V u 1 := fun _ h => (mem_ball_one hu).2 (Or.inr h)
  have BV : B⊆V := fun _ h => ball_subset (mem_sdiff.mp h).1
  have WV : W⊆V := fun _ h => ball_subset (mem_sdiff.mp h).1
  have A7 : A.card=7 := ho u hu
  have b2 v (hv : v∈V) := paired_profile_two hf ho hv (b3 v hv) (b4 v hv)
  have B8 : B.card=8 := by
    have h := card_sdiff_add_card_eq_card (ball_mono_radius (D:=D) (W:=V) (u:=u) (by decide : 1≤2))
    change B.card+(ball D V u 1).card=(ball D V u 2).card at h
    rw [card_B1 (hf.mono_bound (by decide : 4≤7)) hu,ho u hu,b2 u hu] at h
    omega
  have T6 : T.card=6 := by
    have h := card_sdiff_add_card_eq_card (ball_mono_radius (D:=D) (W:=V) (u:=u) (by decide : 2≤3))
    change T.card+(ball D V u 2).card=(ball D V u 3).card at h
    rw [b2 u hu,b3 u hu] at h
    omega
  have W6 : W.card=6 := by
    have h := card_sdiff_add_card_eq_card (ball_mono_radius (D:=D) (W:=V) (u:=u) (by decide : 3≤4))
    change W.card+(ball D V u 3).card=(ball D V u 4).card at h
    rw [b3 u hu,b4 u hu] at h
    omega
  have rmem (s v) : v∈R s ↔ ExclusiveBasin D A s v ∧ D (k s) v=true := by
    constructor
    · intro hv
      exact ⟨(mem_filter.mp (mem_filter.mp hv).1).2,(mem_filter.mp hv).2⟩
    · rintro ⟨p,h⟩
      exact mem_filter.mpr ⟨mem_filter.mpr ⟨p.1,p⟩,h⟩
  have head_omit (s : ℕ) (ss : IsA s) : outN D V s = B.erase (k s) := by
    ext y
    constructor
    · intro hy
      obtain ⟨hyv,hsy⟩ := mem_outN.mp hy
      have yb : y∈B := by
        refine mem_sdiff.mpr ⟨ball_step (A1 ss.1) hyv hsy,?_⟩
        intro h
        rcases (mem_ball_one hu).1 h with rfl|hya
        · exact no_back_arc hf hu (A1 ss.1) (by decide : 1+1≤7) hsy
        · exact ss.2 y hya hsy
      exact mem_erase.mpr ⟨fun e => (F.omitted s ss y yb).mpr e hsy,yb⟩
    · intro hy
      obtain ⟨ne,yb⟩ := mem_erase.mp hy
      exact mem_outN.mpr ⟨BV yb,by_contra fun h => ne ((F.omitted s ss y yb).mp h)⟩
  have ptot (s t) (ne : s≠t) : (P s).card+(P t).card≤7 := by
    have d : Disjoint (P s) (P t) := disjoint_left.mpr (fun x xs xt =>
      exclusive_ne (hf.mono_set AV) A7.le ne (mem_filter.mp xs).2 (mem_filter.mp xt).2)
    have h := card_le_card (union_subset (s:=P s) (t:=P t) (filter_subset _ _) (filter_subset _ _))
    rw [card_union_of_disjoint d,A7] at h
    exact h
  have len_label (s x) (bs : ExclusiveBasin D A s x) (p : ShortestSinkPath D A x) :
      ∀ i, i≤p.len → p.vertex i ∈ P s := by
    intro i hi
    have w := p.walk (Nat.zero_le i) hi
    rw [p.start,Nat.sub_zero] at w
    have h := p.mem i hi
    exact mem_filter.mpr ⟨h,exclusive_of_walk bs h w⟩
  have end_label (s x) (bs : ExclusiveBasin D A s x) (p : ShortestSinkPath D A x) :
      p.vertex p.len=s := by
    have w := p.walk (Nat.zero_le p.len) le_rfl
    rw [p.start,Nat.sub_zero] at w
    exact bs.2 _ ⟨p.mem _ le_rfl,p.sink⟩ ⟨_,w⟩
  have len_card (s x) (bs : ExclusiveBasin D A s x) (p : ShortestSinkPath D A x) :
      p.len+1≤(P s).card := by
    have sub : (range (p.len+1)).image p.vertex ⊆ P s := by
      intro y hy
      obtain ⟨i,hi,rfl⟩ := mem_image.mp hy
      exact len_label s x bs p i (by have := mem_range.mp hi; omega)
    have h := card_le_card sub
    rwa [card_image_of_injOn (p.injective (hf.mono_set AV) A7.le),card_range] at h
  have sink_recipient (s) (rs : IsR s) : s∈P s := by
    obtain ⟨x,hx⟩ := rs
    have xs := ((rmem s x).1 hx).1
    obtain ⟨p⟩ := exists_shortest_sink_path (hf.mono_set AV) A7.le xs.1
    have h := len_label s x xs p p.len le_rfl
    rwa [end_label s x xs p] at h
  have pair (s t) (ss : IsA s) (st : IsA t) (nk : k s≠k t)
      (x y) (hx : x∈R s) (hy : y∈R t) (m n)
      (wx : Walk D A x s m) (wy : Walk D A y t n) : 4≤m+n := by
    have es : D s (k t)=true := by
      by_contra h
      exact nk ((F.omitted s ss (k t) (F.omissions t st)).mp h).symm
    have et : D t (k s)=true := by
      by_contra h
      exact nk ((F.omitted t st (k s) (F.omissions s ss)).mp h)
    obtain ⟨xs,ex⟩ := (rmem s x).1 hx
    obtain ⟨yt,ey⟩ := (rmem t y).1 hy
    exact basin_pair_gap hf AV xs.1 yt.1 (BV (F.omissions s ss)) (BV (F.omissions t st)) wx wy es ey et ex
  have cover (s t) (ss : IsA s) (hs : Ret s t)
      (par : ∀ y∈B, D y (k s)≠true) :
      ball D V s 2 ⊆ insert s (((B.erase (k s)) ∪ T) ∪ R t) := by
    intro y hy
    by_cases eq : y=s
    · exact mem_insert.mpr (Or.inl eq)
    obtain ⟨b,hb,eby⟩ := exists_pred (AV ss.1) hy eq
    rcases (mem_ball_one (AV ss.1)).1 hb with rfl|hr
    · have h : y∈outN D V b := mem_outN.mpr ⟨ball_subset hy,eby⟩
      rw [head_omit b ss] at h
      exact mem_insert_of_mem (mem_union_left _ (mem_union_left _ h))
    have bR : b∈B.erase (k s) := head_omit s ss ▸ hr
    obtain ⟨bne,bB⟩ := mem_erase.mp bR
    have y3 := ball_step (mem_sdiff.mp bB).1 (ball_subset hy) eby
    by_cases y2 : y∈ball D V u 2
    · by_cases y1 : y∈ball D V u 1
      · rcases (mem_ball_one hu).1 y1 with rfl|ya
        · exact (no_back_arc hf hu (mem_sdiff.mp bB).1 (by decide : 2+1≤7) eby).elim
        rcases hs b bB y ya eby with ⟨e,_⟩|⟨e,bt⟩
        · exact (bne e).elim
        · exact mem_insert_of_mem (mem_union_right _ ((rmem t y).2 ⟨bt,e ▸ eby⟩))
      · have ym : y≠k s := fun e => par b bB (e ▸ eby)
        exact mem_insert_of_mem (mem_union_left _ (mem_union_left _ (mem_erase.mpr ⟨ym,mem_sdiff.mpr ⟨y2,y1⟩⟩)))
    · exact mem_insert_of_mem (mem_union_left _ (mem_union_right _ (mem_sdiff.mpr ⟨y3,y2⟩)))
  have omit_no_parent (s t) (ss : IsA s) (st : IsA t) (ns : s≠t) (nk : k s≠k t)
      (rs : IsR s) (rt : IsR t) (rev : Ret t s) : ∀ b∈B, D b (k s)≠true := by
    intro b hb arc
    have bne : b≠k s := fun e => loopfree hf (by decide : 1≤7) (BV hb) (e ▸ arc)
    have sb : D s b=true := by
      by_contra no
      exact bne ((F.omitted s ss b hb).mp no)
    have low (x) (hx : x∈R s) (m) (w : Walk D A x s m) : 5≤m := by
      obtain ⟨xs,ex⟩ := (rmem s x).1 hx
      by_contra! short
      exact hf b (m+3) (by omega) (by omega) (by
        simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          (Walk.step (BV (F.omissions s ss)) arc
            (Walk.step (AV xs.1) ex ((w.mono AV).snoc (BV hb) sb))))
    obtain ⟨x,hx⟩ := rs
    have xs := ((rmem s x).1 hx).1
    obtain ⟨p⟩ := exists_shortest_sink_path (hf.mono_set AV) A7.le xs.1
    have ep := end_label s x xs p
    have wx := p.walk (Nat.zero_le p.len) le_rfl
    rw [p.start,Nat.sub_zero,ep] at wx
    have pl := low x hx p.len wx
    have cr := long_basin_budget (hf.mono_set AV) A7.le (filter_subset _ _) ss p ep pl (len_label s x xs p) low
    change (R s).card+5≤(P s).card at cr
    have pc := len_card s x xs p
    have tc := card_pos.mpr rt
    have ct : (R t).card≤(P t).card := card_le_card (filter_subset _ _)
    have total := ptot s t ns
    have one : (P t).card=1 := by omega
    have rtT : t∈R t := by
      have tp := sink_recipient t rt
      obtain ⟨y,hy⟩ := rt
      have yp : y∈P t := (mem_filter.mp hy).1
      have eq : P t={t} := by
        symm
        apply eq_of_subset_of_card_le (singleton_subset_iff.mpr tp)
        simp [one]
      have e : y=t := mem_singleton.mp (eq ▸ yp)
      exact e ▸ hy
    have no_t (y) (hy : y∈B) : D y (k t)≠true := by
      intro edge
      have ne : y≠k t := fun e => loopfree hf (by decide : 1≤7) (BV hy) (e ▸ edge)
      have ety : D t y=true := by
        by_contra no
        exact ne ((F.omitted t st y hy).mp no)
      exact hf t 3 (by decide) (by decide)
        (.step (BV hy) ety (.step (BV (F.omissions t st)) edge
          (.step (AV st.1) ((rmem t t).1 rtT).2 (.refl t))))
    have c := card_le_card (cover t s st rev no_t)
    have d := (card_insert_le t (((B.erase (k t)) ∪ T) ∪ R s)).trans
      (Nat.succ_le_succ ((card_union_le _ _).trans (Nat.add_le_add_right (card_union_le _ _) _)))
    have e : (B.erase (k t)).card=B.card-1 := card_erase_of_mem (F.omissions t st)
    rw [b2 t (AV st.1)] at c
    omega
  have capR (s t) (ss : IsA s) (st : IsA t) (ns : s≠t) (nk : k s≠k t)
      (rs : IsR s) (rt : IsR t) : (R s).card≤2 := by
    obtain ⟨y,hy⟩ := rt
    have yt := ((rmem t y).1 hy).1
    obtain ⟨q⟩ := exists_shortest_sink_path (hf.mono_set AV) A7.le yt.1
    have wy := q.walk (Nat.zero_le q.len) le_rfl
    rw [q.start,Nat.sub_zero,end_label t y yt q] at wy
    have qc := len_card t y yt q
    let rank := 5-(P t).card
    have low (x) (hx : x∈R s) (m) (w : Walk D A x s m) : rank≤m := by
      have pair' := pair s t ss st nk x y hx hy m q.len w wy
      dsimp [rank]
      omega
    obtain ⟨x,hx⟩ := rs
    have xs := ((rmem s x).1 hx).1
    obtain ⟨p⟩ := exists_shortest_sink_path (hf.mono_set AV) A7.le xs.1
    have ep := end_label s x xs p
    have wx := p.walk (Nat.zero_le p.len) le_rfl
    rw [p.start,Nat.sub_zero,ep] at wx
    have c := long_basin_budget (hf.mono_set AV) A7.le (filter_subset _ _) ss p ep
      (low x hx p.len wx) (len_label s x xs p) low
    have total := ptot s t ns
    change (R s).card+(5-(P t).card)≤(P s).card at c
    omega
  have force_sink (s t) (ss : IsA s) (st : IsA t) (ns : s≠t) (ret : Ret s t)
      (par : ∀ y∈B, D y (k s)≠true) (cap : (R t).card≤2) (rt : IsR t) : t∈R t := by
    let C := insert s (((B.erase (k s)) ∪ T) ∪ R t)
    have eqC : ball D V s 2 = C := by
      apply eq_of_subset_of_card_le (cover s t ss ret par)
      change C.card ≤ (ball D V s 2).card
      rw [b2 s (AV ss.1)]
      have d := (card_insert_le s (((B.erase (k s)) ∪ T) ∪ R t)).trans
        (Nat.succ_le_succ ((card_union_le _ _).trans (Nat.add_le_add_right (card_union_le _ _) _)))
      have e : (B.erase (k s)).card=B.card-1 := card_erase_of_mem (F.omissions s ss)
      change C.card≤((B.erase (k s)).card+T.card+(R t).card)+1 at d
      omega
    have tf : T⊆ball D V s 2 := by
      rw [eqC]
      exact fun _ ht => mem_insert_of_mem (mem_union_left _ (mem_union_right _ ht))
    have w3 : W⊆ball D V s 3 := by
      intro y hy
      obtain ⟨z,hz,hzy⟩ := ball_succ_pred hu (mem_sdiff.mp hy).1 (mem_sdiff.mp hy).2
      exact ball_step (tf (mem_sdiff.mpr ⟨hz,fun z2 => (mem_sdiff.mp hy).2 (ball_step z2 (WV hy) hzy)⟩))
        (WV hy) hzy
    have C3u : C⊆ball D V u 3 := by
      intro x hx
      rcases mem_insert.mp hx with rfl|hx
      · exact ball_mono_radius (by decide : 1≤3) (A1 ss.1)
      rcases mem_union.mp hx with hx|hx
      · rcases mem_union.mp hx with hx|hx
        · exact ball_mono_radius (by decide : 2≤3) (mem_sdiff.mp (mem_erase.mp hx).2).1
        · exact (mem_sdiff.mp hx).1
      · exact ball_mono_radius (by decide : 1≤3) (A1 (((rmem t x).1 hx).1.1))
    have dis : Disjoint C W := disjoint_left.mpr fun x hx hw => (mem_sdiff.mp hw).2 (C3u hx)
    have eq3 : ball D V s 3=C∪W := by
      apply (eq_of_subset_of_card_le ?_ ?_).symm
      · apply union_subset ?_ w3
        rw [←eqC]
        exact ball_mono_radius (by decide : 2≤3)
      · rw [card_union_of_disjoint dis,←eqC,b2 s (AV ss.1),W6,b3 s (AV ss.1)]
    have step (x y) (xr : x∈R t) (ya : y∈A) (xy : D x y=true) : y∈R t := by
      have x2 : x∈ball D V s 2 := by
        rw [eqC]; exact mem_insert_of_mem (mem_union_right _ xr)
      have y3 := ball_step x2 (AV ya) xy
      rw [eq3] at y3
      have y1 := A1 ya
      have y2 := ball_mono_radius (by decide : 1≤2) y1
      have y3u := ball_mono_radius (by decide : 2≤3) y2
      rcases mem_union.mp y3 with yc|yw
      · rcases mem_insert.mp yc with eq|yc
        · exact (ns ((((rmem t x).1 xr).1.2) s ss ⟨1,.step (eq ▸ ya) (eq ▸ xy) (.refl s)⟩)).elim
        rcases mem_union.mp yc with yc|yr
        · rcases mem_union.mp yc with yb|yt
          · exact ((mem_sdiff.mp (mem_erase.mp yb).2).2 y1).elim
          · exact ((mem_sdiff.mp yt).2 y2).elim
        · exact yr
      · exact ((mem_sdiff.mp yw).2 y3u).elim
    obtain ⟨x,hx⟩ := rt
    have xs := ((rmem t x).1 hx).1
    obtain ⟨p⟩ := exists_shortest_sink_path (hf.mono_set AV) A7.le xs.1
    have all : ∀ i, i≤p.len → p.vertex i∈R t := by
      intro i
      induction i with
      | zero => intro _; rwa [p.start]
      | succ i ih =>
        intro hi
        exact step _ _ (ih (by omega)) (p.mem _ hi) (p.edge _ (by omega))
    have z := all p.len le_rfl
    rwa [end_label t x xs p] at z
  have ss := F.sSink
  have st := F.tSink
  have ne := F.ne
  have kn := F.missing_ne
  have ret : Ret F.s F.t := F.returns
  have rev : Ret F.t F.s := fun b hb v hv e => (ret b hb v hv e).symm
  have rs : IsR F.s := by obtain ⟨x,h⟩ := F.activeS; exact ⟨x,(rmem _ _).2 h⟩
  have rt : IsR F.t := by obtain ⟨x,h⟩ := F.activeT; exact ⟨x,(rmem _ _).2 h⟩
  have parS := omit_no_parent _ _ ss st ne kn rs rt rev
  have parT := omit_no_parent _ _ st ss ne.symm kn.symm rt rs ret
  have capS := capR _ _ ss st ne kn rs rt
  have capT := capR _ _ st ss ne.symm kn.symm rt rs
  have tR := force_sink _ _ ss st ne ret parS capT rt
  have sR := force_sink _ _ st ss ne.symm rev parT capS rs
  have gap := pair _ _ ss st kn _ _ sR tR 0 0 (.refl _) (.refl _)
  omega

#print axioms paired_profile_impossible

/-- Native endpoint wrapper: the 22/28 growth suppliers exclude order 49,
using exact forward/reverse pairing to preserve the no-twins condition. -/
theorem card_ge_fifty_of_floor {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V 7) (ho : OutEq 7 D V) (hn : V.Nonempty)
    (f4 : ∀ x∈V,28≤(ball D V x 4).card) : 50≤V.card := by
  have f3 := floor_three hf (fun _ h => (ho _ h).ge)
  have order := card_ge_of_two_balls hf (by decide : 3+4≤7) f3 f4 hn
  by_contra! h
  have eq : 22+28=V.card+1 := by omega
  have cards (x) (hx : x∈V) :=
    two_balls_boundary_cards hf (by decide : 3+4≤7) f3 f4 eq x hx
  have revCards (x) (hx : x∈V) :=
    two_balls_boundary_cards hf (by decide : 4+3≤7) f4 f3 (by omega : 28+22=V.card+1) x hx
  have noTwin (s) (hs : s∈V) (t) (ht : t∈V) (same : outN D V s = outN D V t) : s=t := by
    by_contra ne
    by_cases reach : t∈ball D V s 3
    · exact distinct_rows_of_reach hf ne (by decide : 3≤7) reach same
    have cmp := two_balls_boundary_complement hf (by decide : 3+4≤7) f3 f4 eq hs
    have hrev : t∈reverseBall D V s 4 := by
      rw [cmp]
      exact mem_union_left _ (mem_sdiff.mpr ⟨ht,reach⟩)
    exact distinct_rows_of_reach hf (Ne.symm ne) (by decide : 4≤7) (mem_filter.mp hrev).2 same.symm
  obtain ⟨u,hu⟩ := hn
  exact paired_profile_impossible hf ho hu (fun x hx => (cards x hx).1)
    (fun x hx => (revCards x hx).1) noTwin

#print axioms card_ge_fifty_of_floor

end LeanCH.BR.DotDegreeSevenQ7



