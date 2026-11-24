import checkpoints.shen_extension.dot_tensor_research.DotDegreeSevenQ4EndpointVerified_20261121

/-! Degree six, cutoff four: the shared-escort proof, not a boundary regularity premise. -/
namespace LeanCH.BR.DotDegreeSix
open Finset BRq2 BRq3 BR45 BRsGen DotDegreeSevenLow DotClonePairCompletion
open scoped BigOperators
set_option maxHeartbeats 1000000

theorem floor_two12 {D : CH.Digraph} {V : Finset ℕ} {u q : ℕ}
    (hq : 4≤q) (hf : QFree D V q) (hm : ∀ v∈V, 6≤(outN D V v).card) (hu : u∈V) : 12≤(ball D V u 2).card := by
  obtain ⟨G,sub,ho⟩ := exists_outEq hm
  have f := qfree_sub sub hf
  have dm : ∀ v∈V, 6≤(outN G V v).card := fun _ hv => (ho _ hv).ge
  have lo : 12≤(ball G V u 2).card := by
    by_contra! low
    have one : (ball G V u 1).card=7 := by
      rw [card_B1 (f.mono_bound hq) hu,ho u hu]
    have lc := card_sdiff_add_card_eq_card
      (ball_mono_radius (D:=G) (W:=V) (u:=u) (by decide : 1≤2))
    let A := (ball G V u 1).erase u
    have a : A.card=6 := by
      change ((ball G V u 1).erase u).card=6
      rw [card_erase_of_mem (self_mem_ball hu),one]
    have adj : ∀ v∈A,2≤(outN G A v).card :=
      minOut_prefix_erase (d:=2) f hu (by omega : 1+1≤q) dm (by
        simp only [Nat.reduceAdd]
        omega)
    have h := corB (U:=A) (by omega : 1≤q) (f.mono_set ((erase_subset u _).trans ball_subset))
      adj (card_pos.mp (by omega))
    change 2*q+1≤A.card at h
    omega
  exact lo.trans (card_le_card (ball_sub sub))

structure MarksSix (D : CH.Digraph) (V X J : Finset ℕ)
    (s a : ℕ→ℕ) (T : ℕ→Finset ℕ) : Prop where
  xV : X⊆V
  x6 : X.card=6
  sMem : ∀ i∈J, s i∈X
  sInj : (↑J : Set ℕ).InjOn s
  avoidS : ∀ i∈J, ∀ x∈X, D x (s i)≠true
  aV : ∀ i∈J, a i∈V
  aOut : ∀ i∈J, a i∉X
  aArc : ∀ i∈J, D (s i) (a i)=true
  aNot : ∀ i∈J, a i∉T i
  aOther : ∀ i∈J, ∀ j∈J, i≠j → a i∈T j
  support : ∀ i∈J, ∀ x∈X, x≠s i → outN D V x⊆X∪T i

theorem all_six
    {D : CH.Digraph} {V J : Finset ℕ} {c : ℕ}
    {s a : ℕ→ℕ} {T : ℕ→Finset ℕ}
    (hf : QFree D V 4) (ho : OutEq 6 D V) (hc : c∈V)
    (P : MarksSix D V (outN D V c) J s a T) (j7 : J.card=6) :
    18≤(ball D V c 2).card := by
  classical
  let X := outN D V c
  let Y := J.image s
  let W := J.image a
  have yX : Y⊆X := by
    intro x hx
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hx
    exact P.sMem i hi
  have yJ : Y.card=J.card := card_image_of_injOn P.sInj
  have yEq : Y=X := eq_of_subset_of_card_le yX (by rw [yJ,j7,ho c hc])
  have indep (x) (hx : x∈X) (y) (hy : y∈X) : D x y≠true := by
    have h : y∈Y := yEq.symm ▸ hy
    obtain ⟨i,hi,rfl⟩ := mem_image.mp h
    exact P.avoidS i hi x hx
  have wJ : W.card=J.card := by
    apply card_image_of_injOn
    intro i hi j hj e
    by_contra ne
    have mem := P.aOther i hi j hj ne
    rw [e] at mem
    exact P.aNot j hj mem
  have hsupport (i j : ℕ) (hi : i∈J) (hj : j∈J) (neq : i≠j) :
      outN D V (s j)⊆T i := by
    intro x hx
    have jX : s j∈X := P.sMem j hj
    have ne : s j≠s i := fun e => neq (P.sInj hj hi e).symm
    rcases mem_union.mp (P.support i hi (s j) jX ne hx) with xX|xT
    · exact (indep (s j) jX x xX (mem_outN.mp hx).2).elim
    · exact xT
  obtain ⟨h,hh⟩ := card_pos.mp (by omega : 0<J.card)
  let Z := (outN D V (s h)).erase (a h)
  have z6 : Z.card=5 := by
    have mem : a h∈outN D V (s h) := mem_outN.mpr ⟨P.aV h hh,P.aArc h hh⟩
    have hV := (mem_outN.mp (P.sMem h hh)).1
    rw [show Z=(outN D V (s h)).erase (a h) from rfl,card_erase_of_mem mem,ho _ hV]
  have nz (i) (hi : i∈J) : a i∉Z := by
    intro ia
    have ne : i≠h := by
      intro e
      subst i
      exact (mem_erase.mp ia).1 rfl
    exact P.aNot i hi (hsupport i h hi hh ne (mem_of_mem_erase ia))
  have nW : Disjoint (insert c X) W := disjoint_left.mpr (by
    intro x hx xW
    obtain ⟨i,hi,rfl⟩ := mem_image.mp xW
    rcases mem_insert.mp hx with ce|inX
    · have sc : D (s i) c=true := ce ▸ P.aArc i hi
      have ⟨iv,cs⟩ := mem_outN.mp (P.sMem i hi)
      exact hf c 2 (by decide) (by decide) (.step iv cs (.step hc sc (.refl c)))
    · exact P.aOut i hi inX)
  have nZ : Disjoint (insert c X ∪ W) Z := disjoint_left.mpr (by
    intro x mx xz
    have e := (mem_outN.mp (mem_of_mem_erase xz)).2
    rcases mem_union.mp mx with ix|wx
    · rcases mem_insert.mp ix with xc|xx
      · have ⟨sv,cs⟩ := mem_outN.mp (P.sMem h hh)
        exact hf c 2 (by decide) (by decide) (.step sv cs (.step hc (xc ▸ e) (.refl c)))
      · exact indep _ (P.sMem h hh) _ xx e
    · obtain ⟨i,hi,rfl⟩ := mem_image.mp wx
      exact nz i hi xz)
  have xin : insert c X⊆ball D V c 2 := by
    intro x hx
    rcases mem_insert.mp hx with rfl|xX
    · exact self_mem_ball hc
    · obtain ⟨xv,e⟩ := mem_outN.mp xX
      exact mem_ball.mpr ⟨xv,1,by decide,.step xv e (.refl x)⟩
  have win : W⊆ball D V c 2 := by
    intro x hx
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hx
    obtain ⟨sv,cs⟩ := mem_outN.mp (P.sMem i hi)
    exact mem_ball.mpr ⟨P.aV i hi,2,by decide,
      .step sv cs (.step (P.aV i hi) (P.aArc i hi) (.refl _))⟩
  have zin : Z⊆ball D V c 2 := by
    intro x hx
    obtain ⟨xv,e⟩ := mem_outN.mp (mem_of_mem_erase hx)
    obtain ⟨sv,cs⟩ := mem_outN.mp (P.sMem h hh)
    exact mem_ball.mpr ⟨xv,2,by decide,.step sv cs (.step xv e (.refl x))⟩
  have notCX : c∉X := by
    intro cx
    exact hf c 1 (by decide) (by decide) (.step hc (mem_outN.mp cx).2 (.refl c))
  have lower := card_le_card (union_subset (union_subset xin win) zin)
  rw [card_union_of_disjoint nZ,card_union_of_disjoint nW,card_insert_of_notMem notCX,
    wJ,j7,z6,ho c hc] at lower
  omega

/-- At cutoff four the common core may have five labels. A row
of internal degree at most one suffices for the exact payment. -/
theorem thick_spill {D : CH.Digraph} {V X J : Finset ℕ}
    {s a : ℕ→ℕ} {T : ℕ→Finset ℕ}
    (hf : QFree D V 4) (ho : OutEq 6 D V)
    (P : MarksSix D V X J s a T) (lo : 2≤J.card) (hi : J.card≤5) :
    ∀ i∈J, J.card+5≤(T i).card := by
  classical
  let Y := J.image s
  let K := X\Y
  have yX : Y⊆X := by
    intro x hx
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hx
    exact P.sMem i hi
  have yJ : Y.card=J.card := card_image_of_injOn P.sInj
  have size : K.card+J.card=6 := by
    have e := card_sdiff_add_card_eq_card yX
    simpa only [K,yJ,P.x6] using e
  have kv : K⊆V := sdiff_subset.trans P.xV
  obtain ⟨y,hy,ys⟩ := exists_sink (hf.mono_set kv) (card_pos.mp (by omega)) (by omega)
  have yd : (outN D K y).card=0 := by
    apply card_eq_zero.mpr
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact ys x (mem_outN.mp hx).1 (mem_outN.mp hx).2
  let W := outN D V y \ K
  have il : outN D V y∩K=outN D K y := by
    ext x
    simp only [mem_inter,mem_outN]
    exact ⟨fun h => ⟨h.2,h.1.2⟩,fun h => ⟨⟨kv h.1,h.2⟩,h.1⟩⟩
  have w6 : 6≤W.card := by
    have k := card_sdiff_add_card_inter (outN D V y) K
    change W.card+(outN D V y∩K).card=(outN D V y).card at k
    rw [il,ho y (kv hy)] at k
    omega
  have my (i) (hi : i∈J) : W⊆T i := by
    have yX := (mem_sdiff.mp hy).1
    have nes : y≠s i := by
      intro e
      exact (mem_sdiff.mp hy).2 (mem_image.mpr ⟨i,hi,e.symm⟩)
    intro x hx
    obtain ⟨hd,hk⟩ := mem_sdiff.mp hx
    rcases mem_union.mp (P.support i hi y yX nes hd) with inX|inT
    · have arc := (mem_outN.mp hd).2
      by_cases xy : x∈Y
      · obtain ⟨j,jJ,rfl⟩ := mem_image.mp xy
        exact (P.avoidS j jJ y yX arc).elim
      · exact (hk (mem_sdiff.mpr ⟨inX,xy⟩)).elim
    · exact inT
  intro i ii
  let A := (J.erase i).image a
  have aT : A⊆T i := by
    intro x hx
    obtain ⟨j,jm,rfl⟩ := mem_image.mp hx
    exact P.aOther j (mem_erase.mp jm).2 i ii (mem_erase.mp jm).1
  have ai : (↑J : Set ℕ).InjOn a := by
    intro u hu v hv eq
    by_contra n
    have h := P.aOther u hu v hv n
    rw [eq] at h
    exact P.aNot v hv h
  have aJ : A.card=J.card-1 := by
    rw [show A=(J.erase i).image a from rfl,card_image_of_injOn,card_erase_of_mem ii]
    exact ai.mono (fun _ hx => mem_of_mem_erase hx)
  have sep : Disjoint A W := disjoint_left.mpr (by
    intro x xa xy
    obtain ⟨j,hj,rfl⟩ := mem_image.mp xa
    exact (P.aNot j (mem_erase.mp hj).2) (my j (mem_erase.mp hj).2 xy))
  have cnt := card_le_card (union_subset aT (my i ii))
  rw [card_union_of_disjoint sep,aJ] at cnt
  omega

noncomputable def spillQ4 (D : CH.Digraph) (V B : Finset ℕ) :=
  B.biUnion (fun b => outN D V b \ B)

structure GuardFrame (D : CH.Digraph) (V : Finset ℕ) (c u s a : ℕ)
    : Prop extends FullCycleFrame D V c u s a where
  cA : c∈(ball D V u 1).erase u
  noC : ∀ b∈SecondBank D V u, D b c≠true
  noS : ∀ b∈SecondBank D V u, D b s≠true
  noA : ∀ b∈SecondBank D V u, D b a≠true

theorem q4_shared_marks_of_frames {D : CH.Digraph} {V J : Finset ℕ} {c : ℕ} {s a : ℕ→ℕ}
    (hf : QFree D V 4) (ho : OutEq 6 D V) (hc : c∈V)
    (_jV : J⊆V) (_short : ∀ u∈J, (ball D V u 2).card=12)
    (inj : (↑J : Set ℕ).InjOn (SecondBank D V))
    (fr : ∀ u∈J, GuardFrame D V c u (s u) (a u)) :
    MarksSix D V (outN D V c) J s a (fun u => spillQ4 D V (SecondBank D V u)) := by
  let X := outN D V c
  have av (u) : (ball D V u 1).erase u⊆V := (erase_subset _ _).trans ball_subset
  have row (u) (hu : u∈J) : X=insert (s u) (SecondBank D V u) := (fr u hu).row
  have bank (u) (hu : u∈J) : SecondBank D V u=X.erase (s u) := by
    have sn : s u∉SecondBank D V u :=
      fun m => (mem_sdiff.mp m).2 (mem_of_mem_erase (fr u hu).sA)
    rw [row u hu,erase_insert sn]
  have head (u) (hu : u∈J) (x) (hx : x∈SecondBank D V u) :
      outN D V x⊆SecondBank D V u∪spillQ4 D V (SecondBank D V u) := by
    intro y hy
    by_cases yB : y∈SecondBank D V u
    · exact mem_union_left _ yB
    · have m : y∈(SecondBank D V u).biUnion (fun z => outN D V z \ SecondBank D V u) :=
        mem_biUnion.mpr ⟨x,hx,mem_sdiff.mpr ⟨hy,yB⟩⟩
      exact mem_union_right _ m
  have outside (u) (hu : u∈J) : a u∉X := by
    intro m
    rw [row u hu] at m
    rcases mem_insert.mp m with e|m
    · exact (fr u hu).aS e
    · exact (mem_sdiff.mp m).2 (mem_of_mem_erase (fr u hu).aA)
  have ins (u) (hu : u∈J) : s u∈X := by rw [row u hu]; exact mem_insert_self ..
  have injS : (↑J : Set ℕ).InjOn s := by
    intro i hi j hj e
    apply inj hi hj
    rw [bank i hi,bank j hj,e]
  refine ⟨outN_subset,ho c hc,ins,injS,?_,?_,outside,?_,?_,?_,?_⟩
  · intro i hi x xX e
    by_cases n : x=s i
    · subst x
      have sv := av i (fr i hi).sA
      exact hf (s i) 1 (by decide) (by decide) (.step sv e (.refl _))
    have xb : x∈SecondBank D V i := by
      rw [bank i hi]
      exact mem_erase.mpr ⟨n,xX⟩
    exact (fr i hi).noS x xb e
  · exact fun i hi => av i (fr i hi).aA
  · exact fun i hi => (fr i hi).arc
  · intro i hi m
    obtain ⟨b,hb,ha⟩ := mem_biUnion.mp m
    exact (fr i hi).noA b hb (mem_outN.mp (mem_sdiff.mp ha).1).2
  · intro i hi j hj ne
    have sb : s i∈SecondBank D V j := by
      rw [bank j hj]
      exact mem_erase.mpr ⟨fun e => ne (injS hi hj e),ins i hi⟩
    rcases mem_union.mp (head j hj _ sb (mem_outN.mpr ⟨av i (fr i hi).aA,(fr i hi).arc⟩)) with m|m
    · exact (outside i hi (by rw [row j hj]; exact mem_insert_of_mem m)).elim
    · exact m
  · intro i hi x xx ne y hy
    have xb : x∈SecondBank D V i := by
      rw [bank i hi]
      exact mem_erase.mpr ⟨ne,xx⟩
    rcases mem_union.mp (head i hi x xb hy) with h|h
    · exact mem_union_left _ (by change y∈X; rw [row i hi]; exact mem_insert_of_mem h)
    · exact mem_union_right _ h


theorem q4_guarded_frame_gain {D : CH.Digraph} {V : Finset ℕ} {c u s a : ℕ}
    (hf : QFree D V 4) (ho : OutEq 6 D V) (hu : u∈V)
    (short : (ball D V u 2).card=12)
    (F : GuardFrame D V c u s a) :
    8+(spillQ4 D V (SecondBank D V u)).card≤(ball D V c 2).card := by
  classical
  let B := SecondBank D V u
  let T := spillQ4 D V B
  let A := (ball D V u 1).erase u
  have av : A⊆V := (erase_subset _ _).trans ball_subset
  have bv : B⊆V := fun _ h => ball_subset (mem_sdiff.mp h).1
  have b6 : B.card=5 := by
    have st := card_sdiff_add_card_eq_card
      (ball_mono_radius (D:=D) (W:=V) (u:=u) (by decide : 1≤2))
    rw [card_B1 hf hu,ho u hu] at st
    change B.card+7=(ball D V u 2).card at st
    omega
  have bs : D c s=true := (mem_outN.mp (F.row.symm ▸ mem_insert_self s B)).2
  have sc : s≠c := by
    intro e
    subst s
    exact hf c 1 (by decide) (by decide) (.step F.cV bs (.refl c))
  let I : Finset ℕ := {c,s,a}
  have iA : I⊆A := by
    intro x hx
    simp only [I,mem_insert,mem_singleton] at hx
    rcases hx with rfl|rfl|rfl
    · exact F.cA
    · exact F.sA
    · exact F.aA
  have i3 : I.card=3 := by simp [I,Ne.symm sc,Ne.symm F.aC,Ne.symm F.aS]
  have ib : Disjoint I B := disjoint_left.mpr
    (fun _ hi hb => (mem_sdiff.mp hb).2 (mem_of_mem_erase (iA hi)))
  have it : Disjoint (I∪B) T := disjoint_left.mpr (by
    intro x hx ht
    obtain ⟨b,hb,hx'⟩ := mem_biUnion.mp ht
    have sx := (mem_sdiff.mp hx').2
    have ex := (mem_outN.mp (mem_sdiff.mp hx').1).2
    rcases mem_union.mp hx with hi|hB
    · simp only [I,mem_insert,mem_singleton] at hi
      rcases hi with rfl|rfl|rfl
      · exact F.noC b hb ex
      · exact F.noS b hb ex
      · exact F.noA b hb ex
    · exact sx hB)
  have ih : I⊆ball D V c 2 := by
    intro x hx
    simp only [I,mem_insert,mem_singleton] at hx
    rcases hx with rfl|rfl|rfl
    · exact self_mem_ball F.cV
    · exact mem_ball.mpr ⟨av F.sA,1,by decide,.step (av F.sA) bs (.refl _)⟩
    · exact mem_ball.mpr ⟨av F.aA,2,by decide,
        .step (av F.sA) bs (.step (av F.aA) F.arc (.refl _))⟩
  have full (b) (hb : b∈B) : D c b=true :=
    (mem_outN.mp (F.row.symm ▸ mem_insert_of_mem hb)).2
  have bh : B⊆ball D V c 2 := fun b hb =>
    mem_ball.mpr ⟨bv hb,1,by decide,.step (bv hb) (full b hb) (.refl b)⟩
  have th : T⊆ball D V c 2 := by
    intro x hx
    obtain ⟨b,hb,ht⟩ := mem_biUnion.mp hx
    obtain ⟨xv,bt⟩ := mem_outN.mp (mem_sdiff.mp ht).1
    exact mem_ball.mpr ⟨xv,2,by decide,.step (bv hb) (full b hb) (.step xv bt (.refl x))⟩
  have q := card_le_card (union_subset (union_subset ih bh) th)
  rw [card_union_of_disjoint it,card_union_of_disjoint ib,i3,b6] at q
  exact q

theorem q4_spill_at_least_six {D : CH.Digraph} {V B : Finset ℕ}
    (hf : QFree D V 4) (ho : OutEq 6 D V) (bv : B⊆V) (b6 : B.card=5) :
    5≤(spillQ4 D V B).card := by
  by_contra! small
  let T := spillQ4 D V B
  have sub (b) (hb : b∈B) : outN D V b⊆outN D B b∪T := by
    intro x hx
    by_cases z : x∈B
    · exact mem_union_left _ (mem_outN.mpr ⟨z,(mem_outN.mp hx).2⟩)
    · exact mem_union_right _ (mem_biUnion.mpr ⟨b,hb,mem_sdiff.mpr ⟨hx,z⟩⟩)
  have dg (b) (hb : b∈B) : 2≤(outN D B b).card := by
    have q := (card_le_card (sub b hb)).trans (card_union_le _ _)
    rw [ho b (bv hb)] at q
    change T.card<5 at small
    omega
  have lo := corB (D:=D) (q:=4) (by decide) (hf.mono_set bv) dg
    (card_pos.mp (by omega))
  omega

def LocalGuardQ4 (D : CH.Digraph) (A : Finset ℕ) (x : ℕ) : Prop :=
  ∃ y∈A, (outN D A y).card=1 ∧ ∃ k≤2, Walk D A x y k

def LocalTwoQ4 (D : CH.Digraph) (A : Finset ℕ) : Prop :=
  ∃ P⊆A, P.card=2 ∧ ∀ c∈P, (outN D A c).card=1 ∧
    ∃ s∈A, ∃ a∈A, D c s=true ∧ D s a=true ∧ LocalGuardQ4 D A s ∧ LocalGuardQ4 D A a

/-- Transport the two protected local frames on first-layer labels
to their actual second bank, preserving each source-label walk. -/
theorem q4_local_selection_to_frames {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V 4) (ho : OutEq 6 D V)
    (sel : ∀ A⊆V, A.card=6 → (∀ v∈A, 1≤(outN D A v).card) →
      LocalTwoQ4 D A) :
    ∀ u∈V, (ball D V u 2).card=12 →
      ∃ P⊆V, P.card=2 ∧ ∀ c∈P, ∃ s a, GuardFrame D V c u s a := by
  intro u hu short
  let A := (ball D V u 1).erase u
  let B := SecondBank D V u
  let U := (ball D V u 2).erase u
  have av : A⊆V := (erase_subset _ _).trans ball_subset
  have bv : B⊆V := fun _ h => ball_subset (mem_sdiff.mp h).1
  have join : A∪B=U := (erase_ball_succ_eq_union (k:=1) hu).symm
  have a7 : A.card=6 := by
    change ((ball D V u 1).erase u).card=6
    rw [erase_ball_one_eq_outN hf (by decide : 1≤4) hu,ho u hu]
  have b6 : B.card=5 := by
    have st := card_sdiff_add_card_eq_card
      (ball_mono_radius (D:=D) (W:=V) (u:=u) (by decide : 1≤2))
    rw [card_B1 hf hu,ho u hu] at st
    change B.card+7=(ball D V u 2).card at st
    omega
  have ge (v) (hv : v∈V) : 6≤(outN D V v).card := (ho v hv).ge
  have minA : ∀ v∈A,1≤(outN D A v).card :=
    minOut_prefix_erase (d:=1) hf hu (by decide : 1+1≤4) ge (by change 1+B.card≤6; omega)
  have ab : Disjoint A B := disjoint_left.mpr
    (fun _ x y => (mem_sdiff.mp y).2 (mem_of_mem_erase x))
  have full (x) (hx : x∈A) (one : (outN D A x).card=1) : ∀ b∈B, D x b=true := by
    have keep := (ge x (av hx)).trans
      (card_le_card (outN_prefix_erase_root hf hu (by decide : 1+1≤4) (mem_of_mem_erase hx)))
    change 6≤(outN D U x).card at keep
    have sp := card_outN_union (D:=D) ab x
    rw [join] at sp
    have all : outN D B x=B := eq_of_subset_of_card_le outN_subset (by omega)
    exact fun b hb => (mem_outN.mp (all.symm ▸ hb)).2
  have no (x) (hx : x∈A) (g : LocalGuardQ4 D A x) (b) (hb : b∈B) : D b x≠true := by
    intro bt
    obtain ⟨y,hy,one,k,kk,w⟩ := g
    exact hf b (k+1+1) (by omega) (by omega)
      (.step (av hx) bt ((w.mono av).snoc (bv hb) (full y hy one b hb)))
  obtain ⟨P,pA,p2,prop⟩ := sel A av a7 minA
  refine ⟨P,pA.trans av,p2,?_⟩
  intro c cp
  have ca := pA cp
  obtain ⟨one,s,sa,a,aa,cs,ar,gs,ga⟩ := prop c cp
  have sB : s∉B := fun h => (mem_sdiff.mp h).2 (mem_of_mem_erase sa)
  have row : outN D V c=insert s B := by
    apply (eq_of_subset_of_card_le
      (insert_subset (mem_outN.mpr ⟨av sa,cs⟩)
        (fun b hb => mem_outN.mpr ⟨bv hb,full c ca one b hb⟩)) ?_).symm
    rw [ho c (av ca),card_insert_of_notMem sB,b6]
  have as' : a≠s := by
    intro e
    subst a
    exact hf s 1 (by decide) (by decide) (.step (av sa) ar (.refl s))
  have ac : a≠c := by
    intro e
    subst a
    exact hf c 2 (by decide) (by decide) (.step (av sa) cs (.step (av ca) ar (.refl c)))
  exact ⟨s,a,⟨av ca,sa,aa,as',ac,row,ar⟩,ca,
    no c ca ⟨c,ca,one,0,by decide,.refl c⟩,no s sa gs,no a aa ga⟩

theorem same_bank_no_two_q4 {D : CH.Digraph} {V : Finset ℕ} {u v : ℕ}
    (hf : QFree D V 4) (ho : OutEq 6 D V) (hu : u∈V) (hv : v∈V) (ne : u≠v)
    (eq : SecondBank D V u=SecondBank D V v) :
    v∉ball D V u 2 := by
  have no1 : v∉ball D V u 1 := by
    intro m
    have uv : D u v=true := (mem_outN.mp
      ((erase_ball_one_eq_outN hf (by decide : 1≤4) hu) ▸
        (mem_erase.mpr ⟨ne.symm,m⟩ : v∈(ball D V u 1).erase u))).2
    have sub : outN D V v ⊆ outN D V u := by
      intro x hx
      obtain ⟨xv,vx⟩ := mem_outN.mp hx
      have x2 : x∈ball D V u 2 := ball_step m xv vx
      have x1 : x∈ball D V u 1 := by
        by_contra n
        have xb : x∈SecondBank D V u := mem_sdiff.mpr ⟨x2,n⟩
        rw [eq] at xb
        exact (mem_sdiff.mp xb).2 ((mem_ball_one hv).mpr (Or.inr hx))
      have xx : x≠u := by
        intro e
        subst x
        exact hf u 2 (by decide) (by decide)
          (.step hv uv (.step hu vx (.refl u)))
      rw [←erase_ball_one_eq_outN hf (by decide : 1≤4) hu]
      exact mem_erase.mpr ⟨xx,x1⟩
    have equal : outN D V v=outN D V u :=
      eq_of_subset_of_card_le sub (by rw [ho u hu,ho v hv])
    have self : v∈outN D V v := equal ▸ mem_outN.mpr ⟨hv,uv⟩
    exact hf v 1 (by decide) (by decide) (.step hv (mem_outN.mp self).2 (.refl v))
  have no2 : v∉ball D V u 2 := by
    intro vv
    have b : v∈SecondBank D V u := mem_sdiff.mpr ⟨vv,no1⟩
    rw [eq] at b
    exact (mem_sdiff.mp b).2 (self_mem_ball hv)
  exact no2
theorem order24_guarded_bank_budget {ι : Type*} [DecidableEq ι]
    {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V 4) (ho : OutEq 6 D V) (hn : V.card=24)
    (K : Finset ι) (roots escorts : ι→Finset ℕ)
    (partition : V.filter (fun v => (ball D V v 2).card=12) = K.biUnion roots)
    (dis : (↑K : Set ι).PairwiseDisjoint roots)
    (esub : ∀ B∈K, escorts B⊆V) (e2 : ∀ B∈K, (escorts B).card=2)
    (miss : ∀ g∈K, ∀ v∈roots g,
      (roots g).erase v⊆V \ (ball D V v 2 ∪ reverseBall D V v 2))
    (pay : ∀ v∈V, 12+(K.filter (fun B => v∈escorts B)).card ≤
      (ball D V v 2).card) : False := by
  classical
  let L := V.filter (fun v => (ball D V v 2).card=12)
  let N := V.filter (fun v => 12<(ball D V v 2).card)
  let E (v : ℕ) := (ball D V v 2).card-12
  have floor (v) (hv : v∈V) : 12≤(ball D V v 2).card :=
    floor_two12 (by decide) hf (fun x hx => (ho x hx).ge) hv
  have mb := incomparable_reach_identity hf (by decide : 2+2≤4)
  have summ :
      (∑ v∈V,(ball D V v 2).card)=12*V.card+∑ v∈V,E v := by
    rw [Nat.mul_comm 12,←Finset.sum_const_nat (s:=V) (fun _ _ => rfl),←sum_add_distrib]
    apply sum_congr rfl
    intro v hv
    have a := floor v hv
    change (ball D V v 2).card=12+((ball D V v 2).card-12)
    omega
  rw [summ,hn] at mb
  have es : (orderedIncomparable D V 2).card+2*(∑ v∈V,E v)=24 := by omega
  have nel : N.card≤∑ v∈V,E v := by
    have h : (∑ v∈N,(1:ℕ))≤∑ v∈N,E v := by
      apply sum_le_sum
      intro v hv
      have n := (mem_filter.mp hv).2
      change 1≤(ball D V v 2).card-12
      omega
    rw [Finset.sum_const_nat (fun _ _ => rfl),Nat.mul_one] at h
    exact h.trans (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => Nat.zero_le _))
  have CN : N=V\L := by
    ext v
    simp only [N,L,mem_filter,mem_sdiff]
    constructor
    · rintro ⟨hv,gt⟩
      exact ⟨hv,fun h => (Nat.ne_of_gt gt) h.2⟩
    · rintro ⟨hv,neq⟩
      exact ⟨hv,by have a:=floor v hv; by_contra! n; exact neq ⟨hv,by omega⟩⟩
  have split : N.card+L.card=24 := by
    rw [CN,←hn]
    exact card_sdiff_add_card_eq_card (filter_subset _ _)
  have tax : (∑ v∈V,(K.filter (fun B => v∈escorts B)).card)=2*K.card := by
    calc
      _ = ∑ v∈V, ∑ B∈K, (if v∈escorts B then (1 : ℕ) else 0) := by
        apply sum_congr rfl
        intro v hv
        rw [←sum_filter]
        simp
      _ = ∑ B∈K, ∑ v∈V, (if v∈escorts B then (1 : ℕ) else 0) := sum_comm
      _ = ∑ B∈K,(2 : ℕ) := by
        apply sum_congr rfl
        intro B hB
        simp [sum_ite_mem, inter_eq_right.mpr (esub B hB),e2 B hB]
      _ = 2*K.card := by rw [Finset.sum_const_nat (fun _ _ => rfl),Nat.mul_comm]
  have total := sum_le_sum pay
  rw [sum_add_distrib,tax,Finset.sum_const_nat (fun _ _ => rfl),summ,Nat.mul_comm V.card 12] at total
  have ll : L.card=∑ g∈K,(roots g).card := by
    rw [show L=K.biUnion roots from partition,card_biUnion dis]
  have ml :
      (∑ g∈K,(roots g).card*((roots g).card-1))≤(orderedIncomparable D V 2).card := by
    rw [incomparable_card_rows]
    calc
      _ = ∑ g∈K,∑ _v∈roots g,((roots g).card-1) := by
        simp only [Finset.sum_const_nat (fun _ _ => rfl)]
      _ ≤ ∑ g∈K,∑ v∈roots g,(V\(ball D V v 2∪reverseBall D V v 2)).card := by
        apply sum_le_sum
        intro g hg
        apply sum_le_sum
        intro v hv
        simpa only [card_erase_of_mem hv] using card_le_card (miss g hg v hv)
      _ = ∑ v∈L,(V\(ball D V v 2∪reverseBall D V v 2)).card := by
        rw [show L=K.biUnion roots from partition,sum_biUnion dis]
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => Nat.zero_le _)
  have group (g : ι) (_ : g∈K) :
      2*(roots g).card≤(roots g).card*((roots g).card-1)+2 := by
    let t := (roots g).card
    change 2*t≤t*(t-1)+2
    cases t with
    | zero => decide
    | succ a =>
      cases a with
      | zero => decide
      | succ b => simp [Nat.add_mul,Nat.mul_add,Nat.mul_comm]; omega
  have ag := sum_le_sum group
  rw [←mul_sum,←ll,sum_add_distrib,Finset.sum_const_nat (fun _ _ => rfl)] at ag
  have pos : 0<K.card := by
    by_contra! h
    have z : K=∅ := card_eq_zero.mp (by omega)
    simp [z] at ll
    omega
  omega

theorem order24_of_guarded_local_selection {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V 4) (ho : OutEq 6 D V) (hn : V.card=24)
    (localSelect : ∀ u∈V, (ball D V u 2).card=12 →
      ∃ P⊆V, P.card=2 ∧ ∀ c∈P, ∃ s a, GuardFrame D V c u s a) : False := by
  classical
  let L := V.filter (fun v => (ball D V v 2).card=12)
  let bank := SecondBank D V
  let K := L.image bank
  let roots (B : Finset ℕ) := L.filter (fun v => bank v=B)
  have partition : L=K.biUnion roots := by
    ext u
    constructor
    · intro hu
      exact mem_biUnion.mpr ⟨bank u,mem_image.mpr ⟨u,hu,rfl⟩,mem_filter.mpr ⟨hu,rfl⟩⟩
    · intro hu
      obtain ⟨_,_,h⟩ := mem_biUnion.mp hu
      exact (mem_filter.mp h).1
  have dis : (↑K : Set (Finset ℕ)).PairwiseDisjoint roots := by
    intro B _ C _ ne
    apply disjoint_left.mpr
    intro v b c
    exact ne (((mem_filter.mp b).2).symm.trans (mem_filter.mp c).2)
  have miss (B) (_ : B∈K) (v) (hv : v∈roots B) :
      (roots B).erase v ⊆ V \ (ball D V v 2 ∪ reverseBall D V v 2) := by
    intro x hx
    obtain ⟨ne,xr⟩ := mem_erase.mp hx
    have vx := (mem_filter.mp (mem_filter.mp hv).1).1
    have xx := (mem_filter.mp (mem_filter.mp xr).1).1
    have eq := ((mem_filter.mp hv).2).trans ((mem_filter.mp xr).2).symm
    refine mem_sdiff.mpr ⟨xx,?_⟩
    intro h
    rcases mem_union.mp h with h|h
    · exact same_bank_no_two_q4 hf ho vx xx ne.symm eq h
    · exact same_bank_no_two_q4 hf ho xx vx ne eq.symm (mem_filter.mp h).2
  have get (B) (hb : B∈K) : ∃ v∈L, bank v=B := mem_image.mp hb
  let r (B : Finset ℕ) : ℕ := if h : B∈K then Classical.choose (get B h) else 0
  have rr (B) (hb : B∈K) : r B∈L ∧ bank (r B)=B := by
    simpa only [r,dite_eq_left hb] using Classical.choose_spec (get B hb)
  have rinj : (↑K : Set (Finset ℕ)).InjOn r := by
    intro B hb C hc eq
    have h := (rr B hb).2
    rw [eq,(rr C hc).2] at h
    exact h.symm
  have E (B) (hb : B∈K) :
      ∃ P⊆V, P.card=2 ∧ ∀ c∈P, ∃ s a, GuardFrame D V c (r B) s a :=
    localSelect (r B) (mem_filter.mp (rr B hb).1).1 (mem_filter.mp (rr B hb).1).2
  let escorts (B : Finset ℕ) : Finset ℕ := if h : B∈K then Classical.choose (E B h) else ∅
  have Spec (B) (hb : B∈K) :
      escorts B⊆V ∧ (escorts B).card=2 ∧ ∀ c∈escorts B, ∃ s a, GuardFrame D V c (r B) s a := by
    simpa only [escorts,dite_eq_left hb] using Classical.choose_spec (E B hb)
  refine order24_guarded_bank_budget hf ho hn K roots escorts partition dis
    (fun B hb => (Spec B hb).1) (fun B hb => (Spec B hb).2.1) miss ?_
  intro c cv
  let T := K.filter (fun B => c∈escorts B)
  let J := T.image r
  have cardJ : J.card=T.card := card_image_of_injOn (rinj.mono (fun _ hm => (mem_filter.mp hm).1))
  have group (u) (hu : u∈J) : u∈L ∧ ∃ s a, GuardFrame D V c u s a := by
    obtain ⟨B,bh,rfl⟩ := mem_image.mp hu
    obtain ⟨bk,bp⟩ := mem_filter.mp bh
    exact ⟨(rr B bk).1,(Spec B bk).2.2 c bp⟩
  have sv (u) (hu : u∈J) : u∈V := (mem_filter.mp (group u hu).1).1
  have short (u) (hu : u∈J) : (ball D V u 2).card=12 := (mem_filter.mp (group u hu).1).2
  have binj : (↑J : Set ℕ).InjOn bank := by
    intro u hu v hv eq
    obtain ⟨B,bh,rfl⟩ := mem_image.mp hu
    obtain ⟨C,ch,rfl⟩ := mem_image.mp hv
    rw [(rr B (mem_filter.mp bh).1).2,(rr C (mem_filter.mp ch).1).2] at eq
    rw [eq]
  let s (u : ℕ) := if h : u∈J then Classical.choose (group u h).2 else 0
  let a (u : ℕ) := if h : u∈J then Classical.choose (Classical.choose_spec (group u h).2) else 0
  have frame (u) (hu : u∈J) : GuardFrame D V c u (s u) (a u) := by
    simpa only [s,a,dite_eq_left hu] using
      Classical.choose_spec (Classical.choose_spec (group u hu).2)
  have mark := q4_shared_marks_of_frames hf ho cv sv short binj frame
  have j7 : J.card≤6 := by
    have ci := card_image_of_injOn mark.sInj
    have sub : J.image s⊆outN D V c := by
      intro v hv
      obtain ⟨i,hi,rfl⟩ := mem_image.mp hv
      exact mark.sMem i hi
    have q := card_le_card sub
    rw [ci,ho c cv] at q
    exact q
  change 12+T.card≤(ball D V c 2).card
  rw [←cardJ]
  by_cases zero : J.card=0
  · simpa only [zero,Nat.add_zero] using
      floor_two12 (by decide : 4≤4) hf (fun v hv => (ho v hv).ge) cv
  obtain ⟨u,hu⟩ := card_pos.mp (Nat.pos_of_ne_zero zero)
  have g := q4_guarded_frame_gain hf ho (sv u hu) (short u hu) (frame u hu)
  by_cases one : J.card=1
  · have b6 : (bank u).card=5 := by
      have st := card_sdiff_add_card_eq_card
        (ball_mono_radius (D:=D) (W:=V) (u:=u) (by decide : 1≤2))
      rw [card_B1 hf (sv u hu),ho u (sv u hu)] at st
      change (bank u).card+7=(ball D V u 2).card at st
      have := short u hu
      omega
    have q := q4_spill_at_least_six hf ho (B:=bank u)
      (fun _ h => ball_subset (mem_sdiff.mp h).1) b6
    change 5≤(spillQ4 D V (SecondBank D V u)).card at q
    omega
  by_cases eq : J.card=6
  · have q := all_six hf ho cv mark eq
    omega
  · have q := thick_spill hf ho mark (by omega) (by omega) u hu
    omega


/-- A shortest cycle on six labels has at most one extra label; at most two
    cycle labels can send to that extra, so every cycle label is guarded. -/
theorem local_two_six {D : CH.Digraph} {A : Finset ℕ}
    (hf : QFree D A 4) (hc : A.card=6)
    (hm : ∀ v∈A, 1≤(outN D A v).card) : LocalTwoQ4 D A := by
  classical
  obtain ⟨p,M,hp,hfree,hMA,hM,cy⟩ :=
    exists_minimal_cycle_support (by decide : 1 ≤ 4) hf hm (card_pos.mp (by omega))
  let E := A \ M
  have hE : E.card≤1 := by
    rw [show E=A\M from rfl,card_sdiff_of_subset hMA,hc]
    omega
  let P := M.filter (fun v => (outN D A v).card=1)
  have pM : P⊆M := filter_subset _ _
  have three : M.card≤P.card+2 := by
    by_cases en : E.Nonempty
    · obtain ⟨z,hz⟩ := en
      have za := (mem_sdiff.mp hz).1
      have zm := (mem_sdiff.mp hz).2
      have sole (x) (hx : x∈E) : x=z := card_le_one.mp hE x hx z hz
      have ret : (outN D M z).Nonempty := by
        obtain ⟨x,hx,zx⟩ := Finset.card_pos.mp (hm z za) |>.imp fun x hx => mem_outN.mp hx
        by_cases xm : x∈M
        · exact ⟨x,mem_outN.mpr ⟨xm,zx⟩⟩
        · have e := sole x (mem_sdiff.mpr ⟨hx,xm⟩)
          subst x
          exact (hf z 1 (by decide) (by decide) (.step za zx (.refl z))).elim
      have cap : (inN D M z).card≤2 := by
        by_cases ine : (inN D M z).Nonempty
        · have k := BRsub.cycle_two_sided_contact_cap (by omega : 2≤p) hfree hMA hM cy za ine ret
          have := card_pos.mpr ret
          omega
        · have e : (inN D M z).card=0 := card_eq_zero.mpr (not_nonempty_iff_eq_empty.mp ine)
          omega
      have sub : M \ inN D M z ⊆ P := by
        intro v hv
        obtain ⟨vm,n⟩ := mem_sdiff.mp hv
        have eq : outN D A v=outN D M v := by
          ext x
          simp only [mem_outN]
          constructor
          · rintro ⟨xa,vx⟩
            by_cases xm : x∈M
            · exact ⟨xm,vx⟩
            · have e := sole x (mem_sdiff.mpr ⟨xa,xm⟩)
              subst x
              exact (n (mem_inN.mpr ⟨vm,vx⟩)).elim
          · exact fun ⟨xm,vx⟩ => ⟨hMA xm,vx⟩
        exact mem_filter.mpr ⟨vm,by rw [eq,cy v vm]⟩
      have l := card_le_card sub
      rw [card_sdiff_of_subset (fun _ h => (mem_inN.mp h).1)] at l
      omega
    · have sub : M⊆P := by
        intro v vm
        have eq : outN D A v=outN D M v := by
          ext x
          simp only [mem_outN]
          exact ⟨fun ⟨xa,vx⟩ => ⟨by by_contra x; exact en ⟨_,mem_sdiff.mpr ⟨xa,x⟩⟩,vx⟩,
                 fun ⟨xm,vx⟩ => ⟨hMA xm,vx⟩⟩
        exact mem_filter.mpr ⟨vm,by rw [eq,cy v vm]⟩
      have l := card_le_card sub
      omega
  have next (x) (xm : x∈M) : ∃ y∈M, D x y=true := by
    have nz : 0<(outN D M x).card := by rw [cy x xm]; decide
    obtain ⟨y,hy⟩ := card_pos.mp nz
    exact ⟨y,(mem_outN.mp hy).1,(mem_outN.mp hy).2⟩
  have all (x) (xm : x∈M) : LocalGuardQ4 D A x := by
    obtain ⟨y,ym,xy⟩ := next x xm
    obtain ⟨z,zm,yz⟩ := next y ym
    have ne1 : x≠y := fun e => by subst y; exact hf x 1 (by decide) (by decide) (.step (hMA xm) xy (.refl x))
    have ne2 : y≠z := fun e => by subst z; exact hf y 1 (by decide) (by decide) (.step (hMA ym) yz (.refl y))
    have ne3 : x≠z := fun e => by subst z; exact hf x 2 (by decide) (by decide) (.step (hMA ym) xy (.step (hMA xm) yz (.refl x)))
    by_cases xp : x∈P
    · exact ⟨x,hMA xm,(mem_filter.mp xp).2,0,by decide,.refl x⟩
    by_cases yp : y∈P
    · exact ⟨y,hMA ym,(mem_filter.mp yp).2,1,by decide,.step (hMA ym) xy (.refl y)⟩
    by_cases zp : z∈P
    · exact ⟨z,hMA zm,(mem_filter.mp zp).2,2,by decide,.step (hMA ym) xy (.step (hMA zm) yz (.refl z))⟩
    have d : Disjoint P ({x,y,z} : Finset ℕ) := disjoint_left.mpr (by
      intro v vp vv
      simp only [mem_insert,mem_singleton] at vv
      rcases vv with rfl|rfl|rfl
      · exact xp vp
      · exact yp vp
      · exact zp vp)
    have le := card_le_card (union_subset pM (insert_subset xm (insert_subset ym (singleton_subset_iff.mpr zm))))
    rw [card_union_of_disjoint d,show ({x,y,z} : Finset ℕ).card=3 by simp [ne1,ne2,ne3]] at le
    have := card_le_card hMA
    omega
  obtain ⟨c,cp,d,dp,cd⟩ := one_lt_card.mp (show 1<P.card by omega)
  refine ⟨{c,d},(insert_subset (hMA (pM cp)) (singleton_subset_iff.mpr (hMA (pM dp)))),by simp [cd],?_⟩
  intro v hv
  have vp : v∈P := by
    rcases (show v=c ∨ v=d by simpa using hv) with rfl|rfl <;> assumption
  obtain ⟨s,sm,vs⟩ := next v (pM vp)
  obtain ⟨a,am,sa⟩ := next s sm
  exact ⟨(mem_filter.mp vp).2,s,hMA sm,a,hMA am,vs,sa,all s sm,all a am⟩

theorem endpoint_four_six : DotDegreeSeven.Endpoint 4 6 := by
  intro D V hf hne hn hd
  obtain ⟨G,sub,ho⟩ := exists_outEq hd
  have free := qfree_sub sub hf
  apply order24_of_guarded_local_selection free ho (by simpa using hn)
  apply q4_local_selection_to_frames free ho
  exact fun A av ac hm => local_two_six (free.mono_set av) ac hm

#print axioms endpoint_four_six

end LeanCH.BR.DotDegreeSix



