import checkpoints.shen_extension.dot_tensor_research.DotDegreeSevenLowCutoffs_20261121

namespace LeanCH.BR.DotDegreeSevenLow
open Finset BRq2 BRq3 BR45 BRsGen

private theorem cycle_take_start {D : CH.Digraph} {U : Finset ℕ}
    (hf : QFree D U 5) (hm : ∀ v∈U,1≤(outN D U v).card)
    (hlo : 6≤U.card) (hhi : U.card≤7) :
    ∃ M, M⊆U ∧ 6≤M.card ∧ OutEq 1 D M := by
  obtain ⟨_,M,hp,_,sub,hc,hd⟩ := exists_minimal_cycle_support
    (by decide : 1≤5) hf hm (card_pos.mp (by omega))
  exact ⟨M,sub,by omega,hd⟩

private theorem next_two {D : CH.Digraph} {V M : Finset ℕ} {c : ℕ}
    (hf : QFree D V 5) (sub : M⊆V) (ho : OutEq 1 D M) (hc : c∈M) :
    ∃ b∈M, ∃ a∈M, b≠c ∧ a≠c ∧ a≠b ∧ D c b=true ∧ D b a=true := by
  obtain ⟨b,mb⟩ := card_pos.mp (by rw [ho c hc]; decide : 0<(outN D M c).card)
  obtain ⟨a,ma⟩ := card_pos.mp (by rw [ho b (outN_subset mb)]; decide : 0<(outN D M b).card)
  obtain ⟨bM,e1⟩ := mem_outN.mp mb
  obtain ⟨aM,e2⟩ := mem_outN.mp ma
  refine ⟨b,bM,a,aM,?_,?_,?_,e1,e2⟩
  · intro h; subst b
    exact hf c 1 (by decide) (by decide) (.step (sub hc) e1 (.refl c))
  · intro h; subst a
    exact hf c 2 (by decide) (by decide) (.step (sub bM) e1 (.step (sub hc) e2 (.refl c)))
  · intro h; subst a
    exact hf b 1 (by decide) (by decide) (.step (sub bM) e2 (.refl b))

theorem five_free_ge34 {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V 5) (hm : ∀ v∈V,7≤(outN D V v).card) (hne : V.Nonempty) : 34≤V.card := by
  classical
  by_contra! small
  obtain ⟨G,sub,ho⟩ := exists_outEq hm
  have free := qfree_sub sub hf
  have deg (v) (hv : v∈V) : 7≤(outN G V v).card := (ho v hv).ge
  have lo := five_free_ge33 free deg hne
  have hcut := two_balls_boundary_cards (i:=2) (j:=3) free (by decide)
    (fun _ hv => floor_two14 (by decide : 4≤5) free deg hv)
    (fun _ hv => floor_three20 free deg hv) (by omega)
  obtain ⟨u,hu⟩ := hne
  let A := (ball G V u 1).erase u
  let B := ball G V u 2 \ ball G V u 1
  let T := ball G V u 3 \ ball G V u 2
  let U := (ball G V u 2).erase u
  have ca : A.card=7 := by
    change ((ball G V u 1).erase u).card=7
    rw [erase_ball_one_eq_outN free (by decide : 1≤5) hu,ho u hu]
  have cb : B.card=6 := by
    have s := card_sdiff_add_card_eq_card
      (ball_mono_radius (D:=G) (W:=V) (u:=u) (by decide : 1≤2))
    rw [card_B1 (free.mono_bound (by decide : 4≤5)) hu,ho u hu] at s
    have e := (hcut u hu).1
    change (ball G V u 2).card=14 at e
    change B.card+(7+1)=(ball G V u 2).card at s
    omega
  have ct : T.card=6 := by
    have s := card_sdiff_add_card_eq_card
      (ball_mono_radius (D:=G) (W:=V) (u:=u) (by decide : 2≤3))
    have e := hcut u hu
    have e2 := e.2.1
    change T.card+(ball G V u 2).card=(ball G V u 3).card at s
    omega
  have av : A⊆V := (erase_subset _ _).trans ball_subset
  have bv : B⊆V := fun _ h => ball_subset (mem_sdiff.mp h).1
  have tv : T⊆V := fun _ h => ball_subset (mem_sdiff.mp h).1
  have au : A⊆U := erase_subset_erase u (ball_mono_radius (by decide : 1≤2))
  have bu : B⊆U := by
    intro x hx
    refine mem_erase.mpr ⟨?_,(mem_sdiff.mp hx).1⟩
    intro e
    subst x
    exact (mem_sdiff.mp hx).2 (self_mem_ball hu)
  have join : A∪B=U := by
    ext x
    constructor
    · intro h
      rcases mem_union.mp h with ha|hb
      · exact au ha
      · exact bu hb
    · intro h
      by_cases q : x∈ball G V u 1
      · exact mem_union_left _ (mem_erase.mpr ⟨(mem_erase.mp h).1,q⟩)
      · exact mem_union_right _ (mem_sdiff.mpr ⟨(mem_erase.mp h).2,q⟩)
  have dis : Disjoint A B := disjoint_left.mpr
    (fun x hx hy => (mem_sdiff.mp hy).2 (mem_of_mem_erase hx))
  have minA : ∀ v∈A,1≤(outN G A v).card :=
    minOut_prefix_erase (d:=1) free hu (by decide : 1+1≤5) deg (by change 1+B.card≤7; omega)
  have full (x) (hx : x∈A) (one : (outN G A x).card=1) : ∀ b∈B, G x b=true := by
    have keep := (deg x (av hx)).trans
      (card_le_card (outN_prefix_erase_root free hu (by decide : 1+1≤5) (mem_of_mem_erase hx)))
    change 7≤(outN G U x).card at keep
    have sp := card_outN_union (D:=G) dis x
    rw [join] at sp
    have all : outN G B x=B := eq_of_subset_of_card_le outN_subset (by change B.card≤(outN G B x).card; omega)
    exact fun b hb => (mem_outN.mp (all.symm ▸ hb)).2
  obtain ⟨M,ma,mc,mo⟩ := cycle_take_start (free.mono_set av) minA (by omega) (by omega)
  have reach :
      (∃ c∈M, ∀ b∈B,G c b=true) ∧
      (∀ a∈A, ∃ p∈A, ∃ i≤2, Walk G V a p i ∧ ∀ b∈B,G p b=true) := by
    by_cases hMA : M=A
    · subst M
      obtain ⟨c,hc⟩ := card_pos.mp (show 0<A.card by omega)
      exact ⟨⟨c,hc,full c hc (mo c hc)⟩,fun a ha => ⟨a,ha,0,by decide,.refl a,full a ha (mo a ha)⟩⟩
    · have sm := card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨ma,hMA⟩)
      have sd := card_sdiff_add_card_eq_card ma
      obtain ⟨z,hz⟩ := card_pos.mp (show 0<(A\M).card by omega)
      have za := (mem_sdiff.mp hz).1
      have zn := (mem_sdiff.mp hz).2
      have cover : A=insert z M := by
        apply (eq_of_subset_of_card_le (insert_subset za ma) ?_).symm
        rw [card_insert_of_notMem zn]
        omega
      obtain ⟨p,pm⟩ := card_pos.mp (minA z za)
      obtain ⟨pa,zp⟩ := mem_outN.mp pm
      have pp : p∈M := by
        rw [cover] at pa
        rcases mem_insert.mp pa with h|h
        · subst p
          exact (free z 1 (by decide) (by decide) (.step (av za) zp (.refl z))).elim
        · exact h
      have nz : G p z≠true := fun arc =>
        free z 2 (by decide) (by decide) (.step (av (ma pp)) zp (.step (av za) arc (.refl z)))
      have one_of (v) (hv : v∈M) (n : G v z≠true) : (outN G A v).card=1 := by
        have e : outN G A v=outN G M v := by
          ext x
          rw [mem_outN,mem_outN,cover,mem_insert]
          grind
        rw [e,mo v hv]
      have fp := full p (ma pp) (one_of p pp nz)
      refine ⟨⟨p,pp,fp⟩,?_⟩
      intro a ha
      by_cases az : a=z
      · subst a
        exact ⟨p,ma pp,1,by decide,.step (av (ma pp)) zp (.refl p),fp⟩
      have am : a∈M := by rw [cover] at ha; exact (mem_insert.mp ha).resolve_left az
      by_cases e : G a z=true
      · exact ⟨p,ma pp,2,by decide,.step (av za) e (.step (av (ma pp)) zp (.refl p)),fp⟩
      · exact ⟨a,ha,0,by decide,.refl a,full a ha (one_of a am e)⟩
  have noBA (b) (hb : b∈B) (a) (ha : a∈A) : G b a≠true := by
    intro ba
    obtain ⟨p,_,i,ib,walk,pb⟩ := reach.2 a ha
    exact free b (i+1+1) (by omega) (by omega)
      ((Walk.step (av ha) ba (walk.snoc (bv hb) (pb b hb))))
  have stay (b) (hb : b∈B) : outN G V b ⊆ outN G B b ∪ outN G T b := by
    intro x hx
    have base := outN_prefix_loss free hu (by decide : 2+1≤5) (bu hb) hx
    rcases mem_union.mp base with h|h
    · obtain ⟨xU,arc⟩ := mem_outN.mp h
      change x∈U at xU
      rw [←join] at xU
      rcases mem_union.mp xU with ha|hb'
      · exact (noBA b hb x ha arc).elim
      · exact mem_union_left _ (mem_outN.mpr ⟨hb',arc⟩)
    · exact mem_union_right _ (mem_outN.mpr ⟨h,(mem_outN.mp hx).2⟩)
  have bMin (b) (hb : b∈B) : 1≤(outN G B b).card := by
    have h := (deg b (bv hb)).trans ((card_le_card (stay b hb)).trans (card_union_le _ _))
    have c := card_le_card (outN_subset (D:=G) (W:=T) (y:=b))
    omega
  obtain ⟨MB,subB,lb,eqB⟩ := cycle_take_start (free.mono_set bv) bMin (by omega) (by omega)
  have eq : MB=B := eq_of_subset_of_card_le subB (by omega)
  have bfull (b) (hb : b∈B) (t) (ht : t∈T) : G b t=true := by
    have c := (deg b (bv hb)).trans ((card_le_card (stay b hb)).trans (card_union_le _ _))
    have one : (outN G B b).card=1 := by rw [←eq]; exact eqB b (eq.symm ▸ hb)
    have all : outN G T b=T := eq_of_subset_of_card_le outN_subset (by omega)
    exact (mem_outN.mp (all.symm ▸ ht)).2
  obtain ⟨c,hc,cf⟩ := reach.1
  obtain ⟨x,hx,y,hy,nxc,nyc,nyx,e1,e2⟩ := next_two free (ma.trans av) mo hc
  let J : Finset ℕ := {c,x,y}
  have j3 : J.card=3 := by
    simp [J,Ne.symm nxc,Ne.symm nyc,Ne.symm nyx]
  have jA : J⊆A := by
    intro t ht
    simp only [J,mem_insert,mem_singleton] at ht
    rcases ht with rfl|rfl|rfl
    · exact ma hc
    · exact ma hx
    · exact ma hy
  have jb : J⊆ball G V c 2 := by
    intro t ht
    simp only [J,mem_insert,mem_singleton] at ht
    rcases ht with rfl|rfl|rfl
    · exact self_mem_ball (av (ma hc))
    · exact mem_ball.mpr ⟨av (ma hx),1,by decide,.step (av (ma hx)) e1 (.refl _)⟩
    · exact mem_ball.mpr ⟨av (ma hy),2,by decide,.step (av (ma hx)) e1 (.step (av (ma hy)) e2 (.refl _))⟩
  have bb : B⊆ball G V c 2 := fun b hb =>
    mem_ball.mpr ⟨bv hb,1,by decide,.step (bv hb) (cf b hb) (.refl b)⟩
  obtain ⟨b,hb⟩ := card_pos.mp (show 0<B.card by omega)
  have tb : T⊆ball G V c 2 := fun t ht =>
    mem_ball.mpr ⟨tv ht,2,by decide,.step (bv hb) (cf b hb) (.step (tv ht) (bfull b hb t ht) (.refl t))⟩
  have dt : Disjoint (J∪B) T := by
    apply disjoint_left.mpr
    intro t hj ht
    have u' : t∈U := by
      rw [←join]
      rcases mem_union.mp hj with h|h
      · exact mem_union_left _ (jA h)
      · exact mem_union_right _ h
    exact (mem_sdiff.mp ht).2 (mem_of_mem_erase u')
  have len := card_le_card ((union_subset (union_subset jb bb) tb))
  rw [card_union_of_disjoint dt,card_union_of_disjoint (dis.mono_left jA),j3,cb,ct] at len
  have e := (hcut c (av (ma hc))).1
  omega

#print axioms five_free_ge34
end LeanCH.BR.DotDegreeSevenLow
