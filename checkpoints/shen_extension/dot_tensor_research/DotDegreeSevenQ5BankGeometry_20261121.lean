import checkpoints.shen_extension.dot_tensor_research.DotDegreeSevenQ5Prefix_20261121

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

/-- The first layer of a small radius-two ball supplies its actual six-column bank.
The cycle, its full rows, and the path to a full row are retained on native labels. -/
theorem six_bank_first_layer {D : CH.Digraph} {V : Finset ℕ} {u : ℕ}
    (free : QFree D V 5) (ho : OutEq 7 D V) (hu : u∈V)
    (e2 : (ball D V u 2).card=14) :
    let A := (ball D V u 1).erase u
    let B := ball D V u 2 \ ball D V u 1
    A.card=7 ∧ B.card=6 ∧
    ∃ M P : Finset ℕ, M⊆A ∧ 6≤M.card ∧ OutEq 1 D M ∧ P⊆M ∧ P.card=4 ∧
      (∀ c∈P, ∀ b∈B, D c b=true) ∧
      (∀ a∈A, ∃ p∈A, ∃ i≤2, Walk D V a p i ∧ ∀ b∈B, D p b=true) := by
  classical
  have deg (v) (hv : v∈V) : 7≤(outN D V v).card := (ho v hv).ge
  let A := (ball D V u 1).erase u
  let B := ball D V u 2 \ ball D V u 1
  let U := (ball D V u 2).erase u
  have ca : A.card=7 := by
    change ((ball D V u 1).erase u).card=7
    rw [erase_ball_one_eq_outN free (by decide : 1≤5) hu,ho u hu]
  have cb : B.card=6 := by
    have s := card_sdiff_add_card_eq_card
      (ball_mono_radius (D:=D) (W:=V) (u:=u) (by decide : 1≤2))
    rw [card_B1 (free.mono_bound (by decide : 4≤5)) hu,ho u hu] at s
    change B.card+(7+1)=(ball D V u 2).card at s
    omega
  have av : A⊆V := (erase_subset _ _).trans ball_subset
  have bv : B⊆V := fun _ h => ball_subset (mem_sdiff.mp h).1
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
      by_cases q : x∈ball D V u 1
      · exact mem_union_left _ (mem_erase.mpr ⟨(mem_erase.mp h).1,q⟩)
      · exact mem_union_right _ (mem_sdiff.mpr ⟨(mem_erase.mp h).2,q⟩)
  have dis : Disjoint A B := disjoint_left.mpr
    (fun x hx hy => (mem_sdiff.mp hy).2 (mem_of_mem_erase hx))
  have minA : ∀ v∈A,1≤(outN D A v).card :=
    minOut_prefix_erase (d:=1) free hu (by decide : 1+1≤5) deg (by change 1+B.card≤7; omega)
  have full (x) (hx : x∈A) (one : (outN D A x).card=1) : ∀ b∈B, D x b=true := by
    have keep := (deg x (av hx)).trans
      (card_le_card (outN_prefix_erase_root free hu (by decide : 1+1≤5) (mem_of_mem_erase hx)))
    change 7≤(outN D U x).card at keep
    have sp := card_outN_union (D:=D) dis x
    rw [join] at sp
    have all : outN D B x=B := eq_of_subset_of_card_le outN_subset (by change B.card≤(outN D B x).card; omega)
    exact fun b hb => (mem_outN.mp (all.symm ▸ hb)).2
  obtain ⟨M,ma,mc,mo⟩ := cycle_take_start (free.mono_set av) minA (by omega) (by omega)
  have reach :
      (∃ c∈M, ∀ b∈B,D c b=true) ∧
      (∀ a∈A, ∃ p∈A, ∃ i≤2, Walk D V a p i ∧ ∀ b∈B,D p b=true) := by
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
      have nz : D p z≠true := fun arc =>
        free z 2 (by decide) (by decide) (.step (av (ma pp)) zp (.step (av za) arc (.refl z)))
      have one_of (v) (hv : v∈M) (n : D v z≠true) : (outN D A v).card=1 := by
        have e : outN D A v=outN D M v := by
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
      by_cases e : D a z=true
      · exact ⟨p,ma pp,2,by decide,.step (av za) e (.step (av (ma pp)) zp (.refl p)),fp⟩
      · exact ⟨a,ha,0,by decide,.refl a,full a ha (one_of a am e)⟩
  refine ⟨ca,cb,?_⟩
  · let F := M.filter (fun c => ∀ b∈B, D c b=true)
    have fi : F ⊆ M := filter_subset _ _
    have cap : 4≤F.card := by
      by_cases hMA : M=A
      · have s : M⊆F := fun c hc => mem_filter.mpr
            ⟨hc,full c (ma hc) (by simpa only [← hMA] using mo c hc)⟩
        exact (by omega : 4≤M.card).trans (card_le_card s)
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
        have ⟨pa,zp⟩ := mem_outN.mp pm
        have pp : p∈M := by
          rw [cover] at pa
          rcases mem_insert.mp pa with h|h
          · subst p
            exact (free z 1 (by decide) (by decide) (.step (av za) zp (.refl z))).elim
          · exact h
        obtain ⟨b,bm,c,cm,bp,cp,cb',pb,bc⟩ := next_two free (ma.trans av) mo pp
        obtain ⟨w,wmout⟩ := card_pos.mp (by rw [mo c cm]; decide : 0<(outN D M c).card)
        obtain ⟨wm,cw⟩ := mem_outN.mp wmout
        have wp : w≠p := by
          intro z; subst w
          exact free p 3 (by decide) (by decide)
            (.step (av (ma bm)) pb (.step (av (ma cm)) bc (.step (av (ma pp)) cw (.refl p))))
        have wb : w≠b := by
          intro z; subst w
          exact free b 2 (by decide) (by decide)
            (.step (av (ma cm)) bc (.step (av (ma bm)) cw (.refl b)))
        have wc : w≠c := by
          intro z; subst w
          exact free c 1 (by decide) (by decide) (.step (av (ma cm)) cw (.refl c))
        let S : Finset ℕ := {p,b,c,w}
        have cs : S.card=4 := by
          simp [S,bp,cp,cb',wp,wb,wc,Ne.symm bp,Ne.symm cp,Ne.symm cb',Ne.symm wp,Ne.symm wb,Ne.symm wc]
        have sc (v) (hv : v∈S) : ∃ i≤4, Walk D V z v i ∧ v∈M := by
          have zpw : Walk D V z p 1 := .step (av (ma pp)) zp (.refl p)
          have zbw := zpw.snoc (av (ma bm)) pb
          have zcw := zbw.snoc (av (ma cm)) bc
          have zww := zcw.snoc (av (ma wm)) cw
          simp only [S,mem_insert,mem_singleton] at hv
          rcases hv with rfl|rfl|rfl|rfl
          · exact ⟨1,by decide,zpw,pp⟩
          · exact ⟨2,by decide,zbw,bm⟩
          · exact ⟨3,by decide,zcw,cm⟩
          · exact ⟨4,by decide,zww,wm⟩
        have sf : S⊆F := by
          intro v hv
          obtain ⟨i,ib,zw,vm⟩ := sc v hv
          have no : D v z≠true := fun r =>
            free z (i+1) (by omega) (by omega) (zw.snoc (av za) r)
          have sam : outN D A v=outN D M v := by
            ext x
            rw [mem_outN,mem_outN,cover,mem_insert]
            grind
          exact mem_filter.mpr ⟨vm,full v (ma vm) (by rw [sam,mo v vm])⟩
        have h := card_le_card sf
        omega
    obtain ⟨P,pF,p4⟩ := exists_subset_card_eq cap
    exact ⟨M,P,ma,mc,mo,pF.trans fi,p4,fun c hc => (mem_filter.mp (pF hc)).2,reach.2⟩

#print axioms six_bank_first_layer
end LeanCH.BR.DotDegreeSevenLow


