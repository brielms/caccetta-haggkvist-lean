
import checkpoints.shen_extension.dot_tensor_research.DotDegreeSixQ5Budget_20261121
import checkpoints.shen_extension.dot_tensor_research.DotDegreeSixCapstone_20261121

namespace LeanCH.BR.DotDegreeSix
open Finset BRq2 BRq3 BR45 BRsGen
set_option maxHeartbeats 1000000

private theorem second_parent {D : CH.Digraph} {V : Finset ℕ} {u : ℕ}
    (hu : u∈V) (P : SixPrefix D V u) {b : ℕ} (hb : b∈P.B) :
    ∃ a∈P.A, D a b=true := by
  have bb := hb
  rw [P.b_eq] at bb
  obtain ⟨_,k,k2,w⟩ := mem_ball.mp (mem_sdiff.mp bb).1
  have ek : k=2 := by
    by_contra n
    exact (mem_sdiff.mp bb).2 (mem_ball.mpr ⟨P.bV hb,k,by omega,w⟩)
  subst k
  obtain ⟨a,p,_,e⟩ := w.unsnoc
  have aV : a∈V := (p.end_mem_or).elim (fun h => h.symm ▸ hu) id
  refine ⟨a,?_,e⟩
  rw [P.a_eq]
  exact mem_erase.mpr ⟨fun e' => (mem_sdiff.mp bb).2 (ball_of_adj (P.bV hb) (e' ▸ e)),
    mem_ball.mpr ⟨aV,1,by decide,p⟩⟩

private theorem one_head_to_second {D : CH.Digraph} {V : Finset ℕ} {u : ℕ}
    (ho : OutEq 6 D V) (P : SixPrefix D V u) (ct : P.T.card=5)
    {b : ℕ} (bb : b∈P.B) (nr : (outN D P.A b).card=0)
    (one : (outN D P.B b).card≤1) : ∀ t∈P.T, D b t=true := by
  have ke : outN D V b⊆outN D ((P.A∪P.B)∪P.T) b := fun x hx =>
    mem_outN.mpr ⟨P.second b bb hx,(mem_outN.mp hx).2⟩
  have q := card_le_card ke
  rw [ho b (P.bV bb),card_outN_union (D:=D) P.at',card_outN_union (D:=D) P.ab,nr] at q
  have eq : outN D P.T b=P.T := eq_of_subset_of_card_le outN_subset (by omega)
  exact fun t tt => (mem_outN.mp (eq.symm ▸ tt)).2

theorem six_uniform_false {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V 5) (ho : OutEq 6 D V) (hne : V.Nonempty)
    (uniform : ∀ a∈V, (ball D V a 2).card=13 ∧ (ball D V a 3).card=18) : False := by
  classical
  obtain ⟨u,hu⟩ := hne
  let P := sixPrefix hf ho hu
  let A := P.A
  let B := P.B
  let T := P.T
  obtain ⟨uv2,uv3⟩ := uniform u hu
  have b6 : B.card=6 := by change P.B.card=6; have h := P.two; omega
  have t5 : T.card=5 := by change P.T.card=5; have h := P.three; have bc : P.B.card=6 := b6; omega
  have af : QFree D A 5 := hf.mono_set P.aV
  have bf : QFree D B 5 := hf.mono_set P.bV
  have uf : QFree D (A∪B) 5 := hf.mono_set (union_subset P.aV P.bV)
  have keep := prefix_keepA ho P
  have mid : ∀ b∈B, 1≤(outN D (A∪B) b).card := by
    have m := minOut_prefix_erase (d:=1) hf hu (by decide : 2+1≤5)
      (fun v hv => (ho v hv).ge) (by simp only [Nat.reduceAdd]; rw [←P.t_eq]; have tc : P.T.card=5 := t5; omega)
    have eq : (ball D V u 2).erase u=A∪B := by
      change (ball D V u 2).erase u=P.A∪P.B
      rw [P.a_eq,P.b_eq]
      exact erase_ball_succ_eq_union (k:=1) hu
    rw [eq] at m
    exact fun b hb => m b (mem_union_right _ hb)
  have midY (b) (hb : b∈B) (n : outN D A b=∅) :
      1≤(outN D B b).card := by
    have k := card_outN_union (D:=D) P.ab b
    change (outN D (A∪B) b).card=(outN D A b).card+(outN D B b).card at k
    rw [n,card_empty,zero_add] at k
    exact k ▸ mid b hb
  rcases six_acyclic_or_cycle af P.ca with ac | cy
  · have noback (b) (bb : b∈B) (a) (aa : a∈A) : D b a≠true := by
      intro ba
      have f := acyclic_back_arc_others (s:=6) (by decide) uf ac P.ab P.ca b6 keep aa bb ba
      have h5 : (B.erase b).card=5 := by rw [card_erase_of_mem bb,b6]
      obtain ⟨c,hc,cs⟩ := exists_sink (T:=B.erase b) (bf.mono_set (erase_subset _ _))
        (card_pos.mp (by omega)) (by omega)
      have no : outN D A c=∅ := eq_empty_iff_forall_notMem.mpr (fun a h =>
        f.2.1 c hc a (mem_outN.mp h).1 (mem_outN.mp h).2)
      obtain ⟨z,hz⟩ := card_pos.mp (midY c (mem_of_mem_erase hc) no)
      have nb : z≠b := fun e => f.2.2 c hc (e ▸ (mem_outN.mp hz).2)
      exact cs z (mem_erase.mpr ⟨nb,(mem_outN.mp hz).1⟩) (mem_outN.mp hz).2
    obtain ⟨a,aa,astop⟩ := exists_sink ac (card_pos.mp (by rw [P.ca]; decide)) (by rw [P.ca])
    have sub : outN D V a⊆B := fun x hx =>
      (mem_union.mp (P.first a aa hx)).resolve_left (fun xa => astop x xa (mem_outN.mp hx).2)
    have sub2 : ball D V a 2⊆insert a (B∪T) := by
      intro x hx
      obtain ⟨_,k,kl,w⟩ := mem_ball.mp hx
      cases w with
      | refl => exact mem_insert_self ..
      | @step a y x j yV ay wy =>
        have yb := sub (mem_outN.mpr ⟨yV,ay⟩)
        cases wy with
        | refl => exact mem_insert_of_mem (mem_union_left _ yb)
        | @step y z x l zV yz wz =>
          have zz : z=x := by
            have e : l=0 := by omega
            subst l
            cases wz
            rfl
          subst z
          rcases mem_union.mp (P.second y yb (mem_outN.mpr ⟨zV,yz⟩)) with l | r
          · rcases mem_union.mp l with xa|xb
            · exact (noback y yb x xa yz).elim
            · exact mem_insert_of_mem (mem_union_left _ xb)
          · exact mem_insert_of_mem (mem_union_right _ r)
    have k := (card_le_card sub2).trans ((card_insert_le _ _).trans (Nat.add_le_add_right (card_union_le _ _) 1))
    have z := (uniform a (P.aV aa)).1
    omega
  · have cyFive (a) (aa : a∈A) : (outN D B a).card=5 := by
      have roweq : outN D V a=outN D (A∪B) a := by
        ext v
        simp only [mem_outN]
        exact ⟨fun ⟨vV,edge⟩ => ⟨P.first a aa (mem_outN.mpr ⟨vV,edge⟩),edge⟩,
          fun ⟨vB,edge⟩ => ⟨union_subset P.aV P.bV vB,edge⟩⟩
      have k := card_outN_union (D:=D) P.ab a
      rw [←roweq,ho a (P.aV aa),cy a aa] at k
      change 6=1+(outN D B a).card at k
      omega
    have contradiction (a) (aa : a∈A) (allB : B⊆ball D V a 2) (allT : T⊆ball D V a 2) : False := by
      let I := ball D A a 2
      have ia : I⊆A := ball_subset
      have lift : I⊆ball D V a 2 := by
        intro x h
        obtain ⟨xa,k,k2,w⟩ := mem_ball.mp h
        exact mem_ball.mpr ⟨P.aV xa,k,k2,w.mono P.aV⟩
      have lo : 3≤I.card := ball_one_growth af (fun v hv => (cy v hv).ge) aa 2 (by decide)
      have k := card_le_card (union_subset (union_subset lift allB) allT)
      rw [card_union_of_disjoint (P.at'.mono_left (union_subset_union ia (Subset.refl _))),
        card_union_of_disjoint (P.ab.mono_left ia),b6,t5] at k
      have z := (uniform a (P.aV aa)).1
      omega
    by_cases back : ∃ r∈B, (outN D A r).Nonempty
    · obtain ⟨r,rb,re⟩ := back
      have no (y) (hy : y∈B.erase r) : outN D A y=∅ := by
        by_contra! h
        exact (mem_erase.mp hy).1
          (cyclic_return_unique uf P.ca b6 P.ab cy keep (mem_of_mem_erase hy) rb h re)
      have b5 : (B.erase r).card=5 := by rw [card_erase_of_mem rb,b6]
      obtain ⟨y,hy,stop⟩ := exists_sink (T:=B.erase r) (bf.mono_set (erase_subset _ _))
        (card_pos.mp (by omega)) (by omega)
      have one : (outN D B y).card≤1 := by
        have sub : outN D B y⊆{r} := by
          intro z hz
          obtain ⟨zb,yz⟩ := mem_outN.mp hz
          by_cases n : z=r
          · simp [n]
          · exact (stop z (mem_erase.mpr ⟨n,zb⟩) yz).elim
        simpa using card_le_card sub
      have ty := one_head_to_second ho P t5 (mem_of_mem_erase hy)
        (by rw [no y hy,card_empty]) one
      let M := A.filter (fun a => D a r≠true)
      have mA : M⊆A := filter_subset _ _
      obtain ⟨a₀,a₀A,a₀r⟩ := second_parent hu P rb
      have a₀n : a₀∉M := fun h => (mem_filter.mp h).2 a₀r
      have m5 : M.card≤5 := by
        have sub : M⊆A.erase a₀ := fun a h => mem_erase.mpr ⟨fun e => a₀n (e ▸ h),mA h⟩
        have q := card_le_card sub
        rw [card_erase_of_mem a₀A,P.ca] at q
        exact q
      have mne : M.Nonempty := by
        by_contra hn
        have eq : M=∅ := not_nonempty_iff_eq_empty.mp hn
        have edge (a) (aa : a∈A) : D a r=true := by
          by_contra he
          have h : a∈M := mem_filter.mpr ⟨aa,he⟩
          rw [eq] at h
          exact notMem_empty _ h
        obtain ⟨i,hi,j,hj,n⟩ := one_lt_card.mp (show 1<A.card by rw [P.ca]; decide)
        have k := BRsub.cycle_two_sided_contact_cap (by decide : 2≤5) uf subset_union_left
          P.ca cy (mem_union_right _ rb) (by exact ⟨i,mem_inN.mpr ⟨hi,edge i hi⟩⟩) re
        have cap : A⊆inN D A r := fun x hx => mem_inN.mpr ⟨hx,edge x hx⟩
        have q := card_le_card cap
        have e : A.card=6 := P.ca
        omega
      obtain ⟨a,am,astop⟩ := exists_sink (af.mono_set mA) mne (by omega)
      have aa := mA am
      have ar := (mem_filter.mp am).2
      obtain ⟨x,hx⟩ := card_pos.mp (show 0<(outN D A a).card by rw [cy a aa]; decide)
      obtain ⟨xa,ax⟩ := mem_outN.mp hx
      have xr : D x r=true := by
        by_contra h
        exact astop x (mem_filter.mpr ⟨xa,h⟩) ax
      have row : outN D B a=B.erase r :=
        eq_of_subset_of_card_le (fun z hz => mem_erase.mpr
          ⟨fun e => ar (e ▸ (mem_outN.mp hz).2),(mem_outN.mp hz).1⟩)
          (by rw [cyFive a aa,b5])
      have bl : B.erase r⊆ball D V a 1 := fun z hz =>
        ball_of_adj (P.bV (mem_of_mem_erase hz)) (mem_outN.mp (row.symm ▸ hz)).2
      exact contradiction a aa
        (fun z hz => by
          by_cases e : z=r
          · subst z
            exact ball_step (ball_of_adj (P.aV xa) ax) (P.bV rb) xr
          · exact ball_mono_radius (by decide : 1≤2) (bl (mem_erase.mpr ⟨e,hz⟩)))
        (fun t tt => ball_step (bl hy) (P.tV tt) (ty t tt))
    · push Not at back
      have ym : ∀ y∈B, 1≤(outN D B y).card := fun y yy => midY y yy (back y yy)
      have byc : OutEq 1 D B := by
        rcases six_acyclic_or_cycle bf b6 with bacy | eq
        · obtain ⟨y,yy,ys⟩ := exists_sink bacy (card_pos.mp (by omega)) (by omega)
          obtain ⟨z,hz⟩ := card_pos.mp (ym y yy)
          exact (ys z (mem_outN.mp hz).1 (mem_outN.mp hz).2).elim
        · exact eq
      have parent (z) (zz : z∈B) : ∃ y∈B.erase z, D y z=true := by
        by_contra h
        push Not at h
        have c : (B.erase z).card=5 := by rw [card_erase_of_mem zz,b6]
        obtain ⟨y,yy,sink⟩ := exists_sink (T:=B.erase z) (bf.mono_set (erase_subset _ _))
          (card_pos.mp (by omega)) (by omega)
        obtain ⟨w,hw⟩ := card_pos.mp (ym y (mem_of_mem_erase yy))
        obtain ⟨wb,yw⟩ := mem_outN.mp hw
        have nw : w≠z := fun e => h y yy (e ▸ yw)
        exact sink w (mem_erase.mpr ⟨nw,wb⟩) yw
      obtain ⟨a,aa⟩ := card_pos.mp (show 0<A.card by change 0<P.A.card; rw [P.ca]; decide)
      have b1 : outN D B a⊆ball D V a 1 := fun b hb =>
        ball_of_adj (P.bV (mem_outN.mp hb).1) (mem_outN.mp hb).2
      have reachB : B⊆ball D V a 2 := by
        intro b bb
        by_cases he : D a b=true
        · exact ball_mono_radius (by decide : 1≤2) (b1 (mem_outN.mpr ⟨bb,he⟩))
        · have eq : outN D B a=B.erase b := eq_of_subset_of_card_le
            (fun y hy => mem_erase.mpr ⟨fun e => he (e ▸ (mem_outN.mp hy).2),(mem_outN.mp hy).1⟩)
            (by rw [card_erase_of_mem bb,b6,cyFive a aa])
          obtain ⟨y,hy,yb⟩ := parent b bb
          exact ball_step (b1 (eq.symm ▸ hy)) (P.bV bb) yb
      obtain ⟨y,hy⟩ := card_pos.mp (show 0<(outN D B a).card by rw [cyFive a aa]; decide)
      have yy := (mem_outN.mp hy).1
      have ty := one_head_to_second ho P t5 yy (by rw [back y yy,card_empty]) (by rw [byc y yy])
      exact contradiction a aa reachB (fun t tt => ball_step (b1 hy) (P.tV tt) (ty t tt))

theorem endpoint_five_six : DotDegreeSeven.Endpoint 5 6 := by
  intro D V hf hne hn hd
  obtain ⟨G,sub,ho⟩ := exists_outEq hd
  have f := qfree_sub sub hf
  exact six_uniform_false f ho hne (six_order30_uniform f ho (by simpa using hn))

theorem ch_six (n : ℕ) (hn : 0<n) (G : CH.Digraph) (hl : CH.Loopless G n)
    (hd : CH.MinOutdegreeAtLeast G n 6) : CH.HasDirectedCycleAtMost G n (CH.ceilDiv n 6) :=
  ch_six_of_endpoint_five endpoint_five_six n hn G hl hd

#print axioms endpoint_five_six
#print axioms ch_six
end LeanCH.BR.DotDegreeSix



