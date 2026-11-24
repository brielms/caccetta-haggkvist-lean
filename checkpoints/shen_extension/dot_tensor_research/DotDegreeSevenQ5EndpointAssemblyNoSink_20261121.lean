import checkpoints.shen_extension.dot_tensor_research.DotDegreeSevenQ5EndpointAssemblyAcyclic_20261121
import checkpoints.shen_extension.dot_tensor_research.DotDegreeSevenQ5ExactReturnBank_20261121
import checkpoints.shen_extension.dot_tensor_research.DotDegreeSevenQ5ExactLayers_20261121

namespace LeanCH.BR.DotDegreeSevenLow
open Finset BRq2 BRq3 BR45 BRsGen

/-- No first layer has a sink at the saturated endpoint: if a sink is
not universally reachable, the closed six-cycle around it also fails. -/
theorem endpoint_first_layer_no_sink {D : CH.Digraph} {V : Finset ℕ} {u z : ℕ}
    (hf : QFree D V 5) (ho : OutEq 7 D V) (n : V.card=35)
    (noLow : ∀ v∈V, 15≤(ball D V v 2).card) (hu : u∈V)
    (hz : z∈outN D V u) (sink : ∀ x∈outN D V u,D z x≠true) : False := by
  classical
  let A := EndpointLayer1 D V u
  let B := EndpointLayer2 D V u
  let T := EndpointLayer3 D V u
  let C := A.filter (fun x => ¬ ∃ i, Walk D A x z i)
  have av : A⊆V := fun _ x => (mem_outN.mp x).1
  have bv : B⊆V := sdiff_subset.trans ball_subset
  have tv : T⊆V := sdiff_subset.trans ball_subset
  have hzA : z∈A := hz
  have zv := av hzA
  have ca : C⊆A := filter_subset _ _
  have cv := ca.trans av
  have hcards := exact_endpoint_cards hf ho n noLow
  obtain ⟨a7,b7,t6⟩ := exact_endpoint_layer_cards hf ho hu (hcards u hu)
  change A.card=7 at a7
  change B.card=7 at b7
  change T.card=6 at t6
  obtain ⟨supA,supB⟩ := exact_endpoint_layer_out hf hu
  change (∀ x∈A, outN D V x⊆A∪B) at supA
  change (∀ x∈B, outN D V x⊆(A∪B)∪T) at supB
  have btD : Disjoint B T := disjoint_left.mpr (fun _ hb ht =>
    (mem_sdiff.mp ht).2 (mem_sdiff.mp hb).1)
  have abD : Disjoint A B := disjoint_left.mpr (fun _ ha hb =>
    (mem_sdiff.mp hb).2 ((mem_ball_one hu).mpr (Or.inr ha)))
  have sink_row (x) (hx : x∈A) (xs : ∀ y∈A,D x y≠true) : outN D V x=B := by
    have h : outN D V x⊆B := by
      intro y hy
      rcases mem_union.mp (supA x hx hy) with ya|yb
      · exact (xs y ya (mem_outN.mp hy).2).elim
      · exact yb
    exact eq_of_subset_of_card_le h (by rw [ho x (av hx),b7])
  have zrow := sink_row z hz sink
  have uniq (x) (hx : x∈A) (xs : ∀ y∈A,D x y≠true) : x=z := by
    by_contra ne
    exact saturated_mixed_endpoint_no_twins hf ho n noLow (av hx) zv ne
      ((sink_row x hx xs).trans zrow.symm)
  have zn : z∉C := by
    intro h
    exact (mem_filter.mp h).2 ⟨0,.refl z⟩
  have cne : C.Nonempty := by
    by_cases h : C.Nonempty
    · exact h
    exfalso
    apply endpoint_no_reachable_sink hf ho n noLow hu hz sink
    intro x hx
    by_contra no
    exact h ⟨x,mem_filter.mpr ⟨hx,no⟩⟩
  have ckeep (x) (hx : x∈C) (y) (hy : y∈A) (xy : D x y=true) : y∈C := by
    refine mem_filter.mpr ⟨hy,?_⟩
    rintro ⟨k,w⟩
    exact (mem_filter.mp hx).2 ⟨k+1,.step hy xy w⟩
  have cmd : ∀ x∈C, 1≤(outN D C x).card := by
    intro x hx
    by_contra! lt
    have zero : (outN D C x).card=0 := by omega
    have s : ∀ y∈A,D x y≠true := by
      intro y hy e
      exact notMem_empty y ((card_eq_zero.mp zero) ▸ mem_outN.mpr ⟨ckeep x hx y hy e,e⟩)
    exact zn ((uniq x (ca hx) s) ▸ hx)
  have c6 : C.card=6 := by
    have le := card_le_card (insert_subset hzA ca)
    rw [card_insert_of_notMem zn,a7] at le
    by_contra! ne
    obtain ⟨x,hx,xs⟩ := exists_sink (hf.mono_set cv) cne (by omega : C.card≤5)
    obtain ⟨y,hy⟩ := card_pos.mp (cmd x hx)
    exact xs y (mem_outN.mp hy).1 (mem_outN.mp hy).2
  have ac : A=insert z C :=
    (eq_of_subset_of_card_le (insert_subset hzA ca) (by rw [card_insert_of_notMem zn,c6,a7])).symm
  have cone : OutEq 1 D C := (dt_reg (by decide : 1≤5) (ball_q_one 5 (by decide))
    (hf.mono_set cv) cmd (by simpa only [Nat.mul_one,Nat.reduceAdd] using c6)).1
  have csup (x) (hx : x∈C) : outN D V x⊆C∪B := by
    intro y hy
    rcases mem_union.mp (supA x (ca hx) hy) with ya|yb
    · exact mem_union_left _ (ckeep x hx y ya (mem_outN.mp hy).2)
    · exact mem_union_right _ yb
  have miss (x) (hx : x∈C) : (B \ outN D V x).card≤1 := by
    have eq : outN D (C∪B) x=outN D V x := by
      ext w
      simp only [mem_outN]
      exact ⟨fun h => ⟨union_subset cv bv h.1,h.2⟩,
        fun h => ⟨csup x hx (mem_outN.mpr h),h.2⟩⟩
    have count := card_outN_union (D:=D) (x:=x) (abD.mono_left ca)
    rw [eq,ho x (cv hx),cone x hx] at count
    have split : B∩outN D V x=outN D B x := by
      ext v
      simp only [mem_inter,mem_outN]
      exact ⟨fun h => ⟨h.1,h.2.2⟩,fun h => ⟨h.1,bv h.1,h.2⟩⟩
    rw [card_sdiff,inter_comm,split,b7]
    omega
  have bz (x) (hx : x∈B) : D x z≠true := by
    intro e
    exact hf z 2 (by decide) (by decide)
      (.step (bv hx) (mem_outN.mp (zrow.symm ▸ hx)).2 (.step zv e (.refl z)))
  have tz (x) (hx : x∈T) : D x z≠true := by
    intro e
    obtain ⟨y,hy,yx⟩ := exact_endpoint_layer3_parent hu hx
    change y∈B at hy
    exact hf z 3 (by decide) (by decide)
      (.step (bv hy) (mem_outN.mp (zrow.symm ▸ hy)).2 (.step (tv hx) yx (.step zv e (.refl z))))
  have cz (x) (hx : x∈C) : D x z≠true := fun e => zn (ckeep x hx z hz e)
  have bsup (x) (hx : x∈B) : outN D V x⊆C∪(B∪T) := by
    intro y hy
    rcases mem_union.mp (supB x hx hy) with m|m
    · rcases mem_union.mp m with m|m
      · rw [ac] at m
        rcases mem_insert.mp m with e|m
        · exact (bz x hx (e ▸ (mem_outN.mp hy).2)).elim
        · exact mem_union_left _ m
      · exact mem_union_right _ (mem_union_left _ m)
    · exact mem_union_right _ (mem_union_right _ m)
  have back_no := exact_no_cycle_bank_returns hf ho n.le (fun v hv => (hcards v hv).1.le)
    cv bv tv btD (by omega : C.card≤7) b7 t6.le miss
    (fun x hx => let ⟨y,hy⟩ := card_pos.mp (cmd x hx); ⟨y,mem_outN.mp hy⟩) bsup
  obtain ⟨x,hx⟩ := cne
  have stepC (y) (hy : y∈C) (i) (hi : i≤2) {w} (ww : Walk D V y w i) :
      w∈C∪(B∪T) := by
    have ones (y) (hy : y∈C) {v} (vv : Walk D V y v 1) : v∈C∪B := by
      cases vv with
      | step vV e tail =>
        cases tail
        exact csup y hy (mem_outN.mpr ⟨vV,e⟩)
    interval_cases i
    · cases ww
      exact mem_union_left _ hy
    · rcases mem_union.mp (ones y hy ww) with l|r
      · exact mem_union_left _ l
      · exact mem_union_right _ (mem_union_left _ r)
    · obtain ⟨v,pref,vV,e⟩ := ww.unsnoc
      rcases mem_union.mp (ones y hy pref) with l|r
      · rcases mem_union.mp (csup v l (mem_outN.mpr ⟨vV,e⟩)) with l'|r'
        · exact mem_union_left _ l'
        · exact mem_union_right _ (mem_union_left _ r')
      · exact bsup v r (mem_outN.mpr ⟨vV,e⟩)
  have nxz : z∉ball D V x 3 := by
    intro m
    obtain ⟨_,i,hi,w⟩ := mem_ball.mp m
    cases i with
    | zero =>
      have eq : x=z := by cases w; rfl
      exact zn (eq ▸ hx)
    | succ i =>
      obtain ⟨v,pref,_,e⟩ := w.unsnoc
      rcases mem_union.mp (stepC x hx i (by omega) pref) with c|bt
      · exact cz v c e
      · rcases mem_union.mp bt with b|t
        · exact bz v b e
        · exact tz v t e
  have xr : z∈reverseBall D V x 2 := by
    rw [(saturated_mixed_endpoint hf ho n noLow x (cv hx)).2]
    exact mem_union_left _ (mem_sdiff.mpr ⟨zv,nxz⟩)
  have x2 := (mem_filter.mp xr).2
  have nx1 : x∉ball D V z 1 := by
    intro m
    rcases (mem_ball_one zv).mp m with e|b
    · exact zn (e ▸ hx)
    · rw [zrow] at b
      exact disjoint_left.mp abD (ca hx) b
  obtain ⟨w,w1,wx⟩ := ball_succ_pred zv x2 nx1
  rcases (mem_ball_one zv).mp w1 with e|wb
  · exact sink x (ca hx) (e ▸ wx)
  · rw [zrow] at wb
    exact back_no w wb x hx 1 (by decide) (by decide) (.step (cv hx) wx (.refl x))

#print axioms endpoint_first_layer_no_sink
end LeanCH.BR.DotDegreeSevenLow
