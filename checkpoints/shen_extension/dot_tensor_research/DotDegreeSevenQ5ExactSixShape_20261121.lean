import checkpoints.shen_extension.dot_tensor_research.DotDegreeSevenQ5ExactGoodReturn_20261121

namespace LeanCH.BR.DotDegreeSevenLow
open Finset BRq2 BRq3 BR45 BRsGen

private theorem row_good_split {D : CH.Digraph} {V A B C : Finset ℕ} {z g : ℕ}
    (bV : B⊆V) (cV : C⊆V)
    (az : A=insert z C) (no : D g z≠true)
    (keep : outN D V g⊆A∪B) :
    outN D V g = outN D (C∪B) g := by
  ext x
  simp only [mem_outN]
  refine ⟨fun h => ⟨?_,h.2⟩,fun h => ⟨union_subset cV bV h.1,h.2⟩⟩
  rcases mem_union.mp (keep (mem_outN.mpr h)) with hA|hB
  · rw [az,mem_insert] at hA
    rcases hA with rfl|hC
    · exact (no h.2).elim
    · exact mem_union_left _ hC
  · exact mem_union_right _ hB

/-- Local six-plus-one geometry, required at every actual root, is already
inconsistent with the exact endpoint. The second use is at a good
cycle label, not a fresh abstract copy of the graph. -/
theorem exact_endpoint_of_six_shapes {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V 5) (ho : OutEq 7 D V) (n : V.card=35)
    (noLow : ∀ v∈V, 15≤(ball D V v 2).card)
    (shape : ∀ u∈V, ∃ C z, EndpointLayer1 D V u=insert z C ∧ z∉C ∧
      C.card=6 ∧ OutEq 1 D C ∧ ∃ p∈C, D z p=true) : False := by
  classical
  obtain ⟨u,hu⟩ := card_pos.mp (show 0<V.card by omega)
  let A := EndpointLayer1 D V u
  let B := EndpointLayer2 D V u
  let T := EndpointLayer3 D V u
  have av : A⊆V := outN_subset
  have bv : B⊆V := sdiff_subset.trans ball_subset
  have tv : T⊆V := sdiff_subset.trans ball_subset
  have ab : Disjoint A B := disjoint_left.mpr (by
    intro x ax bx
    exact (mem_sdiff.mp bx).2 ((mem_ball_one hu).mpr (Or.inr ax)))
  have bt : Disjoint B T := disjoint_left.mpr (by
    intro x bx tx
    exact (mem_sdiff.mp tx).2 (mem_sdiff.mp bx).1)
  have ec := exact_endpoint_cards hf ho n noLow
  have cap (v) (hv : v∈V) := (ec v hv).1.le
  obtain ⟨ca,cb,ct⟩ := exact_endpoint_layer_cards hf ho hu (ec u hu)
  obtain ⟨ka,kb⟩ := exact_endpoint_layer_out hf hu
  obtain ⟨C,z,az,zc,c6,one,p,hp,e⟩ := shape u hu
  have cvA : C⊆A := by rw [show A=insert z C from az]; exact subset_insert _ _
  have zvA : z∈A := by rw [show A=insert z C from az]; exact mem_insert_self _ _
  have cv := cvA.trans av
  let G := C.filter (fun x => D x z≠true)
  obtain ⟨gNe,gReach,pg⟩ := exact_cycle_good_bank hf cv (av zvA) c6 one hp e
  have g6 : G.card≤6 := (card_filter_le _ _).trans c6.le
  have gA : G⊆A := (filter_subset _ _).trans cvA
  have reach (a) (ha : a∈A) : ∃ g∈G, ∃ j≤2, Walk D V a g j := by
    rw [show A=insert z C from az,mem_insert] at ha
    rcases ha with rfl|h
    · exact ⟨p,pg,1,by decide,.step (cv hp) e (.refl p)⟩
    · exact gReach a h
  have split (g) (hg : g∈G) : outN D V g=outN D (C∪B) g :=
    row_good_split bv cv az (mem_filter.mp hg).2 (ka g (gA hg))
  have miss (g) (hg : g∈G) : (B \ outN D V g).card≤1 := by
    have sum : 7=1+(outN D B g).card := by
      rw [← one g (mem_filter.mp hg).1,← card_outN_union (ab.mono_left cvA),
        ←split g hg,ho g (av (gA hg))]
    have em : B \ outN D V g = B \ outN D B g := by
      ext y
      simp only [mem_sdiff,mem_outN]
      exact ⟨fun h => ⟨h.1, fun h' => h.2 ⟨bv h'.1,h'.2⟩⟩,
        fun h => ⟨h.1,fun h' => h.2 ⟨h.1,h'.2⟩⟩⟩
    rw [em,card_sdiff_of_subset outN_subset]
    change B.card - (outN D B g).card ≤ 1
    change B.card=7 at cb
    omega
  have noReturn : ∀ b∈B, ∀ a∈A, D b a≠true :=
    exact_good_bank_no_direct_return hf ho n.le cap av bv tv bt g6 cb ct.le miss reach
      (fun b hb y hy => by simpa only [union_assoc] using kb b hb hy)
  obtain ⟨g,hg⟩ := gNe
  have gv := av (gA hg)
  obtain ⟨C',z',cz',_,c'6,one',_,_,_⟩ := shape g gv
  have cpRow : C'⊆outN D V g := by
    change C'⊆EndpointLayer1 D V g
    rw [cz']
    exact subset_insert _ _
  have c'V := cpRow.trans outN_subset
  have cpB : C'⊆B := by
    intro a aa
    have hr := cpRow aa
    rw [split g hg] at hr
    rcases mem_union.mp (mem_outN.mp hr).1 with ac|aB
    · exfalso
      have indeg := (dt_reg (by decide : 1≤5) (ball_q_one 5 (by decide))
        (hf.mono_set c'V) (fun x hx => (one' x hx).ge)
        (by simpa only [Nat.mul_one,Nat.reduceAdd] using c'6)).2 a aa
      obtain ⟨y,hy⟩ := card_pos.mp (show 0<(inN D C' a).card by omega)
      obtain ⟨yc,edge⟩ := mem_inN.mp hy
      have yr := cpRow yc
      rw [split g hg] at yr
      rcases mem_union.mp (mem_outN.mp yr).1 with yC|yB
      · have hyga : y∈outN D C g := mem_outN.mpr ⟨yC,(mem_outN.mp yr).2⟩
        have haga : a∈outN D C g := mem_outN.mpr ⟨ac,(mem_outN.mp hr).2⟩
        have he := card_le_one.mp (one g (mem_filter.mp hg).1).le y hyga a haga
        subst y
        exact loopfree hf (by decide) (cv ac) edge
      · exact noReturn y yB a (cvA ac) edge
    · exact aB
  have bcDiff : (B \ C').card=1 := by
    rw [card_sdiff_of_subset cpB,cb,c'6]
  obtain ⟨v,hv⟩ := card_eq_one.mp bcDiff
  have vbDiff : v∈B \ C' := hv.symm ▸ mem_singleton_self _
  have vB := (mem_sdiff.mp vbDiff).1
  have vV := bv vB
  have bv' : B=insert v C' := by
    ext x
    rw [mem_insert]
    constructor
    · intro hx
      by_cases hc : x∈C'
      · exact Or.inr hc
      · have h : x∈B \ C' := mem_sdiff.mpr ⟨hx,hc⟩
        rw [hv] at h
        exact Or.inl (mem_singleton.mp h)
    · rintro (rfl|h)
      · exact vB
      · exact cpB h
  have keepB (b) (hb : b∈B) : outN D V b⊆B∪T := by
    intro x hx
    have k := kb b hb hx
    rcases mem_union.mp k with h|h
    · rcases mem_union.mp h with ax|bx
      · exact (noReturn b hb x ax (mem_outN.mp hx).2).elim
      · exact mem_union_left _ bx
    · exact mem_union_right _ h
  have vp : ∃ p∈C', D v p=true := by
    by_contra h
    push Not at h
    have k : outN D V v⊆T := by
      intro x hx
      rcases mem_union.mp (keepB v vB hx) with bx|tx
      · rw [bv',mem_insert] at bx
        rcases bx with rfl|c
        · exact (loopfree hf (by decide) vV (mem_outN.mp hx).2).elim
        · exact (h x c (mem_outN.mp hx).2).elim
      · exact tx
    have cnt := card_le_card k
    rw [ho v vV,ct] at cnt
    omega
  obtain ⟨p',hp',ep'⟩ := vp
  let G' := C'.filter (fun x => D x v≠true)
  obtain ⟨g'Ne,g'Reach,_⟩ := exact_cycle_good_bank hf c'V vV c'6 one' hp' ep'
  have full (b) (hb : b∈G') : ∀ t∈T, D b t=true := by
    have bC := (mem_filter.mp hb).1
    have rs := row_good_split tv c'V bv' (mem_filter.mp hb).2 (keepB b (cpB bC))
    have sum : 7=1+(outN D T b).card := by
      rw [← one' b bC,←card_outN_union (bt.mono_left cpB),←rs,ho b (c'V bC)]
    have es : outN D T b=T := eq_of_subset_of_card_le outN_subset (by rw [show T.card=6 from ct]; omega)
    intro t ht
    exact (mem_outN.mp (es.symm ▸ ht)).2
  have noFromT (t) (ht : t∈T) (c) (hc : c∈C') : D t c≠true := by
    intro e'
    obtain ⟨b,hb,j,hj,w⟩ := g'Reach c hc
    exact hf c (j+2) (by omega) (by omega)
      (w.append (.step (tv ht) (full b hb t ht) (.step (c'V hc) e' (.refl c))))
  obtain ⟨b,hb⟩ := g'Ne
  exact exact_cycle_spill_excluded hf ho n.le cap c'V tv one' ct (bt.mono_left cpB)
    noFromT (mem_filter.mp hb).1 (full b hb)

#print axioms exact_endpoint_of_six_shapes

end LeanCH.BR.DotDegreeSevenLow

