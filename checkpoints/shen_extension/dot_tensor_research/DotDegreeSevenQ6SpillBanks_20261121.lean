import checkpoints.shen_extension.dot_tensor_research.DotDegreeSevenQ6Order41Profile_20261121

namespace LeanCH.BR.DotDegreeSevenQ6
open Finset BRq2 BRq3 BR45 BRsGen

/-- Complete spill banks of size q+1 cannot partially overlap. -/
theorem completeSpill_banks_disjoint_or_equal {D : CH.Digraph} {V B C T U : Finset ℕ} {q : ℕ}
    (hf : QFree D V q) (hq : 2≤q) (hB : B ⊆ V) (hC : C ⊆ V)
    (cB : B.card=q+1) (cC : C.card=q+1)
    (eB : OutEq 1 D B) (eC : OutEq 1 D C)
    (keepB : ∀ b∈B, outN D V b ⊆ B ∪ T)
    (keepC : ∀ c∈C, outN D V c ⊆ C ∪ U)
    (spillB : ∀ b∈B, ∀ t∈T, D b t=true)
    (spillC : ∀ c∈C, ∀ t∈U, D c t=true) :
    Disjoint B C ∨ B=C := by
  classical
  by_cases dis : Disjoint B C
  · exact Or.inl dis
  right
  have int : (B∩C).Nonempty := not_disjoint_iff_nonempty_inter.mp dis
  have mn (x) (hx : x∈B∩C) : 1≤(outN D (B∩C) x).card := by
    obtain ⟨xb,xc⟩ := mem_inter.mp hx
    obtain ⟨b,hb⟩ := card_pos.mp (by rw [eB x xb]; decide : 0<(outN D B x).card)
    obtain ⟨c,hc⟩ := card_pos.mp (by rw [eC x xc]; decide : 0<(outN D C x).card)
    obtain ⟨mb,ab⟩ := mem_outN.mp hb
    obtain ⟨mc,ac⟩ := mem_outN.mp hc
    have eb : b=c := by
      by_contra ne
      have nb : b∉C := by
        intro h
        have cb : b∈outN D C x := mem_outN.mpr ⟨h,ab⟩
        have hin : ({b,c} : Finset ℕ) ⊆ outN D C x := by simp [insert_subset_iff,cb,hc]
        have ll := card_le_card hin
        rw [eC x xc,card_pair ne] at ll
        omega
      have nc : c∉B := by
        intro h
        have cc : c∈outN D B x := mem_outN.mpr ⟨h,ac⟩
        have hin : ({b,c} : Finset ℕ) ⊆ outN D B x := by simp [insert_subset_iff,hb,cc]
        have ll := card_le_card hin
        rw [eB x xb,card_pair ne] at ll
        omega
      have bU := (mem_union.mp (keepC x xc (mem_outN.mpr ⟨hB mb,ab⟩))).resolve_left nb
      have cT := (mem_union.mp (keepB x xb (mem_outN.mpr ⟨hC mc,ac⟩))).resolve_left nc
      exact hf b 2 (by decide) hq
        (.step (hC mc) (spillB b mb c cT) (.step (hB mb) (spillC c mc b bU) (.refl b)))
    subst c
    exact Nat.succ_le_of_lt (card_pos.mpr ⟨b,mem_outN.mpr ⟨mem_inter.mpr ⟨mb,mc⟩,ab⟩⟩)
  have num : q+1≤(B∩C).card := by
    by_contra! small
    obtain ⟨v,hv,stop⟩ := exists_sink (hf.mono_set (inter_subset_left.trans hB)) int (by omega)
    obtain ⟨w,hw⟩ := card_pos.mp (mn v hv)
    exact stop w (mem_outN.mp hw).1 (mem_outN.mp hw).2
  have eb : B∩C=B := eq_of_subset_of_card_le inter_subset_left (by omega)
  have ec : B∩C=C := eq_of_subset_of_card_le inter_subset_right (by omega)
  exact eb.symm.trans ec


structure SevenSpill (D : CH.Digraph) (V B T : Finset ℕ) : Prop where
  subB : B⊆V
  subT : T⊆V
  seven : B.card=7
  six : T.card=6
  apart : Disjoint B T
  one : OutEq 1 D B
  keep : ∀ b∈B, outN D V b⊆B∪T
  full : ∀ b∈B, ∀ t∈T, D b t=true

/-- A complete bank supplies seven actual tall vertices, even at
the non-saturated order 42. -/
theorem sevenSpill_tall {D : CH.Digraph} {V B T : Finset ℕ}
    (hf : QFree D V 6) (ho : OutEq 7 D V) (h : SevenSpill D V B T) :
    ∀ b∈B, 16≤(ball D V b 2).card ∧ 22≤(ball D V b 3).card := by
  obtain ⟨t,ht,stop⟩ := exists_sink (hf.mono_set h.subT)
    (card_pos.mp (by rw [h.six]; decide)) h.six.le
  let W := outN D V t
  have w7 : W.card=7 := ho t (h.subT ht)
  have wt : Disjoint T W := disjoint_left.mpr (by
    intro w hw ww
    exact stop w hw (mem_outN.mp ww).2)
  have wb : Disjoint B W := disjoint_left.mpr (by
    intro w hw ww
    exact hf w 2 (by decide) (by decide)
      (.step (h.subT ht) (h.full w hw t ht)
        (.step (h.subB hw) (mem_outN.mp ww).2 (.refl w))))
  intro b hb
  let I := ball D B b 2
  have iB : I⊆B := ball_subset
  have i3 : 3≤I.card := ball_one_growth (hf.mono_set h.subB)
    (fun x hx => (h.one x hx).ge) hb 2 (by decide)
  have reachI : I⊆ball D V b 2 := by
    intro x hx
    obtain ⟨xb,i,ib,wi⟩ := mem_ball.mp hx
    exact mem_ball.mpr ⟨h.subB xb,i,ib,wi.mono h.subB⟩
  have reachT : T⊆ball D V b 2 := fun x hx =>
    mem_ball.mpr ⟨h.subT hx,1,by decide,.step (h.subT hx) (h.full b hb x hx) (.refl x)⟩
  have reachW : W⊆ball D V b 2 := by
    intro w hw
    obtain ⟨wv,e⟩ := mem_outN.mp hw
    exact mem_ball.mpr ⟨wv,2,by decide,
      .step (h.subT ht) (h.full b hb t ht) (.step wv e (.refl w))⟩
  have hc := card_le_card (union_subset (union_subset reachI reachT) reachW)
  rw [card_union_of_disjoint (disjoint_union_left.mpr ⟨wb.mono_left iB,wt⟩),
    card_union_of_disjoint (h.apart.mono_left iB),h.six,w7] at hc
  have large : 16≤(ball D V b 2).card := by omega
  refine ⟨large,?_⟩
  have lo := floor_three21 hf (fun x hx => (ho x hx).ge) (h.subB hb)
  by_contra! small
  have cap := tight_three_cap_two hf ho (h.subB hb) (by omega)
  omega

#print axioms completeSpill_banks_disjoint_or_equal
#print axioms sevenSpill_tall
end LeanCH.BR.DotDegreeSevenQ6
