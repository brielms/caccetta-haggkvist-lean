import checkpoints.shen_extension.dot_tensor_research.DotDegreeSevenQ5Prefix_20261121

namespace LeanCH.BR.DotDegreeSevenLow
open Finset BRq2 BRq3 BR45 BRsGen

/-- In a common host, two six-cycle banks with full spill rows are equal
or disjoint. The proof matches successors in the same physical rows. -/
theorem spill_banks_disjoint_or_equal {D : CH.Digraph} {V B C T U : Finset ℕ}
    (hf : QFree D V 5) (hB : B ⊆ V) (hC : C ⊆ V)
    (cB : B.card=6) (cC : C.card=6)
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
      exact hf b 2 (by decide) (by decide)
        (.step (hC mc) (spillB b mb c cT) (.step (hB mb) (spillC c mc b bU) (.refl b)))
    subst c
    exact Nat.succ_le_of_lt (card_pos.mpr ⟨b,mem_outN.mpr ⟨mem_inter.mpr ⟨mb,mc⟩,ab⟩⟩)
  have num : 6≤(B∩C).card := by
    by_contra! small
    obtain ⟨v,hv,stop⟩ := exists_sink (hf.mono_set (inter_subset_left.trans hB)) int (by omega)
    obtain ⟨w,hw⟩ := card_pos.mp (mn v hv)
    exact stop w (mem_outN.mp hw).1 (mem_outN.mp hw).2
  have eb : B∩C=B := eq_of_subset_of_card_le inter_subset_left (by omega)
  have ec : B∩C=C := eq_of_subset_of_card_le inter_subset_right (by omega)
  exact eb.symm.trans ec

/-- A reverse radius-two column, not a global size average, bounds the
number of roots supported by an identical bank. -/
theorem bank_group_bound {D : CH.Digraph} {V B P L : Finset ℕ} {b n : ℕ}
    (hf : QFree D V 5) (ho : ∀ v∈V,7≤(outN D V v).card)
    (hn : V.card=n) (hb : b∈V) (three : B.card=3) (four : P.card=4)
    (dbp : Disjoint B P) (dbl : Disjoint (B∪P) L)
    (bCol : B ⊆ reverseBall D V b 2)
    (pCol : P ⊆ reverseBall D V b 2)
    (lCol : L ⊆ reverseBall D V b 2) :
    L.card + 26 ≤ n := by
  have sub := union_subset (union_subset bCol pCol) lCol
  have count := card_le_card sub
  rw [card_union_of_disjoint dbl,card_union_of_disjoint dbp,three,four] at count
  have hc := reverseBall_subset_complement (i:=3) (j:=2) (v:=b) hf (by decide)
  have up := (card_le_card hc).trans (card_union_le _ _)
  rw [card_sdiff_of_subset ball_subset,card_singleton,hn] at up
  have floor := floor_three20 hf ho hb
  have within := card_le_card (ball_subset (D:=D) (W:=V) (u:=b) (k:=3))
  rw [hn] at within
  omega

#print axioms spill_banks_disjoint_or_equal
#print axioms bank_group_bound
end LeanCH.BR.DotDegreeSevenLow

