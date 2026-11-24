import LeanCH.BR.BRCyclicTriple
import LeanCH.BR.BRAcyclicPair
import LeanCH.BR.BRAcyclicTriple

/-! The uniform return exclusion for three equal sets, with no first-set cycle assumption. -/

namespace LeanCH.BR.BRsGen

open BRq2 BRq3 BR45

variable {D : CH.Digraph} {X Y Z : Finset ℕ} {s : ℕ}

/-- Three equal sets with degree floors s,s,1 and third-set parents have no third-set return. -/
theorem triple_no_back (hs : 6 ≤ s)
    (hf : QFree D (X ∪ Y ∪ Z) (s - 1)) (hXY : Disjoint X Y)
    (houter : Disjoint (X ∪ Y) Z)
    (hX : X.card = s) (hY : Y.card = s) (hZ : Z.card = s)
    (hhighX : ∀ x ∈ X, s ≤ (outN D (X ∪ Y) x).card)
    (hhighY : ∀ y ∈ Y, s ≤ (outN D (X ∪ Y ∪ Z) y).card)
    (hlowZ : ∀ z ∈ Z, 1 ≤ (outN D (X ∪ Y ∪ Z) z).card)
    (hparents : ∀ z ∈ Z, ∃ y ∈ Y, D y z = true) :
    ∀ z ∈ Z, ∀ v ∈ X ∪ Y, ¬ D z v = true := by
  classical
  by_cases hint : ∀ x ∈ X, 1 ≤ (outN D X x).card
  · exact cyclic_triple_no_back hs hf hXY houter hX hY hZ hhighX hhighY hlowZ hint hparents
  have hXU : X ⊆ X ∪ Y ∪ Z := Finset.subset_union_left.trans Finset.subset_union_left
  have hYU : Y ⊆ X ∪ Y ∪ Z := Finset.subset_union_right.trans Finset.subset_union_left
  have hZU : Z ⊆ X ∪ Y ∪ Z := Finset.subset_union_right
  have hYZ : Disjoint Y Z := houter.mono_left Finset.subset_union_right
  have hacy : QFree D X s := by
    push Not at hint
    obtain ⟨t, ht, htc⟩ := hint
    have hsink : ∀ v ∈ X, ¬ D t v = true := by
      intro v hv htv
      have := Finset.card_pos.mpr ⟨v, mem_outN.mpr ⟨hv, htv⟩⟩
      omega
    have := qfree_succ_of_sink (hf.mono_set hXU) (by omega : X.card = s - 1 + 1) ht hsink
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ s)] using this
  have hnoZX := acyclic_first_no_third_to_first hs hf hacy hXY hX hY hZ hhighX hhighY hparents
  have hnoZY : ∀ z ∈ Z, ∀ y ∈ Y, ¬ D z y = true := by
    by_cases hb : ∃ b ∈ Y, ∃ a ∈ X, D b a = true
    · obtain ⟨b, hb, a, ha, hba⟩ := hb
      obtain ⟨hreach, hnoYX, hnoYb⟩ := acyclic_back_arc_others hs
        (hf.mono_set Finset.subset_union_left) hacy hXY hX hY hhighX ha hb hba
      have hnoZb : ∀ z ∈ Z, ¬ D z b = true := by
        intro z hz hzb
        obtain ⟨y, hy, hyz⟩ := hparents z hz
        by_cases hyb : y = b
        · exact digonfree hf (by omega) (hYU hb) (hZU hz) (hyb ▸ hyz) hzb
        · obtain ⟨m, hm, w⟩ := hreach y (Finset.mem_erase.mpr ⟨hyb, hy⟩)
          exact hf a (m + 1 + 1 + 1) (by omega) (by omega)
            ((((w.mono Finset.subset_union_left).snoc (hZU hz) hyz).snoc (hYU hb) hzb).snoc (hXU ha) hba)
      have hsubY : ∀ y ∈ Y.erase b, outN D (X ∪ Y ∪ Z) y ⊆ outN D (Y.erase b ∪ Z) y := by
        intro y hy v hv
        obtain ⟨hvU, hyv⟩ := mem_outN.mp hv
        refine mem_outN.mpr ⟨?_, hyv⟩
        rcases Finset.mem_union.mp hvU with hvXY | hvZ
        · rcases Finset.mem_union.mp hvXY with hvX | hvY
          · exact (hnoYX y hy v hvX hyv).elim
          · exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨fun h => hnoYb y hy (h ▸ hyv), hvY⟩)
        · exact Finset.mem_union_right _ hvZ
      have hsubZ : ∀ z ∈ Z, outN D (X ∪ Y ∪ Z) z ⊆ outN D (Y.erase b ∪ Z) z := by
        intro z hz v hv
        obtain ⟨hvU, hzv⟩ := mem_outN.mp hv
        refine mem_outN.mpr ⟨?_, hzv⟩
        rcases Finset.mem_union.mp hvU with hvXY | hvZ
        · rcases Finset.mem_union.mp hvXY with hvX | hvY
          · exact (hnoZX z hz v hvX hzv).elim
          · exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨fun h => hnoZb z hz (h ▸ hzv), hvY⟩)
        · exact Finset.mem_union_right _ hvZ
      have hn := narrow_pair_no_back (by omega : 4 ≤ s)
        (hf.mono_set (Finset.union_subset ((Finset.erase_subset _ _).trans hYU) hZU))
        (hYZ.mono_left (Finset.erase_subset _ _))
        (by rw [Finset.card_erase_of_mem hb, hY]) hZ
        (fun y hy => (hhighY y (Finset.mem_of_mem_erase hy)).trans (Finset.card_le_card (hsubY y hy)))
        (fun z hz => (hlowZ z hz).trans (Finset.card_le_card (hsubZ z hz)))
      intro z hz y hy hzy
      by_cases hyb : y = b
      · exact hnoZb z hz (hyb ▸ hzy)
      · exact hn z hz y (Finset.mem_erase.mpr ⟨hyb, hy⟩) hzy
    · have hnoYX : ∀ y ∈ Y, ∀ x ∈ X, ¬ D y x = true := by
        intro y hy x hx hyx
        exact hb ⟨y, hy, x, hx, hyx⟩
      have hretain : ∀ v ∈ Y ∪ Z, outN D (X ∪ Y ∪ Z) v ⊆ outN D (Y ∪ Z) v := by
        intro v hv w hw
        obtain ⟨hwU, hvw⟩ := mem_outN.mp hw
        refine mem_outN.mpr ⟨?_, hvw⟩
        rcases Finset.mem_union.mp hwU with hwXY | hwZ
        · rcases Finset.mem_union.mp hwXY with hwX | hwY
          · rcases Finset.mem_union.mp hv with hvY | hvZ
            · exact (hnoYX v hvY w hwX hvw).elim
            · exact (hnoZX v hvZ w hwX hvw).elim
          · exact Finset.mem_union_left _ hwY
        · exact Finset.mem_union_right _ hwZ
      exact equal_pair_no_back (by omega) (hf.mono_set (Finset.union_subset hYU hZU)) hYZ hY hZ
        (fun y hy => (hhighY y hy).trans (Finset.card_le_card (hretain y (Finset.mem_union_left _ hy))))
        (fun z hz => (hlowZ z hz).trans (Finset.card_le_card (hretain z (Finset.mem_union_right _ hz))))
  intro z hz v hv hzv
  rcases Finset.mem_union.mp hv with hvX | hvY
  · exact hnoZX z hz v hvX hzv
  · exact hnoZY z hz v hvY hzv

end LeanCH.BR.BRsGen
