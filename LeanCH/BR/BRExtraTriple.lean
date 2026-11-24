import LeanCH.BR.BRTripleReturn
import LeanCH.BR.BRHighTwoCore
import LeanCH.BR.BRAlmostFullEntry

/-! The first unequal third layer: a size-s+1 third set of retained degree two. -/

namespace LeanCH.BR.BRsGen

open BRq2 BRq3 BR45

variable {D : CH.Digraph} {X Y Z : Finset ℕ} {s a b : ℕ}

/-- Both possible first-set structures give the same isolated-return control. -/
theorem first_back_arc_control (hs : 6 ≤ s) (hf : QFree D (X ∪ Y) (s - 1))
    (hXY : Disjoint X Y) (hX : X.card = s) (hY : Y.card = s)
    (hhigh : ∀ x ∈ X, s ≤ (outN D (X ∪ Y) x).card)
    (ha : a ∈ X) (hb : b ∈ Y) (hba : D b a = true) :
    (∀ y ∈ Y.erase b, ∃ m, m ≤ 2 ∧ Walk D (X ∪ Y) a y m) ∧
    (∀ y ∈ Y.erase b, ∀ x ∈ X, ¬ D y x = true) ∧
    (∀ y ∈ Y.erase b, ¬ D y b = true) := by
  classical
  by_cases hint : ∀ x ∈ X, 1 ≤ (outN D X x).card
  · obtain ⟨hall, hnX, hnb⟩ := cyclic_back_arc_others (by omega) hf hXY hX hY hhigh hint hb ha hba
    refine ⟨?_, hnX, hnb⟩
    intro y hy
    exact ⟨1, by decide, .step (Finset.mem_union_right _ (Finset.mem_of_mem_erase hy)) (hall y hy) (.refl y)⟩
  · push Not at hint
    obtain ⟨t, ht, htc⟩ := hint
    have hsink : ∀ v ∈ X, ¬ D t v = true := by
      intro v hv htv
      have := Finset.card_pos.mpr ⟨v, mem_outN.mpr ⟨hv, htv⟩⟩
      omega
    have hacy := qfree_succ_of_sink (hf.mono_set Finset.subset_union_left)
      (by omega : X.card = s - 1 + 1) ht hsink
    rw [Nat.sub_add_cancel (by omega : 1 ≤ s)] at hacy
    exact acyclic_back_arc_others hs hf hacy hXY hX hY hhigh ha hb hba

/-- With one extra third vertex and retained degree two, some third row must return to the first set. -/
theorem one_extra_has_first_return (hs : 6 ≤ s)
    (hf : QFree D (X ∪ Y ∪ Z) (s - 1)) (hXY : Disjoint X Y)
    (houter : Disjoint (X ∪ Y) Z)
    (hX : X.card = s) (hY : Y.card = s) (hZ : Z.card = s + 1)
    (hhighX : ∀ x ∈ X, s ≤ (outN D (X ∪ Y) x).card)
    (hhighY : ∀ y ∈ Y, s ≤ (outN D (X ∪ Y ∪ Z) y).card)
    (hlowZ : ∀ z ∈ Z, 2 ≤ (outN D (X ∪ Y ∪ Z) z).card)
    (hparents : ∀ z ∈ Z, ∃ y ∈ Y, D y z = true) :
    ∃ z ∈ Z, ∃ a ∈ X, D z a = true := by
  classical
  by_contra hn
  have hnoZX : ∀ z ∈ Z, ∀ x ∈ X, ¬ D z x = true := fun z hz x hx hzx => hn ⟨z, hz, x, hx, hzx⟩
  have hXU : X ⊆ X ∪ Y ∪ Z := Finset.subset_union_left.trans Finset.subset_union_left
  have hYU : Y ⊆ X ∪ Y ∪ Z := Finset.subset_union_right.trans Finset.subset_union_left
  have hZU : Z ⊆ X ∪ Y ∪ Z := Finset.subset_union_right
  have hYZ : Disjoint Y Z := houter.mono_left Finset.subset_union_right
  by_cases hb : ∃ b ∈ Y, ∃ a ∈ X, D b a = true
  · obtain ⟨b, hb, a, ha, hba⟩ := hb
    obtain ⟨hreach, hnoYX, hnoYb⟩ := first_back_arc_control hs
      (hf.mono_set Finset.subset_union_left) hXY hX hY hhighX ha hb hba
    have hnoZb : ∀ z ∈ Z, ¬ D z b = true := by
      intro z hz hzb
      obtain ⟨y, hy, hyz⟩ := hparents z hz
      by_cases hyb : y = b
      · exact digonfree hf (by omega) (hYU hb) (hZU hz) (hyb ▸ hyz) hzb
      · obtain ⟨m, hm, w⟩ := hreach y (Finset.mem_erase.mpr ⟨hyb, hy⟩)
        exact hf a (m + 1 + 1 + 1) (by omega) (by omega)
          ((((w.mono Finset.subset_union_left).snoc (hZU hz) hyz).snoc (hYU hb) hzb).snoc (hXU ha) hba)
    let R := Y.erase b
    have hRU : R ⊆ X ∪ Y ∪ Z := (Finset.erase_subset _ _).trans hYU
    have hRZ : Disjoint R Z := hYZ.mono_left (Finset.erase_subset _ _)
    have hRc : R.card = s - 1 := by dsimp only [R]; rw [Finset.card_erase_of_mem hb, hY]
    have hretain : ∀ v ∈ R ∪ Z, outN D (X ∪ Y ∪ Z) v ⊆ outN D (R ∪ Z) v := by
      intro v hv w hw
      obtain ⟨hwU, hvw⟩ := mem_outN.mp hw
      refine mem_outN.mpr ⟨?_, hvw⟩
      rcases Finset.mem_union.mp hwU with hwXY | hwZ
      · rcases Finset.mem_union.mp hwXY with hwX | hwY
        · rcases Finset.mem_union.mp hv with hvR | hvZ
          · exact (hnoYX v hvR w hwX hvw).elim
          · exact (hnoZX v hvZ w hwX hvw).elim
        · refine Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨?_, hwY⟩)
          intro hwb
          rcases Finset.mem_union.mp hv with hvR | hvZ
          · exact hnoYb v hvR (hwb ▸ hvw)
          · exact hnoZb v hvZ (hwb ▸ hvw)
      · exact Finset.mem_union_right _ hwZ
    have hmin : ∀ v ∈ R ∪ Z, 2 ≤ (outN D (R ∪ Z) v).card := by
      intro v hv
      have hc := Finset.card_le_card (hretain v hv)
      rcases Finset.mem_union.mp hv with hvR | hvZ
      · have := hhighY v (Finset.mem_of_mem_erase hvR); omega
      · exact (hlowZ v hvZ).trans hc
    have hcard : (R ∪ Z).card = 2 * s := by rw [Finset.card_union_of_disjoint hRZ, hRc, hZ]; omega
    apply two_core_many_high_false (q := s - 1) (H := R) (by omega)
      (hf.mono_set (Finset.union_subset hRU hZU)) (by omega) hmin Finset.subset_union_left
      (by rw [hcard, hRc]; omega)
    intro r hr
    have hc := (hhighY r (Finset.mem_of_mem_erase hr)).trans
      (Finset.card_le_card (hretain r (Finset.mem_union_left _ hr)))
    omega
  · have hnoYX : ∀ y ∈ Y, ∀ x ∈ X, ¬ D y x = true := fun y hy x hx hyx => hb ⟨y, hy, x, hx, hyx⟩
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
    have hmin : ∀ v ∈ Y ∪ Z, 2 ≤ (outN D (Y ∪ Z) v).card := by
      intro v hv
      have hc := Finset.card_le_card (hretain v hv)
      rcases Finset.mem_union.mp hv with hvY | hvZ
      · have := hhighY v hvY; omega
      · exact (hlowZ v hvZ).trans hc
    apply high_half_two_core_false (H := Y) (by omega : 5 ≤ s)
      (hf.mono_set (Finset.union_subset hYU hZU))
      (by rw [Finset.card_union_of_disjoint hYZ, hY, hZ]; omega)
      hmin Finset.subset_union_left hY
    intro y hy
    exact (hhighY y hy).trans (Finset.card_le_card (hretain y (Finset.mem_union_left _ hy)))

end LeanCH.BR.BRsGen
