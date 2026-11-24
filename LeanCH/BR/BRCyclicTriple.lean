import LeanCH.BR.BREqualPair

/-! Three equal layers when the first layer has positive internal degree. -/

namespace LeanCH.BR.BRsGen

open BRq2 BRq3 BR45

variable {D : CH.Digraph} {X Y Z : Finset ℕ} {s : ℕ}

/-- A third-set return to the cyclic first set forces a short cycle. -/
theorem cyclic_first_no_third_to_first (hs : 6 ≤ s)
    (hf : QFree D (X ∪ Y ∪ Z) (s - 1)) (hXY : Disjoint X Y)
    (hX : X.card = s) (hY : Y.card = s) (hZ : Z.card = s)
    (hhighX : ∀ x ∈ X, s ≤ (outN D (X ∪ Y) x).card)
    (hhighY : ∀ y ∈ Y, s ≤ (outN D (X ∪ Y ∪ Z) y).card)
    (hint : ∀ x ∈ X, 1 ≤ (outN D X x).card)
    (hparents : ∀ z ∈ Z, ∃ y ∈ Y, D y z = true) :
    ∀ z ∈ Z, ∀ a ∈ X, ¬ D z a = true := by
  classical
  have hXU : X ⊆ X ∪ Y ∪ Z := Finset.subset_union_left.trans Finset.subset_union_left
  have hYU : Y ⊆ X ∪ Y ∪ Z := Finset.subset_union_right.trans Finset.subset_union_left
  have hZU : Z ⊆ X ∪ Y ∪ Z := Finset.subset_union_right
  have hfX := hf.mono_set hXU
  have hreg := (dt_reg (by omega : 1 ≤ s - 1) (ball_q_one _ (by omega)) hfX hint
    (by rw [hX]; omega)).1
  intro z hz a ha hza
  obtain ⟨b, hb, hbz⟩ := hparents z hz
  let A := ball D X a (s - 4)
  have hAX : A ⊆ X := ball_subset
  have hAc : s - 3 ≤ A.card := by
    have := ball_one_growth hfX hint ha (s - 4) (by omega)
    change s - 3 ≤ (ball D X a (s - 4)).card
    omega
  have hmiss : ∀ x ∈ A, ¬ D x b = true := by
    intro x hx hxb
    obtain ⟨_, m, hm, w⟩ := mem_ball.mp hx
    exact hf a (m + 1 + 1 + 1) (by omega) (by omega)
      ((((w.mono hXU).snoc (hYU hb) hxb).snoc (hZU hz) hbz).snoc (hXU ha) hza)
  have hall : ∀ x ∈ A, ∀ y ∈ Y.erase b, D x y = true := by
    intro x hx
    have hsub : outN D Y x ⊆ Y.erase b := by
      intro y hy
      obtain ⟨hyY, hxy⟩ := mem_outN.mp hy
      exact Finset.mem_erase.mpr ⟨fun h => hmiss x hx (h ▸ hxy), hyY⟩
    have heq := Finset.eq_of_subset_of_card_le hsub (by
      rw [Finset.card_erase_of_mem hb, hY]
      have hh := hhighX x (hAX hx)
      rw [card_outN_union hXY, hreg x (hAX hx)] at hh
      omega)
    intro y hy
    exact (mem_outN.mp (heq.symm ▸ hy)).2
  have hnear : ∀ x ∈ X, ∃ v ∈ A, v ∈ ball D X x 3 := by
    intro x hx
    have hc := ball_one_growth hfX hint hx 3 (by omega)
    have hi : (A ∩ ball D X x 3).Nonempty := by
      by_contra hn
      have hd : Disjoint A (ball D X x 3) := Finset.disjoint_iff_inter_eq_empty.mpr
        (Finset.not_nonempty_iff_eq_empty.mp hn)
      have hu := Finset.card_le_card (Finset.union_subset hAX
        (ball_subset (D := D) (W := X) (u := x) (k := 3)))
      rw [Finset.card_union_of_disjoint hd, hX] at hu
      omega
    obtain ⟨v, hv⟩ := hi
    exact ⟨v, (Finset.mem_inter.mp hv).1, (Finset.mem_inter.mp hv).2⟩
  have hnoX : ∀ y ∈ Y.erase b, ∀ x ∈ X, ¬ D y x = true := by
    intro y hy x hx hyx
    obtain ⟨v, hvA, hv⟩ := hnear x hx
    obtain ⟨_, m, hm, w⟩ := mem_ball.mp hv
    exact hf x (m + 1 + 1) (by omega) (by omega)
      (((w.mono hXU).snoc (hYU (Finset.mem_of_mem_erase hy)) (hall v hvA y hy)).snoc (hXU hx) hyx)
  have hnoZ : ∀ y ∈ Y.erase b, ¬ D y z = true := by
    intro y hy hyz
    exact hf a 3 (by decide) (by omega)
      (.step (hYU (Finset.mem_of_mem_erase hy)) (hall a (self_mem_ball ha) y hy)
        (.step (hZU hz) hyz (.step (hXU ha) hza (.refl a))))
  obtain ⟨y, hy, hys⟩ := exists_sink (hf.mono_set ((Finset.erase_subset _ _).trans hYU))
    (show (Y.erase b).Nonempty by rw [← Finset.card_pos, Finset.card_erase_of_mem hb, hY]; omega)
    (by rw [Finset.card_erase_of_mem hb, hY])
  have hyb : D y b = true := by
    by_contra hn
    have hsub : outN D (X ∪ Y ∪ Z) y ⊆ Z.erase z := by
      intro v hv
      obtain ⟨hvU, hyv⟩ := mem_outN.mp hv
      rcases Finset.mem_union.mp hvU with hvXY | hvZ
      · rcases Finset.mem_union.mp hvXY with hvX | hvY
        · exact (hnoX y hy v hvX hyv).elim
        · by_cases hvb : v = b
          · exact (hn (hvb ▸ hyv)).elim
          · exact (hys v (Finset.mem_erase.mpr ⟨hvb, hvY⟩) hyv).elim
      · exact Finset.mem_erase.mpr ⟨fun h => hnoZ y hy (h ▸ hyv), hvZ⟩
    have hc := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem hz, hZ] at hc
    have hh := hhighY y (Finset.mem_of_mem_erase hy)
    omega
  exact hf a 4 (by decide) (by omega)
    (.step (hYU (Finset.mem_of_mem_erase hy)) (hall a (self_mem_ball ha) y hy)
      (.step (hYU hb) hyb (.step (hZU hz) hbz (.step (hXU ha) hza (.refl a)))))

/-- With a cyclic first set, every third-set arc stays out of the preceding two sets. -/
theorem cyclic_triple_no_back (hs : 6 ≤ s)
    (hf : QFree D (X ∪ Y ∪ Z) (s - 1)) (hXY : Disjoint X Y)
    (houter : Disjoint (X ∪ Y) Z)
    (hX : X.card = s) (hY : Y.card = s) (hZ : Z.card = s)
    (hhighX : ∀ x ∈ X, s ≤ (outN D (X ∪ Y) x).card)
    (hhighY : ∀ y ∈ Y, s ≤ (outN D (X ∪ Y ∪ Z) y).card)
    (hlowZ : ∀ z ∈ Z, 1 ≤ (outN D (X ∪ Y ∪ Z) z).card)
    (hint : ∀ x ∈ X, 1 ≤ (outN D X x).card)
    (hparents : ∀ z ∈ Z, ∃ y ∈ Y, D y z = true) :
    ∀ z ∈ Z, ∀ v ∈ X ∪ Y, ¬ D z v = true := by
  classical
  have hXU : X ⊆ X ∪ Y ∪ Z := Finset.subset_union_left.trans Finset.subset_union_left
  have hYU : Y ⊆ X ∪ Y ∪ Z := Finset.subset_union_right.trans Finset.subset_union_left
  have hZU : Z ⊆ X ∪ Y ∪ Z := Finset.subset_union_right
  have hYZ : Disjoint Y Z := houter.mono_left Finset.subset_union_right
  have hnoZX := cyclic_first_no_third_to_first hs hf hXY hX hY hZ hhighX hhighY hint hparents
  have hnoZY : ∀ z ∈ Z, ∀ y ∈ Y, ¬ D z y = true := by
    by_cases hb : ∃ b ∈ Y, ∃ a ∈ X, D b a = true
    · obtain ⟨b, hb, a, ha, hba⟩ := hb
      obtain ⟨hall, hnoYX, hnoYb⟩ := cyclic_back_arc_others (by omega)
        (hf.mono_set Finset.subset_union_left) hXY hX hY hhighX hint hb ha hba
      have hnoZb : ∀ z ∈ Z, ¬ D z b = true := by
        intro z hz hzb
        obtain ⟨y, hy, hyz⟩ := hparents z hz
        by_cases hyb : y = b
        · exact digonfree hf (by omega) (hYU hb) (hZU hz) (hyb ▸ hyz) hzb
        · exact hf a 4 (by decide) (by omega)
            (.step (hYU hy) (hall y (Finset.mem_erase.mpr ⟨hyb, hy⟩))
              (.step (hZU hz) hyz (.step (hYU hb) hzb (.step (hXU ha) hba (.refl a)))))
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
