import LeanCH.BR.BRCyclicTriple

/-! Control from one parented return into a cyclic first set, independent of third-set size. -/

namespace LeanCH.BR.BRsGen

open BRq2 BRq3 BR45

variable {D : CH.Digraph} {X Y Z : Finset ℕ} {s a b z : ℕ}

theorem cyclic_parent_return_control (hs : 6 ≤ s)
    (hf : QFree D (X ∪ Y ∪ Z) (s - 1)) (hXY : Disjoint X Y)
    (hX : X.card = s) (hY : Y.card = s)
    (hhighX : ∀ x ∈ X, s ≤ (outN D (X ∪ Y) x).card)
    (hint : ∀ x ∈ X, 1 ≤ (outN D X x).card)
    (ha : a ∈ X) (hb : b ∈ Y) (hz : z ∈ Z) (hbz : D b z = true) (hza : D z a = true) :
    (∀ y ∈ Y.erase b, D a y = true) ∧
    (∀ y ∈ Y.erase b, ∀ x ∈ X, ¬ D y x = true) ∧
    (∀ y ∈ Y.erase b, ¬ D y b = true) ∧
    (∀ y ∈ Y.erase b, ¬ D y z = true) := by
  classical
  have hXU : X ⊆ X ∪ Y ∪ Z := Finset.subset_union_left.trans Finset.subset_union_left
  have hYU : Y ⊆ X ∪ Y ∪ Z := Finset.subset_union_right.trans Finset.subset_union_left
  have hZU : Z ⊆ X ∪ Y ∪ Z := Finset.subset_union_right
  have hfX := hf.mono_set hXU
  have hreg := (dt_reg (by omega : 1 ≤ s - 1) (ball_q_one _ (by omega)) hfX hint
    (by rw [hX]; omega)).1
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
  refine ⟨hall a (self_mem_ball ha), ?_, ?_, ?_⟩
  · intro y hy x hx hyx
    obtain ⟨v, hvA, hv⟩ := hnear x hx
    obtain ⟨_, m, hm, w⟩ := mem_ball.mp hv
    exact hf x (m + 1 + 1) (by omega) (by omega)
      (((w.mono hXU).snoc (hYU (Finset.mem_of_mem_erase hy)) (hall v hvA y hy)).snoc (hXU hx) hyx)
  · intro y hy hyb
    exact hf a 4 (by decide) (by omega)
      (.step (hYU (Finset.mem_of_mem_erase hy)) (hall a (self_mem_ball ha) y hy)
        (.step (hYU hb) hyb (.step (hZU hz) hbz (.step (hXU ha) hza (.refl a)))))
  · intro y hy hyz
    exact hf a 3 (by decide) (by omega)
      (.step (hYU (Finset.mem_of_mem_erase hy)) (hall a (self_mem_ball ha) y hy)
        (.step (hZU hz) hyz (.step (hXU ha) hza (.refl a))))

/-- The unique exceptional middle label receives no third-set arc. -/
theorem parented_return_no_third_parent_label (hs : 6 ≤ s)
    (hf : QFree D (X ∪ Y ∪ Z) (s - 1))
    (ha : a ∈ X) (hb : b ∈ Y) (hz : z ∈ Z) (hbz : D b z = true) (hza : D z a = true)
    (hall : ∀ y ∈ Y.erase b, D a y = true)
    (hparents : ∀ w ∈ Z, ∃ y ∈ Y, D y w = true) :
    ∀ w ∈ Z, ¬ D w b = true := by
  have hXU : X ⊆ X ∪ Y ∪ Z := Finset.subset_union_left.trans Finset.subset_union_left
  have hYU : Y ⊆ X ∪ Y ∪ Z := Finset.subset_union_right.trans Finset.subset_union_left
  have hZU : Z ⊆ X ∪ Y ∪ Z := Finset.subset_union_right
  intro w hw hwb
  obtain ⟨y, hy, hyw⟩ := hparents w hw
  by_cases hyb : y = b
  · exact digonfree hf (by omega) (hYU hb) (hZU hw) (hyb ▸ hyw) hwb
  · exact hf a 5 (by decide) (by omega)
      (.step (hYU hy) (hall y (Finset.mem_erase.mpr ⟨hyb, hy⟩))
        (.step (hZU hw) hyw (.step (hYU hb) hwb
          (.step (hZU hz) hbz (.step (hXU ha) hza (.refl a))))))

end LeanCH.BR.BRsGen
