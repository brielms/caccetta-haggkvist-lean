import LeanCH.BR.BRExtraTripleTargets

/-! The cyclic-first branch of the unequal-triple target is impossible. -/

namespace LeanCH.BR.BRsGen

open BRq2 BRq3 BR45

/-- The first unequal third layer cannot have positive internal degree everywhere in X. -/
theorem OneExtraTriple.cyclic_false {s D X Y Z} (h : OneExtraTriple D X Y Z s)
    (hint : ∀ x ∈ X, 1 ≤ (outN D X x).card) : False := by
  classical
  have hs := h.large
  have hf := h.free
  have hXU : X ⊆ X ∪ Y ∪ Z := Finset.subset_union_left.trans Finset.subset_union_left
  have hYU : Y ⊆ X ∪ Y ∪ Z := Finset.subset_union_right.trans Finset.subset_union_left
  have hZU : Z ⊆ X ∪ Y ∪ Z := Finset.subset_union_right
  have hfX := hf.mono_set hXU
  have hreg := (dt_reg (by omega : 1 ≤ s - 1) (ball_q_one _ (by omega)) hfX hint
    (by rw [h.card_first]; omega)).1
  obtain ⟨z, hz, a, ha, hza⟩ := h.forced_return
  obtain ⟨b, hb, hbz⟩ := h.parents z hz
  let R := Y.erase b
  let S := Z.erase z
  have hRY : R ⊆ Y := Finset.erase_subset _ _
  have hSZ : S ⊆ Z := Finset.erase_subset _ _
  have hRU : R ⊆ X ∪ Y ∪ Z := hRY.trans hYU
  have hSU : S ⊆ X ∪ Y ∪ Z := hSZ.trans hZU
  have hRSU : R ∪ S ⊆ X ∪ Y ∪ Z := Finset.union_subset hRU hSU
  have hRc : R.card = s - 1 := by simp only [R, Finset.card_erase_of_mem hb, h.card_second]
  have hSc : S.card = s := by simp only [S, Finset.card_erase_of_mem hz, h.card_third, Nat.add_sub_cancel]
  have hRS : Disjoint R S :=
    (h.disjoint_third.mono_left Finset.subset_union_right).mono hRY hSZ
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
  have hall : ∀ x ∈ A, ∀ y ∈ R, D x y = true := by
    intro x hx
    have hsub : outN D Y x ⊆ R := by
      intro y hy
      obtain ⟨hyY, hxy⟩ := mem_outN.mp hy
      exact Finset.mem_erase.mpr ⟨fun heq => hmiss x hx (heq ▸ hxy), hyY⟩
    have heq := Finset.eq_of_subset_of_card_le hsub (by
      rw [hRc]
      have hh := h.high_first x (hAX hx)
      rw [card_outN_union h.disjoint_first, hreg x (hAX hx)] at hh
      omega)
    intro y hy
    exact (mem_outN.mp (heq.symm ▸ hy)).2
  have haR : ∀ y ∈ R, D a y = true := hall a (self_mem_ball ha)
  have hnear : ∀ x ∈ X, ∃ v ∈ A, v ∈ ball D X x 3 := by
    intro x hx
    have hc := ball_one_growth hfX hint hx 3 (by omega)
    have hi : (A ∩ ball D X x 3).Nonempty := by
      by_contra hn
      have hd : Disjoint A (ball D X x 3) := Finset.disjoint_iff_inter_eq_empty.mpr
        (Finset.not_nonempty_iff_eq_empty.mp hn)
      have hu := Finset.card_le_card (Finset.union_subset hAX
        (ball_subset (D := D) (W := X) (u := x) (k := 3)))
      rw [Finset.card_union_of_disjoint hd, h.card_first] at hu
      omega
    obtain ⟨v, hv⟩ := hi
    exact ⟨v, (Finset.mem_inter.mp hv).1, (Finset.mem_inter.mp hv).2⟩
  have hnoRX : ∀ y ∈ R, ∀ x ∈ X, ¬ D y x = true := by
    intro y hy x hx hyx
    obtain ⟨v, hvA, hv⟩ := hnear x hx
    obtain ⟨_, m, hm, w⟩ := mem_ball.mp hv
    exact hf x (m + 1 + 1) (by omega) (by omega)
      (((w.mono hXU).snoc (hRU hy) (hall v hvA y hy)).snoc (hXU hx) hyx)
  have hnoRz : ∀ y ∈ R, ¬ D y z = true := by
    intro y hy hyz
    exact hf a 3 (by decide) (by omega)
      (.step (hRU hy) (haR y hy) (.step (hZU hz) hyz (.step (hXU ha) hza (.refl a))))
  have hnoRb : ∀ y ∈ R, ¬ D y b = true := by
    intro y hy hyb
    exact hf a 4 (by decide) (by omega)
      (.step (hRU hy) (haR y hy) (.step (hYU hb) hyb
        (.step (hZU hz) hbz (.step (hXU ha) hza (.refl a)))))
  have hretainR : ∀ y ∈ R, outN D (X ∪ Y ∪ Z) y ⊆ outN D (R ∪ S) y := by
    intro y hy v hv
    obtain ⟨hvU, hyv⟩ := mem_outN.mp hv
    refine mem_outN.mpr ⟨?_, hyv⟩
    rcases Finset.mem_union.mp hvU with hvXY | hvZ
    · rcases Finset.mem_union.mp hvXY with hvX | hvY
      · exact (hnoRX y hy v hvX hyv).elim
      · exact Finset.mem_union_left _
          (Finset.mem_erase.mpr ⟨fun heq => hnoRb y hy (heq ▸ hyv), hvY⟩)
    · exact Finset.mem_union_right _
        (Finset.mem_erase.mpr ⟨fun heq => hnoRz y hy (heq ▸ hyv), hvZ⟩)
  have hhighR : ∀ y ∈ R, s ≤ (outN D (R ∪ S) y).card :=
    fun y hy => (h.high_second y (hRY hy)).trans (Finset.card_le_card (hretainR y hy))
  have hentry : ∀ x ∈ X, R.card ≤ (outN D R x).card + 1 := by
    intro x hx
    have hh := h.high_first x hx
    rw [card_outN_union h.disjoint_first, hreg x hx] at hh
    have hsub : outN D Y x ⊆ insert b (outN D R x) := by
      intro v hv
      obtain ⟨hvY, hxv⟩ := mem_outN.mp hv
      by_cases hvb : v = b
      · exact Finset.mem_insert.mpr (Or.inl hvb)
      · exact Finset.mem_insert.mpr (Or.inr
          (mem_outN.mpr ⟨Finset.mem_erase.mpr ⟨hvb, hvY⟩, hxv⟩))
    have hc := (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
    omega
  have hreachS : ∀ x ∈ X, ∀ w ∈ S,
      ∃ m, 1 ≤ m ∧ m ≤ 3 ∧ Walk D (R ∪ S) x w m := by
    intro x hx
    exact almost_full_entry_funnel (hf.mono_set hRU) hRc.le (by omega) hSc hhighR (hentry x hx)
  have hnoSX : ∀ w ∈ S, ∀ x ∈ X, ¬ D w x = true := by
    intro w hw x hx hwx
    obtain ⟨m, hm, hm3, wm⟩ := hreachS x hx w hw
    exact hf x (m + 1) (by omega) (by omega) ((wm.mono hRSU).snoc (hXU hx) hwx)
  obtain ⟨r, hr, hrs⟩ := exists_sink (hf.mono_set hRU)
    (Finset.card_pos.mp (by omega : 0 < R.card)) hRc.le
  have hrfull : ∀ w ∈ S, D r w = true := by
    have hsub : outN D (R ∪ S) r ⊆ S := by
      intro v hv
      obtain ⟨hvRS, hrv⟩ := mem_outN.mp hv
      rcases Finset.mem_union.mp hvRS with hvR | hvS
      · exact (hrs v hvR hrv).elim
      · exact hvS
    have heq := Finset.eq_of_subset_of_card_le hsub (by rw [hSc]; exact hhighR r hr)
    intro w hw
    exact (mem_outN.mp (heq.symm ▸ hw)).2
  have haS : ∀ w ∈ S, Walk D (X ∪ Y ∪ Z) a w 2 :=
    fun w hw => .step (hRU hr) (haR r hr) (.step (hSU hw) (hrfull w hw) (.refl w))
  have hnoSz : ∀ w ∈ S, ¬ D w z = true := by
    intro w hw hwz
    exact hf a 4 (by decide) (by omega) (((haS w hw).snoc (hZU hz) hwz).snoc (hXU ha) hza)
  have hnoSb : ∀ w ∈ S, ¬ D w b = true := by
    intro w hw hwb
    exact hf a 5 (by decide) (by omega)
      ((((haS w hw).snoc (hYU hb) hwb).snoc (hZU hz) hbz).snoc (hXU ha) hza)
  have hretainS : ∀ w ∈ S, outN D (X ∪ Y ∪ Z) w ⊆ outN D (R ∪ S) w := by
    intro w hw v hv
    obtain ⟨hvU, hwv⟩ := mem_outN.mp hv
    refine mem_outN.mpr ⟨?_, hwv⟩
    rcases Finset.mem_union.mp hvU with hvXY | hvZ
    · rcases Finset.mem_union.mp hvXY with hvX | hvY
      · exact (hnoSX w hw v hvX hwv).elim
      · exact Finset.mem_union_left _
          (Finset.mem_erase.mpr ⟨fun heq => hnoSb w hw (heq ▸ hwv), hvY⟩)
    · exact Finset.mem_union_right _
        (Finset.mem_erase.mpr ⟨fun heq => hnoSz w hw (heq ▸ hwv), hvZ⟩)
  have hmin : ∀ v ∈ R ∪ S, 2 ≤ (outN D (R ∪ S) v).card := by
    intro v hv
    rcases Finset.mem_union.mp hv with hvR | hvS
    · exact (by omega : 2 ≤ s).trans (hhighR v hvR)
    · exact (h.low_third v (hSZ hvS)).trans (Finset.card_le_card (hretainS v hvS))
  have hc : (R ∪ S).card = (s - 1) + s := by
    rw [Finset.card_union_of_disjoint hRS, hRc, hSc]
  exact two_core_many_high_false (by omega : 1 ≤ s - 1) (hf.mono_set hRSU)
    (by omega) hmin (H := R) Finset.subset_union_left (by omega)
    (fun v hv => (by omega : 5 ≤ s).trans (hhighR v hv))

/-- Any surviving unequal triple has an acyclic first set. -/
theorem OneExtraTriple.acyclic_first {s D X Y Z} (h : OneExtraTriple D X Y Z s) :
    QFree D X s := by
  classical
  have hs := h.large
  have hn : ¬ ∀ x ∈ X, 1 ≤ (outN D X x).card := h.cyclic_false
  push Not at hn
  obtain ⟨t, ht, htc⟩ := hn
  have hsink : ∀ v ∈ X, ¬ D t v = true := by
    intro v hv htv
    have := Finset.card_pos.mpr ⟨v, mem_outN.mpr ⟨hv, htv⟩⟩
    omega
  have hfX := h.free.mono_set
    (Finset.subset_union_left.trans Finset.subset_union_left : X ⊆ X ∪ Y ∪ Z)
  have hacy := qfree_succ_of_sink hfX (by rw [h.card_first]; omega) ht hsink
  simpa only [Nat.sub_add_cancel (by omega : 1 ≤ s)] using hacy

/-- The remaining unequal-triple research target. UNPROVED. -/
def OneExtraAcyclicReturnExcluded : Prop :=
  ∀ s D X Y Z, OneExtraTriple D X Y Z s → QFree D X s →
    ∀ z ∈ Z, ∀ a ∈ X, ¬ D z a = true

/-- The cyclic branch has been discharged; the target is now exactly its acyclic branch. -/
theorem one_extra_impossible_iff_acyclic_return_excluded :
    OneExtraTripleImpossible ↔ OneExtraAcyclicReturnExcluded := by
  rw [one_extra_impossible_iff_return_excluded]
  refine ⟨fun h s D X Y Z hc _ => h s D X Y Z hc, ?_⟩
  intro h s D X Y Z hc
  exact h s D X Y Z hc hc.acyclic_first

end LeanCH.BR.BRsGen
