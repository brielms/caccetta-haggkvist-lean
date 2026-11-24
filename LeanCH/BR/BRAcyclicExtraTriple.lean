import LeanCH.BR.BRCyclicExtraTriple

/-! Acyclic returns with no restriction on third-set degree: the closed middle basin. -/

namespace LeanCH.BR.BRsGen

open BRq2 BRq3 BR45

variable {D : CH.Digraph} {X Y Z : Finset ℕ} {s a b z : ℕ}

/-- A parented return to an acyclic first set supplies a large closed middle set.
No cardinality or degree assumption on Z is needed. -/
theorem acyclic_parent_return_basin (hs : 6 ≤ s)
    (hf : QFree D (X ∪ Y ∪ Z) (s - 1)) (hacy : QFree D X s)
    (hXY : Disjoint X Y) (hX : X.card = s) (hY : Y.card = s)
    (hhighX : ∀ x ∈ X, s ≤ (outN D (X ∪ Y) x).card)
    (ha : a ∈ X) (hb : b ∈ Y) (hz : z ∈ Z)
    (hbz : D b z = true) (hza : D z a = true) :
    ∃ R : Finset ℕ, R ⊆ Y ∧ s - 2 ≤ R.card ∧ R.card ≤ s - 1 ∧
      R ⊆ ball D (X ∪ Y ∪ Z) a 2 ∧
      (∀ r ∈ R, ∀ y ∈ Y, D r y = true → y ∈ R) ∧
      (∀ r ∈ R, ¬ D r z = true) := by
  classical
  have hXU : X ⊆ X ∪ Y ∪ Z := Finset.subset_union_left.trans Finset.subset_union_left
  have hYU : Y ⊆ X ∪ Y ∪ Z := Finset.subset_union_right.trans Finset.subset_union_left
  have hZU : Z ⊆ X ∪ Y ∪ Z := Finset.subset_union_right
  obtain ⟨p, hlong⟩ := third_return_long_sink_path (by omega) hf hacy hX hY hhighX ha hb hz hbz hza
  have hlen : p.len < s := by have := p.bounded; omega
  let P := (Finset.range (p.len + 1)).image p.vertex
  let E := X \ P
  let H := outN D X a
  let R := Y ∩ ball D (X ∪ Y ∪ Z) a 2
  have hPX : P ⊆ X := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    exact p.mem i (by have := Finset.mem_range.mp hi; omega)
  have hPc : P.card = p.len + 1 :=
    (Finset.card_image_of_injOn (p.injective hacy hX.le)).trans (Finset.card_range _)
  have hEc : E.card = s - (p.len + 1) := by
    change (X \ P).card = s - (p.len + 1)
    rw [Finset.card_sdiff_of_subset hPX, hX, hPc]
  have hPget : ∀ x ∈ P, ∃ i, i ≤ p.len ∧ p.vertex i = x := by
    intro x hx
    obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp hx
    exact ⟨i, by have := Finset.mem_range.mp hi; omega, heq⟩
  have hHsub : H ⊆ insert (p.vertex 1) E := by
    intro x hx
    obtain ⟨hxX, hax⟩ := mem_outN.mp hx
    by_cases hxP : x ∈ P
    · obtain ⟨i, hi, rfl⟩ := hPget x hxP
      have he : D (p.vertex 0) (p.vertex i) = true := by simpa only [p.start] using hax
      have hi1 := p.no_chord hacy hX.le (Nat.zero_le _) hi he
      simpa only [Nat.zero_add, hi1] using Finset.mem_insert_self (p.vertex 1) E
    · exact Finset.mem_insert_of_mem (Finset.mem_sdiff.mpr ⟨hxX, hxP⟩)
  have hHcap := (Finset.card_le_card hHsub).trans (Finset.card_insert_le _ _)
  have hRY : R ⊆ Y := Finset.inter_subset_left
  have hRball : R ⊆ ball D (X ∪ Y ∪ Z) a 2 := Finset.inter_subset_right
  have hbR : b ∉ R := by
    intro hbR
    obtain ⟨_, m, hm, w⟩ := mem_ball.mp (hRball hbR)
    exact hf a (m + 1 + 1) (by omega) (by omega)
      ((w.snoc (hZU hz) hbz).snoc (hXU ha) hza)
  have hRsub : R ⊆ Y.erase b := fun _ hr =>
    Finset.mem_erase.mpr ⟨fun h => hbR (h ▸ hr), hRY hr⟩
  have hRhi : R.card ≤ s - 1 := by
    have := Finset.card_le_card hRsub
    rwa [Finset.card_erase_of_mem hb, hY] at this
  have hnoZ : ∀ r ∈ R, ¬ D r z = true := by
    intro r hr hrz
    obtain ⟨_, m, hm, w⟩ := mem_ball.mp (hRball hr)
    exact hf a (m + 1 + 1) (by omega) (by omega)
      ((w.snoc (hZU hz) hrz).snoc (hXU ha) hza)
  have hnoB : ∀ r ∈ R, ¬ D r b = true := by
    intro r hr hrb
    obtain ⟨_, m, hm, w⟩ := mem_ball.mp (hRball hr)
    exact hf a (m + 1 + 1 + 1) (by omega) (by omega)
      (((w.snoc (hYU hb) hrb).snoc (hZU hz) hbz).snoc (hXU ha) hza)
  have hdirect : outN D Y a ⊆ R := by
    intro y hy
    obtain ⟨hyY, hay⟩ := mem_outN.mp hy
    exact Finset.mem_inter.mpr ⟨hyY, mem_ball_of_walk
      (.step (hYU hyY) hay (.refl y)) (by decide : 1 ≤ 2) (hYU hyY)⟩
  have hlarge : 3 ≤ H.card → s - 1 ≤ R.card := by
    intro hH3
    have hp : p.len = s - 3 := by omega
    have hE2 : E.card = 2 := by omega
    have hspan : H = insert (p.vertex 1) E := Finset.eq_of_subset_of_card_le hHsub
      ((Finset.card_insert_le _ _).trans (by omega))
    obtain ⟨w, hw, hws⟩ := exists_sink (hacy.mono_set (outN_subset (D := D) (W := X) (y := a)))
      (Finset.card_pos.mp (by omega : 0 < H.card)) (by change H.card ≤ s; omega)
    have hwX : w ∈ X := outN_subset hw
    have haw : D a w = true := (mem_outN.mp hw).2
    have hwcap : (outN D X w).card ≤ 1 := by
      have hsub : outN D X w ⊆ {p.vertex 2} := by
        intro x hx
        obtain ⟨hxX, hwx⟩ := mem_outN.mp hx
        by_cases hxP : x ∈ P
        · obtain ⟨j, hj, rfl⟩ := hPget x hxP
          have hmin := p.minimal (p.vertex p.len) (p.mem _ le_rfl) p.sink
            (p.len - j + 1 + 1)
            (.step hwX haw (.step (p.mem j hj) hwx (p.walk hj le_rfl)))
          have hj0 : j ≠ 0 := by
            intro heq
            have hwa : D w a = true := by simpa only [heq, p.start] using hwx
            exact digonfree hacy (by omega) ha hwX haw hwa
          have hj1 : j ≠ 1 := by
            intro heq
            have hp1H : p.vertex 1 ∈ H := hspan.symm ▸ Finset.mem_insert_self _ _
            exact hws _ hp1H (heq ▸ hwx)
          exact Finset.mem_singleton.mpr (congrArg p.vertex (by omega : j = 2))
        · have hxH : x ∈ H := hspan.symm ▸
            Finset.mem_insert_of_mem (Finset.mem_sdiff.mpr ⟨hxX, hxP⟩)
          exact (hws x hxH hwx).elim
      exact (Finset.card_le_card hsub).trans (by simp)
    have hwb : ¬ D w b = true := by
      intro hwb
      exact hf a 4 (by decide) (by omega)
        (.step (hXU hwX) haw (.step (hYU hb) hwb (.step (hZU hz) hbz
          (.step (hXU ha) hza (.refl a)))))
    have hsubY : outN D Y w ⊆ Y.erase b := by
      intro y hy
      obtain ⟨hyY, hwy⟩ := mem_outN.mp hy
      exact Finset.mem_erase.mpr ⟨fun h => hwb (h ▸ hwy), hyY⟩
    have hfull : outN D Y w = Y.erase b := Finset.eq_of_subset_of_card_le hsubY (by
      rw [Finset.card_erase_of_mem hb, hY]
      have hh := hhighX w hwX
      rw [card_outN_union hXY] at hh
      omega)
    have hsubR : Y.erase b ⊆ R := by
      intro y hy
      have hyY := Finset.mem_of_mem_erase hy
      exact Finset.mem_inter.mpr ⟨hyY, mem_ball_of_walk
        (.step (hXU hwX) haw (.step (hYU hyY) (mem_outN.mp (hfull.symm ▸ hy)).2 (.refl y)))
        le_rfl (hYU hyY)⟩
    have := Finset.card_le_card hsubR
    rwa [Finset.card_erase_of_mem hb, hY] at this
  have hsmall : H.card ≤ 2 → s - 2 ≤ (outN D Y a).card := by
    intro hc
    have hh := hhighX a ha
    rw [card_outN_union hXY] at hh
    change (outN D X a).card ≤ 2 at hc
    omega
  have hRlo : s - 2 ≤ R.card := by
    by_cases hh : 3 ≤ H.card
    · have := hlarge hh; omega
    · have := (hsmall (by omega)).trans (Finset.card_le_card hdirect)
      omega
  have hclosed : ∀ r ∈ R, ∀ y ∈ Y, D r y = true → y ∈ R := by
    by_cases hfull : R.card = s - 1
    · have heq : R = Y.erase b := Finset.eq_of_subset_of_card_le hRsub
        (by rw [Finset.card_erase_of_mem hb, hY, hfull])
      intro r hr y hy hry
      exact heq.symm ▸ Finset.mem_erase.mpr ⟨fun h => hnoB r hr (h ▸ hry), hy⟩
    · have hH2 : H.card ≤ 2 := by
        by_contra hn
        have := hlarge (by omega)
        omega
      have heq : outN D Y a = R := Finset.eq_of_subset_of_card_le hdirect
        (by have := hsmall hH2; omega)
      intro r hr y hy hry
      have har : D a r = true := (mem_outN.mp (heq.symm ▸ hr)).2
      exact Finset.mem_inter.mpr ⟨hy, mem_ball_of_walk
        (.step (hYU (hRY hr)) har (.step (hYU hy) hry (.refl y))) le_rfl (hYU hy)⟩
  exact ⟨R, hRY, hRlo, hRhi, hRball, hclosed, hnoZ⟩

/-- With one extra third vertex, a closed middle basin has a row heading every other third vertex. -/
theorem closed_middle_sink_tail_full_exit {c : ℕ} {R : Finset ℕ} (hs : 6 ≤ s)
    (hf : QFree D (X ∪ Y ∪ Z) (s - 1)) (hacy : QFree D X s)
    (hXY : Disjoint X Y) (hX : X.card = s) (hY : Y.card = s) (hZ : Z.card = s + 1)
    (hhighX : ∀ x ∈ X, s ≤ (outN D (X ∪ Y) x).card)
    (hhighY : ∀ y ∈ Y, s ≤ (outN D (X ∪ Y ∪ Z) y).card)
    (p : ShortestSinkPath D X c) (hlen : p.len = s - 3)
    (hRY : R ⊆ Y) (hRlo : s - 3 ≤ R.card) (hRhi : R.card ≤ s - 1)
    (hclosed : ∀ r ∈ R, ∀ y ∈ Y, D r y = true → y ∈ R)
    (hz : z ∈ Z) (hnoZ : ∀ r ∈ R, ¬ D r z = true) :
    ∃ r ∈ R, ∀ w ∈ Z.erase z, D r w = true := by
  classical
  by_contra hnot
  have hXU : X ⊆ X ∪ Y ∪ Z := Finset.subset_union_left.trans Finset.subset_union_left
  have hYU : Y ⊆ X ∪ Y ∪ Z := Finset.subset_union_right.trans Finset.subset_union_left
  have hZU : Z ⊆ X ∪ Y ∪ Z := Finset.subset_union_right
  let P := (Finset.range (p.len + 1)).image p.vertex
  let E := X \ P
  have hPX : P ⊆ X := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    exact p.mem i (by have := Finset.mem_range.mp hi; omega)
  have hPc : P.card = p.len + 1 :=
    (Finset.card_image_of_injOn (p.injective hacy hX.le)).trans (Finset.card_range _)
  have hEc : E.card = 2 := by
    change (X \ P).card = 2
    rw [Finset.card_sdiff_of_subset hPX, hX, hPc, hlen]
    omega
  have hEX : E ⊆ X := Finset.sdiff_subset
  have hPget : ∀ x ∈ P, ∃ i, i ≤ p.len ∧ p.vertex i = x := by
    intro x hx
    obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp hx
    exact ⟨i, by have := Finset.mem_range.mp hi; omega, heq⟩
  have hfull : ∀ y ∈ Y, D (p.vertex p.len) y = true := by
    have hsub : outN D (X ∪ Y) (p.vertex p.len) ⊆ Y := by
      intro y hy
      obtain ⟨hyXY, hty⟩ := mem_outN.mp hy
      rcases Finset.mem_union.mp hyXY with hyX | hyY
      · exact (p.sink y hyX hty).elim
      · exact hyY
    have heq := Finset.eq_of_subset_of_card_le hsub
      (by rw [hY]; exact hhighX _ (p.mem _ le_rfl))
    intro y hy
    exact (mem_outN.mp (heq.symm ▸ hy)).2
  have hnoP : ∀ r ∈ R, ∀ x ∈ P, ¬ D r x = true := by
    intro r hr x hx hrx
    obtain ⟨i, hi, rfl⟩ := hPget x hx
    exact hf (p.vertex i) (p.len - i + 1 + 1) (by omega) (by omega)
      ((((p.walk hi le_rfl).mono hXU).snoc (hYU (hRY hr)) (hfull r (hRY hr))).snoc
        (hXU (p.mem i hi)) hrx)
  have hminR : ∀ r ∈ R, 1 ≤ (outN D (R ∪ E) r).card := by
    intro r hr
    have hsub : outN D (X ∪ Y ∪ Z) r ⊆ outN D (R ∪ E) r ∪ Z.erase z := by
      intro v hv
      obtain ⟨hvU, hrv⟩ := mem_outN.mp hv
      rcases Finset.mem_union.mp hvU with hvXY | hvZ
      · refine Finset.mem_union_left _ (mem_outN.mpr ⟨?_, hrv⟩)
        rcases Finset.mem_union.mp hvXY with hvX | hvY
        · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hvX, fun hvP => hnoP r hr v hvP hrv⟩)
        · exact Finset.mem_union_left _ (hclosed r hr v hvY hrv)
      · exact Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨fun h => hnoZ r hr (h ▸ hrv), hvZ⟩)
    by_contra hn
    have hempty : outN D (R ∪ E) r = ∅ := Finset.card_eq_zero.mp (by omega)
    have hsubS : outN D (X ∪ Y ∪ Z) r ⊆ Z.erase z := by
      intro v hv
      rcases Finset.mem_union.mp (hsub hv) with hvR | hvS
      · rw [hempty] at hvR
        simp at hvR
      · exact hvS
    have heq := Finset.eq_of_subset_of_card_le hsubS (by
      rw [Finset.card_erase_of_mem hz, hZ, Nat.add_sub_cancel]
      exact hhighY r (hRY hr))
    exact hnot ⟨r, hr, fun w hw => (mem_outN.mp (heq.symm ▸ hw)).2⟩
  apply two_escape_high_return_false hs
    (hf.mono_set (Finset.union_subset (hRY.trans hYU) (hEX.trans hXU)))
    ((hXY.mono hEX hRY).symm) hRlo hRhi hEc.le hminR
  intro e he hp
  obtain ⟨r, hr, hre⟩ := hp
  have heX := hEX he
  have hcapX : (outN D X e).card ≤ 2 := by
    have hsub : outN D X e ⊆ insert (p.vertex 0) (E.erase e) := by
      intro x hx
      obtain ⟨hxX, hex⟩ := mem_outN.mp hx
      by_cases hxP : x ∈ P
      · obtain ⟨i, hi, rfl⟩ := hPget x hxP
        have hi0 : i = 0 := by
          by_contra hn
          have wt := (((p.walk hi le_rfl).mono hXU).snoc (hYU (hRY hr))
            (hfull r (hRY hr))).snoc (hXU heX) hre
          exact hf e (p.len - i + 1 + 1 + 1) (by omega) (by omega)
            (.step (hXU (p.mem i hi)) hex wt)
        simp only [hi0, Finset.mem_insert, true_or]
      · exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr
          ⟨fun h => loopfree hacy (by omega) heX (h ▸ hex), Finset.mem_sdiff.mpr ⟨hxX, hxP⟩⟩)
    have hc := (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
    rw [Finset.card_erase_of_mem he, hEc] at hc
    omega
  have hcapY : (outN D Y e).card ≤ (outN D R e).card + (Y \ R).card := by
    apply (Finset.card_le_card (show outN D Y e ⊆ outN D R e ∪ (Y \ R) from ?_)).trans
      (Finset.card_union_le _ _)
    intro y hy
    obtain ⟨hyY, hey⟩ := mem_outN.mp hy
    by_cases hyR : y ∈ R
    · exact Finset.mem_union_left _ (mem_outN.mpr ⟨hyR, hey⟩)
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hyY, hyR⟩)
  rw [Finset.card_sdiff_of_subset hRY, hY] at hcapY
  have hh := hhighX e heX
  rw [card_outN_union hXY] at hh
  omega

/-- A parented acyclic return reaches every other third vertex within three steps. -/
theorem acyclic_one_extra_return_funnel (hs : 6 ≤ s)
    (hf : QFree D (X ∪ Y ∪ Z) (s - 1)) (hacy : QFree D X s)
    (hXY : Disjoint X Y) (hX : X.card = s) (hY : Y.card = s) (hZ : Z.card = s + 1)
    (hhighX : ∀ x ∈ X, s ≤ (outN D (X ∪ Y) x).card)
    (hhighY : ∀ y ∈ Y, s ≤ (outN D (X ∪ Y ∪ Z) y).card)
    (ha : a ∈ X) (hb : b ∈ Y) (hz : z ∈ Z)
    (hbz : D b z = true) (hza : D z a = true) :
    ∀ w ∈ Z.erase z, ∃ m, 1 ≤ m ∧ m ≤ 3 ∧ Walk D (X ∪ Y ∪ Z) a w m := by
  obtain ⟨R, hRY, hRlo, hRhi, hRball, hclosed, hnoZ⟩ :=
    acyclic_parent_return_basin hs hf hacy hXY hX hY hhighX ha hb hz hbz hza
  obtain ⟨p, hlong⟩ :=
    third_return_long_sink_path (by omega) hf hacy hX hY hhighX ha hb hz hbz hza
  let t := p.suffix (i := p.len - (s - 3)) (Nat.sub_le _ _)
  have htlen : t.len = s - 3 := by
    change p.len - (p.len - (s - 3)) = s - 3
    omega
  obtain ⟨r, hr, hrfull⟩ := closed_middle_sink_tail_full_exit hs hf hacy hXY hX hY hZ
    hhighX hhighY t htlen hRY (by omega) hRhi hclosed hz hnoZ
  obtain ⟨_, m, hm, wm⟩ := mem_ball.mp (hRball hr)
  intro w hw
  exact ⟨m + 1, by omega, by omega,
    wm.snoc (Finset.mem_union_right _ (Finset.mem_of_mem_erase hw)) (hrfull w hw)⟩

/-- A third vertex returning to an acyclic first set has no parent in its own set.
The degree-two hypothesis on Z is not needed for this restriction. -/
theorem acyclic_one_extra_return_no_third_parent (hs : 6 ≤ s)
    (hf : QFree D (X ∪ Y ∪ Z) (s - 1)) (hacy : QFree D X s)
    (hXY : Disjoint X Y) (hX : X.card = s) (hY : Y.card = s) (hZ : Z.card = s + 1)
    (hhighX : ∀ x ∈ X, s ≤ (outN D (X ∪ Y) x).card)
    (hhighY : ∀ y ∈ Y, s ≤ (outN D (X ∪ Y ∪ Z) y).card)
    (ha : a ∈ X) (hb : b ∈ Y) (hz : z ∈ Z)
    (hbz : D b z = true) (hza : D z a = true) :
    ∀ w ∈ Z, ¬ D w z = true := by
  intro w hw hwz
  by_cases hwzEq : w = z
  · exact loopfree hf (by omega) (Finset.mem_union_right _ hz) (hwzEq ▸ hwz)
  · obtain ⟨m, hm, hm3, wm⟩ := acyclic_one_extra_return_funnel hs hf hacy hXY hX hY hZ
      hhighX hhighY ha hb hz hbz hza w (Finset.mem_erase.mpr ⟨hwzEq, hw⟩)
    exact hf a (m + 1 + 1) (by omega) (by omega)
      ((wm.snoc (Finset.mem_union_right _ hz) hwz).snoc
        (Finset.mem_union_left _ (Finset.mem_union_left _ ha)) hza)

/-- Every first-return vertex in a surviving unequal triple is a source inside Z. -/
theorem OneExtraTriple.return_no_third_parent (h : OneExtraTriple D X Y Z s)
    (hz : z ∈ Z) (ha : a ∈ X) (hza : D z a = true) :
    ∀ w ∈ Z, ¬ D w z = true := by
  obtain ⟨b, hb, hbz⟩ := h.parents z hz
  exact acyclic_one_extra_return_no_third_parent h.large h.free h.acyclic_first
    h.disjoint_first h.card_first h.card_second h.card_third
    h.high_first h.high_second ha hb hz hbz hza

/-- The remaining return exclusion, restricted to sources inside the third set. UNPROVED. -/
def OneExtraSourceReturnExcluded : Prop :=
  ∀ s D X Y Z, OneExtraTriple D X Y Z s → QFree D X s →
    ∀ z ∈ Z, ∀ a ∈ X, (∀ w ∈ Z, ¬ D w z = true) → ¬ D z a = true

/-- Both proved restrictions are consumed in the next structural goal. -/
theorem one_extra_impossible_iff_source_return_excluded :
    OneExtraTripleImpossible ↔ OneExtraSourceReturnExcluded := by
  rw [one_extra_impossible_iff_acyclic_return_excluded]
  refine ⟨fun h s D X Y Z hc hacy z hz a ha _ => h s D X Y Z hc hacy z hz a ha, ?_⟩
  intro h s D X Y Z hc hacy z hz a ha hza
  exact h s D X Y Z hc hacy z hz a ha (hc.return_no_third_parent hz ha hza) hza

end LeanCH.BR.BRsGen

