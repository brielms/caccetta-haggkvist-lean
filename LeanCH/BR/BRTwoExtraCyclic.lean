import LeanCH.BR.BRTwoExtraTriple
import LeanCH.BR.BRCyclicReturnControl

/-! The cyclic branch of the third-layer excess-two target. -/

namespace LeanCH.BR.BRsGen

open BRq2 BRq3 BR45

variable {D : CH.Digraph} {X Y Z : Finset ℕ} {s : ℕ}

theorem TwoExtraTriple.forced_return (h : TwoExtraTriple D X Y Z s) :
    ∃ z ∈ Z, ∃ a ∈ X, D z a = true := by
  classical
  have hs := h.large
  have hf := h.free
  have hX := h.card_first
  have hY := h.card_second
  have hZ := h.card_third
  by_contra hn
  have hnoZX : ∀ z ∈ Z, ∀ x ∈ X, ¬ D z x = true :=
    fun z hz x hx hzx => hn ⟨z, hz, x, hx, hzx⟩
  have hXU : X ⊆ X ∪ Y ∪ Z := Finset.subset_union_left.trans Finset.subset_union_left
  have hYU : Y ⊆ X ∪ Y ∪ Z := Finset.subset_union_right.trans Finset.subset_union_left
  have hZU : Z ⊆ X ∪ Y ∪ Z := Finset.subset_union_right
  have hZne : Z.Nonempty := Finset.card_pos.mp (by omega)
  by_cases hb : ∃ b ∈ Y, ∃ a ∈ X, D b a = true
  · obtain ⟨b, hb, a, ha, hba⟩ := hb
    obtain ⟨hreach, hnoYX, hnoYb⟩ := first_back_arc_control hs
      (hf.mono_set Finset.subset_union_left) h.disjoint_first hX hY h.high_first ha hb hba
    have hnoZb : ∀ z ∈ Z, ¬ D z b = true := by
      intro z hz hzb
      obtain ⟨y, hy, hyz⟩ := h.parents z hz
      by_cases hyb : y = b
      · exact digonfree hf (by omega) (hYU hb) (hZU hz) (hyb ▸ hyz) hzb
      · obtain ⟨m, hm, w⟩ := hreach y (Finset.mem_erase.mpr ⟨hyb, hy⟩)
        exact hf a (m + 1 + 1 + 1) (by omega) (by omega)
          ((((w.mono Finset.subset_union_left).snoc (hZU hz) hyz).snoc (hYU hb) hzb).snoc (hXU ha) hba)
    let R := Y.erase b
    have hRU : R ⊆ X ∪ Y ∪ Z := (Finset.erase_subset _ _).trans hYU
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
    have hmin : ∀ v ∈ R ∪ Z, 3 ≤ (outN D (R ∪ Z) v).card := by
      intro v hv
      have hc := Finset.card_le_card (hretain v hv)
      rcases Finset.mem_union.mp hv with hvR | hvZ
      · have := h.high_second v (Finset.mem_of_mem_erase hvR); omega
      · exact (h.low_third v hvZ).trans hc
    have hsize := dt_size (by omega : 1 ≤ s - 1) (BRq3.ball_all _ (by omega))
      (hf.mono_set (Finset.union_subset hRU hZU)) hmin (hZne.mono Finset.subset_union_right)
    have hc := Finset.card_union_le R Z
    omega
  · have hnoYX : ∀ y ∈ Y, ∀ x ∈ X, ¬ D y x = true :=
      fun y hy x hx hyx => hb ⟨y, hy, x, hx, hyx⟩
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
    have hmin : ∀ v ∈ Y ∪ Z, 3 ≤ (outN D (Y ∪ Z) v).card := by
      intro v hv
      have hc := Finset.card_le_card (hretain v hv)
      rcases Finset.mem_union.mp hv with hvY | hvZ
      · have := h.high_second v hvY; omega
      · exact (h.low_third v hvZ).trans hc
    have hsize := dt_size (by omega : 1 ≤ s - 1) (BRq3.ball_all _ (by omega))
      (hf.mono_set (Finset.union_subset hYU hZU)) hmin (hZne.mono Finset.subset_union_right)
    have hc := Finset.card_union_le Y Z
    omega

/-- Two first returns cannot have distinct middle-layer parent labels. -/
theorem TwoExtraTriple.cyclic_return_parent_unique (h : TwoExtraTriple D X Y Z s)
    (hint : ∀ x ∈ X, 1 ≤ (outN D X x).card)
    {a b z a' c w : ℕ}
    (ha : a ∈ X) (hb : b ∈ Y) (hz : z ∈ Z) (hbz : D b z = true) (hza : D z a = true)
    (ha' : a' ∈ X) (hc : c ∈ Y) (hw : w ∈ Z) (hcw : D c w = true) (hwa : D w a' = true) :
    c = b := by
  classical
  by_contra hcb
  have hs := h.large
  have hf := h.free
  have hX := h.card_first
  have hY := h.card_second
  have hZ := h.card_third
  have hXU : X ⊆ X ∪ Y ∪ Z := Finset.subset_union_left.trans Finset.subset_union_left
  have hYU : Y ⊆ X ∪ Y ∪ Z := Finset.subset_union_right.trans Finset.subset_union_left
  have hZU : Z ⊆ X ∪ Y ∪ Z := Finset.subset_union_right
  obtain ⟨hall, hnoX, hnoB, hnoZ⟩ := cyclic_parent_return_control hs hf h.disjoint_first
    hX hY h.high_first hint ha hb hz hbz hza
  obtain ⟨hall', hnoX', hnoC, hnoW⟩ := cyclic_parent_return_control hs hf h.disjoint_first
    hX hY h.high_first hint ha' hc hw hcw hwa
  have hnoZb := parented_return_no_third_parent_label hs hf ha hb hz hbz hza hall h.parents
  have hnoZc := parented_return_no_third_parent_label hs hf ha' hc hw hcw hwa hall' h.parents
  have hwz : w ≠ z := fun heq => hnoZ c (Finset.mem_erase.mpr ⟨hcb, hc⟩) (heq ▸ hcw)
  let Q := (Y.erase b).erase c
  let S := (Z.erase z).erase w
  have hQb : Q ⊆ Y.erase b := Finset.erase_subset _ _
  have hQY : Q ⊆ Y := hQb.trans (Finset.erase_subset _ _)
  have hQc : Q ⊆ Y.erase c := by
    intro v hv
    exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hv).1, hQY hv⟩
  have hSZ : S ⊆ Z := (Finset.erase_subset _ _).trans (Finset.erase_subset _ _)
  have hQU := hQY.trans hYU
  have hSU := hSZ.trans hZU
  have hQSU : Q ∪ S ⊆ X ∪ Y ∪ Z := Finset.union_subset hQU hSU
  have hQcard : Q.card = s - 2 := by
    dsimp only [Q]
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hcb, hc⟩),
      Finset.card_erase_of_mem hb, hY]
    omega
  have hScard : S.card = s := by
    dsimp only [S]
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hwz, hw⟩),
      Finset.card_erase_of_mem hz, hZ]
    omega
  have hhighQ : ∀ v ∈ Q, s ≤ (outN D (Q ∪ S) v).card := by
    intro v hv
    apply (h.high_second v (hQY hv)).trans
    apply Finset.card_le_card
    intro t ht
    obtain ⟨htU, hvt⟩ := mem_outN.mp ht
    refine mem_outN.mpr ⟨?_, hvt⟩
    rcases Finset.mem_union.mp htU with htXY | htZ
    · rcases Finset.mem_union.mp htXY with htX | htY
      · exact (hnoX v (hQb hv) t htX hvt).elim
      · exact Finset.mem_union_left _ (Finset.mem_erase.mpr
          ⟨fun heq => hnoC v (hQc hv) (heq ▸ hvt), Finset.mem_erase.mpr
            ⟨fun heq => hnoB v (hQb hv) (heq ▸ hvt), htY⟩⟩)
    · exact Finset.mem_union_right _ (Finset.mem_erase.mpr
        ⟨fun heq => hnoW v (hQc hv) (heq ▸ hvt), Finset.mem_erase.mpr
          ⟨fun heq => hnoZ v (hQb hv) (heq ▸ hvt), htZ⟩⟩)
  have hreg := (dt_reg (by omega : 1 ≤ s - 1) (ball_q_one _ (by omega))
    (hf.mono_set hXU) hint (by omega : X.card = (s - 1) * 1 + 1)).1
  have hentry : ∀ x ∈ X, Q.card ≤ (outN D Q x).card + 1 := by
    intro x hx
    have hh := h.high_first x hx
    rw [card_outN_union h.disjoint_first, hreg x hx] at hh
    have hsub : outN D Y x ⊆ outN D Q x ∪ {b, c} := by
      intro t ht
      obtain ⟨htY, hxt⟩ := mem_outN.mp ht
      by_cases htb : t = b
      · exact Finset.mem_union_right _ (by simp [htb])
      · by_cases htc : t = c
        · exact Finset.mem_union_right _ (by simp [htc])
        · exact Finset.mem_union_left _ (mem_outN.mpr
            ⟨Finset.mem_erase.mpr ⟨htc, Finset.mem_erase.mpr ⟨htb, htY⟩⟩, hxt⟩)
    have hcount := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    have hpair : ({b, c} : Finset ℕ).card = 2 := by simp [Ne.symm hcb]
    rw [hpair] at hcount
    omega
  have hreach : ∀ x ∈ X, ∀ t ∈ S, ∃ m, 1 ≤ m ∧ m ≤ 3 ∧
      Walk D (X ∪ Y ∪ Z) x t m := by
    intro x hx t ht
    obtain ⟨m, hm, hm3, walk⟩ := almost_full_entry_funnel (hf.mono_set hQU)
      (by omega) (by omega) hScard hhighQ (hentry x hx) t ht
    exact ⟨m, hm, hm3, walk.mono hQSU⟩
  have hnoSX : ∀ t ∈ S, ∀ x ∈ X, ¬ D t x = true := by
    intro t ht x hx htx
    obtain ⟨m, hm, hm3, walk⟩ := hreach x hx t ht
    exact hf x (m + 1) (by omega) (by omega) (walk.snoc (hXU hx) htx)
  have hnoSz : ∀ t ∈ S, ¬ D t z = true := by
    intro t ht htz
    obtain ⟨m, hm, hm3, walk⟩ := hreach a ha t ht
    exact hf a (m + 1 + 1) (by omega) (by omega)
      ((walk.snoc (hZU hz) htz).snoc (hXU ha) hza)
  have hnoSw : ∀ t ∈ S, ¬ D t w = true := by
    intro t ht htw
    obtain ⟨m, hm, hm3, walk⟩ := hreach a' ha' t ht
    exact hf a' (m + 1 + 1) (by omega) (by omega)
      ((walk.snoc (hZU hw) htw).snoc (hXU ha') hwa)
  have hlowS : ∀ t ∈ S, 3 ≤ (outN D (Q ∪ S) t).card := by
    intro t ht
    apply (h.low_third t (hSZ ht)).trans
    apply Finset.card_le_card
    intro v hv
    obtain ⟨hvU, htv⟩ := mem_outN.mp hv
    refine mem_outN.mpr ⟨?_, htv⟩
    rcases Finset.mem_union.mp hvU with hvXY | hvZ
    · rcases Finset.mem_union.mp hvXY with hvX | hvY
      · exact (hnoSX t ht v hvX htv).elim
      · exact Finset.mem_union_left _ (Finset.mem_erase.mpr
          ⟨fun heq => hnoZc t (hSZ ht) (heq ▸ htv), Finset.mem_erase.mpr
            ⟨fun heq => hnoZb t (hSZ ht) (heq ▸ htv), hvY⟩⟩)
    · exact Finset.mem_union_right _ (Finset.mem_erase.mpr
        ⟨fun heq => hnoSw t ht (heq ▸ htv), Finset.mem_erase.mpr
          ⟨fun heq => hnoSz t ht (heq ▸ htv), hvZ⟩⟩)
  have hmin : ∀ v ∈ Q ∪ S, 3 ≤ (outN D (Q ∪ S) v).card := by
    intro v hv
    rcases Finset.mem_union.mp hv with hvQ | hvS
    · exact (by omega : 3 ≤ s).trans (hhighQ v hvQ)
    · exact hlowS v hvS
  have hne : S.Nonempty := Finset.card_pos.mp (by omega)
  have hsize := dt_size (by omega : 1 ≤ s - 1) (BRq3.ball_all _ (by omega))
    (hf.mono_set hQSU) hmin (hne.mono Finset.subset_union_right)
  have hc := Finset.card_union_le Q S
  omega

/-- The middle vertices outside the unique return label supply a forbidden small core. -/
theorem TwoExtraTriple.cyclic_false (h : TwoExtraTriple D X Y Z s)
    (hint : ∀ x ∈ X, 1 ≤ (outN D X x).card) : False := by
  classical
  have hs := h.large
  have hf := h.free
  have hX := h.card_first
  have hY := h.card_second
  have hZ := h.card_third
  have hXU : X ⊆ X ∪ Y ∪ Z := Finset.subset_union_left.trans Finset.subset_union_left
  have hYU : Y ⊆ X ∪ Y ∪ Z := Finset.subset_union_right.trans Finset.subset_union_left
  have hZU : Z ⊆ X ∪ Y ∪ Z := Finset.subset_union_right
  obtain ⟨z, hz, a, ha, hza⟩ := h.forced_return
  obtain ⟨b, hb, hbz⟩ := h.parents z hz
  obtain ⟨hall, hnoX, hnoB, hnoZ⟩ := cyclic_parent_return_control hs hf h.disjoint_first
    hX hY h.high_first hint ha hb hz hbz hza
  have hnoZb := parented_return_no_third_parent_label hs hf ha hb hz hbz hza hall h.parents
  let R := Y.erase b
  let G := Z.filter (fun w => ∃ r ∈ R, D r w = true)
  have hRY : R ⊆ Y := Finset.erase_subset _ _
  have hRU := hRY.trans hYU
  have hGZ : G ⊆ Z := Finset.filter_subset _ _
  have hGU := hGZ.trans hZU
  have hRGU : R ∪ G ⊆ X ∪ Y ∪ Z := Finset.union_subset hRU hGU
  have hRc : R.card = s - 1 := by dsimp only [R]; rw [Finset.card_erase_of_mem hb, hY]
  have hzG : z ∉ G := by
    intro hzG
    obtain ⟨_, r, hr, hrz⟩ := Finset.mem_filter.mp hzG
    exact hnoZ r hr hrz
  have hGcUpper : G.card ≤ s + 1 := by
    have hsub : G ⊆ Z.erase z := by
      intro w hw
      exact Finset.mem_erase.mpr ⟨fun heq => hzG (heq ▸ hw), hGZ hw⟩
    have hc := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem hz, hZ] at hc
    omega
  have hhighR : ∀ r ∈ R, s ≤ (outN D (R ∪ G) r).card := by
    intro r hr
    apply (h.high_second r (hRY hr)).trans
    apply Finset.card_le_card
    intro v hv
    obtain ⟨hvU, hrv⟩ := mem_outN.mp hv
    refine mem_outN.mpr ⟨?_, hrv⟩
    rcases Finset.mem_union.mp hvU with hvXY | hvZ
    · rcases Finset.mem_union.mp hvXY with hvX | hvY
      · exact (hnoX r hr v hvX hrv).elim
      · exact Finset.mem_union_left _ (Finset.mem_erase.mpr
          ⟨fun heq => hnoB r hr (heq ▸ hrv), hvY⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hvZ, r, hr, hrv⟩)
  have hGcLower : s ≤ G.card := by
    obtain ⟨r, hr, hsink⟩ := exists_sink (hf.mono_set hRU)
      (Finset.card_pos.mp (by omega)) (by omega)
    have hsub : outN D (R ∪ G) r ⊆ G := by
      intro v hv
      obtain ⟨hvRG, hrv⟩ := mem_outN.mp hv
      rcases Finset.mem_union.mp hvRG with hvR | hvG
      · exact (hsink v hvR hrv).elim
      · exact hvG
    exact (hhighR r hr).trans (Finset.card_le_card hsub)
  have hnoGX : ∀ w ∈ G, ∀ x ∈ X, ¬ D w x = true := by
    intro w hw x hx hwx
    obtain ⟨hwZ, r, hr, hrw⟩ := Finset.mem_filter.mp hw
    have heq := h.cyclic_return_parent_unique hint ha hb hz hbz hza
      hx (hRY hr) hwZ hrw hwx
    exact (Finset.mem_erase.mp hr).1 heq
  have hnoGz : ∀ w ∈ G, ¬ D w z = true := by
    intro w hw hwz
    obtain ⟨hwZ, r, hr, hrw⟩ := Finset.mem_filter.mp hw
    exact hf a 4 (by decide) (by omega)
      (.step (hRU hr) (hall r hr) (.step (hZU hwZ) hrw
        (.step (hZU hz) hwz (.step (hXU ha) hza (.refl a)))))
  let B := (Z \ G).erase z
  have hBc : B.card ≤ 1 := by
    dsimp only [B]
    rw [Finset.card_erase_of_mem (Finset.mem_sdiff.mpr ⟨hz, hzG⟩),
      Finset.card_sdiff_of_subset hGZ, hZ]
    omega
  have hlowG : ∀ w ∈ G, 2 ≤ (outN D (R ∪ G) w).card := by
    intro w hw
    have hsub : outN D (X ∪ Y ∪ Z) w ⊆ outN D (R ∪ G) w ∪ B := by
      intro v hv
      obtain ⟨hvU, hwv⟩ := mem_outN.mp hv
      rcases Finset.mem_union.mp hvU with hvXY | hvZ
      · rcases Finset.mem_union.mp hvXY with hvX | hvY
        · exact (hnoGX w hw v hvX hwv).elim
        · exact Finset.mem_union_left _ (mem_outN.mpr
            ⟨Finset.mem_union_left _ (Finset.mem_erase.mpr
              ⟨fun heq => hnoZb w (hGZ hw) (heq ▸ hwv), hvY⟩), hwv⟩)
      · by_cases hvG : v ∈ G
        · exact Finset.mem_union_left _ (mem_outN.mpr ⟨Finset.mem_union_right _ hvG, hwv⟩)
        · exact Finset.mem_union_right _ (Finset.mem_erase.mpr
            ⟨fun heq => hnoGz w hw (heq ▸ hwv), Finset.mem_sdiff.mpr ⟨hvZ, hvG⟩⟩)
    have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    have hh := h.low_third w (hGZ hw)
    omega
  have hmin : ∀ v ∈ R ∪ G, 2 ≤ (outN D (R ∪ G) v).card := by
    intro v hv
    rcases Finset.mem_union.mp hv with hvR | hvG
    · exact (by omega : 2 ≤ s).trans (hhighR v hvR)
    · exact hlowG v hvG
  have hc := Finset.card_union_le R G
  exact two_core_many_high_false (by omega : 1 ≤ s - 1) (hf.mono_set hRGU)
    (by omega) hmin (H := R) Finset.subset_union_left (by omega)
    (fun v hv => (by omega : 5 ≤ s).trans (hhighR v hv))

theorem TwoExtraTriple.false (h : TwoExtraTriple D X Y Z s) : False := by
  classical
  by_cases hint : ∀ x ∈ X, 1 ≤ (outN D X x).card
  · exact h.cyclic_false hint
  · push Not at hint
    obtain ⟨t, ht, htc⟩ := hint
    have hs := h.large
    have hsink : ∀ v ∈ X, ¬ D t v = true := by
      intro v hv htv
      have := Finset.card_pos.mpr ⟨v, mem_outN.mpr ⟨hv, htv⟩⟩
      omega
    have hfX := h.free.mono_set
      (Finset.subset_union_left.trans Finset.subset_union_left : X ⊆ X ∪ Y ∪ Z)
    have hacy := qfree_succ_of_sink hfX (by rw [h.card_first]; omega) ht hsink
    rw [Nat.sub_add_cancel (by omega : 1 ≤ s)] at hacy
    exact h.acyclic_false hacy

/-- The excess-two target is now proved uniformly for every s at least six. -/
theorem two_extra_triple_impossible : TwoExtraTripleImpossible := by
  intro s D X Y Z hs hf hXY houter hX hY hZ hhighX hhighY hlowZ hparents
  exact (TwoExtraTriple.mk hs hf hXY houter hX hY hZ hhighX hhighY hlowZ hparents).false

end LeanCH.BR.BRsGen
