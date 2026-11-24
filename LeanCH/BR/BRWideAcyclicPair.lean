import LeanCH.BR.BRAcyclicTriple

/-! A return to an acyclic first set with one extra vertex leaves two escapes. -/

namespace LeanCH.BR.BRsGen
open BRq2 BRq3 BR45
variable {D : CH.Digraph} {X Y : Finset ℕ} {s a b : ℕ}

theorem wide_pair_long_sink_path (hs : 4 ≤ s)
    (hf : QFree D (X ∪ Y) (s - 1)) (hacy : QFree D X (s + 1))
    (hX : X.card = s + 1) (hY : Y.card = s)
    (hhigh : ∀ x ∈ X, s ≤ (outN D (X ∪ Y) x).card)
    (ha : a ∈ X) (hb : b ∈ Y) (hba : D b a = true) :
    ∃ p : ShortestSinkPath D X a, s - 2 ≤ p.len := by
  classical
  obtain ⟨p⟩ := exists_shortest_sink_path hacy hX.le ha
  refine ⟨p, ?_⟩
  have hsub : outN D (X ∪ Y) (p.vertex p.len) ⊆ Y := by
    intro v hv
    rcases Finset.mem_union.mp (mem_outN.mp hv).1 with hvX | hvY
    · exact (p.sink v hvX (mem_outN.mp hv).2).elim
    · exact hvY
  have heq := Finset.eq_of_subset_of_card_le hsub
    (by rw [hY]; exact hhigh _ (p.mem _ le_rfl))
  have htb := (mem_outN.mp (heq.symm ▸ hb)).2
  by_contra hn
  have w := p.walk (Nat.zero_le p.len) le_rfl
  rw [p.start, Nat.sub_zero] at w
  exact hf a (p.len + 1 + 1) (by omega) (by omega)
    (((w.mono Finset.subset_union_left).snoc (Finset.mem_union_right _ hb) htb).snoc
      (Finset.mem_union_left _ ha) hba)

/-- A back arc supplies a closed middle set of size at least s-2, reached in two steps. -/
theorem acyclic_wide_return_basin (hs : 6 ≤ s)
    (hf : QFree D (X ∪ Y) (s - 1)) (hacy : QFree D X (s + 1))
    (hXY : Disjoint X Y) (hX : X.card = s + 1) (hY : Y.card = s)
    (hhighX : ∀ x ∈ X, s ≤ (outN D (X ∪ Y) x).card)
    (ha : a ∈ X) (hb : b ∈ Y) (hba : D b a = true) :
    ∃ R : Finset ℕ, R ⊆ Y ∧ s - 2 ≤ R.card ∧ R.card ≤ s - 1 ∧
      R ⊆ ball D (X ∪ Y) a 2 ∧
      (∀ r ∈ R, ∀ y ∈ Y, D r y = true → y ∈ R) ∧
      (∀ r ∈ R, ¬ D r b = true) := by
  classical
  have hXU : X ⊆ X ∪ Y := Finset.subset_union_left
  have hYU : Y ⊆ X ∪ Y := Finset.subset_union_right
  obtain ⟨p, hlong⟩ := wide_pair_long_sink_path (by omega) hf hacy hX hY hhighX ha hb hba
  have hlen : p.len < s + 1 := by have := p.bounded; omega
  let P := (Finset.range (p.len + 1)).image p.vertex
  let E := X \ P
  let H := outN D X a
  let R := Y ∩ ball D (X ∪ Y) a 2
  have hPX : P ⊆ X := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    exact p.mem i (by have := Finset.mem_range.mp hi; omega)
  have hPc : P.card = p.len + 1 :=
    (Finset.card_image_of_injOn (p.injective hacy hX.le)).trans (Finset.card_range _)
  have hEc : E.card = s + 1 - (p.len + 1) := by
    change (X \ P).card = s + 1 - (p.len + 1)
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
  have hRball : R ⊆ ball D (X ∪ Y) a 2 := Finset.inter_subset_right
  have hbR : b ∉ R := by
    intro hbR
    obtain ⟨_, m, hm, w⟩ := mem_ball.mp (hRball hbR)
    exact hf a (m + 1) (by omega) (by omega) (w.snoc (hXU ha) hba)
  have hRsub : R ⊆ Y.erase b := fun _ hr =>
    Finset.mem_erase.mpr ⟨fun h => hbR (h ▸ hr), hRY hr⟩
  have hRhi : R.card ≤ s - 1 := by
    have := Finset.card_le_card hRsub
    rwa [Finset.card_erase_of_mem hb, hY] at this
  have hnoB : ∀ r ∈ R, ¬ D r b = true := by
    intro r hr hrb
    obtain ⟨_, m, hm, w⟩ := mem_ball.mp (hRball hr)
    exact hf a (m + 1 + 1) (by omega) (by omega)
      ((w.snoc (hYU hb) hrb).snoc (hXU ha) hba)
  have hdirect : outN D Y a ⊆ R := by
    intro y hy
    obtain ⟨hyY, hay⟩ := mem_outN.mp hy
    exact Finset.mem_inter.mpr ⟨hyY, mem_ball_of_walk
      (.step (hYU hyY) hay (.refl y)) (by decide : 1 ≤ 2) (hYU hyY)⟩
  have hlarge : 3 ≤ H.card → s - 1 ≤ R.card := by
    intro hH3
    have hp : p.len = s - 2 := by omega
    have hE2 : E.card = 2 := by omega
    have hspan : H = insert (p.vertex 1) E := Finset.eq_of_subset_of_card_le hHsub
      ((Finset.card_insert_le _ _).trans (by omega))
    obtain ⟨w, hw, hws⟩ := exists_sink (hacy.mono_set (outN_subset (D := D) (W := X) (y := a)))
      (Finset.card_pos.mp (by omega : 0 < H.card)) (by change H.card ≤ s + 1; omega)
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
      exact hf a 3 (by decide) (by omega)
        (.step (hXU hwX) haw (.step (hYU hb) hwb (.step (hXU ha) hba (.refl a))))
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
  exact ⟨R, hRY, hRlo, hRhi, hRball, hclosed, hnoB⟩

/-- With positive middle rows, an acyclic first (s+1)-set excludes every back
arc. The two remaining escape vertices are handled together. -/
theorem acyclic_wide_pair_no_back (hs : 6 ≤ s)
    (hf : QFree D (X ∪ Y) (s - 1)) (hacy : QFree D X (s + 1))
    (hXY : Disjoint X Y) (hX : X.card = s + 1) (hY : Y.card = s)
    (hhigh : ∀ x ∈ X, s ≤ (outN D (X ∪ Y) x).card)
    (hlow : ∀ y ∈ Y, 1 ≤ (outN D (X ∪ Y) y).card) :
    ∀ b ∈ Y, ∀ a ∈ X, ¬ D b a = true := by
  classical
  intro b hb a ha hba
  obtain ⟨R, hRY, hRlo, hRhi, hRball, hclosed, _⟩ :=
    acyclic_wide_return_basin hs hf hacy hXY hX hY hhigh ha hb hba
  obtain ⟨p, hlong⟩ := wide_pair_long_sink_path (by omega) hf hacy hX hY hhigh ha hb hba
  let t := p.suffix (i := p.len - (s - 3)) (Nat.sub_le _ _)
  have htlen : t.len = s - 3 := by
    change p.len - (p.len - (s - 3)) = s - 3
    omega
  let P := (Finset.range (t.len + 1)).image t.vertex
  let E := (X \ P).erase a
  have hXU : X ⊆ X ∪ Y := Finset.subset_union_left
  have hYU : Y ⊆ X ∪ Y := Finset.subset_union_right
  have hPX : P ⊆ X := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    exact t.mem i (by have := Finset.mem_range.mp hi; omega)
  have hPc : P.card = s - 2 := by
    have hc := (Finset.card_image_of_injOn (t.injective hacy hX.le)).trans (Finset.card_range _)
    change P.card = t.len + 1 at hc
    omega
  have haP : a ∉ P := by
    intro hap
    obtain ⟨i, hi, hia⟩ := Finset.mem_image.mp hap
    have hi' : i ≤ s - 3 := by have := Finset.mem_range.mp hi; omega
    change p.vertex (p.len - (s - 3) + i) = a at hia
    have hia0 := hia.trans p.start.symm
    have he := p.injective hacy hX.le
      (Finset.mem_range.mpr (by omega : p.len - (s - 3) + i < p.len + 1))
      (Finset.mem_range.mpr (by omega : 0 < p.len + 1)) hia0
    omega
  have hEc : E.card = 2 := by
    rw [show E = (X \ P).erase a from rfl,
      Finset.card_erase_of_mem (Finset.mem_sdiff.mpr ⟨ha, haP⟩),
      Finset.card_sdiff_of_subset hPX, hX, hPc]
    omega
  have hEX : E ⊆ X := (Finset.erase_subset _ _).trans Finset.sdiff_subset
  have hPget : ∀ x ∈ P, ∃ i, i ≤ t.len ∧ t.vertex i = x := by
    intro x hx
    obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp hx
    exact ⟨i, by have := Finset.mem_range.mp hi; omega, heq⟩
  have hfull : ∀ y ∈ Y, D (t.vertex t.len) y = true := by
    have hsub : outN D (X ∪ Y) (t.vertex t.len) ⊆ Y := by
      intro y hy
      rcases Finset.mem_union.mp (mem_outN.mp hy).1 with hyX | hyY
      · exact (t.sink y hyX (mem_outN.mp hy).2).elim
      · exact hyY
    have heq := Finset.eq_of_subset_of_card_le hsub
      (by rw [hY]; exact hhigh _ (t.mem _ le_rfl))
    intro y hy
    exact (mem_outN.mp (heq.symm ▸ hy)).2
  have hnoP : ∀ r ∈ R, ∀ x ∈ P, ¬ D r x = true := by
    intro r hr x hx hrx
    obtain ⟨i, hi, rfl⟩ := hPget x hx
    exact hf (t.vertex i) (t.len - i + 1 + 1) (by omega) (by omega)
      ((((t.walk hi le_rfl).mono hXU).snoc (hYU (hRY hr)) (hfull r (hRY hr))).snoc
        (hXU (t.mem i hi)) hrx)
  have hnoA : ∀ r ∈ R, ¬ D r a = true :=
    fun r hr => no_back_arc hf (hXU ha) (hRball hr) (by omega)
  have hminR : ∀ r ∈ R, 1 ≤ (outN D (R ∪ E) r).card := by
    intro r hr
    apply (hlow r (hRY hr)).trans
    apply Finset.card_le_card
    intro x hx
    obtain ⟨hxU, hrx⟩ := mem_outN.mp hx
    refine mem_outN.mpr ⟨?_, hrx⟩
    rcases Finset.mem_union.mp hxU with hxX | hxY
    · exact Finset.mem_union_right _ (Finset.mem_erase.mpr
        ⟨fun heq => hnoA r hr (heq ▸ hrx),
          Finset.mem_sdiff.mpr ⟨hxX, fun hxP => hnoP r hr x hxP hrx⟩⟩)
    · exact Finset.mem_union_left _ (hclosed r hr x hxY hrx)
  apply two_escape_high_return_false hs
    (hf.mono_set (Finset.union_subset (hRY.trans hYU) (hEX.trans hXU)))
    ((hXY.mono hEX hRY).symm) (by omega) hRhi hEc.le hminR
  intro e he hp
  obtain ⟨r, hr, hre⟩ := hp
  have heX := hEX he
  have hea : ¬ D e a = true := by
    intro hea
    obtain ⟨_, k, hk, w⟩ := mem_ball.mp (hRball hr)
    exact hf a (k + 1 + 1) (by omega) (by omega)
      ((w.snoc (hXU heX) hre).snoc (hXU ha) hea)
  have heb : ¬ D e b = true := by
    intro heb
    obtain ⟨_, k, hk, w⟩ := mem_ball.mp (hRball hr)
    exact hf a (k + 1 + 1 + 1) (by omega) (by omega)
      (((w.snoc (hXU heX) hre).snoc (hYU hb) heb).snoc (hXU ha) hba)
  have hcapX : (outN D X e).card ≤ 2 := by
    have hsub : outN D X e ⊆ insert (t.vertex 0) (E.erase e) := by
      intro x hx
      obtain ⟨hxX, hex⟩ := mem_outN.mp hx
      by_cases hxP : x ∈ P
      · obtain ⟨i, hi, rfl⟩ := hPget x hxP
        have hi0 : i = 0 := by
          by_contra hn
          have wt := (((t.walk hi le_rfl).mono hXU).snoc (hYU (hRY hr))
            (hfull r (hRY hr))).snoc (hXU heX) hre
          exact hf e (t.len - i + 1 + 1 + 1) (by omega) (by omega)
            (.step (hXU (t.mem i hi)) hex wt)
        simp only [hi0, Finset.mem_insert, true_or]
      · exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr
          ⟨fun h => loopfree hacy (by omega) heX (h ▸ hex),
            Finset.mem_erase.mpr ⟨fun h => hea (h ▸ hex), Finset.mem_sdiff.mpr ⟨hxX, hxP⟩⟩⟩)
    have hc := (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
    rw [Finset.card_erase_of_mem he, hEc] at hc
    omega
  have hbR : b ∉ R := fun h => no_back_arc hf (hXU ha) (hRball h) (by omega) hba
  have hRsub : R ⊆ Y.erase b := fun r hr =>
    Finset.mem_erase.mpr ⟨fun heq => hbR (heq ▸ hr), hRY hr⟩
  have hcapY : (outN D Y e).card ≤ (outN D R e).card + ((Y.erase b) \ R).card := by
    apply (Finset.card_le_card (show outN D Y e ⊆ outN D R e ∪ ((Y.erase b) \ R) from ?_)).trans
      (Finset.card_union_le _ _)
    intro y hy
    obtain ⟨hyY, hey⟩ := mem_outN.mp hy
    by_cases hyR : y ∈ R
    · exact Finset.mem_union_left _ (mem_outN.mpr ⟨hyR, hey⟩)
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr
        ⟨Finset.mem_erase.mpr ⟨fun heq => heb (heq ▸ hey), hyY⟩, hyR⟩)
  rw [Finset.card_sdiff_of_subset hRsub, Finset.card_erase_of_mem hb, hY] at hcapY
  have hh := hhigh e heX
  rw [card_outN_union hXY] at hh
  omega

end LeanCH.BR.BRsGen
