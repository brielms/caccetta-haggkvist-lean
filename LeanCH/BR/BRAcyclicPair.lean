import LeanCH.BR.BR45Base
import LeanCH.BR.BRFiniteWalk

/-! An acyclic first set confines middle-to-first returns to a single middle vertex. -/

namespace LeanCH.BR.BRsGen

open BRq2 BRq3 BR45

variable {D : CH.Digraph} {X Y : Finset ℕ} {s a b : ℕ}

/-- A back arc at an acyclic first set isolates its middle vertex and gives a two-step funnel. -/
theorem acyclic_back_arc_others (hs : 6 ≤ s) (hf : QFree D (X ∪ Y) (s - 1))
    (hacy : QFree D X s) (hXY : Disjoint X Y) (hX : X.card = s) (hY : Y.card = s)
    (hhigh : ∀ x ∈ X, s ≤ (outN D (X ∪ Y) x).card)
    (ha : a ∈ X) (hb : b ∈ Y) (hba : D b a = true) :
    (∀ y ∈ Y.erase b, ∃ m, m ≤ 2 ∧ Walk D (X ∪ Y) a y m) ∧
    (∀ y ∈ Y.erase b, ∀ x ∈ X, ¬ D y x = true) ∧
    (∀ y ∈ Y.erase b, ¬ D y b = true) := by
  classical
  have hXU : X ⊆ X ∪ Y := Finset.subset_union_left
  have hYU : Y ⊆ X ∪ Y := Finset.subset_union_right
  have sinkY : ∀ t ∈ X, (∀ x ∈ X, ¬ D t x = true) → ∀ y ∈ Y, D t y = true := by
    intro t ht hts
    have hsub : outN D (X ∪ Y) t ⊆ Y := by
      intro y hy
      obtain ⟨hyXY, hty⟩ := mem_outN.mp hy
      rcases Finset.mem_union.mp hyXY with hyX | hyY
      · exact (hts y hyX hty).elim
      · exact hyY
    have heq := Finset.eq_of_subset_of_card_le hsub (by rw [hY]; exact hhigh t ht)
    intro y hy
    exact (mem_outN.mp (heq.symm ▸ hy)).2
  obtain ⟨p⟩ := exists_shortest_sink_path hacy hX.le ha
  have hlen : p.len < s := by have := p.bounded; omega
  have hlong : s - 2 ≤ p.len := by
    by_contra hn
    have w := p.walk (Nat.zero_le p.len) le_rfl
    rw [p.start, Nat.sub_zero] at w
    exact hf a (p.len + 1 + 1) (by omega) (by omega)
      (((w.mono hXU).snoc (hYU hb) (sinkY _ (p.mem _ le_rfl) p.sink b hb)).snoc (hXU ha) hba)
  let P := (Finset.range (p.len + 1)).image p.vertex
  let E := X \ P
  let H := outN D X a
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
  have hchord {i j : ℕ} (hi : i ≤ p.len) (hj : j ≤ p.len)
      (he : D (p.vertex i) (p.vertex j) = true) : j = i + 1 := p.no_chord hacy hX.le hi hj he
  have hHsub : H ⊆ insert (p.vertex 1) E := by
    intro x hx
    obtain ⟨hxX, hax⟩ := mem_outN.mp hx
    by_cases hxP : x ∈ P
    · obtain ⟨i, hi, rfl⟩ := hPget x hxP
      have he : D (p.vertex 0) (p.vertex i) = true := by simpa only [p.start] using hax
      have hi1 := hchord (Nat.zero_le _) hi he
      simpa only [Nat.zero_add, hi1] using Finset.mem_insert_self (p.vertex 1) E
    · exact Finset.mem_insert_of_mem (Finset.mem_sdiff.mpr ⟨hxX, hxP⟩)
  have hHcap := (Finset.card_le_card hHsub).trans (Finset.card_insert_le _ _)
  have full : ∀ w ∈ X, (outN D X w).card ≤ 1 → ¬ D w b = true →
      ∀ y ∈ Y.erase b, D w y = true := by
    intro w hw hc hwb
    have hsub : outN D Y w ⊆ Y.erase b := by
      intro y hy
      obtain ⟨hyY, hwy⟩ := mem_outN.mp hy
      exact Finset.mem_erase.mpr ⟨fun h => hwb (h ▸ hwy), hyY⟩
    have heq := Finset.eq_of_subset_of_card_le hsub (by
      rw [Finset.card_erase_of_mem hb, hY]
      have hh := hhigh w hw
      rw [card_outN_union hXY] at hh
      omega)
    intro y hy
    exact (mem_outN.mp (heq.symm ▸ hy)).2
  have hreach : ∀ y ∈ Y.erase b, ∃ m, m ≤ 2 ∧ Walk D (X ∪ Y) a y m := by
    by_cases hH1 : H.card ≤ 1
    · have hall := full a ha hH1 (fun hab => digonfree hf (by omega) (hXU ha) (hYU hb) hab hba)
      intro y hy
      exact ⟨1, by decide, .step (hYU (Finset.mem_of_mem_erase hy)) (hall y hy) (.refl y)⟩
    · have hp : p.len = s - 2 := by omega
      have hE1 : E.card = 1 := by omega
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
              (p.len - j + 1 + 1) (.step hwX haw (.step (p.mem j hj) hwx (p.walk hj le_rfl)))
            have hj0 : j ≠ 0 := by
              intro h
              exact digonfree hacy (by omega) ha hwX haw (by simpa only [h, p.start] using hwx)
            have hj1 : j ≠ 1 := by
              intro h
              exact hws _ (hspan.symm ▸ Finset.mem_insert_self _ _) (h ▸ hwx)
            exact Finset.mem_singleton.mpr (congrArg p.vertex (by omega : j = 2))
          · have hxH : x ∈ H := hspan.symm ▸ Finset.mem_insert_of_mem (Finset.mem_sdiff.mpr ⟨hxX, hxP⟩)
            exact (hws x hxH hwx).elim
        exact (Finset.card_le_card hsub).trans (by simp)
      have hwb : ¬ D w b = true := fun hwb => hf a 3 (by decide) (by omega)
        (.step (hXU hwX) haw (.step (hYU hb) hwb (.step (hXU ha) hba (.refl a))))
      intro y hy
      exact ⟨2, le_rfl, .step (hXU hwX) haw
        (.step (hYU (Finset.mem_of_mem_erase hy)) (full w hwX hwcap hwb y hy) (.refl y))⟩
  have hnoB : ∀ y ∈ Y.erase b, ¬ D y b = true := by
    intro y hy hyb
    obtain ⟨m, hm, w⟩ := hreach y hy
    exact hf a (m + 1 + 1) (by omega) (by omega) ((w.snoc (hYU hb) hyb).snoc (hXU ha) hba)
  have hnoP : ∀ y ∈ Y.erase b, ∀ x ∈ P, ¬ D y x = true := by
    intro y hy x hx hyx
    obtain ⟨i, hi, rfl⟩ := hPget x hx
    by_cases ht : p.len - i ≤ s - 3
    · exact hf (p.vertex i) (p.len - i + 1 + 1) (by omega) (by omega)
        ((((p.walk hi le_rfl).mono hXU).snoc (hYU (Finset.mem_of_mem_erase hy))
          (sinkY _ (p.mem _ le_rfl) p.sink y (Finset.mem_of_mem_erase hy))).snoc (hXU (p.mem i hi)) hyx)
    · by_cases hi0 : i = 0
      · obtain ⟨m, hm, w⟩ := hreach y hy
        have hya : D y a = true := by simpa only [hi0, p.start] using hyx
        exact hf a (m + 1) (by omega) (by omega) (w.snoc (hXU ha) hya)
      · have hp : p.len = s - 1 := by omega
        have hi1 : i = 1 := by omega
        have hE0 : E.card = 0 := by omega
        have hspan : P = X := Finset.eq_of_subset_of_card_le hPX (by omega)
        have hicap : (outN D X (p.vertex i)).card ≤ 1 := by
          have hsub : outN D X (p.vertex i) ⊆ {p.vertex (i + 1)} := by
            intro v hv
            obtain ⟨hvX, hiv⟩ := mem_outN.mp hv
            obtain ⟨j, hj, rfl⟩ := hPget v (hspan.symm ▸ hvX)
            exact Finset.mem_singleton.mpr (congrArg p.vertex (hchord hi hj hiv))
          exact (Finset.card_le_card hsub).trans (by simp)
        have hib : ¬ D (p.vertex i) b = true := by
          intro hib
          have w := p.walk (Nat.zero_le i) hi
          rw [p.start, Nat.sub_zero] at w
          exact hf a (i + 1 + 1) (by omega) (by omega)
            (((w.mono hXU).snoc (hYU hb) hib).snoc (hXU ha) hba)
        exact digonfree hf (by omega) (hXU (p.mem i hi)) (hYU (Finset.mem_of_mem_erase hy))
          (full _ (p.mem i hi) hicap hib y hy) hyx
  refine ⟨hreach, ?_, hnoB⟩
  intro y hy e heX hye
  have heP : e ∉ P := fun heP => hnoP y hy e heP hye
  have he : e ∈ E := Finset.mem_sdiff.mpr ⟨heX, heP⟩
  have hEpos := Finset.card_pos.mpr ⟨e, he⟩
  have hp : p.len = s - 2 := by omega
  have hE1 : E.card = 1 := by omega
  have hea : ¬ D e a = true := by
    intro hea
    obtain ⟨m, hm, w⟩ := hreach y hy
    exact hf a (m + 1 + 1) (by omega) (by omega) ((w.snoc (hXU heX) hye).snoc (hXU ha) hea)
  have heb : ¬ D e b = true := by
    intro heb
    obtain ⟨m, hm, w⟩ := hreach y hy
    exact hf a (m + 1 + 1 + 1) (by omega) (by omega)
      (((w.snoc (hXU heX) hye).snoc (hYU hb) heb).snoc (hXU ha) hba)
  have hcapX : (outN D X e).card ≤ 1 := by
    have hsub : outN D X e ⊆ {p.vertex 1} := by
      intro x hx
      obtain ⟨hxX, hex⟩ := mem_outN.mp hx
      by_cases hxP : x ∈ P
      · obtain ⟨j, hj, rfl⟩ := hPget x hxP
        have hj0 : j ≠ 0 := by intro h; exact hea (by simpa only [h, p.start] using hex)
        have hj2 : j < 2 := by
          by_contra hn
          have wt := (((p.walk hj le_rfl).mono hXU).snoc (hYU (Finset.mem_of_mem_erase hy))
            (sinkY _ (p.mem _ le_rfl) p.sink y (Finset.mem_of_mem_erase hy))).snoc (hXU heX) hye
          exact hf e (p.len - j + 1 + 1 + 1) (by omega) (by omega)
            (.step (hXU (p.mem j hj)) hex wt)
        exact Finset.mem_singleton.mpr (congrArg p.vertex (by omega : j = 1))
      · have hxe := Finset.card_le_one.mp hE1.le x (Finset.mem_sdiff.mpr ⟨hxX, hxP⟩) e he
        exact (loopfree hacy (by omega) heX (hxe ▸ hex)).elim
    exact (Finset.card_le_card hsub).trans (by simp)
  have hcapY : (outN D Y e).card ≤ s - 2 := by
    have hsub : outN D Y e ⊆ (Y.erase b).erase y := by
      intro v hv
      obtain ⟨hvY, hev⟩ := mem_outN.mp hv
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_erase.mpr ⟨fun h => heb (h ▸ hev), hvY⟩⟩
      intro h
      exact digonfree hf (by omega) (hYU (Finset.mem_of_mem_erase hy)) (hXU heX) hye (h ▸ hev)
    have := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem hy, Finset.card_erase_of_mem hb, hY] at this
    omega
  have hh := hhigh e heX
  rw [card_outN_union hXY] at hh
  omega

end LeanCH.BR.BRsGen
