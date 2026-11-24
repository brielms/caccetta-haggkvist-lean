import LeanCH.BR.BRq3Base

/-! A narrow acyclic set followed by a set one vertex larger. -/

namespace LeanCH.BR.BRsGen

open BRq2 BRq3

variable {D : CH.Digraph} {X Y : Finset ℕ} {s : ℕ}

/-- With `s-1` first vertices of degree at least `s` and `s` second vertices
of positive degree, girth at least `s` excludes every back arc. -/
theorem narrow_pair_no_back (hs : 4 ≤ s) (hf : QFree D (X ∪ Y) (s - 1))
    (_hdisj : Disjoint X Y) (hX : X.card = s - 1) (hY : Y.card = s)
    (hhigh : ∀ x ∈ X, s ≤ (outN D (X ∪ Y) x).card)
    (hlow : ∀ y ∈ Y, 1 ≤ (outN D (X ∪ Y) y).card) :
    ∀ y ∈ Y, ∀ x ∈ X, ¬ D y x = true := by
  classical
  let U := X ∪ Y
  let Reach (j a : ℕ) : Prop := ∀ b ∈ Y, ∃ m, 1 ≤ m ∧ m ≤ j ∧ Walk D U a b m
  have hXU : X ⊆ U := Finset.subset_union_left
  have hYU : Y ⊆ U := Finset.subset_union_right
  have hstep (j a : ℕ) (ha : a ∈ X)
      (hr : ∀ c ∈ X, D a c = true → Reach j c) : Reach (j + 1) a := by
    by_cases hh : ∃ c ∈ X, D a c = true
    · obtain ⟨c, hc, hac⟩ := hh
      intro b hb
      obtain ⟨m, hm, hmj, w⟩ := hr c hc hac b hb
      exact ⟨m + 1, by omega, by omega, .step (hXU hc) hac w⟩
    · have hsub : outN D U a ⊆ Y := by
        intro c hc
        rcases Finset.mem_union.mp (mem_outN.mp hc).1 with h | h
        · exact (hh ⟨c, h, (mem_outN.mp hc).2⟩).elim
        · exact h
      have heq := Finset.eq_of_subset_of_card_le hsub (by rw [hY]; exact hhigh a ha)
      intro b hb
      have hab : b ∈ outN D U a := heq.symm ▸ hb
      exact ⟨1, le_rfl, by omega, .step (hYU hb) (mem_outN.mp hab).2 (.refl b)⟩
  have hadd {S : Finset ℕ} {j : ℕ} (hSX : S ⊆ X) (hSc : S.card = j)
      (hj : j < s - 1) (hSr : ∀ a ∈ S, Reach j a) :
      ∃ t ∈ X, t ∉ S ∧ Reach (j + 1) t := by
    have hTc : (X \ S).card = s - 1 - j := by rw [Finset.card_sdiff_of_subset hSX, hX, hSc]
    obtain ⟨t, ht, htSink⟩ := exists_sink (hf.mono_set (Finset.sdiff_subset.trans hXU))
      (show (X \ S).Nonempty by rw [← Finset.card_pos, hTc]; omega)
      (by rw [hTc]; omega)
    obtain ⟨htX, htS⟩ := Finset.mem_sdiff.mp ht
    refine ⟨t, htX, htS, hstep j t htX (fun c hc htc => ?_)⟩
    by_cases hcS : c ∈ S
    · exact hSr c hcS
    · exact (htSink c (Finset.mem_sdiff.mpr ⟨hc, hcS⟩) htc).elim
  have hchain : ∀ j, j ≤ s - 1 → ∃ S ⊆ X, S.card = j ∧ ∀ a ∈ S, Reach j a := by
    intro j
    induction j with
    | zero => exact fun _ => ⟨∅, Finset.empty_subset _, rfl, fun a ha => (Finset.notMem_empty a ha).elim⟩
    | succ j ih =>
      intro hj
      obtain ⟨S, hSX, hSc, hSr⟩ := ih (by omega)
      obtain ⟨t, ht, htS, htr⟩ := hadd hSX hSc (by omega) hSr
      refine ⟨insert t S, Finset.insert_subset ht hSX,
        by rw [Finset.card_insert_of_notMem htS, hSc], ?_⟩
      intro a ha b hb
      rcases Finset.mem_insert.mp ha with rfl | ha
      · exact htr b hb
      · obtain ⟨m, hm, hmj, w⟩ := hSr a ha b hb
        exact ⟨m, hm, by omega, w⟩
  obtain ⟨S, hSX, hSc, hSr⟩ := hchain (s - 3) (by omega)
  obtain ⟨t, ht, htS, htr⟩ := hadd hSX hSc (by omega) hSr
  have hTX : insert t S ⊆ X := Finset.insert_subset ht hSX
  have hTc : (insert t S).card = s - 2 := by rw [Finset.card_insert_of_notMem htS, hSc]; omega
  have hTr : ∀ a ∈ insert t S, Reach (s - 2) a := by
    intro a ha b hb
    rcases Finset.mem_insert.mp ha with rfl | ha
    · obtain ⟨m, hm, hmj, w⟩ := htr b hb
      exact ⟨m, hm, by omega, w⟩
    · obtain ⟨m, hm, hmj, w⟩ := hSr a ha b hb
      exact ⟨m, hm, by omega, w⟩
  have hRc : (X \ insert t S).card = 1 := by
    rw [Finset.card_sdiff_of_subset hTX, hX, hTc]; omega
  have huniq : ∀ a ∈ X, a ∉ insert t S → ∀ a' ∈ X, a' ∉ insert t S → a = a' := by
    intro a ha haT a' ha' ha'T
    exact Finset.card_le_one.mp hRc.le a (Finset.mem_sdiff.mpr ⟨ha, haT⟩)
      a' (Finset.mem_sdiff.mpr ⟨ha', ha'T⟩)
  have hnoT : ∀ b ∈ Y, ∀ a ∈ insert t S, ¬ D b a = true := by
    intro b hb a ha hba
    obtain ⟨m, hm, hmj, w⟩ := hTr a ha b hb
    exact hf a (m + 1) (by omega) (by omega) (w.snoc (hXU (hTX ha)) hba)
  intro b hb a ha hba
  have haT : a ∉ insert t S := fun h => hnoT b hb a h hba
  have hO1 : ∀ c ∈ X, D a c = true → c = t := by
    intro c hc hac
    by_contra hct
    by_cases hcS : c ∈ S
    · obtain ⟨m, hm, hmj, w⟩ := hSr c hcS b hb
      exact hf a (m + 1 + 1) (by omega) (by omega)
        ((Walk.step (hXU hc) hac w).snoc (hXU ha) hba)
    · have hcT : c ∉ insert t S := by simp [hct, hcS]
      have heq := huniq c hc hcT a ha haT
      exact loopfree hf (by omega) (hXU ha) (heq ▸ hac)
  have hsub : (outN D U a).erase t ⊆ Y.erase b := by
    intro c hc
    obtain ⟨hct, hcO⟩ := Finset.mem_erase.mp hc
    obtain ⟨hcU, hac⟩ := mem_outN.mp hcO
    refine Finset.mem_erase.mpr ⟨?_, ?_⟩
    · intro hcb
      exact digonfree hf (by omega) (hXU ha) (hYU hb) (hcb ▸ hac) hba
    · rcases Finset.mem_union.mp hcU with h | h
      · exact (hct (hO1 c h hac)).elim
      · exact h
  have heq := Finset.eq_of_subset_of_card_le hsub (by
    rw [Finset.card_erase_of_mem hb, hY]
    have h := Finset.pred_card_le_card_erase (s := outN D U a) (a := t)
    have hh := hhigh a ha
    change s ≤ (outN D U a).card at hh
    omega)
  have haY : ∀ b' ∈ Y.erase b, D a b' = true := by
    intro b' hb'
    rw [← heq] at hb'
    exact (mem_outN.mp (Finset.mem_of_mem_erase hb')).2
  obtain ⟨y, hy, hsink⟩ := exists_sink (hf.mono_set ((Finset.erase_subset _ _).trans hYU))
    (show (Y.erase b).Nonempty by rw [← Finset.card_pos, Finset.card_erase_of_mem hb, hY]; omega)
    (by rw [Finset.card_erase_of_mem hb, hY])
  have hyY := Finset.mem_of_mem_erase hy
  obtain ⟨z, hz⟩ := Finset.card_pos.mp (hlow y hyY)
  obtain ⟨hzU, hyz⟩ := mem_outN.mp hz
  rcases Finset.mem_union.mp hzU with hzX | hzY
  · have hzT : z ∉ insert t S := fun h => hnoT y hyY z h hyz
    have hza := huniq z hzX hzT a ha haT
    exact digonfree hf (by omega) (hXU ha) (hYU hyY) (haY y hy) (hza ▸ hyz)
  · have hzb : z ≠ b := by
      intro h
      exact hf a 3 (by decide) (by omega)
        (.step (hYU hyY) (haY y hy) (.step (hYU hb) (h ▸ hyz) (.step (hXU ha) hba (.refl a))))
    exact hsink z (Finset.mem_erase.mpr ⟨hzb, hzY⟩) hyz

end LeanCH.BR.BRsGen
