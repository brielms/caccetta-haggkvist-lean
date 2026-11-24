import LeanCH.BR.BRsubSetBall
import LeanCH.BR.BRNarrowPair

/-! A strict improvement of the five-set growth bound at degree six. -/

namespace LeanCH.BR.BRsub

open BRq2 BRq3 BR45

variable {E : CH.Digraph} {V Y : Finset ℕ}

private theorem retained_min {k c : ℕ}
    (hout : ∀ x ∈ ballSet E V Y k, 6 ≤ (outN E V x).card)
    (hnext : c + (ballSet E V Y (k + 1) \ ballSet E V Y k).card ≤ 6) :
    ∀ x ∈ ballSet E V Y k, c ≤ (outN E (ballSet E V Y k) x).card := by
  intro x hx
  let A := ballSet E V Y k
  let B := ballSet E V Y (k + 1) \ A
  have hsub : outN E V x ⊆ outN E (A ∪ B) x := by
    intro z hz
    have hz' := outN_subset_ballSet_succ hx hz
    exact mem_outN.mpr ⟨Finset.mem_union.mpr (or_iff_not_imp_left.mpr
      (fun h => Finset.mem_sdiff.mpr ⟨hz', h⟩)), (mem_outN.mp hz).2⟩
  have hle := Finset.card_le_card hsub
  rw [card_outN_union Finset.disjoint_sdiff] at hle
  change (outN E V x).card ≤ (outN E A x).card + (outN E B x).card at hle
  have hb := Finset.card_le_card (outN_subset (D := E) (W := B) (y := x))
  have h6 := hout x hx
  change c + B.card ≤ 6 at hnext
  change c ≤ (outN E A x).card
  omega

private theorem mixed_count {U T : Finset ℕ} {c : ℕ} (hc : 1 ≤ c) (hc4 : c ≤ 4)
    (hf : QFree E U 5) (hTU : T ⊆ U)
    (hmin : ∀ v ∈ U, c ≤ (outN E U v).card)
    (hhigh : ∀ v ∈ T, 6 ≤ (outN E U v).card) :
    T.card * 6 + (U \ T).card * c ≤ U.card * (U.card - (4 * c + 1)) := by
  have hball := ball_of_min (ball_five_small hc hc4) hf hmin
  have hin : ∀ v ∈ U, (inN E U v).card ≤ U.card - (4 * c + 1) := by
    intro v hv
    have hsub : inN E U v ⊆ U \ ball E U v 4 := by
      intro z hz
      exact Finset.mem_sdiff.mpr ⟨(mem_inN.mp hz).1,
        fun hzB => no_back_arc hf hv hzB (by decide) (mem_inN.mp hz).2⟩
    have h := Finset.card_le_card hsub
    rw [Finset.card_sdiff_of_subset ball_subset] at h
    have hb := hball v hv
    change c * 4 + 1 ≤ (ball E U v 4).card at hb
    omega
  have hlo := Finset.sum_le_sum (fun v hv => hmin v (Finset.mem_sdiff.mp hv).1) (s := U \ T)
  have hhi := Finset.sum_le_sum hhigh
  have hup := Finset.sum_le_sum hin
  rw [Finset.sum_const_nat (fun _ _ => rfl)] at hlo hhi hup
  have he := Finset.sum_sdiff hTU (f := fun v => (outN E U v).card)
  have hsum : ∑ v ∈ U, (outN E U v).card = ∑ v ∈ U, (inN E U v).card :=
    Compose.ThinRigid.sum_out_eq_sum_in E U
  omega

private theorem retained_high {k : ℕ} (hout : ∀ x ∈ ballSet E V Y k, 6 ≤ (outN E V x).card) :
    ∀ x ∈ ballSet E V Y k, 6 ≤ (outN E (ballSet E V Y (k + 1)) x).card := by
  intro x hx
  exact (hout x hx).trans (Finset.card_le_card (fun z hz =>
    mem_outN.mpr ⟨outN_subset_ballSet_succ hx hz, (mem_outN.mp hz).2⟩))

/-- A five-set followed by layers of sizes six and five forces a tight
six-module, and every starting vertex heads that module. -/
theorem set_module_65 (hf : QFree E V 5) (hYV : Y ⊆ V) (hY : Y.card = 5)
    (hout : ∀ x ∈ ballSet E V Y 2, 6 ≤ (outN E V x).card)
    (hB : (ballSet E V Y 1 \ Y).card = 6)
    (hC : (ballSet E V Y 2 \ ballSet E V Y 1).card = 5) :
    (∀ b ∈ ballSet E V Y 1 \ Y, (outN E V b).card = 6 ∧
      (outN E (ballSet E V Y 1 \ Y) b).card = 1 ∧
      (inN E (ballSet E V Y 1 \ Y) b).card = 1) ∧
    (∀ b ∈ ballSet E V Y 1 \ Y, ∀ c ∈ ballSet E V Y 2 \ ballSet E V Y 1, E b c = true) ∧
    (∀ y ∈ Y, ∃ b ∈ ballSet E V Y 1 \ Y, E y b = true) := by
  classical
  let B := ballSet E V Y 1 \ Y
  let C := ballSet E V Y 2 \ ballSet E V Y 1
  have hB1 : Y ∪ B = ballSet E V Y 1 := Finset.union_sdiff_of_subset (subset_ballSet hYV)
  have hC2 : (Y ∪ B) ∪ C = ballSet E V Y 2 := by
    rw [hB1]; exact Finset.union_sdiff_of_subset (ballSet_mono (by decide))
  have hY2 : Y ⊆ ballSet E V Y 2 := subset_ballSet hYV
  have hBV : B ⊆ V := fun _ hb => ballSet_subset (Finset.mem_sdiff.mp hb).1
  have hCV : C ⊆ V := fun _ hc => ballSet_subset (Finset.mem_sdiff.mp hc).1
  have hhigh : ∀ y ∈ Y, 6 ≤ (outN E (Y ∪ B) y).card := by
    intro y hy
    rw [hB1]
    exact (hout y (hY2 hy)).trans (Finset.card_le_card (fun z hz => mem_outN.mpr
      ⟨mem_ballSet.mpr ⟨y, hy, ball_of_adj (mem_outN.mp hz).1 (mem_outN.mp hz).2⟩, (mem_outN.mp hz).2⟩))
  have hlow : ∀ b ∈ B, 1 ≤ (outN E (Y ∪ B) b).card := by
    intro b hb
    rw [hB1]
    exact retained_min (k := 1) (c := 1)
      (fun x hx => hout x (ballSet_mono (by decide) hx))
      (by change 1 + (ballSet E V Y 2 \ ballSet E V Y 1).card ≤ 6; omega)
      b (Finset.mem_sdiff.mp hb).1
  have hback := BRsGen.narrow_pair_no_back (s := 6) (by decide)
    (hf.mono_set (by rw [hB1]; exact ballSet_subset)) Finset.disjoint_sdiff hY hB hhigh hlow
  have hminB : ∀ b ∈ B, 1 ≤ (outN E B b).card := by
    intro b hb
    have hsub : outN E (Y ∪ B) b ⊆ outN E B b := by
      intro z hz
      obtain ⟨hzU, hbz⟩ := mem_outN.mp hz
      rcases Finset.mem_union.mp hzU with hy | hzB
      · exact (hback b hb z hy hbz).elim
      · exact mem_outN.mpr ⟨hzB, hbz⟩
    exact (hlow b hb).trans (Finset.card_le_card hsub)
  have hreg := dt_reg (q := 5) (s := 1) (by decide) (ball_q_one 5 (by decide))
    (hf.mono_set hBV) hminB hB
  have hBC : ∀ b ∈ B, outN E V b ⊆ outN E (B ∪ C) b := by
    intro b hb z hz
    have hz2 := outN_subset_ballSet_succ (Finset.mem_sdiff.mp hb).1 hz
    rw [← hC2] at hz2
    obtain (hzY | hzB) | hzC := Finset.mem_union.mp hz2 |>.elim
      (fun h => Or.inl (Finset.mem_union.mp h)) Or.inr
    · exact (hback b hb z hzY (mem_outN.mp hz).2).elim
    · exact mem_outN.mpr ⟨Finset.mem_union_left _ hzB, (mem_outN.mp hz).2⟩
    · exact mem_outN.mpr ⟨Finset.mem_union_right _ hzC, (mem_outN.mp hz).2⟩
  have hBCdisj : Disjoint B C := Finset.disjoint_left.mpr (fun z hzB hzC =>
    (Finset.mem_sdiff.mp hzC).2 (Finset.mem_sdiff.mp hzB).1)
  have hall : ∀ b ∈ B, ∀ c ∈ C, E b c = true := by
    intro b hb
    have h6 := hout b (ballSet_mono (by decide) (Finset.mem_sdiff.mp hb).1)
    have hle := Finset.card_le_card (hBC b hb)
    rw [card_outN_union hBCdisj, hreg.1 b hb] at hle
    have heq : outN E C b = C := Finset.eq_of_subset_of_card_le outN_subset (by
      change C.card = 5 at hC
      omega)
    intro c hc
    exact (mem_outN.mp (heq.symm ▸ hc)).2
  have hYhead : ∀ y ∈ Y, ∃ b ∈ B, E y b = true := by
    intro y hy
    by_contra h
    push Not at h
    have hsub : outN E (Y ∪ B) y ⊆ Y := by
      intro z hz
      exact (Finset.mem_union.mp (mem_outN.mp hz).1).resolve_right (fun hb => h z hb (mem_outN.mp hz).2)
    have hle := Finset.card_le_card hsub
    have h6 := hhigh y hy
    omega
  refine ⟨?_, hall, hYhead⟩
  intro b hb
  refine ⟨?_, hreg.1 b hb, hreg.2 b hb⟩
  have hle := Finset.card_le_card (hBC b hb)
  rw [card_outN_union hBCdisj, hreg.1 b hb] at hle
  have hCcap := Finset.card_le_card (outN_subset (D := E) (W := C) (y := b))
  have h6 := hout b (ballSet_mono (by decide) (Finset.mem_sdiff.mp hb).1)
  change C.card = 5 at hC
  omega

/-- The remaining `5,6,5,4` set-layer profile is impossible. -/
private theorem no_654 (hf : QFree E V 5) (hYV : Y ⊆ V) (hY : Y.card = 5)
    (hout : ∀ x ∈ ballSet E V Y 2, 6 ≤ (outN E V x).card)
    (hB : (ballSet E V Y 1 \ Y).card = 6)
    (hC : (ballSet E V Y 2 \ ballSet E V Y 1).card = 5)
    (hK : (ballSet E V Y 3 \ ballSet E V Y 2).card = 4) : False := by
  let B := ballSet E V Y 1 \ Y
  let C := ballSet E V Y 2 \ ballSet E V Y 1
  let K := ballSet E V Y 3 \ ballSet E V Y 2
  have hBV : B ⊆ V := fun _ hb => ballSet_subset (Finset.mem_sdiff.mp hb).1
  have hCV : C ⊆ V := fun _ hc => ballSet_subset (Finset.mem_sdiff.mp hc).1
  have hB1 : Y ∪ B = ballSet E V Y 1 := Finset.union_sdiff_of_subset (subset_ballSet hYV)
  have hC2 : (Y ∪ B) ∪ C = ballSet E V Y 2 := by
    rw [hB1]; exact Finset.union_sdiff_of_subset (ballSet_mono (by decide))
  obtain ⟨_, hall, hYhead⟩ := set_module_65 hf hYV hY hout hB hC
  obtain ⟨c, hc, hcsink⟩ := exists_sink (hf.mono_set hCV)
    (show C.Nonempty by rw [← Finset.card_pos]; change C.card = 5 at hC; omega) hC.le
  have hsub : outN E V c ⊆ K := by
    intro z hz
    have hz3 := outN_subset_ballSet_succ (Finset.mem_sdiff.mp hc).1 hz
    refine Finset.mem_sdiff.mpr ⟨hz3, ?_⟩
    intro hz2
    rw [← hC2] at hz2
    rcases Finset.mem_union.mp hz2 with hz1 | hzC
    · rcases Finset.mem_union.mp hz1 with hzY | hzB
      · obtain ⟨b, hb, hzb⟩ := hYhead z hzY
        exact hf z 3 (by decide) (by decide)
          (.step (hBV hb) hzb (.step (hCV hc) (hall b hb c hc)
            (.step (hYV hzY) (mem_outN.mp hz).2 (.refl z))))
      · exact digonfree hf (by decide) (hBV hzB) (hCV hc) (hall z hzB c hc) (mem_outN.mp hz).2
    · exact hcsink z hzC (mem_outN.mp hz).2
  have hle := Finset.card_le_card hsub
  have h6 := hout c (Finset.mem_sdiff.mp hc).1
  change K.card = 4 at hK
  omega

/-- Five starting vertices whose radius-two ball has minimum ambient
out-degree six reach at least twenty-one vertices within three steps. -/
theorem card_ballSet_three_ge_twenty_one (hf : QFree E V 5) (hYV : Y ⊆ V)
    (hY : Y.card = 5) (hout : ∀ x ∈ ballSet E V Y 2, 6 ≤ (outN E V x).card) :
    21 ≤ (ballSet E V Y 3).card := by
  by_contra hsmall
  have h20 := card_ballSet_three_ge_twenty hf hYV hY hout
  have hYne : Y.Nonempty := Finset.card_pos.mp (by omega)
  let b (k : ℕ) := (ballSet E V Y k).card
  let l (k : ℕ) := (ballSet E V Y (k + 1) \ ballSet E V Y k).card
  have hb : b 3 = 20 := by dsimp [b]; omega
  have h2 : l 1 + b 1 = b 2 := Finset.card_sdiff_add_card_eq_card (ballSet_mono (by decide))
  have h3 : l 2 + b 2 = b 3 := Finset.card_sdiff_add_card_eq_card (ballSet_mono (by decide))
  have hmin1 := fun x hx => hout x (ballSet_mono (by decide : 1 ≤ 2) hx)
  have hhighY : ∀ y ∈ Y, 6 ≤ (outN E (ballSet E V Y 1) y).card := by
    intro y hy
    exact (hout y (subset_ballSet hYV hy)).trans (Finset.card_le_card (fun z hz =>
      mem_outN.mpr ⟨mem_ballSet.mpr ⟨y, hy, ball_of_adj (mem_outN.mp hz).1 (mem_outN.mp hz).2⟩,
        (mem_outN.mp hz).2⟩))
  have h1 : 11 ≤ b 1 := by
    obtain ⟨y, hy, hsink⟩ := exists_sink (hf.mono_set hYV) hYne hY.le
    have hsub : outN E (ballSet E V Y 1) y ⊆ ballSet E V Y 1 \ Y := by
      intro z hz
      exact Finset.mem_sdiff.mpr ⟨(mem_outN.mp hz).1, fun hzY => hsink z hzY (mem_outN.mp hz).2⟩
    have hc := Finset.card_sdiff_add_card_eq_card (subset_ballSet (k := 1) (E := E) hYV)
    have hle := (hhighY y hy).trans (Finset.card_le_card hsub)
    change 11 ≤ (ballSet E V Y 1).card
    omega
  have htest₁ (c : ℕ) (hc : 1 ≤ c) (hc4 : c ≤ 4) (h : c + l 1 ≤ 6) : 5 * c + 2 ≤ b 1 :=
    ballSet_deletion (k := 0) hc hc4 hf hYV hYne hmin1 h
  have htest₂ (c : ℕ) (hc : 1 ≤ c) (hc4 : c ≤ 4) (h : c + l 2 ≤ 6) : 5 * c + 2 ≤ b 2 :=
    ballSet_deletion (k := 1) hc hc4 hf hYV hYne hout h
  have h12 : l 1 ≤ 4 → 12 ≤ b 1 := fun h => htest₁ 2 (by decide) (by decide) (by omega)
  have h13 : l 1 ≤ 3 → 17 ≤ b 1 := fun h => htest₁ 3 (by decide) (by decide) (by omega)
  have h14 : l 1 ≤ 2 → 22 ≤ b 1 := fun h => htest₁ 4 (by decide) (by decide) (by omega)
  have h22 : l 2 ≤ 4 → 12 ≤ b 2 := fun h => htest₂ 2 (by decide) (by decide) (by omega)
  have h23 : l 2 ≤ 3 → 17 ≤ b 2 := fun h => htest₂ 3 (by decide) (by decide) (by omega)
  have h24 : l 2 ≤ 2 → 22 ≤ b 2 := fun h => htest₂ 4 (by decide) (by decide) (by omega)
  have hcases : (b 1 = 11 ∧ b 2 = 16) ∨ (b 2 = 17 ∧ l 2 = 3) ∨
      (b 1 = 12 ∧ l 1 = 4 ∧ l 2 = 4) := by omega
  rcases hcases with ⟨hb1, hb2⟩ | ⟨hb2, hl2⟩ | ⟨hb1, hl1, hl2⟩
  · apply no_654 hf hYV hY hout
    · have h := Finset.card_sdiff_add_card_eq_card (subset_ballSet (E := E) (k := 1) hYV)
      change (ballSet E V Y 1 \ Y).card + Y.card = b 1 at h
      omega
    · change l 1 = 5
      omega
    · change l 2 = 4
      omega
  · have hmin := retained_min (k := 2) (c := 3) hout (by change 3 + l 2 ≤ 6; omega)
    have h := mixed_count (c := 3) (by decide) (by decide) (hf.mono_set ballSet_subset)
      (ballSet_mono (by decide : 1 ≤ 2)) hmin (retained_high hmin1)
    change b 1 * 6 + l 1 * 3 ≤ b 2 * (b 2 - (4 * 3 + 1)) at h
    rw [hb2] at h
    norm_num at h
    omega
  · have hmin := retained_min (k := 1) (c := 2) hmin1 (by change 2 + l 1 ≤ 6; omega)
    have h := mixed_count (c := 2) (by decide) (by decide) (hf.mono_set ballSet_subset)
      (subset_ballSet hYV) hmin hhighY
    rw [Finset.card_sdiff_of_subset (subset_ballSet hYV)] at h
    change Y.card * 6 + (b 1 - Y.card) * 2 ≤ b 1 * (b 1 - (4 * 2 + 1)) at h
    rw [hb1, hY] at h
    norm_num at h

/-- The improved set-ball estimate bounds the outside parent set by four. -/
theorem tightModule_WM_le_four {M : Finset ℕ} (hf : QFree E V 5) (hV : V.card = 31)
    (hmin : ∀ x ∈ V, 6 ≤ (outN E V x).card) (hMV : M ⊆ V) (hYV : Y ⊆ V)
    (hM : M.card = 6) (hY : Y.card = 5) (hhead : ∀ x ∈ M, ∀ y ∈ Y, E x y = true) :
    (WM E V M Y 5).card ≤ 4 := by
  have hball := card_ballSet_three_ge_twenty_one hf hYV hY
    (fun x hx => hmin x (ballSet_subset hx))
  have hd : Disjoint M (ballSet E V Y 3) := (lemmaM_a (by decide) hf hMV hYV hhead).1
  have hsum := Finset.card_sdiff_add_card_eq_card
    (Finset.union_subset hMV (ballSet_subset (E := E) (Y := Y) (k := 3)))
  rw [Finset.card_union_of_disjoint hd, hV, hM] at hsum
  change (WM E V M Y 5).card + (6 + (ballSet E V Y 3).card) = 31 at hsum
  omega

/-- Tight-module members have in-degree at most five at boundary order 31. -/
theorem tightModule_in_le_five {M : Finset ℕ} (hf : QFree E V 5) (hsat : Sat 5 E V)
    (hV : V.card = 31) (hmin : ∀ x ∈ V, 6 ≤ (outN E V x).card)
    (hMV : M ⊆ V) (hYV : Y ⊆ V) (hM : M.card = 6) (hY : Y.card = 5)
    (hhead : ∀ x ∈ M, ∀ y ∈ Y, E x y = true) (hout : ∀ x ∈ M, (outN E V x).card = 6)
    (hcyc : ∀ x ∈ M, (outN E M x).card = 1 ∧ (inN E M x).card = 1)
    {x : ℕ} (hx : x ∈ M) : (inN E V x).card ≤ 5 := by
  rw [lemmaM_card (by decide : 5 + 1 = 6) (by decide) hf hsat hMV hYV hY hhead hout hcyc hx]
  have hw := tightModule_WM_le_four hf hV hmin hMV hYV hM hY hhead
  omega

/-- In a saturated `(5,6)` boundary graph, no five-set has successive
set layers of sizes six and five. Those five starters would all parent
the forced tight module, exceeding its four-parent cap. -/
theorem no_five_six_five_set_layers (hf : QFree E V 5) (hsat : Sat 5 E V)
    (hV : V.card = 31) (hmin : ∀ x ∈ V, 6 ≤ (outN E V x).card)
    (hYV : Y ⊆ V) (hY : Y.card = 5)
    (hB : (ballSet E V Y 1 \ Y).card = 6)
    (hC : (ballSet E V Y 2 \ ballSet E V Y 1).card = 5) : False := by
  let B := ballSet E V Y 1 \ Y
  let C := ballSet E V Y 2 \ ballSet E V Y 1
  have hBV : B ⊆ V := fun _ hb => ballSet_subset (Finset.mem_sdiff.mp hb).1
  have hCV : C ⊆ V := fun _ hc => ballSet_subset (Finset.mem_sdiff.mp hc).1
  obtain ⟨hdeg, hall, hYhead⟩ := set_module_65 hf hYV hY
    (fun x hx => hmin x (ballSet_subset hx)) hB hC
  have hcap := tightModule_WM_le_four hf hV hmin hBV hCV hB hC hall
  have hsub : Y ⊆ WM E V B C 5 := by
    intro y hy
    obtain ⟨b, hb, hyb⟩ := hYhead y hy
    have hin : y ∈ inN E V b := mem_inN.mpr ⟨hYV hy, hyb⟩
    rw [lemmaM (by decide : 5 + 1 = 6) (by decide) hf hsat hBV hCV hC hall
      (fun b hb => (hdeg b hb).1) (fun b hb => (hdeg b hb).2.1) hb] at hin
    rcases Finset.mem_union.mp hin with h | h
    · exact ((Finset.mem_sdiff.mp (mem_inN.mp h).1).2 hy).elim
    · exact h
  have hle := Finset.card_le_card hsub
  omega

/-- At the `(5,6)` boundary, every five-set reaches at least seventeen
vertices within two steps. This closes the full tight-first-layer branch. -/
theorem card_ballSet_two_ge_seventeen (hf : QFree E V 5) (hsat : Sat 5 E V)
    (hV : V.card = 31) (hmin : ∀ x ∈ V, 6 ≤ (outN E V x).card)
    (hYV : Y ⊆ V) (hY : Y.card = 5) : 17 ≤ (ballSet E V Y 2).card := by
  by_contra hsmall
  have hYne : Y.Nonempty := Finset.card_pos.mp (by omega)
  have hhighY : ∀ y ∈ Y, 6 ≤ (outN E (ballSet E V Y 1) y).card := by
    intro y hy
    exact (hmin y (hYV hy)).trans (Finset.card_le_card (fun z hz =>
      mem_outN.mpr ⟨mem_ballSet.mpr ⟨y, hy, ball_of_adj (mem_outN.mp hz).1 (mem_outN.mp hz).2⟩,
        (mem_outN.mp hz).2⟩))
  have h1 : 11 ≤ (ballSet E V Y 1).card := by
    obtain ⟨y, hy, hsink⟩ := exists_sink (hf.mono_set hYV) hYne hY.le
    have hsub : outN E (ballSet E V Y 1) y ⊆ ballSet E V Y 1 \ Y := by
      intro z hz
      exact Finset.mem_sdiff.mpr ⟨(mem_outN.mp hz).1, fun hzY => hsink z hzY (mem_outN.mp hz).2⟩
    have hc := Finset.card_sdiff_add_card_eq_card (subset_ballSet (k := 1) (E := E) hYV)
    have hle := (hhighY y hy).trans (Finset.card_le_card hsub)
    omega
  let l := (ballSet E V Y 2 \ ballSet E V Y 1).card
  have hsum : l + (ballSet E V Y 1).card = (ballSet E V Y 2).card :=
    Finset.card_sdiff_add_card_eq_card (ballSet_mono (by decide))
  have htest (c : ℕ) (hc : 1 ≤ c) (hc4 : c ≤ 4) (h : c + l ≤ 6) :
      5 * c + 2 ≤ (ballSet E V Y 1).card :=
    ballSet_deletion (k := 0) hc hc4 hf hYV hYne (fun x hx => hmin x (ballSet_subset hx)) h
  have h3 : 4 ≤ l := by
    by_contra h
    have ht := htest 3 (by decide) (by decide) (by omega)
    omega
  have hcases : (l = 4 ∧ (ballSet E V Y 1).card = 12) ∨
      (l = 5 ∧ (ballSet E V Y 1).card = 11) := by
    have h2 : l ≤ 4 → 12 ≤ (ballSet E V Y 1).card :=
      fun h => htest 2 (by decide) (by decide) (by omega)
    omega
  rcases hcases with ⟨hl, hb⟩ | ⟨hl, hb⟩
  · have hminA := retained_min (k := 1) (c := 2)
      (fun x hx => hmin x (ballSet_subset hx)) (by change 2 + l ≤ 6; omega)
    have h := mixed_count (c := 2) (by decide) (by decide) (hf.mono_set ballSet_subset)
      (subset_ballSet hYV) hminA hhighY
    rw [Finset.card_sdiff_of_subset (subset_ballSet hYV), hb, hY] at h
    norm_num at h
  · apply no_five_six_five_set_layers hf hsat hV hmin hYV hY
    · rw [Finset.card_sdiff_of_subset (subset_ballSet hYV), hb, hY]
    · exact hl

end LeanCH.BR.BRsub
