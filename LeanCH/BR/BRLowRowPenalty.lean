import LeanCH.BR.BRSmallHighSet

/-! A sharp weighted row bound on sets at most one above the cycle cutoff. -/

namespace LeanCH.BR.BRsGen
open BRq2 BRq3 BR45

def lowExitCredit (d : ℕ) : ℕ := min 2 (3 - d)

theorem low_row_penalty (d : ℕ) : 3 ≤ d + 4 * lowExitCredit d := by
  unfold lowExitCredit
  omega

theorem low_row_penalty_of_le_one {d : ℕ} (hd : d ≤ 1) :
    8 ≤ d + 4 * lowExitCredit d := by
  unfold lowExitCredit
  omega

theorem low_row_penalty_of_le_two {d : ℕ} (hd : d ≤ 2) :
    6 ≤ d + 4 * lowExitCredit d := by
  unfold lowExitCredit
  omega

theorem near_boundary_low_row_penalty {D : CH.Digraph} {L : Finset ℕ} {q : ℕ}
    (hq : 2 ≤ q) (hf : QFree D L q) (hlo : 3 ≤ L.card) (hsmall : L.card ≤ q + 1) :
    3 * L.card + 13 ≤ (∑ v ∈ L, (outN D L v).card) +
      4 * ∑ v ∈ L, lowExitCredit (outN D L v).card := by
  classical
  let f := fun v => (outN D L v).card + 4 * lowExitCredit (outN D L v).card
  have htotal : 3 * L.card + 13 ≤ ∑ v ∈ L, f v := by
    by_cases hmin : ∀ v ∈ L, 1 ≤ (outN D L v).card
    · have hsize := dt_size (by omega : 1 ≤ q) (ball_q_one q (by omega)) hf hmin
        (Finset.card_pos.mp (by omega))
      have hreg := (dt_reg (by omega : 1 ≤ q) (ball_q_one q (by omega)) hf hmin
        (by omega : L.card = q * 1 + 1)).1
      have he : ∀ v ∈ L, f v = 9 := by
        intro v hv
        simp [f, hreg v hv, lowExitCredit]
      rw [Finset.sum_const_nat he]
      omega
    · push Not at hmin
      obtain ⟨z, hz, hzsmall⟩ := hmin
      have hzcap : 8 ≤ f z := low_row_penalty_of_le_one (by omega)
      let L1 := L.erase z
      have hL1L : L1 ⊆ L := Finset.erase_subset _ _
      have hL1c : L1.card = L.card - 1 := Finset.card_erase_of_mem hz
      have hLp : 0 < L.card := Finset.card_pos.mpr ⟨z, hz⟩
      obtain ⟨y, hy, hys⟩ := exists_sink (hf.mono_set hL1L)
        (Finset.card_pos.mp (by omega)) (by omega)
      let L2 := L1.erase y
      have hL2L1 : L2 ⊆ L1 := Finset.erase_subset _ _
      have hL2c : L2.card = L1.card - 1 := Finset.card_erase_of_mem hy
      have hL1p : 0 < L1.card := Finset.card_pos.mpr ⟨y, hy⟩
      obtain ⟨x, hx, hxs⟩ := exists_sink (hf.mono_set (hL2L1.trans hL1L))
        (Finset.card_pos.mp (by omega)) (by omega)
      have hL2p : 0 < L2.card := Finset.card_pos.mpr ⟨x, hx⟩
      have hcap : ∀ R ⊆ L, ∀ v ∈ R, (∀ w ∈ R, ¬ D v w = true) →
          (outN D L v).card ≤ (L \ R).card := by
        intro R hRL v hv hsink
        apply Finset.card_le_card
        intro w hw
        exact Finset.mem_sdiff.mpr
          ⟨(mem_outN.mp hw).1, fun hwR => hsink w hwR (mem_outN.mp hw).2⟩
      have hycap : 8 ≤ f y := by
        apply low_row_penalty_of_le_one
        have hh := hcap L1 hL1L y hy hys
        have hc := Finset.card_sdiff_add_card_eq_card hL1L
        omega
      have hxcap : 6 ≤ f x := by
        apply low_row_penalty_of_le_two
        have hh := hcap L2 (hL2L1.trans hL1L) x hx hxs
        have hc := Finset.card_sdiff_add_card_eq_card (hL2L1.trans hL1L)
        omega
      have hs := Finset.sum_le_sum (s := L2.erase x)
        (fun v _ => low_row_penalty (outN D L v).card)
      change (∑ _v ∈ L2.erase x, 3) ≤ ∑ v ∈ L2.erase x, f v at hs
      rw [Finset.sum_const_nat (fun _ _ => rfl)] at hs
      have hs0 := Finset.sum_erase_add L f hz
      have hs1 := Finset.sum_erase_add L1 f hy
      have hs2 := Finset.sum_erase_add L2 f hx
      change (∑ v ∈ L1, f v) + _ = _ at hs0
      change (∑ v ∈ L2, f v) + _ = _ at hs1
      have hc2 := Finset.card_erase_of_mem hx
      omega
  simpa only [f, Finset.sum_add_distrib, Finset.mul_sum] using htotal

end LeanCH.BR.BRsGen
