import LeanCH.BR.BRHighTwoCore
import LeanCH.BR.BRq3BallAll

/-! A degree-three core with many high rows cannot fit in order 2s+5. -/

namespace LeanCH.BR.BRsGen

open BRq2 BRq3 BR45

theorem three_core_high_rows_false {D : CH.Digraph} {W H : Finset ℕ} {s : ℕ}
    (hs : 6 ≤ s) (hf : QFree D W (s - 1)) (hcard : W.card ≤ 2 * s + 5)
    (hmin : ∀ v ∈ W, 3 ≤ (outN D W v).card)
    (hHW : H ⊆ W) (hH : H.card = s)
    (hhigh : ∀ v ∈ H, s ≤ (outN D W v).card) : False := by
  classical
  have hcap : ∀ v ∈ W, (inN D W v).card ≤ 4 := by
    intro v hv
    have hb := ball_of_min (BRq3.ball_all (s - 1) (by omega)) hf hmin v hv
    have hsub : inN D W v ⊆ W \ ball D W v (s - 1 - 1) := by
      intro x hx
      obtain ⟨hxW, hxv⟩ := mem_inN.mp hx
      exact Finset.mem_sdiff.mpr ⟨hxW, fun hxB => no_back_arc hf hv hxB (by omega) hxv⟩
    have hc := Finset.card_le_card hsub
    rw [Finset.card_sdiff_of_subset ball_subset] at hc
    have hbW := Finset.card_le_card
      (ball_subset (D := D) (W := W) (u := v) (k := s - 1 - 1))
    omega
  have hloH := Finset.sum_le_sum hhigh
  have hloL := Finset.sum_le_sum (fun v hv => hmin v (Finset.mem_sdiff.mp hv).1) (s := W \ H)
  have hup := Finset.sum_le_sum hcap
  rw [Finset.sum_const_nat (fun _ _ => rfl), hH] at hloH
  rw [Finset.sum_const_nat (fun _ _ => rfl)] at hloL hup
  have ho := Finset.sum_sdiff hHW (f := fun v => (outN D W v).card)
  have he : (∑ v ∈ W, (outN D W v).card) = ∑ v ∈ W, (inN D W v).card :=
    Compose.ThinRigid.sum_out_eq_sum_in D W
  have hc := Finset.card_sdiff_add_card_eq_card hHW
  rw [hH] at hc
  nlinarith [Nat.mul_le_mul_right s hs]

end LeanCH.BR.BRsGen
