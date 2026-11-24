import LeanCH.BR.BRWeightedDeletionThreshold
import LeanCH.BR.BRSerialChain
import LeanCH.BR.BRCycleReturn

/-! Exact weighted interfaces of shortest cycles, with both graph orientations
kept separate. The cycle incidence restriction is used with actual q-freeness. -/
namespace LeanCH.BR.WeightedSD
open Finset BRq2 BRq3 BR45 BRsub BRsGen

def cycleRichReceivers (D : CH.Digraph) (V M : Finset ℕ) : Finset ℕ :=
  (V \ M).filter (fun z => 2 ≤ (inN D M z).card)

def cycleRichSenders (D : CH.Digraph) (V M : Finset ℕ) : Finset ℕ :=
  (V \ M).filter (fun z => 2 ≤ (outN D M z).card)

theorem sum_outW_cycle_incidence (D : CH.Digraph) (V M : Finset ℕ) (w : ℕ → ℚ) :
    (∑ v ∈ M, outW D V w v) = ∑ z ∈ V, ((inN D M z).card : ℚ) * w z := by
  unfold outW
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  calc
    _ = ∑ _v ∈ inN D M z, w z := by simp only [inN, Finset.sum_filter]
    _ = _ := by simp

/-- The complete exterior budget, with no replacement of w by the dual p. -/
theorem cycle_outside_balance {q : ℕ} {D : CH.Digraph} {V M : Finset ℕ}
    (hMV : M ⊆ V) (hM : M.card = q + 1)
    (hin : ∀ v ∈ M, (inN D M v).card = 1)
    (w : ℕ → ℚ) (c : ℚ) (hr : ∀ v ∈ M, row q D V w v = c) :
    (∑ z ∈ V \ M, ((q : ℚ) * (inN D M z).card - (q + 1)) * w z) =
      (q + 1) * (c - mass V w) := by
  have hcard : (M.card : ℚ) = q + 1 := by exact_mod_cast hM
  have hs : (∑ v ∈ M, row q D V w v) = (q + 1) * c := by
    simp only [Finset.sum_congr rfl (fun v hv => hr v hv), Finset.sum_const,
      nsmul_eq_mul, hcard]
  simp only [row, Finset.sum_add_distrib, ← Finset.mul_sum,
    sum_outW_cycle_incidence] at hs
  have hi : (∑ z ∈ M, ((inN D M z).card : ℚ) * w z) = mass M w := by
    apply Finset.sum_congr rfl
    intro z hz
    rw [hin z hz]
    simp
  have hsplit := Finset.sum_sdiff hMV (f := fun z => ((inN D M z).card : ℚ) * w z)
  rw [hi] at hsplit
  have hm : mass (V \ M) w + mass M w = mass V w := Finset.sum_sdiff hMV
  simp only [sub_mul, mul_assoc, Finset.sum_sub_distrib, ← Finset.mul_sum]
  change (q : ℚ) * (∑ z ∈ V \ M, ((inN D M z).card : ℚ) * w z) -
    (q + 1) * mass (V \ M) w = _
  change mass M w + (q : ℚ) * (∑ z ∈ V, ((inN D M z).card : ℚ) * w z) = _ at hs
  rw [← hsplit] at hs
  rw [← hm]
  nlinarith

theorem cycle_reverse_outside_balance {q : ℕ} {D : CH.Digraph} {V M : Finset ℕ}
    (hMV : M ⊆ V) (hM : M.card = q + 1) (hout : OutEq 1 D M)
    (p : ℕ → ℚ) (c : ℚ) (hc : ∀ v ∈ M, col q D V p v = c) :
    (∑ z ∈ V \ M, ((q : ℚ) * (outN D M z).card - (q + 1)) * p z) =
      (q + 1) * (c - mass V p) :=
  cycle_outside_balance (D := fun x y => D y x) hMV hM hout p c hc

/-- Keep the mass of all non-rich exterior vertices as a debit. -/
theorem cycle_rich_receiver_mass {q : ℕ} {D : CH.Digraph} {V M : Finset ℕ}
    (hMV : M ⊆ V) (hM : M.card = q + 1)
    (hin : ∀ v ∈ M, (inN D M v).card = 1)
    (w : ℕ → ℚ) (hw : ∀ v ∈ V, 0 ≤ w v) (c : ℚ)
    (hr : ∀ v ∈ M, row q D V w v = c) :
    (q + 1) * (c - mass V w) + mass (V \ M) w ≤
      (q : ℚ)^2 * mass (cycleRichReceivers D V M) w := by
  have hterm : ∀ z ∈ V \ M,
      ((q : ℚ) * (inN D M z).card - (q + 1)) * w z ≤
        (q : ℚ)^2 * (if 2 ≤ (inN D M z).card then w z else 0) - w z := by
    intro z hz
    have hwn := hw z (Finset.mem_sdiff.mp hz).1
    by_cases hrich : 2 ≤ (inN D M z).card
    · rw [if_pos hrich]
      have hle : ((inN D M z).card : ℚ) ≤ q + 1 := by
        exact_mod_cast (show (inN D M z).card ≤ q + 1 from
          (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq hM)
      have hq : (0 : ℚ) ≤ q := Nat.cast_nonneg q
      nlinarith [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hle hq) hwn]
    · rw [if_neg hrich, mul_zero, zero_sub]
      have hle : ((inN D M z).card : ℚ) ≤ 1 := by
        exact_mod_cast (show (inN D M z).card ≤ 1 by omega)
      have hq : (0 : ℚ) ≤ q := Nat.cast_nonneg q
      nlinarith [mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hle hq) hwn]
  have hs := Finset.sum_le_sum hterm
  rw [cycle_outside_balance hMV hM hin w c hr] at hs
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum] at hs
  have he : (∑ z ∈ V \ M, if 2 ≤ (inN D M z).card then w z else 0) =
      mass (cycleRichReceivers D V M) w := by
    simp only [mass, cycleRichReceivers, Finset.sum_filter]
  rw [he] at hs
  change _ ≤ (q : ℚ)^2 * mass (cycleRichReceivers D V M) w - mass (V \ M) w at hs
  linarith

theorem cycle_rich_sender_mass {q : ℕ} {D : CH.Digraph} {V M : Finset ℕ}
    (hMV : M ⊆ V) (hM : M.card = q + 1) (hout : OutEq 1 D M)
    (p : ℕ → ℚ) (hp : ∀ v ∈ V, 0 ≤ p v) (c : ℚ)
    (hc : ∀ v ∈ M, col q D V p v = c) :
    (q + 1) * (c - mass V p) + mass (V \ M) p ≤
      (q : ℚ)^2 * mass (cycleRichSenders D V M) p :=
  cycle_rich_receiver_mass (D := fun x y => D y x) hMV hM hout p hp c hc

theorem cycle_rich_receivers_nonempty {q : ℕ} {D : CH.Digraph} {V M : Finset ℕ}
    (hMV : M ⊆ V) (hM : M.card = q + 1)
    (hin : ∀ v ∈ M, (inN D M v).card = 1)
    (w : ℕ → ℚ) (hw : ∀ v ∈ V, 0 ≤ w v) (c : ℚ)
    (hr : ∀ v ∈ M, row q D V w v = c) (hc : mass V w < c) :
    (cycleRichReceivers D V M).Nonempty := by
  have hb := cycle_rich_receiver_mass hMV hM hin w hw c hr
  have hm : 0 ≤ mass (V \ M) w := Finset.sum_nonneg
    (fun v hv => hw v (Finset.mem_sdiff.mp hv).1)
  have hpos : 0 < ((q : ℚ) + 1) * (c - mass V w) :=
    mul_pos (by positivity) (sub_pos.mpr hc)
  by_contra hn
  have he := Finset.not_nonempty_iff_eq_empty.mp hn
  rw [he] at hb
  simp only [mass, Finset.sum_empty, mul_zero] at hb
  change ((q : ℚ) + 1) * (c - mass V w) + mass (V \ M) w ≤ 0 at hb
  linarith

theorem cycle_rich_senders_nonempty {q : ℕ} {D : CH.Digraph} {V M : Finset ℕ}
    (hMV : M ⊆ V) (hM : M.card = q + 1) (hout : OutEq 1 D M)
    (p : ℕ → ℚ) (hp : ∀ v ∈ V, 0 ≤ p v) (c : ℚ)
    (hc : ∀ v ∈ M, col q D V p v = c) (hstrict : mass V p < c) :
    (cycleRichSenders D V M).Nonempty :=
  cycle_rich_receivers_nonempty (D := fun x y => D y x) hMV hM hout p hp c hc hstrict

theorem cycle_rich_sets_disjoint {q : ℕ} (hq : 2 ≤ q) {D : CH.Digraph} {V M : Finset ℕ}
    (hf : QFree D V q) (hMV : M ⊆ V) (hM : M.card = q + 1) (hout : OutEq 1 D M) :
    Disjoint (cycleRichReceivers D V M) (cycleRichSenders D V M) := by
  apply Finset.disjoint_left.mpr
  intro z hzI hzO
  obtain ⟨hz, hi⟩ := Finset.mem_filter.mp hzI
  have ho := (Finset.mem_filter.mp hzO).2
  have hh := cycle_two_sided_contact_cap hq hf hMV hM hout (Finset.mem_sdiff.mp hz).1
    (Finset.card_pos.mp (by omega)) (Finset.card_pos.mp (by omega))
  omega

end LeanCH.BR.WeightedSD
