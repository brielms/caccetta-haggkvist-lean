import LeanCH.BR.BRWeightedOrderCongruence
import LeanCH.BR.BRWeightedCommonParentTransfer

/-! Arithmetic of actual induced unit cores. The subset non-tightness is
the existing checked integer-linear-form rigidity, not a new assumption. -/
namespace LeanCH.BR.WeightedSD
open Finset BRq2 BRq3 BR45 BRsub Matrix WeightedArithmetic
open scoped Matrix

theorem unit_core_columns_of_selfDual {q : ℕ} {D : CH.Digraph} {S : Finset ℕ}
    (hSD : SelfDual q D S) (z : ℕ → ℚ) (hz : ∀ x ∈ S, 0 < z x)
    (hm : mass S z = 1) (hr : ∀ x ∈ S, row q D S z x = 1) :
    ∀ x ∈ S, col q D S z x = 1 := by
  have hc := hSD z (fun x hx => (hz x hx).le) (fun x hx => by rw [hm,hr x hx])
  have ht : ∀ x ∈ S, z x * col q D S z x ≤ z x * 1 := by
    intro x hx
    exact mul_le_mul_of_nonneg_left (by simpa only [hm] using hc x hx) (hz x hx).le
  have he : (∑ x ∈ S, z x * col q D S z x) = ∑ x ∈ S, z x * 1 := by
    rw [← row_col_balance]
    exact sum_congr rfl (fun x hx => by rw [hr x hx])
  intro x hx
  exact mul_left_cancel₀ (ne_of_gt (hz x hx)) ((sum_eq_sum_iff_of_le ht).mp he x hx)

theorem unit_row_subset_mass_ne {q : ℕ} (hq : 2 ≤ q) {D : CH.Digraph}
    {S F : Finset ℕ} (hFS : F ⊆ S) (z : ℕ → ℚ)
    (hr : ∀ x ∈ S, row q D S z x = 1) : (q : ℚ) * mass F z ≠ 1 := by
  have hM : rationalMatrix q (adjacencyMatrix D S) *ᵥ (fun i : S => z i) = fun _ => 1 := by
    funext i; exact (matrix_row q D S z i).trans (hr i i.property)
  let c : S → ℤ := fun i => if (i : ℕ) ∈ F then 1 else 0
  have hfilter : S.filter (fun i => i ∈ F) = F := by
    ext i
    simp only [mem_filter]
    exact and_iff_right_of_imp (fun hi => hFS hi)
  have hs : (∑ i : S, (c i : ℚ) * z i) = mass F z := by
    simp only [c,Int.cast_ite,Int.cast_one,Int.cast_zero,ite_mul,one_mul,zero_mul]
    rw [sum_coe_sort S (fun i => if i ∈ F then z i else 0),← sum_filter,hfilter]
    rfl
  simpa only [hs] using no_integer_linear_form_unit hq (adjacencyMatrix D S) (fun i : S => z i) hM c

theorem unit_core_complement_dvd (q : ℕ) {D : CH.Digraph} {V S : Finset ℕ}
    (hSV : S ⊆ V) (a z : ℕ → ℚ) (ham : mass V a = 1) (hzm : mass S z = 1)
    (har : ∀ x ∈ V, row q D V a x = 1) (hzr : ∀ x ∈ S, row q D S z x = 1) :
    q ∣ (V \ S).card := by
  have hV := normalized_rows_card_mod q D V a ham har
  have hS := normalized_rows_card_mod q D S z hzm hzr
  have he : ((V \ S).card : ZMod q) + (S.card : ZMod q) = (V.card : ZMod q) := by
    simpa only [Nat.cast_add] using congrArg (fun n : ℕ => (n : ZMod q)) (card_sdiff_add_card_eq_card hSV)
  rw [hV,hS] at he
  apply (ZMod.natCast_eq_zero_iff _ _).mp
  simpa only [add_eq_right] using he

theorem unit_core_complement_lower {q : ℕ} {D : CH.Digraph} {V S : Finset ℕ}
    (hSV : S ⊆ V) (hne : S ≠ V) (a z : ℕ → ℚ) (ham : mass V a = 1) (hzm : mass S z = 1)
    (har : ∀ x ∈ V, row q D V a x = 1) (hzr : ∀ x ∈ S, row q D S z x = 1) :
    q ≤ (V \ S).card := by
  have hpos : 0 < (V \ S).card := by
    apply card_pos.mpr
    exact sdiff_nonempty.mpr (fun hVS => hne (Subset.antisymm hSV hVS))
  exact Nat.le_of_dvd hpos (unit_core_complement_dvd q hSV a z ham hzm har hzr)

end LeanCH.BR.WeightedSD
