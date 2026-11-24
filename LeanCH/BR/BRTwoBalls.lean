import LeanCH.BR.BRq3Base

/-! Complementary ball radii and double counting on arbitrary finite hosts. -/

namespace LeanCH.BR.BRq3

open BRq2

variable {D : CH.Digraph} {W : Finset ℕ}

/-- Forward lower bounds at complementary radii force an order bound.
The reverse ball is averaged; no minimum in-degree is assumed. -/
theorem card_ge_of_two_balls {q i j a b : ℕ} (hf : QFree D W q)
    (hij : i + j ≤ q) (hi : ∀ v ∈ W, a ≤ (ball D W v i).card)
    (hj : ∀ v ∈ W, b ≤ (ball D W v j).card) (hne : W.Nonempty) :
    a + b ≤ W.card + 1 := by
  classical
  let E : CH.Digraph := fun v w => decide (w ∈ ball D W v j)
  have hout (v : ℕ) : outN E W v = ball D W v j := by
    ext w
    simp only [mem_outN, E, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun h => ⟨ball_subset h, h⟩⟩
  have hin (v : ℕ) (hv : v ∈ W) :
      (W.filter (fun w => E w v = true)).card ≤ W.card + 1 - a := by
    let R := W.filter (fun w => E w v = true)
    have hsub : R ⊆ (W \ ball D W v i) ∪ {v} := by
      intro w hw
      obtain ⟨hwW, hE⟩ := Finset.mem_filter.mp hw
      have hback : v ∈ ball D W w j := of_decide_eq_true hE
      by_cases hwv : w = v
      · exact Finset.mem_union_right _ (Finset.mem_singleton.mpr hwv)
      · apply Finset.mem_union_left
        refine Finset.mem_sdiff.mpr ⟨hwW, ?_⟩
        intro hforward
        obtain ⟨_, m, hm, wm⟩ := mem_ball.mp hforward
        obtain ⟨_, n, hn, wn⟩ := mem_ball.mp hback
        have hmpos : 0 < m := by
          cases m with
          | zero => cases wm; exact (hwv rfl).elim
          | succ m => omega
        exact hf v (m + n) (by omega) (by omega) (wm.append wn)
    have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    rw [Finset.card_sdiff_of_subset ball_subset, Finset.card_singleton] at hc
    have hbi := hi v hv
    have hle := Finset.card_le_card (ball_subset (D := D) (W := W) (u := v) (k := i))
    change R.card ≤ _
    omega
  have hsum : W.card * b ≤ W.card * (W.card + 1 - a) := by
    calc
      W.card * b = ∑ _v ∈ W, b := (Finset.sum_const_nat (fun _ _ => rfl)).symm
      _ ≤ ∑ v ∈ W, (outN E W v).card := Finset.sum_le_sum (fun v hv => by rw [hout]; exact hj v hv)
      _ = ∑ v ∈ W, (W.filter (fun w => E w v = true)).card := Compose.ThinRigid.sum_out_eq_sum_in E W
      _ ≤ ∑ _v ∈ W, (W.card + 1 - a) := Finset.sum_le_sum hin
      _ = W.card * (W.card + 1 - a) := Finset.sum_const_nat (fun _ _ => rfl)
  have hb := Nat.le_of_mul_le_mul_left hsum (Finset.card_pos.mpr hne)
  obtain ⟨v, hv⟩ := hne
  have ha := (hi v hv).trans (Finset.card_le_card ball_subset)
  omega

end LeanCH.BR.BRq3
