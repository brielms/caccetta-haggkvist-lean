import LeanCH.BR.BRTwoBalls

/-! Equality in the complementary-radius count fixes both forward and reverse balls. -/

namespace LeanCH.BR.BRq3
open BRq2

noncomputable def reverseBall (D : CH.Digraph) (W : Finset ℕ) (v k : ℕ) : Finset ℕ :=
  W.filter (fun u => v ∈ ball D W u k)

theorem reverseBall_subset_complement {D : CH.Digraph} {W : Finset ℕ} {q i j v : ℕ}
    (hf : QFree D W q) (hij : i + j ≤ q) :
    reverseBall D W v j ⊆ (W \ ball D W v i) ∪ {v} := by
  intro w hw
  obtain ⟨hwW, hback⟩ := Finset.mem_filter.mp hw
  by_cases hwv : w = v
  · exact Finset.mem_union_right _ (Finset.mem_singleton.mpr hwv)
  · apply Finset.mem_union_left
    refine Finset.mem_sdiff.mpr ⟨hwW, ?_⟩
    intro hforward
    obtain ⟨_, m, hm, wm⟩ := mem_ball.mp hforward
    obtain ⟨_, n, hn, wn⟩ := mem_ball.mp hback
    have hpos : 0 < m := by
      cases m with
      | zero => cases wm; exact (hwv rfl).elim
      | succ m => omega
    exact hf v (m + n) (by omega) (by omega) (wm.append wn)

theorem reverseBall_add_ball_le {D : CH.Digraph} {W : Finset ℕ} {q i j v : ℕ}
    (hf : QFree D W q) (hij : i + j ≤ q) :
    (reverseBall D W v j).card + (ball D W v i).card ≤ W.card + 1 := by
  have hc := (Finset.card_le_card (reverseBall_subset_complement (v := v) hf hij)).trans
    (Finset.card_union_le _ _)
  rw [Finset.card_sdiff_of_subset ball_subset, Finset.card_singleton] at hc
  have hle := Finset.card_le_card (ball_subset (D := D) (W := W) (u := v) (k := i))
  omega

theorem sum_reverseBall_eq_sum_ball (D : CH.Digraph) (W : Finset ℕ) (j : ℕ) :
    (∑ v ∈ W, (reverseBall D W v j).card) = ∑ v ∈ W, (ball D W v j).card := by
  classical
  let E : CH.Digraph := fun v w => decide (w ∈ ball D W v j)
  have hout (v : ℕ) : outN E W v = ball D W v j := by
    ext w
    simp only [mem_outN, E, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun h => ⟨ball_subset h, h⟩⟩
  have hin (v : ℕ) : W.filter (fun w => E w v = true) = reverseBall D W v j := by
    simp [E, reverseBall]
  have he : (∑ v ∈ W, (outN E W v).card) =
      ∑ v ∈ W, (W.filter (fun w => E w v = true)).card :=
    Compose.ThinRigid.sum_out_eq_sum_in E W
  simpa only [hout, hin] using he.symm

theorem two_balls_boundary_cards {D : CH.Digraph} {W : Finset ℕ} {q i j a b : ℕ}
    (hf : QFree D W q) (hij : i + j ≤ q)
    (hi : ∀ v ∈ W, a ≤ (ball D W v i).card)
    (hj : ∀ v ∈ W, b ≤ (ball D W v j).card)
    (heq : a + b = W.card + 1) :
    ∀ v ∈ W, (ball D W v i).card = a ∧ (ball D W v j).card = b ∧
      (reverseBall D W v j).card = b := by
  have hr : ∀ v ∈ W, (reverseBall D W v j).card ≤ b := by
    intro v hv
    have h := reverseBall_add_ball_le (v := v) hf hij
    have hlow := hi v hv
    omega
  have hs1 := Finset.sum_le_sum hj
  have hs2 := Finset.sum_le_sum hr
  have he := sum_reverseBall_eq_sum_ball D W j
  have hsum : (∑ v ∈ W, b) = ∑ v ∈ W, (ball D W v j).card := by omega
  have hout := (Finset.sum_eq_sum_iff_of_le hj).mp hsum
  have hin := (Finset.sum_eq_sum_iff_of_le hr).mp (show
    (∑ v ∈ W, (reverseBall D W v j).card) = ∑ _v ∈ W, b by omega)
  intro v hv
  have h := reverseBall_add_ball_le (v := v) hf hij
  have hlow := hi v hv
  have hb := hin v hv
  exact ⟨by omega, (hout v hv).symm, hb⟩

theorem two_balls_boundary_complement {D : CH.Digraph} {W : Finset ℕ}
    {q i j a b v : ℕ} (hf : QFree D W q) (hij : i + j ≤ q)
    (hi : ∀ w ∈ W, a ≤ (ball D W w i).card)
    (hj : ∀ w ∈ W, b ≤ (ball D W w j).card)
    (heq : a + b = W.card + 1) (hv : v ∈ W) :
    reverseBall D W v j = (W \ ball D W v i) ∪ {v} := by
  have hcards := two_balls_boundary_cards hf hij hi hj heq v hv
  apply Finset.eq_of_subset_of_card_le (reverseBall_subset_complement hf hij)
  have hc := Finset.card_union_le (W \ ball D W v i) {v}
  rw [Finset.card_sdiff_of_subset ball_subset, Finset.card_singleton] at hc
  have hle := Finset.card_le_card (ball_subset (D := D) (W := W) (u := v) (k := i))
  omega

end LeanCH.BR.BRq3
