import LeanCH.BR.BRDeficiencyCompletion
import LeanCH.BR.BRsubSat

/-! Equality in the deficiency bound has no padding: the original graph is regular. -/

namespace LeanCH.BR.BRsGen

open BRq2 BRq3 BR45

/-- A boundary graph with the ball theorem cannot have two identical outgoing rows.
Adding an arc between them is safe and contradicts boundary regularity. -/
theorem boundary_no_equal_rows {D : CH.Digraph} {V : Finset ℕ} {q d a b : ℕ}
    (hq : 1 ≤ q) (hb : Ball q d) (hf : QFree D V q)
    (hmin : ∀ v ∈ V, d ≤ (outN D V v).card) (hc : V.card = q * d + 1)
    (ha : a ∈ V) (hbV : b ∈ V) (hne : a ≠ b)
    (heq : ∀ z ∈ V, D a z = D b z) : False := by
  classical
  have hnot : a ∉ ball D V b (q - 1) := by
    intro h
    obtain ⟨_, m, hm, w⟩ := mem_ball.mp h
    cases m with
    | zero => cases w; exact hne rfl
    | succ m =>
      cases w with
      | step hc hbc w =>
        exact hf a (m + 1) (by omega) (by omega)
          (.step hc (by rw [heq _ hc]; exact hbc) w)
  let F : CH.Digraph := fun x y => D x y || decide (x = a ∧ y = b)
  have hsub : ∀ x y, D x y = true → F x y = true := by
    intro x y h
    simp [F, h]
  have hF : QFree F V q := BRsub.qfree_insertQ hf ha (by
    intro x y h
    simpa only [F, Bool.or_eq_true, decide_eq_true_eq] using h) hnot
  have hminF : ∀ v ∈ V, d ≤ (outN F V v).card := by
    intro v hv
    apply (hmin v hv).trans
    apply Finset.card_le_card
    intro w hw
    exact mem_outN.mpr ⟨(mem_outN.mp hw).1, hsub v w (mem_outN.mp hw).2⟩
  have hreg := (dt_reg hq hb hf hmin hc).1 a ha
  have hregF := (dt_reg hq hb hF hminF hc).1 a ha
  have hbNot : b ∉ outN D V a := by
    intro h
    exact loopfree hf hq hbV (by rw [← heq b hbV]; exact (mem_outN.mp h).2)
  have hheads : insert b (outN D V a) ⊆ outN F V a := by
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact mem_outN.mpr ⟨hbV, by simp [F]⟩
    · exact mem_outN.mpr ⟨(mem_outN.mp hw).1, hsub a w (mem_outN.mp hw).2⟩
  have hcard := Finset.card_le_card hheads
  rw [Finset.card_insert_of_notMem hbNot, hreg, hregF] at hcard
  omega

/-- Equality in the deficiency bound forces the original graph itself to be d-regular. -/
theorem deficiency_equality_regular {D : CH.Digraph} {V : Finset ℕ} {q d : ℕ}
    (hq : 1 ≤ q) (hb : Ball q d) (hf : QFree D V q)
    (hmin : ∀ v ∈ V, 1 ≤ (outN D V v).card)
    (heq : V.card + ∑ v ∈ V, (d - (outN D V v).card) = q * d + 1) :
    OutEq d D V ∧ V.card = q * d + 1 := by
  obtain ⟨F, U, hF, hminF, hc, _, hrows, htwins⟩ :=
    exists_deficiency_completion_rows (d := d) hf hmin
  have hUc : U.card = q * d + 1 := hc.trans heq
  have hreg := (dt_reg hq hb hF hminF hUc).1
  have hnoLow : ∀ v ∈ V, d ≤ (outN D V v).card := by
    intro v hv
    by_contra hn
    obtain ⟨a, ha, b, hbV, hne, hsame⟩ := htwins ⟨v, hv, by omega⟩
    exact boundary_no_equal_rows hq hb hF hminF hUc ha hbV hne (fun z _ => hsame z)
  have hout : OutEq d D V := by
    intro v hv
    obtain ⟨w, hw, hle⟩ := hrows v hv
    rw [hreg w hw] at hle
    exact Nat.le_antisymm hle (hnoLow v hv)
  refine ⟨hout, ?_⟩
  have hz : (∑ v ∈ V, (d - (outN D V v).card)) = 0 :=
    Finset.sum_eq_zero (fun v hv => by rw [hout v hv]; omega)
  omega

/-- Every non-regular positive-minimum graph pays at least one extra unit of deficiency. -/
theorem deficiency_strict_of_not_regular {D : CH.Digraph} {V : Finset ℕ} {q d : ℕ}
    (hq : 1 ≤ q) (hb : Ball q d) (hf : QFree D V q)
    (hmin : ∀ v ∈ V, 1 ≤ (outN D V v).card) (hne : V.Nonempty)
    (hnot : ¬ OutEq d D V) :
    q * d + 2 ≤ V.card + ∑ v ∈ V, (d - (outN D V v).card) := by
  have hlo := deficiency_bound_of_ball hq hb hf hmin hne
  by_contra hn
  exact hnot (deficiency_equality_regular hq hb hf hmin (by omega)).1

end LeanCH.BR.BRsGen
