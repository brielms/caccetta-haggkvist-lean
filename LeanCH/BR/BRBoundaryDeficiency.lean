import LeanCH.BR.BRDeficiencyCompletion
import LeanCH.BR.BRForcedOutSaturation

/-! Deficiency rigidity needs only an order bound and forced regularity at equality.
No arbitrary-host ball theorem is assumed. The two class-wide inputs remain explicit. -/

namespace LeanCH.BR.BRsGen
open BRq2 BRq3 BR45

theorem no_equal_rows_of_forced_regular {D : CH.Digraph} {V : Finset ℕ} {q d a b : ℕ}
    (hq : 1 ≤ q)
    (hreg : ∀ F : CH.Digraph, QFree F V q →
      (∀ v ∈ V, d ≤ (outN F V v).card) → OutEq d F V)
    (hf : QFree D V q) (hmin : ∀ v ∈ V, d ≤ (outN D V v).card)
    (ha : a ∈ V) (hb : b ∈ V) (hne : a ≠ b)
    (heq : ∀ z ∈ V, D a z = D b z) : False := by
  have hsat := sat_of_forced_out_regular hreg hf hmin
  have hab : ¬ D a b = true := by
    intro hab
    exact loopfree hf hq hb (by rw [← heq b hb]; exact hab)
  obtain ⟨_, m, hm, w⟩ := mem_ball.mp (hsat b hb a ha hab)
  cases m with
  | zero => cases w; exact hne rfl
  | succ m =>
    cases w with
    | step hc hbc w =>
      exact hf a (m + 1) (by omega) (by omega)
        (.step hc (by rw [heq _ hc]; exact hbc) w)

theorem deficiency_equality_of_forced_regular {q d n : ℕ} (hq : 1 ≤ q)
    (hreg : ∀ (F : CH.Digraph) (U : Finset ℕ), QFree F U q →
      (∀ v ∈ U, d ≤ (outN F U v).card) → U.card = n → OutEq d F U)
    {D : CH.Digraph} {V : Finset ℕ} (hf : QFree D V q)
    (hmin : ∀ v ∈ V, 1 ≤ (outN D V v).card)
    (heq : V.card + ∑ v ∈ V, (d - (outN D V v).card) = n) :
    OutEq d D V ∧ V.card = n := by
  obtain ⟨F, U, hF, hmF, hc, _, hrows, htwins⟩ :=
    exists_deficiency_completion_rows (d := d) hf hmin
  have hUc : U.card = n := hc.trans heq
  have hregF := hreg F U hF hmF hUc
  have hnoLow : ∀ v ∈ V, d ≤ (outN D V v).card := by
    intro v hv
    by_contra hn
    obtain ⟨a, ha, b, hb, hne, hsame⟩ := htwins ⟨v, hv, by omega⟩
    exact no_equal_rows_of_forced_regular hq
      (fun E hE hmE => hreg E U hE hmE hUc) hF hmF ha hb hne (fun z _ => hsame z)
  have hout : OutEq d D V := by
    intro v hv
    obtain ⟨w, hw, hle⟩ := hrows v hv
    rw [hregF w hw] at hle
    exact Nat.le_antisymm hle (hnoLow v hv)
  refine ⟨hout, ?_⟩
  have hz : (∑ v ∈ V, (d - (outN D V v).card)) = 0 :=
    Finset.sum_eq_zero (fun v hv => by rw [hout v hv]; omega)
  omega

theorem deficiency_strict_of_size_regular {q d n : ℕ} (hq : 1 ≤ q)
    (hsize : ∀ (F : CH.Digraph) (U : Finset ℕ), QFree F U q →
      (∀ v ∈ U, d ≤ (outN F U v).card) → U.Nonempty → n ≤ U.card)
    (hreg : ∀ (F : CH.Digraph) (U : Finset ℕ), QFree F U q →
      (∀ v ∈ U, d ≤ (outN F U v).card) → U.card = n → OutEq d F U)
    {D : CH.Digraph} {V : Finset ℕ} (hf : QFree D V q)
    (hmin : ∀ v ∈ V, 1 ≤ (outN D V v).card) (hne : V.Nonempty)
    (hsmall : V.card < n ∨ ¬ OutEq d D V) :
    n + 1 ≤ V.card + ∑ v ∈ V, (d - (outN D V v).card) := by
  have hlo := deficiency_bound_of_size hsize hf hmin hne
  by_contra hn
  have heq := deficiency_equality_of_forced_regular hq hreg hf hmin (by omega)
  rcases hsmall with hsmall | hnot
  · omega
  · exact hnot heq.1

end LeanCH.BR.BRsGen
