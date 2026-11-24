import LeanCH.BR.BRWeightedCycleEscape

/-! Supply the actual tight cycle in the positive boundary-equality branch.
Proper self-duality is the existing BR induction premise, retained explicitly. -/
namespace LeanCH.BR.WeightedSD
open Finset BRq2 BRq3 BR45 BRsub BRsGen

theorem exists_tight_cycle_of_positive_feasible {q : ℕ} (hq : 1 ≤ q)
    {D : CH.Digraph} {V : Finset ℕ} (hf : QFree D V q) (hsat : Sat q D V)
    (hproper : ∀ U ⊆ V, U ≠ V → SelfDual q D U)
    (hcard : 2 ≤ V.card) (w : ℕ → ℚ) (hw : ∀ v ∈ V, 0 < w v)
    (hr : ∀ v ∈ V, mass V w ≤ row q D V w v) :
    ∃ M ⊆ V, M.card = q + 1 ∧ OutEq 1 D M ∧
      ∀ v ∈ M, (inN D M v).card = 1 := by
  classical
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (by omega : 0 < V.card)
  obtain ⟨z, hz, hza⟩ := Finset.exists_mem_ne (by omega : 1 < V.card) a
  have hzE : z ∈ V.erase a := Finset.mem_erase.mpr ⟨hza, hz⟩
  have hmE : w z ≤ mass (V.erase a) w := by
    simpa [mass] using mass_mono (Finset.singleton_subset_iff.mpr hzE)
      (fun v hv => (hw v (Finset.mem_erase.mp hv).2).le)
  have hsum := Finset.sum_erase_add V w ha
  change mass (V.erase a) w + w a = mass V w at hsum
  have hwa : w a < mass V w := by linarith [hw z hz]
  have hn : (outN D V a).Nonempty := by
    by_contra hn
    have he := Finset.not_nonempty_iff_eq_empty.mp hn
    have haRow := hr a ha
    rw [row, outW_eq_mass, he] at haRow
    simp only [mass, Finset.sum_empty, mul_zero, add_zero] at haRow
    exact (not_lt_of_ge haRow) hwa
  obtain ⟨b, hb⟩ := hn
  have hclosed := arc_closed_walk hq hf hsat hproper w hw hr ha
    (outN_subset hb) (mem_outN.mp hb).2
  obtain ⟨M, hMV, hM, hmin⟩ := boundary_closed_walk_support hf hclosed
  have hreg := dt_reg hq (ball_q_one q hq) (hf.mono_set hMV) hmin (by simpa using hM)
  exact ⟨M, hMV, hM, hreg.1, hreg.2⟩

end LeanCH.BR.WeightedSD
