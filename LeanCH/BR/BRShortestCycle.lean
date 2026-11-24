import LeanCH.BR.BRCyclicRowCap

/-! A shortest closed walk gives a degree-one boundary support at its own cutoff. -/

namespace LeanCH.BR.BRsGen
open BRq2 BRq3 BR45

theorem exists_minimal_cycle_support {D : CH.Digraph} {V : Finset ℕ} {q : ℕ}
    (hq : 1 ≤ q) (hf : QFree D V q)
    (hmin : ∀ v ∈ V, 1 ≤ (outN D V v).card) (hne : V.Nonempty) :
    ∃ p M, q ≤ p ∧ QFree D V p ∧ M ⊆ V ∧ M.card = p + 1 ∧ OutEq 1 D M := by
  classical
  have hn : ¬ QFree D V V.card := by
    intro hfree
    obtain ⟨v, hv, hsink⟩ := exists_sink hfree hne le_rfl
    obtain ⟨w, hw⟩ := Finset.card_pos.mp (hmin v hv)
    exact hsink w (mem_outN.mp hw).1 (mem_outN.mp hw).2
  unfold QFree at hn
  push Not at hn
  obtain ⟨a, m, hm, _, w⟩ := hn
  have hex : ∃ k, ∃ a, 0 < k ∧ Walk D V a a k := ⟨m, a, hm, w⟩
  obtain ⟨a, hm, w⟩ := Nat.find_spec hex
  have hqk : q < Nat.find hex := by
    by_contra hn
    exact hf a _ hm (by omega) w
  have hfree : QFree D V (Nat.find hex - 1) := by
    intro b k hk hkle wb
    have hle := Nat.find_min' hex ⟨b, hk, wb⟩
    omega
  have ww : Walk D V a a ((Nat.find hex - 1) + 1) := by
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ Nat.find hex)] using w
  obtain ⟨M, hMV, hM, hminM⟩ := boundary_closed_walk_support hfree ww
  refine ⟨Nat.find hex - 1, M, by omega, hfree, hMV, hM, ?_⟩
  exact (dt_reg (by omega : 1 ≤ Nat.find hex - 1)
    (ball_q_one _ (by omega)) (hfree.mono_set hMV) hminM (by omega)).1

end LeanCH.BR.BRsGen
