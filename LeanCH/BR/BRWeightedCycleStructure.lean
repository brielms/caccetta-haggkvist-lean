import LeanCH.BR.BRWeightedCycleInterface

/-! Derive an actual shortest-cycle interface in the saturated induction
host. No cycle, rich vertex, or common weighting is assumed to exist. -/
namespace LeanCH.BR.WeightedSD
open Finset BRq2 BRq3 BR45 BRsub BRsGen

theorem strict_cycle_order_lower {q : ℕ} (hq : 2 ≤ q)
    {D : CH.Digraph} {V M : Finset ℕ} (hf : QFree D V q)
    (hMV : M ⊆ V) (hM : M.card = q + 1) (hout : OutEq 1 D M)
    (hin : ∀ v ∈ M, (inN D M v).card = 1)
    (w p : ℕ → ℚ) (hw : ∀ v ∈ V, 0 ≤ w v) (hp : ∀ v ∈ V, 0 ≤ p v)
    (c : ℚ) (hr : ∀ v ∈ M, row q D V w v = c)
    (hc : ∀ v ∈ M, col q D V p v = c)
    (hwc : mass V w < c) (hpc : mass V p < c) : q + 3 ≤ V.card := by
  obtain ⟨a, ha⟩ := cycle_rich_receivers_nonempty hMV hM hin w hw c hr hwc
  obtain ⟨b, hb⟩ := cycle_rich_senders_nonempty hMV hM hout p hp c hc hpc
  have hd := cycle_rich_sets_disjoint hq hf hMV hM hout
  have haVM := (Finset.mem_filter.mp ha).1
  have hbVM := (Finset.mem_filter.mp hb).1
  have hba : b ≠ a := by
    intro he
    subst b
    exact Finset.disjoint_left.mp hd ha hb
  have hnot : b ∉ insert a M := by
    simp only [Finset.mem_insert, not_or]
    exact ⟨hba, (Finset.mem_sdiff.mp hbVM).2⟩
  have hsub : insert b (insert a M) ⊆ V :=
    Finset.insert_subset (Finset.mem_sdiff.mp hbVM).1
      (Finset.insert_subset (Finset.mem_sdiff.mp haVM).1 hMV)
  have hh := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hnot,
    Finset.card_insert_of_notMem (Finset.mem_sdiff.mp haVM).2, hM] at hh
  omega

theorem exists_tight_cycle_of_strict_saturation {q : ℕ} (hq : 1 ≤ q)
    {D : CH.Digraph} {V : Finset ℕ} (hf : QFree D V q) (hsat : Sat q D V)
    (hsmall : SmallerSmallRow q V.card) (hs : StrictPositiveRows q D V) :
    ∃ M ⊆ V, M.card = q + 1 ∧ OutEq 1 D M ∧
      ∀ v ∈ M, (inN D M v).card = 1 := by
  obtain ⟨w, hw, hm, hr⟩ := hs
  have hV : V.Nonempty := by
    by_contra hn
    have he := Finset.not_nonempty_iff_eq_empty.mp hn
    rw [he] at hm
    simp [mass] at hm
  have hstrict : ∀ v ∈ V, mass V w < row q D V w v := by
    intro v hv
    rw [hm]
    exact hr v hv
  have hmin := minOut_one_of_strict w (fun v hv => (hw v hv).le) hstrict
  obtain ⟨a, ha⟩ := hV
  obtain ⟨b, hb⟩ := Finset.card_pos.mp (hmin a ha)
  have hret := arc_return_exact_of_smallRow hq hf hsat (hsmall.induced hf) w
    (fun v hv => (hw v hv).le) hstrict ha (mem_outN.mp hb).1 (mem_outN.mp hb).2
  have hclosed : Walk D V a a (q + 1) := .step (mem_outN.mp hb).1 (mem_outN.mp hb).2 hret
  obtain ⟨M, hMV, hM, hminM⟩ := boundary_closed_walk_support hf hclosed
  have hreg := dt_reg hq (ball_q_one q hq) (hf.mono_set hMV) hminM
    (by simpa using hM)
  exact ⟨M, hMV, hM, hreg.1, hreg.2⟩

theorem strict_saturated_order_lower {q : ℕ} (hq : 2 ≤ q)
    {D : CH.Digraph} {V : Finset ℕ} (hf : QFree D V q) (hsat : Sat q D V)
    (hsmall : SmallerSmallRow q V.card) (hs : StrictPositiveRows q D V) :
    q + 3 ≤ V.card := by
  obtain ⟨M, hMV, hM, hout, hin⟩ :=
    exists_tight_cycle_of_strict_saturation (by omega) hf hsat hsmall hs
  obtain ⟨z, hz, hV, hzr⟩ := strict_witness_of_not_smallRow
    (fun h : SmallRow q D V => h.not_strictPositiveRows hs)
  obtain ⟨w, p, c, hc, hw, hp, hm, hpm, hr, hpc⟩ :=
    strict_pair_of_proper_smallRow (hsmall.induced hf) hV z hz hzr
  exact strict_cycle_order_lower hq hf hMV hM hout hin w p
    (fun v hv => (hw v hv).le) (fun v hv => (hp v hv).le) c
    (fun v hv => hr v (hMV hv)) (fun v hv => hpc v (hMV hv))
    (by rwa [hm]) (by rwa [hpm])

/-- The strict exclusion at this order is derived by genuine order induction. -/
theorem smallRow_of_card_le_add_two {q : ℕ} (hq : 2 ≤ q)
    {D : CH.Digraph} {V : Finset ℕ} (hf : QFree D V q)
    (hcard : V.card ≤ q + 2) : SmallRow q D V := by
  have main : ∀ n : ℕ, n ≤ q + 2 → ∀ (E : CH.Digraph) (U : Finset ℕ),
      U.card = n → QFree E U q → SmallRow q E U := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn E U hUn hUf
      have hsmall : SmallerSmallRow q U.card := by
        intro F T hlt hTf
        exact ih T.card (by omega) (by omega) F T rfl hTf
      by_contra hbad
      obtain ⟨z, hz, hU, hzr⟩ := strict_witness_of_not_smallRow hbad
      obtain ⟨w, p, c, hc, hw, hp, hm, hpm, hr, hpc⟩ :=
        strict_pair_of_proper_smallRow (hsmall.induced hUf) hU z hz hzr
      have hs : StrictPositiveRows q E U :=
        ⟨w, hw, hm, fun v hv => by rw [hr v hv]; exact hc⟩
      obtain ⟨S, hES, hSf, hsat⟩ := exists_satQ hUf
      have hSstrict := hs.mono_graph hES
      have hl := strict_saturated_order_lower hq hSf hsat hsmall hSstrict
      omega
  exact main V.card hcard D V rfl hf

end LeanCH.BR.WeightedSD
