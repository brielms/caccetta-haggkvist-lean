import LeanCH.BR.BRWeightedRichConnection

/-! The actual rich interfaces require a third exterior vertex in a strict
smaller-order induction host. No rich-to-rich arc is assumed here. -/
namespace LeanCH.BR.WeightedSD
open Finset BRq2 BRq3 BR45 BRsub BRsGen

theorem strict_cycle_third_exterior {q : ℕ} (hq : 4 ≤ q)
    {D : CH.Digraph} {V M : Finset ℕ} (hf : QFree D V q)
    (hsmall : SmallerSmallRow q V.card)
    (hMV : M ⊆ V) (hM : M.card = q + 1) (hout : OutEq 1 D M)
    (hin : ∀ v ∈ M, (inN D M v).card = 1)
    (w p : ℕ → ℚ) (hw : ∀ v ∈ V, 0 ≤ w v) (hp : ∀ v ∈ V, 0 ≤ p v)
    (c : ℚ) (hr : ∀ v ∈ V, row q D V w v = c)
    (hc : ∀ v ∈ V, col q D V p v = c)
    (hwc : mass V w < c) (hpc : mass V p < c) :
    ∃ a ∈ cycleRichReceivers D V M, ∃ b ∈ cycleRichSenders D V M,
      ∃ z ∈ V \ M, a ≠ b ∧ z ≠ a ∧ z ≠ b := by
  classical
  obtain ⟨a, ha⟩ := cycle_rich_receivers_nonempty hMV hM hin w hw c
    (fun v hv => hr v (hMV hv)) hwc
  obtain ⟨b, hb⟩ := cycle_rich_senders_nonempty hMV hM hout p hp c
    (fun v hv => hc v (hMV hv)) hpc
  have hd := cycle_rich_sets_disjoint (by omega : 2 ≤ q) hf hMV hM hout
  have habne : a ≠ b := by
    intro he
    subst b
    exact Finset.disjoint_left.mp hd ha hb
  have haV := (Finset.mem_sdiff.mp (Finset.mem_filter.mp ha).1).1
  have haM := (Finset.mem_sdiff.mp (Finset.mem_filter.mp ha).1).2
  have ha2 := (Finset.mem_filter.mp ha).2
  have hrw : ∀ v ∈ V, mass V w < row q D V w v := by
    intro v hv
    rwa [hr v hv]
  have hcp : ∀ v ∈ V, mass V p < col q D V p v := by
    intro v hv
    rwa [hc v hv]
  by_contra hn
  have hext : ∀ z ∈ V \ M, z = a ∨ z = b := by
    intro z hz
    by_cases hza : z = a
    · exact Or.inl hza
    · by_cases hzb : z = b
      · exact Or.inr hzb
      · exact (hn ⟨a, ha, b, hb, z, hz, habne, hza, hzb⟩).elim
  have hab : D a b = true := by
    by_contra hnab
    have hheads : outN D V a ⊆ outN D M a := by
      intro z hz
      have hzV := outN_subset hz
      have haz := (mem_outN.mp hz).2
      refine mem_outN.mpr ⟨?_, haz⟩
      by_contra hzM
      rcases hext z (Finset.mem_sdiff.mpr ⟨hzV, hzM⟩) with rfl | rfl
      · exact loopfree hf (by omega) haV haz
      · exact hnab haz
    obtain ⟨z, hz⟩ := Finset.card_pos.mp (minOut_one_of_strict w hw hrw a haV)
    have hzM := outN_subset (hheads hz)
    obtain ⟨u, hu⟩ := Finset.card_pos.mp (by rw [hin z hzM]; decide)
    have huM := (mem_inN.mp hu).1
    have hau : a ≠ u := fun he => haM (he ▸ huM)
    have hcap := cycle_feed_return_budget (by omega : 2 ≤ q) hf hMV hM hout haV
      (Finset.card_pos.mp (by omega))
    have hOa : (outN D M a).card ≤ 1 := by omega
    apply strict_no_outgoing_domination hsmall hf p hp hcp haV (hMV huM) hau
    intro y hy hay
    have hyN := hheads (mem_outN.mpr ⟨(Finset.mem_erase.mp hy).2, hay⟩)
    have he := Finset.card_le_one.mp hOa y hyN z (hheads hz)
    simpa only [he] using (mem_inN.mp hu).2
  obtain ⟨u, hu, z, hz, hza, hzb, _, _⟩ :=
    rich_connection_escape hq hf hsmall hMV hM hout hin p hp hcp ha hb hab
  exact hn ⟨a, ha, b, hb, z, hz, habne, hza, hzb⟩

theorem strict_saturated_order_lower_four {q : ℕ} (hq : 4 ≤ q)
    {D : CH.Digraph} {V : Finset ℕ} (hf : QFree D V q) (hsat : Sat q D V)
    (hsmall : SmallerSmallRow q V.card) (hs : StrictPositiveRows q D V) :
    q + 4 ≤ V.card := by
  obtain ⟨M, hMV, hM, hout, hin⟩ :=
    exists_tight_cycle_of_strict_saturation (by omega) hf hsat hsmall hs
  obtain ⟨z, hz, hV, hzr⟩ := strict_witness_of_not_smallRow
    (fun h : SmallRow q D V => h.not_strictPositiveRows hs)
  obtain ⟨w, p, c, hc, hw, hp, hm, hpm, hr, hpc⟩ :=
    strict_pair_of_proper_smallRow (hsmall.induced hf) hV z hz hzr
  obtain ⟨a, ha, b, hb, x, hx, hab, hxa, hxb⟩ :=
    strict_cycle_third_exterior hq hf hsmall hMV hM hout hin w p
      (fun v hv => (hw v hv).le) (fun v hv => (hp v hv).le) c hr hpc
      (by rwa [hm]) (by rwa [hpm])
  obtain ⟨haV, haM⟩ := Finset.mem_sdiff.mp (Finset.mem_filter.mp ha).1
  obtain ⟨hbV, hbM⟩ := Finset.mem_sdiff.mp (Finset.mem_filter.mp hb).1
  obtain ⟨hxV, hxM⟩ := Finset.mem_sdiff.mp hx
  have hsub : insert x (insert b (insert a M)) ⊆ V :=
    Finset.insert_subset hxV (Finset.insert_subset hbV (Finset.insert_subset haV hMV))
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem (by simp [hxa, hxb, hxM]),
    Finset.card_insert_of_notMem (by simp [hab.symm, hbM]),
    Finset.card_insert_of_notMem haM, hM] at hcard
  omega

/-- A consequence with the smaller-order premise fully discharged. -/
theorem smallRow_of_card_le_add_three {q : ℕ} (hq : 4 ≤ q)
    {D : CH.Digraph} {V : Finset ℕ} (hf : QFree D V q)
    (hcard : V.card ≤ q + 3) : SmallRow q D V := by
  have main : ∀ n : ℕ, n ≤ q + 3 → ∀ (E : CH.Digraph) (U : Finset ℕ),
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
      have hl := strict_saturated_order_lower_four hq hSf hsat hsmall (hs.mono_graph hES)
      omega
  exact main V.card hcard D V rfl hf

end LeanCH.BR.WeightedSD
