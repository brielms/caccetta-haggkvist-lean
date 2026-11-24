import LeanCH.BR.BRPrefixRetention

/-! High rows inside a set at most one vertex above the cycle cutoff. -/

namespace LeanCH.BR.BRsGen
open BRq2 BRq3 BR45

theorem near_boundary_high_set_card {D : CH.Digraph} {V H : Finset ℕ} {q d : ℕ}
    (hq : 1 ≤ q) (hd : 2 ≤ d) (hf : QFree D V q)
    (hV : V.card ≤ q + 1) (hHV : H ⊆ V)
    (hhigh : ∀ v ∈ H, d ≤ (outN D V v).card) : H.card ≤ V.card - d := by
  classical
  rcases Finset.eq_empty_or_nonempty H with hempty | hne
  · simp [hempty]
  have hHsmall : H.card ≤ q := by
    by_contra hn
    have hc := Finset.card_le_card hHV
    have heq : H = V := Finset.eq_of_subset_of_card_le hHV (by omega)
    have hmin2 : ∀ v ∈ V, 2 ≤ (outN D V v).card := by
      intro v hv
      exact hd.trans (hhigh v (heq.symm ▸ hv))
    have hh := corB hq hf hmin2 (hne.mono hHV)
    omega
  obtain ⟨v, hv, hsink⟩ := exists_sink (hf.mono_set hHV) hne hHsmall
  have hsub : outN D V v ⊆ V \ H := by
    intro w hw
    exact Finset.mem_sdiff.mpr
      ⟨(mem_outN.mp hw).1, fun hwH => hsink w hwH (mem_outN.mp hw).2⟩
  have hc := Finset.card_le_card hsub
  have hh := hhigh v hv
  have hsplit := Finset.card_sdiff_add_card_eq_card hHV
  omega

theorem small_first_high_heads_bound {D : CH.Digraph} {V H : Finset ℕ} {q d s u : ℕ}
    (hq : 2 ≤ q) (hd : 2 ≤ d) (hf : QFree D V q) (hu : u ∈ V)
    (hfirst : (outN D V u).card ≤ q + 1) (hHV : H ⊆ V)
    (hhigh : ∀ v ∈ H, s ≤ (outN D V v).card)
    (hloss : d + (ball D V u 2 \ ball D V u 1).card ≤ s) :
    (outN D H u).card ≤ (outN D V u).card - d := by
  have hKX : outN D H u ⊆ outN D V u := outN_mono hHV u
  apply near_boundary_high_set_card (by omega : 1 ≤ q) hd
    (hf.mono_set outN_subset) hfirst hKX
  intro v hv
  have hve : v ∈ (ball D V u 1).erase u := by
    rw [erase_ball_one_eq_outN hf (by omega) hu]
    exact hKX hv
  have hsub := outN_prefix_loss hf hu (by omega : 1 + 1 ≤ q) hve
  rw [erase_ball_one_eq_outN hf (by omega) hu] at hsub
  have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  change (outN D V v).card ≤ (outN D (outN D V u) v).card +
    (ball D V u 2 \ ball D V u 1).card at hc
  have hh := hhigh v (mem_outN.mp hv).1
  omega

end LeanCH.BR.BRsGen
