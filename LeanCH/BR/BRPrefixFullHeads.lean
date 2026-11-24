import LeanCH.BR.BRPrefixRetention

/-! Equality in a prefix degree-loss bound forces every next-layer head. -/

namespace LeanCH.BR.BRq2
open BRq3 BR45

theorem prefix_loss_full_next {D : CH.Digraph} {V : Finset ℕ} {q k u v : ℕ}
    (hf : QFree D V q) (hu : u ∈ V) (hk : k + 1 ≤ q)
    (hv : v ∈ (ball D V u k).erase u)
    (hfull : (outN D ((ball D V u k).erase u) v).card +
      (ball D V u (k + 1) \ ball D V u k).card ≤ (outN D V v).card) :
    ∀ w ∈ ball D V u (k + 1) \ ball D V u k, D v w = true := by
  classical
  intro w hw
  by_contra hn
  let T := ball D V u (k + 1) \ ball D V u k
  have hsub : outN D V v ⊆ outN D ((ball D V u k).erase u) v ∪ T.erase w := by
    intro x hx
    rcases Finset.mem_union.mp (outN_prefix_loss hf hu hk hv hx) with hin | hout
    · exact Finset.mem_union_left _ hin
    · exact Finset.mem_union_right _ (Finset.mem_erase.mpr
        ⟨fun heq => hn (heq ▸ (mem_outN.mp hx).2), hout⟩)
  have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hpos : 0 < T.card := Finset.card_pos.mpr ⟨w, hw⟩
  rw [Finset.card_erase_of_mem hw] at hc
  change (outN D V v).card ≤ (outN D ((ball D V u k).erase u) v).card + (T.card - 1) at hc
  change (outN D ((ball D V u k).erase u) v).card + T.card ≤ _ at hfull
  omega

end LeanCH.BR.BRq2
