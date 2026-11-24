import LeanCH.BR.BRBoundaryDeficiency
import LeanCH.BR.BRPrefixRetention

/-! A strict prefix budget retains the actual deficiency sum and equality rigidity. -/

namespace LeanCH.BR.BRsGen
open BRq2 BRq3 BR45

theorem prefix_deficiency_sum_le {q d s k u : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V q) (hu : u ∈ V) (hk : k + 2 ≤ q)
    (hm : ∀ v ∈ V, s ≤ (outN D V v).card) (hds : d ≤ s) :
    (∑ v ∈ (ball D V u (k + 1)).erase u,
      (d - (outN D ((ball D V u (k + 1)).erase u) v).card)) ≤
      (ball D V u (k + 1) \ ball D V u k).card *
        (d + (ball D V u (k + 2) \ ball D V u (k + 1)).card - s) := by
  classical
  let U := (ball D V u (k + 1)).erase u
  let S := ball D V u (k + 1) \ ball D V u k
  let T := ball D V u (k + 2) \ ball D V u (k + 1)
  let loss := d + T.card - s
  have hUV : U ⊆ V := (Finset.erase_subset _ _).trans ball_subset
  have hSU : S ⊆ U := by
    intro v hv
    refine Finset.mem_erase.mpr ⟨?_, (Finset.mem_sdiff.mp hv).1⟩
    intro heq; subst v
    exact (Finset.mem_sdiff.mp hv).2 (self_mem_ball hu)
  have hlow : ∀ v ∈ S, d - (outN D U v).card ≤ loss := by
    intro v hv
    have hc := (Finset.card_le_card (outN_prefix_loss hf hu
      (by omega : (k + 1) + 1 ≤ q) (hSU hv))).trans (Finset.card_union_le _ _)
    have hh := hm v (hUV (hSU hv))
    change (outN D V v).card ≤ (outN D U v).card + T.card at hc
    dsimp only [loss]
    omega
  have hzero : ∀ v ∈ U \ S, d - (outN D U v).card = 0 := by
    intro v hv
    obtain ⟨hvU, hvS⟩ := Finset.mem_sdiff.mp hv
    have hvk : v ∈ ball D V u k := by
      by_contra hn
      exact hvS (Finset.mem_sdiff.mpr ⟨Finset.mem_of_mem_erase hvU, hn⟩)
    have hh := (hm v (hUV hvU)).trans (Finset.card_le_card
      (outN_prefix_erase_root hf hu (by omega : k + 1 ≤ q) hvk))
    change s ≤ (outN D U v).card at hh
    omega
  have hsum := Finset.sum_le_sum hlow
  rw [Finset.sum_const_nat (fun _ _ => rfl)] at hsum
  have hz := Finset.sum_eq_zero hzero
  have he := Finset.sum_sdiff hSU (f := fun v => d - (outN D U v).card)
  change (∑ v ∈ U, (d - (outN D U v).card)) ≤ S.card * loss
  omega

theorem prefix_deficiency_strict_of_size_regular {q d n s k u : ℕ} (hq : 1 ≤ q)
    (hsize : ∀ (F : CH.Digraph) (U : Finset ℕ), QFree F U q →
      (∀ v ∈ U, d ≤ (outN F U v).card) → U.Nonempty → n ≤ U.card)
    (hreg : ∀ (F : CH.Digraph) (U : Finset ℕ), QFree F U q →
      (∀ v ∈ U, d ≤ (outN F U v).card) → U.card = n → OutEq d F U)
    {D : CH.Digraph} {V : Finset ℕ} (hf : QFree D V q) (hu : u ∈ V)
    (hk : k + 2 ≤ q) (hm : ∀ v ∈ V, s ≤ (outN D V v).card) (hds : d ≤ s)
    (hnext : (ball D V u (k + 2) \ ball D V u (k + 1)).card < s)
    (hsmall : (ball D V u (k + 1)).card - 1 < n) :
    n + 1 ≤ (ball D V u (k + 1)).card - 1 +
      (ball D V u (k + 1) \ ball D V u k).card *
        (d + (ball D V u (k + 2) \ ball D V u (k + 1)).card - s) := by
  classical
  let U := (ball D V u (k + 1)).erase u
  have hUV : U ⊆ V := (Finset.erase_subset _ _).trans ball_subset
  have hUc : U.card = (ball D V u (k + 1)).card - 1 := Finset.card_erase_of_mem (self_mem_ball hu)
  have hminU : ∀ v ∈ U, 1 ≤ (outN D U v).card :=
    minOut_prefix_erase hf hu (by omega : (k + 1) + 1 ≤ q) hm (by
      change 1 + (ball D V u (k + 2) \ ball D V u (k + 1)).card ≤ s; omega)
  have hne : U.Nonempty := by
    obtain ⟨x, hx⟩ := Finset.card_pos.mp (by have := hm u hu; omega : 0 < (outN D V u).card)
    refine ⟨x, Finset.mem_erase.mpr ⟨?_, ?_⟩⟩
    · intro heq
      exact loopfree hf hq hu (heq ▸ (mem_outN.mp hx).2)
    · exact ball_mono_radius (by omega : 1 ≤ k + 1) ((mem_ball_one hu).mpr (Or.inr hx))
  have hh := deficiency_strict_of_size_regular hq hsize hreg (hf.mono_set hUV)
    hminU hne (Or.inl (by omega : U.card < n))
  have hsum := prefix_deficiency_sum_le hf hu hk hm hds
  change (∑ v ∈ U, (d - (outN D U v).card)) ≤ _ at hsum
  omega

end LeanCH.BR.BRsGen
