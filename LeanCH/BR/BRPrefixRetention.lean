import LeanCH.BR.BR45Base

/-! Degree retention after deleting a root and the next distance layer. -/

namespace LeanCH.BR.BRq2

open BRq3 BR45

variable {D : CH.Digraph} {V : Finset ℕ} {q k u s d : ℕ}

theorem erase_ball_one_eq_outN (hf : QFree D V q) (hq : 1 ≤ q) (hu : u ∈ V) :
    (ball D V u 1).erase u = outN D V u := by
  classical
  have heq : ball D V u 1 = insert u (outN D V u) := by
    ext v
    simp only [mem_ball_one hu, Finset.mem_insert]
  rw [heq, Finset.erase_insert]
  exact fun h => loopfree hf hq hu (mem_outN.mp h).2

theorem erase_ball_succ_eq_union (hu : u ∈ V) :
    (ball D V u (k + 1)).erase u = (ball D V u k).erase u ∪
      (ball D V u (k + 1) \ ball D V u k) := by
  ext v
  simp only [Finset.mem_erase, Finset.mem_union, Finset.mem_sdiff]
  have hmono : v ∈ ball D V u k → v ∈ ball D V u (k + 1) :=
    fun h => ball_mono_radius (by omega) h
  have hself : v = u → v ∈ ball D V u k := by
    intro heq
    subst v
    exact self_mem_ball hu
  tauto

theorem outN_prefix_loss (hf : QFree D V q) (hu : u ∈ V) (hk : k + 1 ≤ q)
    {v : ℕ} (hv : v ∈ (ball D V u k).erase u) :
    outN D V v ⊆ outN D ((ball D V u k).erase u) v ∪
      (ball D V u (k + 1) \ ball D V u k) := by
  intro w hw
  obtain ⟨hwV, hvw⟩ := mem_outN.mp hw
  have hvk := Finset.mem_of_mem_erase hv
  by_cases hwk : w ∈ ball D V u k
  · exact Finset.mem_union_left _ (mem_outN.mpr ⟨Finset.mem_erase.mpr
      ⟨fun heq => no_back_arc hf hu hvk hk (heq ▸ hvw), hwk⟩, hvw⟩)
  · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨ball_step hvk hwV hvw, hwk⟩)

theorem minOut_prefix_erase (hf : QFree D V q) (hu : u ∈ V) (hk : k + 1 ≤ q)
    (hmin : ∀ v ∈ V, s ≤ (outN D V v).card)
    (hloss : d + (ball D V u (k + 1) \ ball D V u k).card ≤ s) :
    ∀ v ∈ (ball D V u k).erase u, d ≤ (outN D ((ball D V u k).erase u) v).card := by
  intro v hv
  have hc := (Finset.card_le_card (outN_prefix_loss hf hu hk hv)).trans (Finset.card_union_le _ _)
  have hh := hmin v (ball_subset (Finset.mem_of_mem_erase hv))
  omega

theorem outN_prefix_erase_root (hf : QFree D V q) (hu : u ∈ V) (hk : k + 1 ≤ q)
    {v : ℕ} (hv : v ∈ ball D V u k) :
    outN D V v ⊆ outN D ((ball D V u (k + 1)).erase u) v := by
  intro w hw
  obtain ⟨hwV, hvw⟩ := mem_outN.mp hw
  exact mem_outN.mpr ⟨Finset.mem_erase.mpr
    ⟨fun heq => no_back_arc hf hu hv hk (heq ▸ hvw), ball_step hv hwV hvw⟩, hvw⟩

end LeanCH.BR.BRq2
