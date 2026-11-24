import LeanCH.BR.BRsubTightSix

/-! The degree-four boundary theorem excludes a deficient fourth layer of size two. -/

namespace LeanCH.BR.BRsub

open BRq2 BRq3 BR45

/-- Every deficient degree-six radius-four ball has at least three fourth-layer vertices. -/
theorem fourth_layer_ge_three {E : CH.Digraph} {V : Finset ℕ} {u : ℕ}
    (hf : QFree E V 5) (hu : u ∈ V)
    (hmin : ∀ v ∈ V, 6 ≤ (outN E V v).card)
    (hb4 : (ball E V u 4).card ≤ 24) :
    3 ≤ (ball E V u 4 \ ball E V u 3).card := by
  classical
  have htwo := fourth_layer_ge_two hf hu hmin hb4
  by_contra hn
  let U := (ball E V u 3).erase u
  let K := ball E V u 4 \ ball E V u 3
  have hK : K.card = 2 := by change (ball E V u 4 \ ball E V u 3).card = 2; omega
  have hUV : U ⊆ V := (Finset.erase_subset _ _).trans ball_subset
  have hUc : U.card ≤ 21 := by
    have hc := Finset.card_sdiff_add_card_eq_card
      (ball_mono_radius (D := E) (W := V) (u := u) (by decide : 3 ≤ 4))
    have he : U.card = (ball E V u 3).card - 1 := Finset.card_erase_of_mem (self_mem_ball hu)
    change (ball E V u 4 \ ball E V u 3).card = 2 at hK
    omega
  have hminU : ∀ v ∈ U, 4 ≤ (outN E U v).card := by
    intro v hv
    have hv3 := Finset.mem_of_mem_erase hv
    have hsub : outN E V v ⊆ outN E U v ∪ K := by
      intro w hw
      obtain ⟨hwV, hvw⟩ := mem_outN.mp hw
      by_cases hw3 : w ∈ ball E V u 3
      · exact Finset.mem_union_left _ (mem_outN.mpr
          ⟨Finset.mem_erase.mpr ⟨fun heq => no_back_arc hf hu hv3 (by decide) (heq ▸ hvw), hw3⟩, hvw⟩)
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨ball_step hv3 hwV hvw, hw3⟩)
    have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    have hh := hmin v (hUV hv)
    omega
  obtain ⟨x, hx⟩ := Finset.card_pos.mp ((by decide : 0 < 6).trans_le (hmin u hu))
  have hx1 : x ∈ ball E V u 1 := (mem_ball_one hu).mpr (Or.inr hx)
  have hxU : x ∈ U := Finset.mem_erase.mpr
    ⟨fun heq => loopfree hf (by decide) hu (heq ▸ (mem_outN.mp hx).2),
      ball_mono_radius (by decide : 1 ≤ 3) hx1⟩
  have hsize := dt_size (by decide : 1 ≤ 5) (BRq4.ball_all4 5 (by decide))
    (hf.mono_set hUV) hminU ⟨x, hxU⟩
  have hreg := (dt_reg (by decide : 1 ≤ 5) (BRq4.ball_all4 5 (by decide))
    (hf.mono_set hUV) hminU (by omega : U.card = 5 * 4 + 1)).1
  have hsubX : outN E V x ⊆ outN E U x := by
    intro w hw
    obtain ⟨hwV, hxw⟩ := mem_outN.mp hw
    exact mem_outN.mpr ⟨Finset.mem_erase.mpr
      ⟨fun heq => no_back_arc hf hu hx1 (by decide) (heq ▸ hxw),
        ball_mono_radius (by decide : 2 ≤ 3) (ball_step hx1 hwV hxw)⟩, hxw⟩
  have hhigh := (hmin x (outN_subset hx)).trans (Finset.card_le_card hsubX)
  rw [hreg x hxU] at hhigh
  omega

end LeanCH.BR.BRsub
