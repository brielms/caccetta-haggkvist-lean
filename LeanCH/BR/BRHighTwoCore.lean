import LeanCH.BR.BR45Base

/-! A large first row in a degree-two host forces extra ball growth. -/

namespace LeanCH.BR.BRsGen

open BRq2 BRq3 BR45

variable {D : CH.Digraph} {W : Finset ℕ} {u q : ℕ}

/-- A row of degree at least q+1 forces a radius-three ball of size at least q+5. -/
theorem high_row_ball_three (hq : 3 ≤ q) (hf : QFree D W q)
    (hmin : ∀ v ∈ W, 2 ≤ (outN D W v).card) (hu : u ∈ W)
    (hhigh : q + 1 ≤ (outN D W u).card) :
    q + 5 ≤ (ball D W u 3).card := by
  classical
  by_contra hn
  have hsmall : (ball D W u 3).card ≤ q + 4 := by omega
  have hB1 : ball D W u 1 = insert u (outN D W u) := by
    ext v
    rw [mem_ball_one hu, Finset.mem_insert]
  have huO : u ∉ outN D W u := fun h => loopfree hf (by omega) hu (mem_outN.mp h).2
  have hB1c : (ball D W u 1).card = (outN D W u).card + 1 := by
    rw [hB1, Finset.card_insert_of_notMem huO]
  have hstrict : ∀ k, 1 ≤ k → k ≤ 2 →
      (ball D W u k).card < (ball D W u (k + 1)).card := by
    intro k hk hk2
    by_contra hn
    have heq : ball D W u (k + 1) = ball D W u k :=
      (Finset.eq_of_subset_of_card_le (ball_mono_radius (by omega : k ≤ k + 1)) (by omega)).symm
    let U := (ball D W u k).erase u
    have hUW : U ⊆ W := (Finset.erase_subset _ _).trans ball_subset
    have hminU : MinOut2 D U := by
      intro v hv
      apply (hmin v (hUW hv)).trans
      apply Finset.card_le_card
      intro w hw
      obtain ⟨hwW, hvw⟩ := mem_outN.mp hw
      exact mem_outN.mpr ⟨Finset.mem_erase.mpr
        ⟨fun h => no_back_arc hf hu (Finset.mem_of_mem_erase hv) (by omega) (h ▸ hvw),
          heq ▸ ball_step (Finset.mem_of_mem_erase hv) hwW hvw⟩, hvw⟩
    have hUlo : q + 1 ≤ U.card := by
      have hc := Finset.card_le_card (ball_mono_radius (D := D) (W := W) (u := u) hk)
      have he := Finset.card_erase_of_mem (self_mem_ball (D := D) (k := k) hu)
      change U.card = (ball D W u k).card - 1 at he
      omega
    have hUhi : U.card ≤ q + 3 := by
      have hc := Finset.card_le_card (ball_mono_radius (D := D) (W := W) (u := u) (by omega : k ≤ 3))
      have he := Finset.card_erase_of_mem (self_mem_ball (D := D) (k := k) hu)
      change U.card = (ball D W u k).card - 1 at he
      omega
    have hc := corB (by omega : 1 ≤ q) (hf.mono_set hUW) hminU
      (Finset.card_pos.mp (by omega : 0 < U.card))
    omega
  have h12 := hstrict 1 (by decide) (by decide)
  have h23 := hstrict 2 (by decide) (by decide)
  change (ball D W u 1).card < (ball D W u 2).card at h12
  change (ball D W u 2).card < (ball D W u 3).card at h23
  have hAc : (outN D W u).card = q + 1 := by omega
  have h2c : (ball D W u 2).card = q + 3 := by omega
  have h3c : (ball D W u 3).card = q + 4 := by omega
  let A := outN D W u
  let B := ball D W u 2 \ ball D W u 1
  let C := ball D W u 3 \ ball D W u 2
  have hAV : A ⊆ W := outN_subset
  have hA1 : A ⊆ ball D W u 1 := fun _ hv => (mem_ball_one hu).mpr (Or.inr hv)
  have hBc : B.card = 1 := by
    change (ball D W u 2 \ ball D W u 1).card = 1
    rw [Finset.card_sdiff_of_subset (ball_mono_radius (by decide : 1 ≤ 2)), h2c, hB1c, hAc]
    omega
  have hCc : C.card = 1 := by
    change (ball D W u 3 \ ball D W u 2).card = 1
    rw [Finset.card_sdiff_of_subset (ball_mono_radius (by decide : 2 ≤ 3)), h3c, h2c]
    omega
  obtain ⟨b, hb⟩ := Finset.card_pos.mp (by omega : 0 < B.card)
  have hbW : b ∈ W := ball_subset (Finset.mem_sdiff.mp hb).1
  have hBsingle : ∀ v ∈ B, v = b := fun v hv => Finset.card_le_one.mp hBc.le v hv b hb
  have hsubA : ∀ a ∈ A, outN D W a ⊆ outN D A a ∪ B := by
    intro a ha v hv
    obtain ⟨hvW, hav⟩ := mem_outN.mp hv
    have hv2 := ball_step (hA1 ha) hvW hav
    by_cases hv1 : v ∈ ball D W u 1
    · rcases (mem_ball_one hu).mp hv1 with hvu | hvA
      · exact (no_back_arc hf hu (hA1 ha) (by omega) (hvu ▸ hav)).elim
      · exact Finset.mem_union_left _ (mem_outN.mpr ⟨hvA, hav⟩)
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hv2, hv1⟩)
  have hminA : ∀ a ∈ A, 1 ≤ (outN D A a).card := by
    intro a ha
    have hc := (Finset.card_le_card (hsubA a ha)).trans (Finset.card_union_le _ _)
    have hh := hmin a (hAV ha)
    omega
  have hreg := (dt_reg (by omega : 1 ≤ q) (ball_q_one _ (by omega))
    (hf.mono_set hAV) hminA (by change (outN D W u).card = q * 1 + 1; omega)).1
  have hab : ∀ a ∈ A, D a b = true := by
    intro a ha
    by_contra hn
    have hsub : outN D W a ⊆ outN D A a := by
      intro v hv
      rcases Finset.mem_union.mp (hsubA a ha hv) with hvA | hvB
      · exact hvA
      · exact (hn (hBsingle v hvB ▸ (mem_outN.mp hv).2)).elim
    have hh := (hmin a (hAV ha)).trans (Finset.card_le_card hsub)
    rw [hreg a ha] at hh
    omega
  have hsubB : outN D W b ⊆ C := by
    intro v hv
    obtain ⟨hvW, hbv⟩ := mem_outN.mp hv
    have hv3 := ball_step (Finset.mem_sdiff.mp hb).1 hvW hbv
    refine Finset.mem_sdiff.mpr ⟨hv3, ?_⟩
    intro hv2
    by_cases hv1 : v ∈ ball D W u 1
    · rcases (mem_ball_one hu).mp hv1 with hvu | hvA
      · exact no_back_arc hf hu (Finset.mem_sdiff.mp hb).1 (by omega) (hvu ▸ hbv)
      · exact digonfree hf (by omega) (hAV hvA) hbW (hab v hvA) hbv
    · have hvB : v ∈ B := Finset.mem_sdiff.mpr ⟨hv2, hv1⟩
      exact loopfree hf (by omega) hbW (hBsingle v hvB ▸ hbv)
  have hh := (hmin b hbW).trans (Finset.card_le_card hsubB)
  omega

/-- A degree-two host of order at most 2s+1 cannot have s rows of degree at least s. -/
theorem high_half_two_core_false {H : Finset ℕ} {s : ℕ} (hs : 5 ≤ s)
    (hf : QFree D W (s - 1)) (hcard : W.card ≤ 2 * s + 1)
    (hmin : ∀ v ∈ W, 2 ≤ (outN D W v).card)
    (hHW : H ⊆ W) (hH : H.card = s) (hhigh : ∀ v ∈ H, s ≤ (outN D W v).card) : False := by
  classical
  have hcap : ∀ v ∈ W, (inN D W v).card ≤ 4 := by
    intro v hv
    have hb := ball_growth (s - 1) (by omega) D W hf hmin v hv (s - 1 - 1) (by omega)
    have hsub : inN D W v ⊆ W \ ball D W v (s - 1 - 1) := by
      intro x hx
      obtain ⟨hxW, hxv⟩ := mem_inN.mp hx
      exact Finset.mem_sdiff.mpr ⟨hxW, fun hxB => no_back_arc hf hv hxB (by omega) hxv⟩
    have hc := Finset.card_le_card hsub
    rw [Finset.card_sdiff_of_subset ball_subset] at hc
    have hbW := Finset.card_le_card (ball_subset (D := D) (W := W) (u := v) (k := s - 1 - 1))
    omega
  have hcapH : ∀ v ∈ H, (inN D W v).card ≤ s - 3 := by
    intro v hv
    have hb := high_row_ball_three (by omega : 3 ≤ s - 1) hf hmin (hHW hv)
      (by have := hhigh v hv; omega : s - 1 + 1 ≤ (outN D W v).card)
    have hsub : inN D W v ⊆ W \ ball D W v 3 := by
      intro x hx
      obtain ⟨hxW, hxv⟩ := mem_inN.mp hx
      exact Finset.mem_sdiff.mpr ⟨hxW, fun hxB => no_back_arc hf (hHW hv) hxB (by omega) hxv⟩
    have hc := Finset.card_le_card hsub
    rw [Finset.card_sdiff_of_subset ball_subset] at hc
    have hbW := Finset.card_le_card (ball_subset (D := D) (W := W) (u := v) (k := 3))
    omega
  have hloH := Finset.sum_le_sum hhigh
  have hloL := Finset.sum_le_sum (fun v hv => hmin v (Finset.mem_sdiff.mp hv).1) (s := W \ H)
  have hupH := Finset.sum_le_sum hcapH
  have hupL := Finset.sum_le_sum (fun v hv => hcap v (Finset.mem_sdiff.mp hv).1) (s := W \ H)
  rw [Finset.sum_const_nat (fun _ _ => rfl), hH] at hloH hupH
  rw [Finset.sum_const_nat (fun _ _ => rfl)] at hloL hupL
  have ho := Finset.sum_sdiff hHW (f := fun v => (outN D W v).card)
  have hi := Finset.sum_sdiff hHW (f := fun v => (inN D W v).card)
  have he : (∑ v ∈ W, (outN D W v).card) = ∑ v ∈ W, (inN D W v).card :=
    Compose.ThinRigid.sum_out_eq_sum_in D W
  have hc := Finset.card_sdiff_add_card_eq_card hHW
  rw [hH] at hc
  have hs3 : s - 3 + 3 = s := by omega
  nlinarith

/-- At most 2q+2 vertices leave incoming cap three; too many degree-five rows are impossible. -/
theorem two_core_many_high_false {H : Finset ℕ} (hq : 1 ≤ q)
    (hf : QFree D W q) (hcard : W.card ≤ 2 * q + 2)
    (hmin : ∀ v ∈ W, 2 ≤ (outN D W v).card)
    (hHW : H ⊆ W) (hmany : W.card < 3 * H.card)
    (hhigh : ∀ v ∈ H, 5 ≤ (outN D W v).card) : False := by
  classical
  have hcap : ∀ v ∈ W, (inN D W v).card ≤ 3 := by
    intro v hv
    have hb := ball_growth q hq D W hf hmin v hv (q - 1) (by omega)
    have hsub : inN D W v ⊆ W \ ball D W v (q - 1) := by
      intro x hx
      obtain ⟨hxW, hxv⟩ := mem_inN.mp hx
      exact Finset.mem_sdiff.mpr ⟨hxW, fun hxB => no_back_arc hf hv hxB (by omega) hxv⟩
    have hc := Finset.card_le_card hsub
    rw [Finset.card_sdiff_of_subset ball_subset] at hc
    have hbW := Finset.card_le_card (ball_subset (D := D) (W := W) (u := v) (k := q - 1))
    omega
  have hloH := Finset.sum_le_sum hhigh
  have hloL := Finset.sum_le_sum (fun v hv => hmin v (Finset.mem_sdiff.mp hv).1) (s := W \ H)
  have hup := Finset.sum_le_sum hcap
  rw [Finset.sum_const_nat (fun _ _ => rfl)] at hloH hloL hup
  have ho := Finset.sum_sdiff hHW (f := fun v => (outN D W v).card)
  have he : (∑ v ∈ W, (outN D W v).card) = ∑ v ∈ W, (inN D W v).card :=
    Compose.ThinRigid.sum_out_eq_sum_in D W
  have hc := Finset.card_sdiff_add_card_eq_card hHW
  omega

end LeanCH.BR.BRsGen
