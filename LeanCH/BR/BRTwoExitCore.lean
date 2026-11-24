import LeanCH.BR.BRHighTwoPredecessor
import LeanCH.BR.BRHighTwoGrowth

/-! Two exits from a small low set strengthen the mixed degree-two density bound. -/

namespace LeanCH.BR.BRsGen
open BRq2 BRq3 BR45

theorem two_low_high_heads {D : CH.Digraph} {V H : Finset ℕ} {q : ℕ}
    (hq : 5 ≤ q) (hf : QFree D V q) (hmin : ∀ v ∈ V, 2 ≤ (outN D V v).card)
    (hHV : H ⊆ V) (hhigh : ∀ v ∈ H, q + 1 ≤ (outN D V v).card)
    (hlo : 2 ≤ (V \ H).card) (hsmall : (V \ H).card ≤ q + 2)
    (hV : V.card ≤ 2 * q + 7) :
    ∃ z ∈ V \ H, ∃ w ∈ V \ H, w ≠ z ∧
      (outN D H z).Nonempty ∧ (outN D H w).Nonempty := by
  classical
  let L := V \ H
  have hLV : L ⊆ V := Finset.sdiff_subset
  change 2 ≤ L.card at hlo
  change L.card ≤ q + 2 at hsmall
  have hex : ∃ z ∈ L, (outN D H z).Nonempty := by
    by_contra hn
    have hminL : ∀ z ∈ L, 2 ≤ (outN D L z).card := by
      intro z hz
      apply (hmin z (hLV hz)).trans
      apply Finset.card_le_card
      intro v hv
      obtain ⟨hvV, hzv⟩ := mem_outN.mp hv
      exact mem_outN.mpr ⟨Finset.mem_sdiff.mpr
        ⟨hvV, fun hvH => hn ⟨z, hz, v, mem_outN.mpr ⟨hvH, hzv⟩⟩⟩, hzv⟩
    have hh := corB (by omega : 1 ≤ q) (hf.mono_set hLV) hminL
      (Finset.card_pos.mp (by omega))
    omega
  obtain ⟨z, hz, hzH⟩ := hex
  have hsecond : ∃ w ∈ L, w ≠ z ∧ (outN D H w).Nonempty := by
    by_contra hn
    let R := L.erase z
    have hRL : R ⊆ L := Finset.erase_subset _ _
    have hRV : R ⊆ V := hRL.trans hLV
    have hRc : R.card = L.card - 1 := Finset.card_erase_of_mem hz
    have havoid : ∀ x ∈ R, outN D V x ⊆ L := by
      intro x hx v hv
      obtain ⟨hvV, hxv⟩ := mem_outN.mp hv
      exact Finset.mem_sdiff.mpr ⟨hvV, fun hvH =>
        hn ⟨x, hRL hx, (Finset.mem_erase.mp hx).1, v, mem_outN.mpr ⟨hvH, hxv⟩⟩⟩
    have hminR : ∀ x ∈ R, 1 ≤ (outN D R x).card := by
      intro x hx
      have hsub : outN D V x ⊆ outN D R x ∪ {z} := by
        intro v hv
        by_cases hvz : v = z
        · exact Finset.mem_union_right _ (Finset.mem_singleton.mpr hvz)
        · exact Finset.mem_union_left _ (mem_outN.mpr
            ⟨Finset.mem_erase.mpr ⟨hvz, havoid x hx hv⟩, (mem_outN.mp hv).2⟩)
      have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
      have hh := hmin x (hRV hx)
      simp only [Finset.card_singleton] at hc
      omega
    have hRlo := dt_size (by omega : 1 ≤ q) (ball_q_one q (by omega))
      (hf.mono_set hRV) hminR (Finset.card_pos.mp (by omega))
    have hReq : R.card = q * 1 + 1 := by omega
    have hreg := (dt_reg (by omega : 1 ≤ q) (ball_q_one q (by omega))
      (hf.mono_set hRV) hminR hReq).1
    have hparents : R ⊆ inN D V z := by
      intro x hx
      refine mem_inN.mpr ⟨hRV hx, ?_⟩
      by_contra hxz
      have hsub : outN D V x ⊆ outN D R x := by
        intro v hv
        exact mem_outN.mpr ⟨Finset.mem_erase.mpr
          ⟨fun heq => hxz (heq ▸ (mem_outN.mp hv).2), havoid x hx hv⟩, (mem_outN.mp hv).2⟩
      have hc := Finset.card_le_card hsub
      have hh := hmin x (hRV hx)
      have hr := hreg x hx
      omega
    obtain ⟨v, hv⟩ := hzH
    have hb := high_two_predecessor_ball_four hq hf hmin (hLV hz)
      (outN_mono hHV z hv) (hhigh v (mem_outN.mp hv).1)
    have hi := incoming_add_ball_le hf (hLV hz) (by omega : 4 + 1 ≤ q)
    have hc := Finset.card_le_card hparents
    omega
  obtain ⟨w, hw, hwz, hwH⟩ := hsecond
  exact ⟨z, hz, w, hw, hwz, hzH, hwH⟩

/-- Every marked low predecessor contributes its own incoming exclusion.
No bound on the order or on the size of the low set is required here. -/
theorem two_core_high_exit_density {D : CH.Digraph} {V H K : Finset ℕ} {q : ℕ}
    (hq : 5 ≤ q) (hf : QFree D V q) (hmin : ∀ v ∈ V, 2 ≤ (outN D V v).card)
    (hHV : H ⊆ V) (hhigh : ∀ v ∈ H, q + 1 ≤ (outN D V v).card)
    (hKL : K ⊆ V \ H) (hexit : ∀ v ∈ K, (outN D H v).Nonempty) :
    (2 * q + 1) * V.card + 7 * H.card + 8 * K.card ≤
      V.card * V.card + q * K.card := by
  classical
  let L := V \ H
  have hLV : L ⊆ V := Finset.sdiff_subset
  have hcap : ∀ v ∈ V, (inN D V v).card + 2 * q ≤ V.card + 1 := by
    intro v hv
    have hb := ball_growth q (by omega) D V hf hmin v hv (q - 1) (by omega)
    have hi := incoming_add_ball_le hf hv (by omega : q - 1 + 1 ≤ q)
    omega
  have hcapH : ∀ v ∈ H, (inN D V v).card + q + 7 ≤ V.card := by
    intro v hv
    have hb := high_two_ball_four hq hf hmin (hHV hv) (hhigh v hv)
    have hi := incoming_add_ball_le hf (hHV hv) (by omega : 4 + 1 ≤ q)
    omega
  have hcapK : ∀ v ∈ K, (inN D V v).card + q + 7 ≤ V.card := by
    intro v hv
    obtain ⟨x, hx⟩ := hexit v hv
    have hb := high_two_predecessor_ball_four hq hf hmin (hLV (hKL hv))
      (outN_mono hHV v hx) (hhigh x (mem_outN.mp hx).1)
    have hi := incoming_add_ball_le hf (hLV (hKL hv)) (by omega : 4 + 1 ≤ q)
    omega
  have hsH := Finset.sum_le_sum hcapH
  have hsK := Finset.sum_le_sum hcapK
  have hsL := Finset.sum_le_sum (s := L \ K)
    (fun v hv => hcap v (hLV (Finset.mem_sdiff.mp hv).1))
  have hoH := Finset.sum_le_sum hhigh
  have hoL := Finset.sum_le_sum (s := L) (fun v hv => hmin v (hLV hv))
  simp only [Finset.sum_add_distrib, Finset.sum_const_nat (fun _ _ => rfl)] at hsH hsK hsL hoH hoL
  have hiK := Finset.sum_sdiff hKL (f := fun v => (inN D V v).card)
  have hcK := Finset.card_sdiff_add_card_eq_card hKL
  have hi := Finset.sum_sdiff hHV (f := fun v => (inN D V v).card)
  have ho := Finset.sum_sdiff hHV (f := fun v => (outN D V v).card)
  have hc := Finset.card_sdiff_add_card_eq_card hHV
  change (∑ v ∈ L \ K, (inN D V v).card) + _ = _ at hiK
  change (L \ K).card + K.card = L.card at hcK
  change (∑ v ∈ L, (inN D V v).card) + _ = _ at hi
  change (∑ v ∈ L, (outN D V v).card) + _ = _ at ho
  change L.card + H.card = V.card at hc
  have he : (∑ v ∈ V, (outN D V v).card) = ∑ v ∈ V, (inN D V v).card :=
    Compose.ThinRigid.sum_out_eq_sum_in D V
  nlinarith

/-- A low set smaller than the minimum-two order bound must have an exit. -/
theorem two_core_one_exit_density {D : CH.Digraph} {V H : Finset ℕ} {q : ℕ}
    (hq : 5 ≤ q) (hf : QFree D V q) (hmin : ∀ v ∈ V, 2 ≤ (outN D V v).card)
    (hHV : H ⊆ V) (hhigh : ∀ v ∈ H, q + 1 ≤ (outN D V v).card)
    (hlo : 1 ≤ (V \ H).card) (hsmall : (V \ H).card ≤ 2 * q) :
    (2 * q + 1) * V.card + 7 * H.card + 8 ≤ V.card * V.card + q := by
  classical
  let L := V \ H
  have hLV : L ⊆ V := Finset.sdiff_subset
  have hex : ∃ z ∈ L, (outN D H z).Nonempty := by
    by_contra hn
    have hminL : ∀ z ∈ L, 2 ≤ (outN D L z).card := by
      intro z hz
      apply (hmin z (hLV hz)).trans
      apply Finset.card_le_card
      intro v hv
      obtain ⟨hvV, hzv⟩ := mem_outN.mp hv
      exact mem_outN.mpr ⟨Finset.mem_sdiff.mpr
        ⟨hvV, fun hvH => hn ⟨z, hz, v, mem_outN.mpr ⟨hvH, hzv⟩⟩⟩, hzv⟩
    have hh := corB (by omega : 1 ≤ q) (hf.mono_set hLV) hminL
      (Finset.card_pos.mp hlo)
    change L.card ≤ 2 * q at hsmall
    omega
  obtain ⟨z, hz, hzH⟩ := hex
  have hKL : ({z} : Finset ℕ) ⊆ V \ H := Finset.singleton_subset_iff.mpr hz
  have hd := two_core_high_exit_density hq hf hmin hHV hhigh hKL
    (by intro v hv; have he : v = z := Finset.mem_singleton.mp hv; simpa [he] using hzH)
  simpa only [Finset.card_singleton, Nat.mul_one] using hd

theorem two_core_two_exit_density {D : CH.Digraph} {V H : Finset ℕ} {q : ℕ}
    (hq : 5 ≤ q) (hf : QFree D V q) (hmin : ∀ v ∈ V, 2 ≤ (outN D V v).card)
    (hHV : H ⊆ V) (hhigh : ∀ v ∈ H, q + 1 ≤ (outN D V v).card)
    (hlo : 2 ≤ (V \ H).card) (hsmall : (V \ H).card ≤ q + 2)
    (hV : V.card ≤ 2 * q + 7) :
    (2 * q + 1) * V.card + 7 * H.card + 16 ≤ V.card * V.card + 2 * q := by
  classical
  obtain ⟨z, hz, w, hw, hwz, hzH, hwH⟩ := two_low_high_heads hq hf hmin hHV hhigh hlo hsmall hV
  have hKL : ({z, w} : Finset ℕ) ⊆ V \ H := by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl <;> assumption
  have hexit : ∀ v ∈ ({z, w} : Finset ℕ), (outN D H v).Nonempty := by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl <;> assumption
  have hc : ({z, w} : Finset ℕ).card = 2 := by simp [Ne.symm hwz]
  have hd := two_core_high_exit_density hq hf hmin hHV hhigh hKL hexit
  rw [hc] at hd
  omega

theorem two_core_fifteen_eight_false {D : CH.Digraph} {V H : Finset ℕ}
    (hf : QFree D V 5) (hmin : ∀ v ∈ V, 2 ≤ (outN D V v).card)
    (hHV : H ⊆ V) (hhigh : ∀ v ∈ H, 6 ≤ (outN D V v).card)
    (hV : V.card = 15) (hH : H.card = 8) : False := by
  have hc := Finset.card_sdiff_add_card_eq_card hHV
  have hd := two_core_two_exit_density (by decide : 5 ≤ 5) hf hmin hHV hhigh
    (by omega) (by omega) (by omega)
  rw [hV, hH] at hd
  omega

end LeanCH.BR.BRsGen
