import LeanCH.BR.BRHighPairGrowth
import LeanCH.BR.BRTwoExitCore

/-! A small low set forces high/high arcs and improves the high-row coefficient. -/

namespace LeanCH.BR.BRsGen
open BRq2 BRq3 BR45

theorem two_core_dense_high_balls {D : CH.Digraph} {V H : Finset ℕ} {q : ℕ}
    (hq : 5 ≤ q) (hf : QFree D V q) (hmin : ∀ v ∈ V, 2 ≤ (outN D V v).card)
    (hHV : H ⊆ V) (hhigh : ∀ v ∈ H, q + 1 ≤ (outN D V v).card)
    (hsmall : (V \ H).card ≤ q) : ∀ v ∈ H, q + 8 ≤ (ball D V v 4).card := by
  intro v hv
  have hex : ∃ w ∈ outN D V v, w ∈ H := by
    by_contra hn
    have hsub : outN D V v ⊆ V \ H := by
      intro w hw
      exact Finset.mem_sdiff.mpr ⟨(mem_outN.mp hw).1, fun hwH => hn ⟨w, hw, hwH⟩⟩
    have hc := Finset.card_le_card hsub
    have hh := hhigh v hv
    omega
  obtain ⟨w, hw, hwH⟩ := hex
  exact high_two_pair_ball_four hq hf hmin (hHV hv) (hhigh v hv) hw (hhigh w hwH)

theorem two_core_dense_high_exit_density {D : CH.Digraph} {V H K : Finset ℕ} {q : ℕ}
    (hq : 5 ≤ q) (hf : QFree D V q) (hmin : ∀ v ∈ V, 2 ≤ (outN D V v).card)
    (hHV : H ⊆ V) (hhigh : ∀ v ∈ H, q + 1 ≤ (outN D V v).card)
    (hsmall : (V \ H).card ≤ q)
    (hKL : K ⊆ V \ H) (hexit : ∀ v ∈ K, (outN D H v).Nonempty) :
    (2 * q + 1) * V.card + 8 * H.card + 8 * K.card ≤
      V.card * V.card + q * K.card := by
  classical
  let L := V \ H
  have hLV : L ⊆ V := Finset.sdiff_subset
  have hcap : ∀ v ∈ V, (inN D V v).card + 2 * q ≤ V.card + 1 := by
    intro v hv
    have hb := ball_growth q (by omega) D V hf hmin v hv (q - 1) (by omega)
    have hi := incoming_add_ball_le hf hv (by omega : q - 1 + 1 ≤ q)
    omega
  have hcapH : ∀ v ∈ H, (inN D V v).card + q + 8 ≤ V.card := by
    intro v hv
    have hb := two_core_dense_high_balls hq hf hmin hHV hhigh hsmall v hv
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


theorem two_core_dense_high_density {D : CH.Digraph} {V H : Finset ℕ} {q : ℕ}
    (hq : 5 ≤ q) (hf : QFree D V q) (hmin : ∀ v ∈ V, 2 ≤ (outN D V v).card)
    (hHV : H ⊆ V) (hhigh : ∀ v ∈ H, q + 1 ≤ (outN D V v).card)
    (hsmall : (V \ H).card ≤ q) :
    (2 * q + 1) * V.card + 8 * H.card ≤ V.card * V.card := by
  have hh := two_core_dense_high_exit_density (K := ∅) hq hf hmin hHV hhigh hsmall
    (Finset.empty_subset _) (by intro v hv; simp at hv)
  simpa using hh

end LeanCH.BR.BRsGen
