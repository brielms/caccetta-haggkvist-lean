import LeanCH.BR.BRThresholdGrowth
import LeanCH.BR.BRSmallLowExits

/-! The lower high-row threshold strengthens the degree-five ball residual. -/

namespace LeanCH.BR.BRsGen
open BRq2 BRq3 BR45

/-- A proved ball bound controls a core with two degree floors. -/
theorem mixed_degree_density_of_ball {D : CH.Digraph} {V H : Finset ℕ} {q d r : ℕ}
    (hq : 1 ≤ q) (hb : Ball q d) (hf : QFree D V q)
    (hmin : ∀ v ∈ V, d ≤ (outN D V v).card)
    (hHV : H ⊆ V) (hhigh : ∀ v ∈ H, r ≤ (outN D V v).card) :
    (q * d + 1) * V.card + r * H.card ≤ V.card * V.card + d * H.card := by
  classical
  have hin : ∀ v ∈ V, (inN D V v).card + (d * (q - 1) + 1) ≤ V.card := by
    intro v hv
    have hg := ball_of_min hb hf hmin v hv
    have hi := incoming_add_ball_le hf hv (by omega : q - 1 + 1 ≤ q)
    omega
  have hs := Finset.sum_le_sum hin
  have hoH := Finset.sum_le_sum hhigh
  have hoL := Finset.sum_le_sum (s := V \ H)
    (fun v hv => hmin v (Finset.mem_sdiff.mp hv).1)
  simp only [Finset.sum_add_distrib, Finset.sum_const_nat (fun _ _ => rfl)] at hs hoH hoL
  have hc := Finset.card_sdiff_add_card_eq_card hHV
  have ho := Finset.sum_sdiff hHV (f := fun v => (outN D V v).card)
  have he : (∑ v ∈ V, (outN D V v).card) = ∑ v ∈ V, (inN D V v).card :=
    Compose.ThinRigid.sum_out_eq_sum_in D V
  have hqeq : q - 1 + 1 = q := by omega
  have heq : (q * d + 1) * V.card = V.card * (d * (q - 1) + 1) + d * V.card := by
    nth_rw 1 [← hqeq]
    simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
    ac_rfl
  rw [heq]
  nlinarith [congrArg (fun n => n * d) hc]

theorem two_core_threshold_exit_density {D : CH.Digraph} {V H K : Finset ℕ} {q : ℕ}
    (hq : 5 ≤ q) (hf : QFree D V q) (hmin : ∀ v ∈ V, 2 ≤ (outN D V v).card)
    (hHV : H ⊆ V) (hhigh : ∀ v ∈ H, q ≤ (outN D V v).card)
    (hKL : K ⊆ V \ H) (hexit : ∀ v ∈ K, (outN D H v).Nonempty) :
    (2 * q + 1) * V.card + 6 * H.card + 7 * K.card ≤
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
    have hb := threshold_two_ball_four hq hf hmin (hHV hv) (hhigh v hv)
    have hi := incoming_add_ball_le hf (hHV hv) (by omega : 4 + 1 ≤ q)
    omega
  have hcapK : ∀ v ∈ K, (inN D V v).card + q + 6 ≤ V.card := by
    intro v hv
    obtain ⟨x, hx⟩ := hexit v hv
    have hb := threshold_two_predecessor_four hq hf hmin (hLV (hKL hv))
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

theorem two_core_sixteen_thirteen_false {D : CH.Digraph} {V H : Finset ℕ}
    (hf : QFree D V 5) (hmin : ∀ v ∈ V, 2 ≤ (outN D V v).card)
    (hHV : H ⊆ V) (hhigh : ∀ v ∈ H, 5 ≤ (outN D V v).card)
    (hV : V.card = 16) (hH : H.card = 13) : False := by
  classical
  let K := (V \ H).filter (fun v => (outN D H v).Nonempty)
  have hLc : (V \ H).card = 3 := by
    have hh := Finset.card_sdiff_add_card_eq_card hHV
    omega
  have hK : 2 ≤ K.card := small_low_exit_count hf hmin (by omega) (by omega)
  have hd := two_core_threshold_exit_density (by decide : 5 ≤ 5) hf hmin hHV hhigh
    (show K ⊆ V \ H from Finset.filter_subset _ _)
    (fun _ hv => (Finset.mem_filter.mp hv).2)
  rw [hV, hH] at hd
  omega

end LeanCH.BR.BRsGen
