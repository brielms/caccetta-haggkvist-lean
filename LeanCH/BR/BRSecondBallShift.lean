import LeanCH.BR.BRSecondBallRegular
import LeanCH.BR.BRsGenRigid
import LeanCH.BR.BRsubSat

/-! A full second-layer head shifts every later ball and propagates uniform upper growth. -/

namespace LeanCH.BR.BRsGen
open BRq2 BRq3 BR45 BRsub Compose.Boundary

theorem ball_succ_card_le_of_full_second {D : CH.Digraph} {V : Finset ℕ}
    {u x k : ℕ} (hu : u ∈ V) (hx : x ∈ ball D V u 1) (hk : 1 ≤ k)
    (hfull : ∀ y ∈ ball D V u 2 \ ball D V u 1, D x y = true) :
    (ball D V u (k + 1)).card + 1 ≤
      (ball D V u 1).card + (ball D V x k).card := by
  classical
  let R := ball D V u (k + 1) \ ball D V u 1
  have hsub : insert x R ⊆ ball D V x k := by
    apply Finset.insert_subset (self_mem_ball (ball_subset hx))
    intro z hz
    have hh := reach_of_heads hu
      (fun y hy2 hy1 => hfull y (Finset.mem_sdiff.mpr ⟨hy2, hy1⟩))
      (by omega : 2 ≤ k + 1) (Finset.mem_sdiff.mp hz).1 (Finset.mem_sdiff.mp hz).2
    simpa only [Nat.add_sub_cancel] using hh
  have hc := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem (fun h => (Finset.mem_sdiff.mp h).2 hx)] at hc
  change R.card + 1 ≤ (ball D V x k).card at hc
  have hp : R.card + (ball D V u 1).card = (ball D V u (k + 1)).card :=
    Finset.card_sdiff_add_card_eq_card
      (ball_mono_radius (D := D) (W := V) (u := u) (by omega : 1 ≤ k + 1))
  omega

theorem ball_upper_of_second_ball_cap {D : CH.Digraph} {V : Finset ℕ} {s : ℕ}
    (hs : 2 ≤ s) (hf : QFree D V s)
    (hmin : ∀ v ∈ V, s ≤ (outN D V v).card)
    (hcap : ∀ v ∈ V, (ball D V v 2).card ≤ 2 * s + 1) :
    ∀ k u, u ∈ V → (ball D V u k).card ≤ s * k + 1 := by
  classical
  have ho := out_regular_of_second_ball_cap hs hf hmin hcap
  have h1 : ∀ u ∈ V, (ball D V u 1).card = s + 1 := by
    intro u hu
    have heq : ball D V u 1 = insert u (outN D V u) := by
      ext v
      simp only [mem_ball_one hu, Finset.mem_insert]
    rw [heq, Finset.card_insert_of_notMem (fun h =>
      loopfree hf (by omega) hu (mem_outN.mp h).2), ho u hu]
  have h2 : ∀ u ∈ V, (ball D V u 2 \ ball D V u 1).card = s := by
    intro u hu
    have hlo := n2_ge_s hs hf ho hu
    change s ≤ (ball D V u 2 \ ball D V u 1).card at hlo
    have hp := Finset.card_sdiff_add_card_eq_card
      (ball_mono_radius (D := D) (W := V) (u := u) (by decide : 1 ≤ 2))
    have ha := h1 u hu
    have hb := hcap u hu
    omega
  intro k
  induction k with
  | zero =>
    intro u hu
    have hsub : ball D V u 0 ⊆ {u} := by
      intro v hv
      obtain ⟨_, m, hm, w⟩ := mem_ball.mp hv
      have hm0 : m = 0 := by omega
      subst m
      cases w
      exact Finset.mem_singleton_self _
    simpa using Finset.card_le_card hsub
  | succ k ih =>
    intro u hu
    by_cases hk : k = 0
    · subst k
      simpa using (h1 u hu).le
    · have hXV : outN D V u ⊆ V := outN_subset
      obtain ⟨x, hx, hsink⟩ := exists_sink (hf.mono_set hXV)
        (Finset.card_pos.mp (by rw [ho u hu]; omega)) (by rw [ho u hu])
      have hfull := sink_all_s hs hf ho hu (h2 u hu) hx hsink
      have hshift := ball_succ_card_le_of_full_second hu
        ((mem_ball_one hu).mpr (Or.inr hx)) (by omega : 1 ≤ k) hfull
      have hb := ih x (hXV hx)
      have ha := h1 u hu
      rw [Nat.mul_add, Nat.mul_one]
      omega

theorem incoming_regular_of_second_ball_cap {D : CH.Digraph} {V : Finset ℕ} {q s : ℕ}
    (hs : 2 ≤ s) (hsq : s ≤ q) (hf : QFree D V q)
    (hmin : ∀ v ∈ V, s ≤ (outN D V v).card) (hsat : BRsub.Sat q D V)
    (hV : V.card = q * s + 1)
    (hcap : ∀ v ∈ V, (ball D V v 2).card ≤ 2 * s + 1) :
    ∀ v ∈ V, (inN D V v).card = s := by
  have hfs := hf.mono_bound hsq
  have ho := out_regular_of_second_ball_cap hs hfs hmin hcap
  have hidentity : s * (q - 1) + s = q * s := by
    calc
      s * (q - 1) + s = s * ((q - 1) + 1) := by rw [Nat.mul_add, Nat.mul_one]
      _ = s * q := by congr 1; omega
      _ = q * s := Nat.mul_comm _ _
  have hge : ∀ v ∈ V, s ≤ (inN D V v).card := by
    intro v hv
    have hb := ball_upper_of_second_ball_cap hs hfs hmin hcap (q - 1) v hv
    have hi := card_inN_of_satQ (by omega : 1 ≤ q) hf hsat hv
    omega
  have hout : (∑ v ∈ V, (outN D V v).card) = ∑ _v ∈ V, s :=
    Finset.sum_congr rfl ho
  have he : (∑ v ∈ V, (outN D V v).card) = ∑ v ∈ V, (inN D V v).card :=
    Compose.ThinRigid.sum_out_eq_sum_in D V
  have heach := (Finset.sum_eq_sum_iff_of_le hge).mp (hout.symm.trans he)
  exact fun v hv => (heach v hv).symm

theorem br_of_second_ball_cap {q s : ℕ} (hs : 2 ≤ s) (hsq : s ≤ q)
    (hcap : ∀ D : CH.Digraph, QFree D (Finset.range (q * s + 1)) q →
      (∀ v ∈ Finset.range (q * s + 1), s ≤ (outN D (Finset.range (q * s + 1)) v).card) →
      ∀ v ∈ Finset.range (q * s + 1),
        (ball D (Finset.range (q * s + 1)) v 2).card ≤ 2 * s + 1) :
    BoundaryRegular q s := by
  apply br_of_satQ
  intro D hf hmin hsat
  exact incoming_regular_of_second_ball_cap hs hsq hf hmin hsat
    (Finset.card_range _) (hcap D hf hmin)

end LeanCH.BR.BRsGen
