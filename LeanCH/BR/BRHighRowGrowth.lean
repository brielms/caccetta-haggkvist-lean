import LeanCH.BR.BRPrefixRetention
import LeanCH.BR.BRHighTwoCore

/-! Sharp radius-three growth from a high row, with arbitrary minimum degree.
The threshold q >= 2d-1 is explicit; no full degree-d ball theorem is assumed. -/

namespace LeanCH.BR.BRsGen

open BRq2 BRq3 BR45

/-- Above the degree-two deletion threshold, a high row forces extra growth. -/
theorem high_row_ball_three_min {D : CH.Digraph} {V : Finset ℕ} {u q d : ℕ}
    (hd : 2 ≤ d) (hqd : 2 * d ≤ q + 1) (hf : QFree D V q)
    (hmin : ∀ v ∈ V, d ≤ (outN D V v).card) (hu : u ∈ V)
    (hhigh : q + 1 ≤ (outN D V u).card) :
    q + 2 * d + 1 ≤ (ball D V u 3).card := by
  classical
  by_contra hn
  have hsmall : (ball D V u 3).card ≤ q + 2 * d := by omega
  let X := outN D V u
  let Y := ball D V u 2 \ ball D V u 1
  let Z := ball D V u 3 \ ball D V u 2
  have hXV : X ⊆ V := outN_subset
  have hX1 : X ⊆ ball D V u 1 := fun _ hx => (mem_ball_one hu).mpr (Or.inr hx)
  have hYV : Y ⊆ V := fun _ hy => ball_subset (Finset.mem_sdiff.mp hy).1
  have hBc : (ball D V u 1).card = (outN D V u).card + 1 := by
    have he := Finset.card_erase_of_mem (self_mem_ball (D := D) (k := 1) hu)
    rw [erase_ball_one_eq_outN hf (by omega) hu] at he
    have hpos : 0 < (ball D V u 1).card := Finset.card_pos.mpr ⟨u, self_mem_ball hu⟩
    omega
  have h12 := Finset.card_sdiff_add_card_eq_card
    (ball_mono_radius (D := D) (W := V) (u := u) (by decide : 1 ≤ 2))
  have h23 := Finset.card_sdiff_add_card_eq_card
    (ball_mono_radius (D := D) (W := V) (u := u) (by decide : 2 ≤ 3))
  have hsum : 1 + X.card + Y.card + Z.card = (ball D V u 3).card := by
    change 1 + (outN D V u).card +
      (ball D V u 2 \ ball D V u 1).card +
      (ball D V u 3 \ ball D V u 2).card = _
    omega
  have hdrop (k : ℕ) (hk : 1 ≤ k) (hk2 : k ≤ 2) :
      d ≤ (ball D V u (k + 1) \ ball D V u k).card + 1 := by
    by_contra hn
    let U := (ball D V u k).erase u
    have hUV : U ⊆ V := (Finset.erase_subset _ _).trans ball_subset
    have hminU := minOut_prefix_erase (d := 2) hf hu (by omega : k + 1 ≤ q) hmin
      (by omega : 2 + (ball D V u (k + 1) \ ball D V u k).card ≤ d)
    have hUhi : U.card ≤ 2 * q := by
      have he : U.card = (ball D V u k).card - 1 :=
        Finset.card_erase_of_mem (self_mem_ball hu)
      have hc := Finset.card_le_card
        (ball_mono_radius (D := D) (W := V) (u := u) (by omega : k ≤ 3))
      omega
    have hXU : X ⊆ U := by
      intro x hx
      exact Finset.mem_erase.mpr
        ⟨fun heq => loopfree hf (by omega) hu (heq ▸ (mem_outN.mp hx).2),
          ball_mono_radius hk (hX1 hx)⟩
    have hne : U.Nonempty :=
      (Finset.card_pos.mp (by change 0 < (outN D V u).card; omega)).mono hXU
    have hsize := corB (by omega : 1 ≤ q) (hf.mono_set hUV) hminU hne
    omega
  have hYlo : d ≤ Y.card + 1 := hdrop 1 (by decide) (by decide)
  have hZlo : d ≤ Z.card + 1 := hdrop 2 (by decide) (by decide)
  have hXc : X.card = q + 1 := by change q + 1 ≤ X.card at hhigh; omega
  have hYc : Y.card + 1 = d := by omega
  have hZc : Z.card + 1 = d := by omega
  have hXE : (ball D V u 1).erase u = X := erase_ball_one_eq_outN hf (by omega) hu
  have hminX : ∀ x ∈ X, 1 ≤ (outN D X x).card := by
    have hh := minOut_prefix_erase (d := 1) hf hu (by omega : 1 + 1 ≤ q) hmin
      (by change 1 + Y.card ≤ d; omega)
    simpa only [hXE] using hh
  have hreg := (dt_reg (by omega : 1 ≤ q) (ball_q_one q (by omega))
    (hf.mono_set hXV) hminX (by omega : X.card = q * 1 + 1)).1
  have hsubX : ∀ x ∈ X, outN D V x ⊆ outN D X x ∪ Y := by
    intro x hx
    have hh := outN_prefix_loss hf hu (by omega : 1 + 1 ≤ q) (hXE.symm ▸ hx)
    simpa only [hXE] using hh
  have hheads : ∀ x ∈ X, ∀ y ∈ Y, D x y = true := by
    intro x hx y hy
    by_contra hnot
    have hsub : outN D V x ⊆ outN D X x ∪ Y.erase y := by
      intro v hv
      rcases Finset.mem_union.mp (hsubX x hx hv) with hvX | hvY
      · exact Finset.mem_union_left _ hvX
      · exact Finset.mem_union_right _ (Finset.mem_erase.mpr
          ⟨fun heq => hnot (heq ▸ (mem_outN.mp hv).2), hvY⟩)
    have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    rw [hreg x hx, Finset.card_erase_of_mem hy] at hc
    have hh := hmin x (hXV hx)
    omega
  obtain ⟨y, hy, hsink⟩ := exists_sink (hf.mono_set hYV)
    (Finset.card_pos.mp (by omega : 0 < Y.card)) (by omega : Y.card ≤ q)
  have hsubY : outN D V y ⊆ Z := by
    intro v hv
    obtain ⟨hvV, hyv⟩ := mem_outN.mp hv
    have hv3 := ball_step (Finset.mem_sdiff.mp hy).1 hvV hyv
    refine Finset.mem_sdiff.mpr ⟨hv3, ?_⟩
    intro hv2
    by_cases hv1 : v ∈ ball D V u 1
    · rcases (mem_ball_one hu).mp hv1 with hvu | hvX
      · exact no_back_arc hf hu (Finset.mem_sdiff.mp hy).1 (by omega) (hvu ▸ hyv)
      · exact digonfree hf (by omega) (hXV hvX) (hYV hy) (hheads v hvX y hy) hyv
    · exact hsink v (Finset.mem_sdiff.mpr ⟨hv2, hv1⟩) hyv
  have hc := (hmin y (hYV hy)).trans (Finset.card_le_card hsubY)
  omega

/-- Incoming neighbours are disjoint from every ball too short to close a forbidden walk. -/
theorem incoming_add_ball_le {D : CH.Digraph} {V : Finset ℕ} {u q k : ℕ}
    (hf : QFree D V q) (hu : u ∈ V) (hk : k + 1 ≤ q) :
    (inN D V u).card + (ball D V u k).card ≤ V.card := by
  have hsub : inN D V u ⊆ V \ ball D V u k := by
    intro x hx
    obtain ⟨hxV, hxu⟩ := mem_inN.mp hx
    exact Finset.mem_sdiff.mpr ⟨hxV, fun hxB => no_back_arc hf hu hxB hk hxu⟩
  have hc := Finset.card_le_card hsub
  have he := Finset.card_sdiff_add_card_eq_card
    (ball_subset (D := D) (W := V) (u := u) (k := k))
  omega

/-- A uniform density obstruction for high rows in a minimum-degree-two core.
For q=5 this is 11N+5|H| <= N^2; it uses the high rows' own ball floor. -/
theorem two_core_high_density {D : CH.Digraph} {V H : Finset ℕ} {q : ℕ}
    (hq : 4 ≤ q) (hf : QFree D V q)
    (hmin : ∀ v ∈ V, 2 ≤ (outN D V v).card)
    (hHV : H ⊆ V) (hhigh : ∀ v ∈ H, q + 1 ≤ (outN D V v).card) :
    (2 * q + 1) * V.card + 5 * H.card ≤ V.card * V.card := by
  classical
  have hcap : ∀ v ∈ V, (inN D V v).card + 2 * q ≤ V.card + 1 := by
    intro v hv
    have hb := ball_growth q (by omega) D V hf hmin v hv (q - 1) (by omega)
    have hi := incoming_add_ball_le hf hv (by omega : q - 1 + 1 ≤ q)
    omega
  have hcapH : ∀ v ∈ H, (inN D V v).card + q + 5 ≤ V.card := by
    intro v hv
    have hb := high_row_ball_three_min (by decide : 2 ≤ 2) (by omega) hf hmin
      (hHV hv) (hhigh v hv)
    have hi := incoming_add_ball_le hf (hHV hv) (by omega : 3 + 1 ≤ q)
    omega
  have hloH := Finset.sum_le_sum hhigh
  have hloL := Finset.sum_le_sum
    (fun v hv => hmin v (Finset.mem_sdiff.mp hv).1) (s := V \ H)
  have hupH := Finset.sum_le_sum hcapH
  have hupL := Finset.sum_le_sum
    (fun v hv => hcap v (Finset.mem_sdiff.mp hv).1) (s := V \ H)
  simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at hloH hloL hupH hupL
  have ho := Finset.sum_sdiff hHV (f := fun v => (outN D V v).card)
  have hi := Finset.sum_sdiff hHV (f := fun v => (inN D V v).card)
  have he : (∑ v ∈ V, (outN D V v).card) = ∑ v ∈ V, (inN D V v).card :=
    Compose.ThinRigid.sum_out_eq_sum_in D V
  have hc := Finset.card_sdiff_add_card_eq_card hHV
  nlinarith

end LeanCH.BR.BRsGen
