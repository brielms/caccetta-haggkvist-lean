import LeanCH.BR.BRTwoBallEquality
import LeanCH.BR.BRSecondBallRegular
import LeanCH.BR.BRForcedOutSaturation
import LeanCH.BR.BRFiveCutoff

/-! Checked structure of every (5,5) boundary graph. The closure is in BR55.lean. -/

namespace LeanCH.BR.BR55
open BRq2 BRq3 BR45 BRsGen BRsub Compose.Boundary

theorem boundary_balls {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V 5) (hmin : ∀ v ∈ V, 5 ≤ (outN D V v).card)
    (hV : V.card = 26) : ∀ v ∈ V,
    (ball D V v 2).card = 11 ∧ (ball D V v 3).card = 16 ∧
    (reverseBall D V v 2).card = 11 ∧ (reverseBall D V v 3).card = 16 := by
  have htwo := fun v hv => card_ball_two_ge_twice (by decide : 2 ≤ 5) hf hmin (u := v) hv
  have hthree := fun v hv => card_ball_three_ge_sixteen hf hmin (u := v) hv
  have h23 := two_balls_boundary_cards hf (by decide : 2 + 3 ≤ 5)
    htwo hthree (by omega : 11 + 16 = V.card + 1)
  have h32 := two_balls_boundary_cards hf (by decide : 3 + 2 ≤ 5)
    hthree htwo (by omega : 16 + 11 = V.card + 1)
  intro v hv
  exact ⟨(h23 v hv).1, (h23 v hv).2.1, (h32 v hv).2.2, (h23 v hv).2.2⟩

theorem boundary_complements {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V 5) (hmin : ∀ v ∈ V, 5 ≤ (outN D V v).card)
    (hV : V.card = 26) : ∀ v ∈ V,
    reverseBall D V v 2 = (V \ ball D V v 3) ∪ {v} ∧
    reverseBall D V v 3 = (V \ ball D V v 2) ∪ {v} := by
  have htwo := fun v hv => card_ball_two_ge_twice (by decide : 2 ≤ 5) hf hmin (u := v) hv
  have hthree := fun v hv => card_ball_three_ge_sixteen hf hmin (u := v) hv
  intro v hv
  exact ⟨two_balls_boundary_complement hf (by decide : 3 + 2 ≤ 5)
      hthree htwo (by omega : 16 + 11 = V.card + 1) hv,
    two_balls_boundary_complement hf (by decide : 2 + 3 ≤ 5)
      htwo hthree (by omega : 11 + 16 = V.card + 1) hv⟩

theorem boundary_out_regular {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V 5) (hmin : ∀ v ∈ V, 5 ≤ (outN D V v).card)
    (hV : V.card = 26) : OutEq 5 D V :=
  out_regular_of_second_ball_cap (by decide) hf hmin
    (fun v hv => ((boundary_balls hf hmin hV v hv).1).le)

theorem boundary_saturated {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V 5) (hmin : ∀ v ∈ V, 5 ≤ (outN D V v).card)
    (hV : V.card = 26) : BRsub.Sat 5 D V :=
  sat_of_forced_out_regular (fun _ he hm => boundary_out_regular he hm hV) hf hmin

theorem boundary_reachable {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V 5) (hmin : ∀ v ∈ V, 5 ≤ (outN D V v).card)
    (hV : V.card = 26) : ∀ u ∈ V, ∀ v ∈ V, ∃ m, Walk D V u v m := by
  classical
  intro u hu v hv
  let R := V.filter (fun x => ∃ m, Walk D V u x m)
  have hRV : R ⊆ V := Finset.filter_subset _ _
  have huR : u ∈ R := Finset.mem_filter.mpr ⟨hu, 0, .refl u⟩
  have hclosed : ∀ x ∈ R, outN D V x ⊆ outN D R x := by
    intro x hx y hy
    obtain ⟨m, wm⟩ := (Finset.mem_filter.mp hx).2
    exact mem_outN.mpr ⟨Finset.mem_filter.mpr ⟨(mem_outN.mp hy).1,
      m + 1, wm.snoc (mem_outN.mp hy).1 (mem_outN.mp hy).2⟩, (mem_outN.mp hy).2⟩
  have hminR : ∀ x ∈ R, 5 ≤ (outN D R x).card :=
    fun x hx => (hmin x (hRV hx)).trans (Finset.card_le_card (hclosed x hx))
  have hsize := card_ge_twenty_six (hf.mono_set hRV) hminR ⟨u, huR⟩
  have hEq : R = V := Finset.eq_of_subset_of_card_le hRV (by omega)
  exact (Finset.mem_filter.mp (show v ∈ R from hEq.symm ▸ hv)).2

/-- The equality balls forbid every arc from the second layer back to the first. -/
theorem boundary_second_no_first {D : CH.Digraph} {V : Finset ℕ} {u : ℕ}
    (hf : QFree D V 5) (hmin : ∀ v ∈ V, 5 ≤ (outN D V v).card)
    (hV : V.card = 26) (hu : u ∈ V) :
    ∀ y ∈ ball D V u 2 \ ball D V u 1, ∀ a ∈ outN D V u, ¬ D y a = true := by
  classical
  let X := outN D V u
  let Y := ball D V u 2 \ ball D V u 1
  let Z := ball D V u 3 \ ball D V u 2
  have ho := boundary_out_regular hf hmin hV
  have hb := boundary_balls hf hmin hV
  have hXc : X.card = 5 := ho u hu
  have h1 : (ball D V u 1).card = 6 := by
    rw [card_B1 (hf.mono_bound (by decide)) hu, ho u hu]
  have hYc : Y.card = 5 := by
    have hc := Finset.card_sdiff_add_card_eq_card
      (ball_mono_radius (D := D) (W := V) (u := u) (by decide : 1 ≤ 2))
    have hh := (hb u hu).1
    change Y.card + _ = _ at hc
    omega
  have hZc : Z.card = 5 := by
    have hc := Finset.card_sdiff_add_card_eq_card
      (ball_mono_radius (D := D) (W := V) (u := u) (by decide : 2 ≤ 3))
    have hh := hb u hu
    change Z.card + _ = _ at hc
    omega
  have hXV : X ⊆ V := outN_subset
  have hX1 : X ⊆ ball D V u 1 := fun _ hx => (mem_ball_one hu).mpr (Or.inr hx)
  obtain ⟨x, hx, hsink⟩ := exists_sink (hf.mono_set hXV)
    (Finset.card_pos.mp (by omega : 0 < X.card)) (by omega : X.card ≤ 5)
  have hfull : ∀ y ∈ Y, D x y = true :=
    sink_all_s (by decide : 2 ≤ 5) hf ho hu hYc hx hsink
  have hB : Y ∪ Z ⊆ ball D V x 2 := by
    intro z hz
    rcases Finset.mem_union.mp hz with hy | hz
    · exact ball_mono_radius (by decide : 1 ≤ 2)
        (ball_of_adj (ball_subset (Finset.mem_sdiff.mp hy).1) (hfull z hy))
    · obtain ⟨y, hy2, hyz⟩ := ball_succ_pred hu
        (Finset.mem_sdiff.mp hz).1 (Finset.mem_sdiff.mp hz).2
      have hy : y ∈ Y := Finset.mem_sdiff.mpr ⟨hy2, by
        intro hy1
        exact (Finset.mem_sdiff.mp hz).2
          (ball_step hy1 (ball_subset (Finset.mem_sdiff.mp hz).1) hyz)⟩
      exact mem_ball.mpr ⟨ball_subset (Finset.mem_sdiff.mp hz).1, 2, le_rfl,
        .step (ball_subset hy2) (hfull y hy)
          (.step (ball_subset (Finset.mem_sdiff.mp hz).1) hyz (.refl z))⟩
  have hnotY : ∀ a ∈ X, a ∉ Y := fun _ ha hy => (Finset.mem_sdiff.mp hy).2 (hX1 ha)
  have hnotZ : ∀ a ∈ X, a ∉ Z := fun _ ha hz => (Finset.mem_sdiff.mp hz).2
    (ball_mono_radius (by decide : 1 ≤ 2) (hX1 ha))
  have hdis : Disjoint Y Z := Finset.disjoint_left.mpr
    (fun _ hy hz => (Finset.mem_sdiff.mp hz).2 (Finset.mem_sdiff.mp hy).1)
  have hc : (insert x (Y ∪ Z)).card = 11 := by
    rw [Finset.card_insert_of_notMem (by
      intro hxU
      exact (Finset.mem_union.mp hxU).elim (hnotY x hx) (hnotZ x hx)),
      Finset.card_union_of_disjoint hdis, hYc, hZc]
  have heq : insert x (Y ∪ Z) = ball D V x 2 :=
    Finset.eq_of_subset_of_card_le (Finset.insert_subset (self_mem_ball (hXV hx)) hB)
      (by rw [hc, (hb x (hXV hx)).1])
  intro y hy a ha hya
  have hab : a ∈ ball D V x 2 := mem_ball.mpr ⟨hXV ha, 2, le_rfl,
    .step (ball_subset (Finset.mem_sdiff.mp hy).1) (hfull y hy)
      (.step (hXV ha) hya (.refl a))⟩
  rw [← heq] at hab
  rcases Finset.mem_insert.mp hab with hax | haU
  · exact digonfree hf (by decide) (hXV hx) (ball_subset (Finset.mem_sdiff.mp hy).1)
      (hfull y hy) (hax ▸ hya)
  · exact (Finset.mem_union.mp haU).elim (hnotY a ha) (hnotZ a ha)

theorem boundary_fourth_ge_three {D : CH.Digraph} {V : Finset ℕ} {u : ℕ}
    (hf : QFree D V 5) (hmin : ∀ v ∈ V, 5 ≤ (outN D V v).card)
    (hV : V.card = 26) (hu : u ∈ V) :
    3 ≤ (ball D V u 4 \ ball D V u 3).card := by
  by_contra hn
  let U := (ball D V u 3).erase u
  have hUV : U ⊆ V := (Finset.erase_subset _ _).trans ball_subset
  have hc : U.card = 15 := by
    have he := Finset.card_erase_of_mem (self_mem_ball (D := D) (k := 3) hu)
    have hb := (boundary_balls hf hmin hV u hu).2.1
    change U.card = _ at he
    omega
  have hm : ∀ v ∈ U, 3 ≤ (outN D U v).card :=
    minOut_prefix_erase hf hu (by decide : 3 + 1 ≤ 5) hmin
      (by change 3 + (ball D V u 4 \ ball D V u 3).card ≤ 5; omega)
  have hs := dt_size (by decide : 1 ≤ 5) (BRq3.ball_all 5 (by decide))
    (hf.mono_set hUV) hm (Finset.card_pos.mp (by omega : 0 < U.card))
  omega

/-- Proven context for the remaining (5,5) incoming-regularity problem. -/
structure BoundaryProfile (D : CH.Digraph) (V : Finset ℕ) : Prop where
  out_regular : OutEq 5 D V
  saturated : BRsub.Sat 5 D V
  reachable : ∀ u ∈ V, ∀ v ∈ V, ∃ m, Walk D V u v m
  balls : ∀ v ∈ V,
    (ball D V v 2).card = 11 ∧ (ball D V v 3).card = 16 ∧
    (reverseBall D V v 2).card = 11 ∧ (reverseBall D V v 3).card = 16
  complements : ∀ v ∈ V,
    reverseBall D V v 2 = (V \ ball D V v 3) ∪ {v} ∧
    reverseBall D V v 3 = (V \ ball D V v 2) ∪ {v}
  second_no_first : ∀ u ∈ V, ∀ y ∈ ball D V u 2 \ ball D V u 1,
    ∀ a ∈ outN D V u, ¬ D y a = true
  fourth_ge_three : ∀ u ∈ V, 3 ≤ (ball D V u 4 \ ball D V u 3).card

theorem boundary_profile {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V 5) (hmin : ∀ v ∈ V, 5 ≤ (outN D V v).card)
    (hV : V.card = 26) : BoundaryProfile D V where
  out_regular := boundary_out_regular hf hmin hV
  saturated := boundary_saturated hf hmin hV
  reachable := boundary_reachable hf hmin hV
  balls := boundary_balls hf hmin hV
  complements := boundary_complements hf hmin hV
  second_no_first := fun _ hu => boundary_second_no_first hf hmin hV hu
  fourth_ge_three := fun _ hu => boundary_fourth_ge_three hf hmin hV hu

/-- The fourth-layer target, discharged by `BR55.fourth_layer_growth` in BR55.lean. -/
def FourthLayerGrowth : Prop :=
  ∀ (D : CH.Digraph) (V : Finset ℕ), QFree D V 5 → V.card = 26 →
    BoundaryProfile D V → ∀ u ∈ V, 5 ≤ (ball D V u 4 \ ball D V u 3).card

/-- This conditional reduction closes the actual BR(5,5) parameter if its open input is supplied. -/
theorem boundary_regular_of_fourth_layer (hgrowth : FourthLayerGrowth) : BoundaryRegular 5 5 := by
  apply br_of_satQ
  intro D hf hmin _
  let V := Finset.range (5 * 5 + 1)
  have hV : V.card = 26 := by simp [V]
  have hp := boundary_profile hf hmin hV
  have hcap : ∀ v ∈ V, (inN D V v).card ≤ 5 := by
    intro v hv
    have h4 := hgrowth D V hf hV hp v hv
    have h3 := (hp.balls v hv).2.1
    change (ball D V v 3).card = 16 at h3
    have h34 := Finset.card_sdiff_add_card_eq_card
      (ball_mono_radius (D := D) (W := V) (u := v) (by decide : 3 ≤ 4))
    have hi := card_inN_of_satQ (by decide : 1 ≤ 5) hf hp.saturated hv
    change (inN D V v).card + (ball D V v 4).card = V.card at hi
    omega
  have hout : (∑ v ∈ V, (outN D V v).card) = ∑ _v ∈ V, 5 :=
    Finset.sum_congr rfl hp.out_regular
  have he : (∑ v ∈ V, (outN D V v).card) = ∑ v ∈ V, (inN D V v).card :=
    Compose.ThinRigid.sum_out_eq_sum_in D V
  exact (Finset.sum_eq_sum_iff_of_le hcap).mp (he.symm.trans hout)

end LeanCH.BR.BR55
