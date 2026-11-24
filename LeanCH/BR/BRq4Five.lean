import LeanCH.BR.BRq4Step
import LeanCH.BR.BRq4Diam3
import LeanCH.BR.BRq4Ball

/-!
# Ball(q,4) route: Theorem 18, `Ball(4,4) ⇒ Ball(5,4)` (Lean 4.35.0)

Paper: `BallQ4b_attempt_subagent.md` §5 (Theorem 18). Level `k = 3`, written as `k = j + 3` with `j = 0` kept as a
hypothesis so that all radii stay in the shape `j + i`.

* `thm18_core`: `(S_3)` with `b_2 ≥ 9`, `b_1 = 5` is contradictory. Cases `|K| = 1` (CH(3) on `B_3 ∖ {u}`),
  `|K| = 2` (profile `[4,6,3,2]`), `|K| = 3` (profiles `[4,5,3,3]`, `[4,4,4,3]` with `|P| = 4` and with `|P| = 3`).
* `thm18`, `ball54` (**Theorem 18**): `Ball(5,4)` from `Ball(4,4)` and Lemma 17.
-/

set_option linter.style.longLine false

namespace LeanCH.BR.BRq4

open LeanCH.BR.BRq2 LeanCH.BR.BRq3 LeanCH.BR.BRsGen

variable {D : CH.Digraph} {W : Finset ℕ} {u j : ℕ}

theorem Zp_disj (H : Setting D W u j) (hnk : (ball D W u (j + 3) \ ball D W u (j + 2)).card ≤ j + 5) :
    ((PP D W u j : Finset ℕ) : Set ℕ).PairwiseDisjoint (Zp D W u j) := by
  intro p hp p' hp' hne
  simp only [Function.onFun]
  rw [Finset.disjoint_left]
  intro z hz hz'
  obtain ⟨hzN, hpz⟩ := mem_outN.mp hz
  obtain ⟨-, hp'z⟩ := mem_outN.mp hz'
  have hzK : z ∉ KK D W u j := fun h =>
    (Finset.mem_sdiff.mp h).2 (ball_mono_radius (by omega) (Finset.mem_sdiff.mp hzN).1)
  exact hne (disj_target H hnk (Finset.mem_coe.mp hp) (Finset.mem_coe.mp hp')
    (ball_subset (Finset.mem_sdiff.mp hzN).1) hzK hpz hp'z)

theorem outN_mono {S S' : Finset ℕ} (h : S ⊆ S') (v : ℕ) : outN D S v ⊆ outN D S' v :=
  fun b hb => mem_outN.mpr ⟨h (mem_outN.mp hb).1, (mem_outN.mp hb).2⟩

theorem out3 {U S1 S2 : Finset ℕ} {v : ℕ} (h : ∀ b ∈ W, D v b = true → b ∈ U ∨ b ∈ S1 ∨ b ∈ S2) :
    (outN D W v).card ≤ (outN D U v).card + (outN D S1 v).card + (outN D S2 v).card := by
  classical
  have hs := out_split (U := U) (S := S1 ∪ S2) (fun b hb hvb => by
    rcases h b hb hvb with h' | h' | h'
    · exact Or.inl h'
    · exact Or.inr (Finset.mem_union_left _ h')
    · exact Or.inr (Finset.mem_union_right _ h'))
  have h2 : outN D (S1 ∪ S2) v ⊆ outN D S1 v ∪ outN D S2 v := by
    intro b hb
    obtain ⟨hb1, hvb⟩ := mem_outN.mp hb
    rcases Finset.mem_union.mp hb1 with h' | h'
    · exact Finset.mem_union_left _ (mem_outN.mpr ⟨h', hvb⟩)
    · exact Finset.mem_union_right _ (mem_outN.mpr ⟨h', hvb⟩)
  have := (Finset.card_le_card h2).trans (Finset.card_union_le _ _)
  omega

theorem thm18_core (H : Setting D W u j) (hj : j = 0) (hbk1 : 4 * (j + 2) + 1 ≤ (ball D W u (j + 2)).card)
    (hb1 : (ball D W u (j + 1)).card = 4 * (j + 1) + 1) : False := by
  classical
  have e3 : (ball D W u (j + 3) \ ball D W u (j + 2)).card + (ball D W u (j + 2)).card = (ball D W u (j + 3)).card :=
    Finset.card_sdiff_add_card_eq_card (ball_mono_radius (by omega))
  have e2 : (ball D W u (j + 2) \ ball D W u (j + 1)).card + (ball D W u (j + 1)).card = (ball D W u (j + 2)).card :=
    Finset.card_sdiff_add_card_eq_card (ball_mono_radius (by omega))
  have eK : (KK D W u j).card + (ball D W u (j + 3)).card = (ball D W u (j + 4)).card :=
    Finset.card_sdiff_add_card_eq_card (ball_mono_radius (by omega))
  have hb := H.hb
  have hbk := H.hbk
  have hb3 := H.hb3
  have hK := H.hK
  have hfree := H.hfree
  have hu := H.hu
  have hU2W : (ball D W u (j + 2)).erase u ⊆ W := (Finset.erase_subset _ _).trans ball_subset
  have hU2c : ((ball D W u (j + 2)).erase u).card + 1 = (ball D W u (j + 2)).card :=
    Finset.card_erase_add_one (self_mem_ball hu)
  have hN2W : ball D W u (j + 2) \ ball D W u (j + 1) ⊆ W := fun x hx => ball_subset (Finset.mem_sdiff.mp hx).1
  have hN3W : ball D W u (j + 3) \ ball D W u (j + 2) ⊆ W := fun x hx => ball_subset (Finset.mem_sdiff.mp hx).1
  -- `|K| = 1`: CH(3) on `B_3 ∖ {u}`
  by_cases hK1 : (KK D W u j).card = 1
  · have hU3W : (ball D W u (j + 3)).erase u ⊆ W := (Finset.erase_subset _ _).trans ball_subset
    have hmin : ∀ v ∈ (ball D W u (j + 3)).erase u, 3 ≤ (outN D ((ball D W u (j + 3)).erase u) v).card := by
      intro v hv
      have hs := out_split (S := KK D W u j) (out_layer H (i := j + 3) (by omega) (Finset.mem_of_mem_erase hv))
      rw [H.hout v (hU3W hv)] at hs
      have := Finset.card_le_card (outN_subset (D := D) (W := KK D W u j) (y := v))
      omega
    have hU := ch3_set (q := j + 5) (by omega) (hfree.mono_set hU3W) hmin
      (Finset.card_pos.mp (by rw [Finset.card_erase_of_mem (self_mem_ball hu)]; omega))
    rw [Finset.card_erase_of_mem (self_mem_ball hu)] at hU
    omega
  have hnk : (ball D W u (j + 3) \ ball D W u (j + 2)).card ≤ j + 5 := by omega
  have hP := P_ge H hnk
  have hPN : (PP D W u j).card ≤ (ball D W u (j + 3) \ ball D W u (j + 2)).card := Finset.card_le_card PP_sub
  have hsum := sum_Zp H hnk
  have h1 : ∑ _p ∈ PP D W u j, 1 ≤ ∑ p ∈ PP D W u j, (Zp D W u j p).card :=
    Finset.sum_le_sum (fun p hp => (Zp_bound H hnk hp).1)
  rw [Finset.sum_const_nat (fun _ _ => rfl)] at h1
  -- `Z`: the `R2` detours, `W'`: the rest of `N_2`
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = (PP D W u j).biUnion (Zp D W u j) := ⟨_, rfl⟩
  have hZc : Z.card = ∑ p ∈ PP D W u j, (Zp D W u j p).card := by rw [hZ, Finset.card_biUnion (Zp_disj H hnk)]
  have hZN : Z ⊆ ball D W u (j + 2) \ ball D W u (j + 1) := by
    rw [hZ]; exact Finset.biUnion_subset.mpr (fun p _ => outN_subset)
  have hZin : ∀ z ∈ Z, ∃ p ∈ PP D W u j, D p z = true := by
    intro z hz
    rw [hZ] at hz
    obtain ⟨p, hp, hzp⟩ := Finset.mem_biUnion.mp hz
    exact ⟨p, hp, (mem_outN.mp hzp).2⟩
  obtain ⟨W', hW'⟩ : ∃ W', W' = (ball D W u (j + 2) \ ball D W u (j + 1)) \ Z := ⟨_, rfl⟩
  have hW'c : W'.card + Z.card = (ball D W u (j + 2) \ ball D W u (j + 1)).card := by
    rw [hW']; exact Finset.card_sdiff_add_card_eq_card hZN
  have hW'N : W' ⊆ ball D W u (j + 2) \ ball D W u (j + 1) := by rw [hW']; exact Finset.sdiff_subset
  have hW'U : W' ⊆ (ball D W u (j + 2)).erase u := by
    intro w hw
    obtain ⟨hw2, hw1⟩ := Finset.mem_sdiff.mp (hW'N hw)
    exact Finset.mem_erase.mpr ⟨by rintro rfl; exact hw1 (self_mem_ball hu), hw2⟩
  have hsplit2 : ∀ v ∈ (ball D W u (j + 2)).erase u, v ∈ ball D W u (j + 1) ∨ v ∈ Z ∨ v ∈ W' := by
    intro v hv
    by_cases hv1 : v ∈ ball D W u (j + 1)
    · exact Or.inl hv1
    · by_cases hvZ : v ∈ Z
      · exact Or.inr (Or.inl hvZ)
      · refine Or.inr (Or.inr ?_)
        rw [hW']
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_of_mem_erase hv, hv1⟩, hvZ⟩
  -- the `R2` detours have at most one arc into `P` once `|P| ≤ 3`
  have harcP : (PP D W u j).card ≤ 3 → ∀ z ∈ Z, (outN D (PP D W u j) z).card ≤ 1 := by
    intro h3 z hz
    obtain ⟨p, hp, hpz⟩ := hZin z hz
    refine Finset.card_le_one.mpr (fun w hw w' hw' => ?_)
    exact tight_arc H hnk (q := 2) (by omega) (by omega) (by omega) hp (hZN hz) hpz (mem_outN.mp hw).1
      (mem_outN.mp hw').1 (mem_outN.mp hw).2 (mem_outN.mp hw').2
  have hlow : ∀ v ∈ ball D W u (j + 1), outN D (ball D W u (j + 3) \ ball D W u (j + 2)) v = ∅ :=
    fun v hv => low_out hv
  have hlowP : ∀ v ∈ ball D W u (j + 1), outN D (PP D W u j) v = ∅ := by
    intro v hv
    exact Finset.subset_empty.mp ((outN_mono PP_sub v).trans (hlow v hv).subset)
  by_cases hK2 : (KK D W u j).card = 2
  · -- profile `[4,6,3,2]`
    have h2 : ∑ _p ∈ PP D W u j, 2 ≤ ∑ p ∈ PP D W u j, (Zp D W u j p).card :=
      Finset.sum_le_sum (fun p hp => (Zp_bound H hnk hp).2 (by omega))
    rw [Finset.sum_const_nat (fun _ _ => rfl)] at h2
    have hPeq : PP D W u j = ball D W u (j + 3) \ ball D W u (j + 2) :=
      Finset.eq_of_subset_of_card_le PP_sub (by omega)
    have hZeq : Z = ball D W u (j + 2) \ ball D W u (j + 1) := Finset.eq_of_subset_of_card_le hZN (by omega)
    have hmin : ∀ v ∈ (ball D W u (j + 2)).erase u, 3 ≤ (outN D ((ball D W u (j + 2)).erase u) v).card := by
      intro v hv
      have hs := out_split (S := ball D W u (j + 3) \ ball D W u (j + 2))
        (out_layer H (i := j + 2) (by omega) (Finset.mem_of_mem_erase hv))
      rw [H.hout v (hU2W hv)] at hs
      have : (outN D (ball D W u (j + 3) \ ball D W u (j + 2)) v).card ≤ 1 := by
        by_cases hv1 : v ∈ ball D W u (j + 1)
        · rw [hlow v hv1]; simp
        · rw [← hPeq]
          refine harcP (by omega) v ?_
          rw [hZeq]; exact Finset.mem_sdiff.mpr ⟨Finset.mem_of_mem_erase hv, hv1⟩
      omega
    have hU := ch3_set (q := j + 5) (by omega) (hfree.mono_set hU2W) hmin
      (Finset.card_pos.mp (by omega))
    omega
  have hK3 : (KK D W u j).card = 3 := by omega
  by_cases hn3 : (ball D W u (j + 3) \ ball D W u (j + 2)).card = 3
  · -- profile `[4,5,3,3]`: `P = N_3`, `|Z| ≥ 3`, `|W'| ≤ 2`
    have hPeq : PP D W u j = ball D W u (j + 3) \ ball D W u (j + 2) :=
      Finset.eq_of_subset_of_card_le PP_sub (by omega)
    have harc3 : ∀ z ∈ Z, (outN D (ball D W u (j + 3) \ ball D W u (j + 2)) z).card ≤ 1 := by
      rw [← hPeq]; exact harcP (by omega)
    by_cases hz2 : ∃ z ∈ Z, ∃ w1 ∈ W', ∃ w2 ∈ W', w1 ≠ w2 ∧ D z w1 = true ∧ D z w2 = true
    · obtain ⟨z, hz, w1, hw1, w2, hw2, hne, hzw1, hzw2⟩ := hz2
      obtain ⟨p, hp, hpz⟩ := hZin z hz
      have hW'eq : ∀ w ∈ W', w = w1 ∨ w = w2 := by
        intro w hw
        by_contra h
        push Not at h
        have hsub : ({w, w1, w2} : Finset ℕ) ⊆ W' := by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl | rfl <;> assumption
        have := Finset.card_le_card hsub
        rw [Finset.card_insert_of_notMem (by simp [h.1, h.2]), Finset.card_pair hne] at this
        omega
      have hzW : z ∈ W := hN2W (hZN hz)
      have hpW : p ∈ W := PP_W hp
      have hnp : ∀ w ∈ W', ¬ D w p = true := by
        intro w hw hwp
        have hzw : D z w = true := by rcases hW'eq w hw with rfl | rfl <;> assumption
        exact tri3 (hfree.mono_bound (by omega)) hzW (hN2W (hW'N hw)) hpW hzw hwp hpz
      have hmin : ∀ v ∈ (ball D W u (j + 2)).erase u, 2 ≤ (outN D ((ball D W u (j + 2)).erase u) v).card := by
        intro v hv
        have hs := out_split (S := ball D W u (j + 3) \ ball D W u (j + 2))
          (out_layer H (i := j + 2) (by omega) (Finset.mem_of_mem_erase hv))
        rw [H.hout v (hU2W hv)] at hs
        have : (outN D (ball D W u (j + 3) \ ball D W u (j + 2)) v).card ≤ 2 := by
          rcases hsplit2 v hv with hv1 | hvZ | hvW
          · rw [hlow v hv1]; simp
          · have := harc3 v hvZ; omega
          · have hsub : outN D (ball D W u (j + 3) \ ball D W u (j + 2)) v ⊆
                (ball D W u (j + 3) \ ball D W u (j + 2)).erase p := by
              intro b hb
              obtain ⟨hbN, hvb⟩ := mem_outN.mp hb
              exact Finset.mem_erase.mpr ⟨by rintro rfl; exact hnp v hvW hvb, hbN⟩
            have := Finset.card_le_card hsub
            rw [Finset.card_erase_of_mem (PP_sub hp)] at this
            omega
        omega
      have hU := ch2_set (q := j + 5) (by omega) (hfree.mono_set hU2W) hmin (Finset.card_pos.mp (by omega))
      omega
    · push Not at hz2
      have hW'1 : ∀ z ∈ Z, (outN D W' z).card ≤ 1 := by
        intro z hz
        refine Finset.card_le_one.mpr (fun a ha b hb => ?_)
        by_contra hab
        exact hz2 z hz a (mem_outN.mp ha).1 b (mem_outN.mp hb).1 hab (mem_outN.mp ha).2 (mem_outN.mp hb).2
      have hU0W : (ball D W u (j + 2)).erase u \ W' ⊆ W := Finset.sdiff_subset.trans hU2W
      have hU0c : ((ball D W u (j + 2)).erase u \ W').card + W'.card = ((ball D W u (j + 2)).erase u).card :=
        Finset.card_sdiff_add_card_eq_card hW'U
      have hmin : ∀ v ∈ (ball D W u (j + 2)).erase u \ W', 2 ≤ (outN D ((ball D W u (j + 2)).erase u \ W') v).card := by
        intro v hv
        obtain ⟨hvU, hvW'⟩ := Finset.mem_sdiff.mp hv
        have hs := out3 (U := (ball D W u (j + 2)).erase u \ W') (S1 := W')
          (S2 := ball D W u (j + 3) \ ball D W u (j + 2)) (v := v) (fun b hb hvb => by
            rcases out_layer H (i := j + 2) (by omega) (Finset.mem_of_mem_erase hvU) b hb hvb with h | h
            · by_cases hbW' : b ∈ W'
              · exact Or.inr (Or.inl hbW')
              · exact Or.inl (Finset.mem_sdiff.mpr ⟨h, hbW'⟩)
            · exact Or.inr (Or.inr h))
        rw [H.hout v (hU2W hvU)] at hs
        have hW'v := Finset.card_le_card (outN_subset (D := D) (W := W') (y := v))
        rcases hsplit2 v hvU with hv1 | hvZ | hvW
        · rw [hlow v hv1] at hs; simp at hs; omega
        · have := harc3 v hvZ; have := hW'1 v hvZ; omega
        · exact absurd hvW hvW'
      have hU := ch2_set (q := j + 5) (by omega) (hfree.mono_set hU0W) hmin (Finset.card_pos.mp (by omega))
      omega
  -- profile `[4,4,4,3]`
  have hn34 : (ball D W u (j + 3) \ ball D W u (j + 2)).card = 4 := by omega
  by_cases hP4 : (PP D W u j).card = 4
  · have hPeq : PP D W u j = ball D W u (j + 3) \ ball D W u (j + 2) :=
      Finset.eq_of_subset_of_card_le PP_sub (by omega)
    have hZeq : Z = ball D W u (j + 2) \ ball D W u (j + 1) := Finset.eq_of_subset_of_card_le hZN (by omega)
    by_cases h3 : ∃ z ∈ ball D W u (j + 2) \ ball D W u (j + 1), 3 ≤ (outN D (ball D W u (j + 3) \ ball D W u (j + 2)) z).card
    · obtain ⟨z, hz, hz3⟩ := h3
      obtain ⟨p, hp, hpz⟩ := hZin z (by rw [hZeq]; exact hz)
      have hzW : z ∈ W := hN2W hz
      have hpW : p ∈ W := PP_W hp
      have hnzp : ¬ D z p = true := fun h => digonfree hfree (by omega) hpW hzW hpz h
      have hsub : outN D (ball D W u (j + 3) \ ball D W u (j + 2)) z ⊆ (ball D W u (j + 3) \ ball D W u (j + 2)).erase p := by
        intro b hb
        obtain ⟨hbN, hzb⟩ := mem_outN.mp hb
        exact Finset.mem_erase.mpr ⟨by rintro rfl; exact hnzp hzb, hbN⟩
      have heq := Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_erase_of_mem (PP_sub hp)]; omega)
      obtain ⟨hp3, hp2, -⟩ := mem_PP.mp hp
      obtain ⟨a, ha2, ha1, hap⟩ := exists_Ap (j := j) hu hp3 hp2
      obtain ⟨p', hp', hp'a⟩ := hZin a (by rw [hZeq]; exact Finset.mem_sdiff.mpr ⟨ha2, ha1⟩)
      have haW : a ∈ W := ball_subset ha2
      have hp'W : p' ∈ W := PP_W hp'
      by_cases hpp : p' = p
      · subst hpp
        exact digonfree hfree (by omega) hp'W haW hp'a hap
      · have hzp' : D z p' = true := by
          have : p' ∈ outN D (ball D W u (j + 3) \ ball D W u (j + 2)) z := by
            rw [heq]; exact Finset.mem_erase.mpr ⟨hpp, PP_sub hp'⟩
          exact (mem_outN.mp this).2
        exact hfree p 4 (by omega) (by omega)
          (.step hzW hpz (.step hp'W hzp' (.step haW hp'a (.step hpW hap (.refl p)))))
    · push Not at h3
      have hmin : ∀ v ∈ (ball D W u (j + 2)).erase u, 2 ≤ (outN D ((ball D W u (j + 2)).erase u) v).card := by
        intro v hv
        have hs := out_split (S := ball D W u (j + 3) \ ball D W u (j + 2))
          (out_layer H (i := j + 2) (by omega) (Finset.mem_of_mem_erase hv))
        rw [H.hout v (hU2W hv)] at hs
        have : (outN D (ball D W u (j + 3) \ ball D W u (j + 2)) v).card ≤ 2 := by
          by_cases hv1 : v ∈ ball D W u (j + 1)
          · rw [hlow v hv1]; simp
          · have := h3 v (Finset.mem_sdiff.mpr ⟨Finset.mem_of_mem_erase hv, hv1⟩); omega
        omega
      have hU := ch2_set (q := j + 5) (by omega) (hfree.mono_set hU2W) hmin (Finset.card_pos.mp (by omega))
      omega
  · -- `|P| = 3`: one more vertex `q0 ∈ N_3 ∖ P`
    have hP3 : (PP D W u j).card = 3 := by omega
    have hq : ((ball D W u (j + 3) \ ball D W u (j + 2)) \ PP D W u j).card = 1 := by
      rw [Finset.card_sdiff_of_subset PP_sub]; omega
    obtain ⟨q0, hq0⟩ := Finset.card_eq_one.mp hq
    have hq0N : q0 ∈ ball D W u (j + 3) \ ball D W u (j + 2) :=
      (Finset.mem_sdiff.mp (hq0 ▸ Finset.mem_singleton_self q0 : q0 ∈ (ball D W u (j + 3) \ ball D W u (j + 2)) \ PP D W u j)).1
    have hq0P : q0 ∉ PP D W u j :=
      (Finset.mem_sdiff.mp (hq0 ▸ Finset.mem_singleton_self q0 : q0 ∈ (ball D W u (j + 3) \ ball D W u (j + 2)) \ PP D W u j)).2
    have hN3 : ∀ b ∈ ball D W u (j + 3) \ ball D W u (j + 2), b ∈ PP D W u j ∨ b = q0 := by
      intro b hb
      by_cases hbP : b ∈ PP D W u j
      · exact Or.inl hbP
      · have : b ∈ (ball D W u (j + 3) \ ball D W u (j + 2)) \ PP D W u j := Finset.mem_sdiff.mpr ⟨hb, hbP⟩
        rw [hq0] at this
        exact Or.inr (Finset.mem_singleton.mp this)
    obtain ⟨hq03, hq02⟩ := Finset.mem_sdiff.mp hq0N
    have hq0W : q0 ∈ W := ball_subset hq03
    have hq0K : ¬ ∃ c ∈ KK D W u j, D q0 c = true := fun h => hq0P (mem_PP.mpr ⟨hq03, hq02, h⟩)
    have hq0in : ∀ p ∈ PP D W u j, ¬ D q0 p = true :=
      fun p hp => no_inP H hnk hp q0 (ball_mono_radius (by omega) hq03) hq02
    have hq0out : ∀ b ∈ W, D q0 b = true → b ∈ (ball D W u (j + 2)).erase u := by
      intro b hb hq0b
      rcases out_layer H (i := j + 3) (by omega) hq03 b hb hq0b with h | h
      · obtain ⟨hbu, hb3⟩ := Finset.mem_erase.mp h
        by_cases hb2 : b ∈ ball D W u (j + 2)
        · exact Finset.mem_erase.mpr ⟨hbu, hb2⟩
        · rcases hN3 b (Finset.mem_sdiff.mpr ⟨hb3, hb2⟩) with hbP | rfl
          · exact absurd hq0b (hq0in b hbP)
          · exact absurd hq0b (loopfree hfree (by omega) hq0W)
      · exact absurd ⟨b, h, hq0b⟩ hq0K
    have hq0U : q0 ∉ (ball D W u (j + 2)).erase u := fun h => hq02 (Finset.mem_of_mem_erase h)
    have hUpW : insert q0 ((ball D W u (j + 2)).erase u) ⊆ W := Finset.insert_subset hq0W hU2W
    have hUpc : (insert q0 ((ball D W u (j + 2)).erase u)).card = ((ball D W u (j + 2)).erase u).card + 1 :=
      Finset.card_insert_of_notMem hq0U
    have hUout : ∀ v ∈ insert q0 ((ball D W u (j + 2)).erase u), ∀ b ∈ W, D v b = true →
        b ∈ insert q0 ((ball D W u (j + 2)).erase u) ∨ b ∈ PP D W u j := by
      intro v hv b hb hvb
      rcases Finset.mem_insert.mp hv with rfl | hv
      · exact Or.inl (Finset.mem_insert_of_mem (hq0out b hb hvb))
      · rcases out_layer H (i := j + 2) (by omega) (Finset.mem_of_mem_erase hv) b hb hvb with h | h
        · exact Or.inl (Finset.mem_insert_of_mem h)
        · rcases hN3 b h with h' | rfl
          · exact Or.inr h'
          · exact Or.inl (Finset.mem_insert_self _ _)
    have hPlow : ∀ v ∈ insert q0 ((ball D W u (j + 2)).erase u), v ∉ W' → (outN D (PP D W u j) v).card ≤ 1 := by
      intro v hv hvW'
      rcases Finset.mem_insert.mp hv with rfl | hv
      · have : outN D (PP D W u j) v = ∅ :=
          Finset.eq_empty_iff_forall_notMem.mpr (fun b hb => hq0in b (mem_outN.mp hb).1 (mem_outN.mp hb).2)
        rw [this]; simp
      · rcases hsplit2 v hv with hv1 | hvZ | hvW
        · rw [hlowP v hv1]; simp
        · exact harcP (by omega) v hvZ
        · exact absurd hvW hvW'
    by_cases hw3 : ∃ w ∈ W', 3 ≤ (outN D (PP D W u j) w).card
    · obtain ⟨w, hw, hw3⟩ := hw3
      have hwall : ∀ p ∈ PP D W u j, D w p = true := by
        have heq := Finset.eq_of_subset_of_card_le (outN_subset (D := D) (W := PP D W u j) (y := w)) (by omega)
        intro p hp
        have : p ∈ outN D (PP D W u j) w := by rw [heq]; exact hp
        exact (mem_outN.mp this).2
      have hW'eq : ∀ w' ∈ W', w' = w := by
        intro w' hw'
        have : W'.card ≤ 1 := by omega
        exact Finset.card_le_one.mp this w' hw' w hw
      have hwU : w ∈ insert q0 ((ball D W u (j + 2)).erase u) := Finset.mem_insert_of_mem (hW'U hw)
      have hUmW : (insert q0 ((ball D W u (j + 2)).erase u)).erase w ⊆ W := (Finset.erase_subset _ _).trans hUpW
      have hmin : ∀ v ∈ (insert q0 ((ball D W u (j + 2)).erase u)).erase w,
          3 ≤ (outN D ((insert q0 ((ball D W u (j + 2)).erase u)).erase w) v).card := by
        intro v hv
        obtain ⟨hvw, hvU⟩ := Finset.mem_erase.mp hv
        have hs := out3 (U := (insert q0 ((ball D W u (j + 2)).erase u)).erase w) (S1 := {w})
          (S2 := PP D W u j) (v := v) (fun b hb hvb => by
            rcases hUout v hvU b hb hvb with h | h
            · by_cases hbw : b = w
              · exact Or.inr (Or.inl (Finset.mem_singleton.mpr hbw))
              · exact Or.inl (Finset.mem_erase.mpr ⟨hbw, h⟩)
            · exact Or.inr (Or.inr h))
        rw [H.hout v (hUpW hvU)] at hs
        have hvW' : v ∉ W' := fun h => hvw (hW'eq v h)
        have hw1 : (outN D {w} v).card ≤ 1 := (Finset.card_le_card outN_subset).trans (by simp)
        have : (outN D {w} v).card + (outN D (PP D W u j) v).card ≤ 1 := by
          rcases Finset.mem_insert.mp hvU with rfl | hvU'
          · have : outN D (PP D W u j) v = ∅ :=
              Finset.eq_empty_iff_forall_notMem.mpr (fun b hb => hq0in b (mem_outN.mp hb).1 (mem_outN.mp hb).2)
            rw [this]; simp; exact hw1
          · rcases hsplit2 v hvU' with hv1 | hvZ | hvW
            · rw [hlowP v hv1]; simp; exact hw1
            · obtain ⟨p, hp, hpv⟩ := hZin v hvZ
              have hnvw : ¬ D v w = true := fun h =>
                tri3 (hfree.mono_bound (by omega)) (hN2W (hW'N hw)) (PP_W hp) (hN2W (hZN hvZ)) (hwall p hp) hpv h
              have : outN D {w} v = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (fun b hb => by
                obtain ⟨hb1, hvb⟩ := mem_outN.mp hb
                rw [Finset.mem_singleton.mp hb1] at hvb
                exact hnvw hvb)
              rw [this]; simp; exact harcP (by omega) v hvZ
            · exact absurd hvW hvW'
        omega
      have hUmc := Finset.card_erase_of_mem hwU
      have hU := ch3_set (q := j + 5) (by omega) (hfree.mono_set hUmW) hmin (Finset.card_pos.mp (by omega))
      omega
    · push Not at hw3
      have hmin : ∀ v ∈ insert q0 ((ball D W u (j + 2)).erase u),
          2 ≤ (outN D (insert q0 ((ball D W u (j + 2)).erase u)) v).card := by
        intro v hv
        have hs := out_split (U := insert q0 ((ball D W u (j + 2)).erase u)) (S := PP D W u j) (hUout v hv)
        rw [H.hout v (hUpW hv)] at hs
        have : (outN D (PP D W u j) v).card ≤ 2 := by
          by_cases hvW : v ∈ W'
          · have := hw3 v hvW; omega
          · have := hPlow v hv hvW; omega
        omega
      have hU := ch2_set (q := j + 5) (by omega) (hfree.mono_set hUpW) hmin (Finset.card_pos.mp (by omega))
      omega

/-- **Theorem 18** at level `k = j + 3` with `j = 0`. -/
theorem thm18 (hj : j = 0) (hS : BallSmall (j + 3) 4) (hb4 : Ball (j + 4) 4) : Ball (j + 5) 4 := by
  intro D W hfree hout u hu
  rw [show j + 5 - 1 = j + 4 by omega]
  by_contra hlt
  have hb1 : (ball D W u (j + 1)).card = 4 * (j + 1) + 1 := by
    subst hj; exact card_ball_one_four (hfree.mono_bound (by omega)) hout hu
  have hbk1 : 4 * (j + 2) + 1 ≤ (ball D W u (j + 2)).card := by
    subst hj
    have h2 := n2_ge_four (hfree.mono_bound (by omega)) hout hu
    have h1 := card_ball_one_four (hfree.mono_bound (by omega)) hout hu
    have e := Finset.card_sdiff_add_card_eq_card (ball_mono_radius (D := D) (W := W) (u := u) (by omega : 1 ≤ 2))
    have h9 : 9 ≤ (ball D W u 2).card := by unfold lay2 at h2; omega
    exact h9
  have h6 := thm6 hS hb4 hfree hout hu hbk1
  have hbk := bk_of_ball hb4 hfree hout hu
  have hb3 : (ball D W u (j + 3)).card ≤ 4 * (j + 3) + 3 := by
    by_contra h
    exact closed_case hb4 hfree hout hu (by omega) (by omega)
  exact thm18_core ⟨hS, hfree, hout, hu, by omega, hbk, hb3⟩ hj hbk1 hb1

/-- **Theorem 18.** `Ball(5,4)`. -/
theorem ball54 : Ball 5 4 := thm18 (j := 0) rfl lemma17 ball44

end LeanCH.BR.BRq4
