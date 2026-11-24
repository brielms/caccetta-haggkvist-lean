import LeanCH.BR.BRq4Fold

/-!
# Ball(q,4) route: Lemma 17, no bad root on at most 13 vertices (Lean 4.35.0)

Paper: `BallQ4b_attempt_subagent.md` §4 (Lemma 17). Every 3-free out-4 digraph on `≤ 13` vertices has
`|B_2(y)| ≥ 9` at every vertex, i.e. `BallSmall 3 4` (the paper's `(Diam_3)`).

* `bad_root`: the configuration `O(v) ⊇ Y := N_2(y)` for every `v ∈ N_1(y)`, `|Y| = 3`, is impossible on `≤ 13`
  vertices. Case `R' = R` by CH(3) on `Y ∪ R`; case `R' ≠ R` by showing that at most one vertex of `R'` has an arc
  into `Y`, and then a sink argument on the other three.
* `lemma17 : BallSmall 3 4`.
-/

set_option linter.style.longLine false

namespace LeanCH.BR.BRq4

open LeanCH.BR.BRq2 LeanCH.BR.BRq3 LeanCH.BR.BRsGen

variable {D : CH.Digraph} {W : Finset ℕ}

theorem tri3 (hfree : QFree D W 3) {a b c : ℕ} (ha : a ∈ W) (hb : b ∈ W) (hc : c ∈ W) (hab : D a b = true)
    (hbc : D b c = true) (hca : D c a = true) : False :=
  hfree a 3 (by omega) le_rfl (.step hb hab (.step hc hbc (.step ha hca (.refl a))))

theorem ball_one_eq {y : ℕ} (hy : y ∈ W) : ball D W y 1 = insert y (outN D W y) := by
  ext v; rw [mem_ball_one hy, Finset.mem_insert]

theorem bad_root (hfree : QFree D W 3) (hout : OutEq 4 D W) (hcard : W.card ≤ 13) {y : ℕ} (hy : y ∈ W)
    (hY3 : (ball D W y 2 \ ball D W y 1).card = 3)
    (hbad : ∀ v ∈ outN D W y, ∀ w ∈ ball D W y 2 \ ball D W y 1, D v w = true) : False := by
  classical
  set V := outN D W y with hVdef
  set Y := ball D W y 2 \ ball D W y 1 with hYdef
  set R := W \ ball D W y 2 with hRdef
  have hV4 : V.card = 4 := hout y hy
  have hyV : y ∉ V := fun h => loopfree hfree (by omega) hy (mem_outN.mp h).2
  have hb1 : (ball D W y 1).card = 5 := by rw [ball_one_eq hy, Finset.card_insert_of_notMem hyV, hV4]
  have hb2 : (ball D W y 2).card = 8 := by
    have : Y.card + (ball D W y 1).card = (ball D W y 2).card :=
      Finset.card_sdiff_add_card_eq_card (ball_mono_radius (by omega))
    omega
  have hRc : R.card ≤ 5 := by
    rw [hRdef, Finset.card_sdiff_of_subset ball_subset]; omega
  have hVW : V ⊆ W := outN_subset
  have hYW : Y ⊆ W := fun x hx => ball_subset (Finset.mem_sdiff.mp hx).1
  have hRW : R ⊆ W := Finset.sdiff_subset
  have hsplit : ∀ b ∈ W, b = y ∨ b ∈ V ∨ b ∈ Y ∨ b ∈ R := by
    intro b hb
    by_cases h2 : b ∈ ball D W y 2
    · by_cases h1 : b ∈ ball D W y 1
      · rcases (mem_ball_one hy).mp h1 with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl (Finset.mem_sdiff.mpr ⟨h2, h1⟩)))
    · exact Or.inr (Or.inr (Or.inr (Finset.mem_sdiff.mpr ⟨hb, h2⟩)))
  obtain ⟨v1, hv1⟩ : V.Nonempty := by rw [← Finset.card_pos]; omega
  have hyv1 : D y v1 = true := (mem_outN.mp hv1).2
  -- (F1): `O(w) ⊆ Y ∪ R` for `w ∈ Y`
  have F1 : ∀ w ∈ Y, ∀ b ∈ W, D w b = true → b ∈ Y ∨ b ∈ R := by
    intro w hw b hb hwb
    rcases hsplit b hb with rfl | hbV | hbY | hbR
    · exact absurd hwb (fun h => tri3 hfree hb (hVW hv1) (hYW hw) hyv1 (hbad v1 hv1 w hw) h)
    · exact absurd hwb (fun h => digonfree hfree (by omega) (hYW hw) (hVW hbV) h (hbad b hbV w hw))
    · exact Or.inl hbY
    · exact Or.inr hbR
  -- (F2): a sink `w3` of `D[Y]`
  obtain ⟨w3, hw3, hsink3⟩ := exists_sink (hfree.mono_set hYW) (Finset.card_pos.mp (by omega)) (by omega)
  set R' := R.filter (fun r => ∃ w ∈ Y, D w r = true) with hR'def
  have hw3R : outN D W w3 ⊆ R' := by
    intro b hb
    obtain ⟨hbW, hwb⟩ := mem_outN.mp hb
    rcases F1 w3 hw3 b hbW hwb with hbY | hbR
    · exact absurd hwb (hsink3 b hbY)
    · exact Finset.mem_filter.mpr ⟨hbR, w3, hw3, hwb⟩
  have hR'4 : 4 ≤ R'.card := by
    have := Finset.card_le_card hw3R
    rwa [hout w3 (hYW hw3)] at this
  have hR'R : R' ⊆ R := Finset.filter_subset _ _
  -- (F3): `r ∈ R'` has no arc into `V`
  have F3 : ∀ r ∈ R', ∀ v ∈ V, ¬ D r v = true := by
    intro r hr v hv hrv
    obtain ⟨hrR, w, hw, hwr⟩ := Finset.mem_filter.mp hr
    exact tri3 hfree (hRW hrR) (hVW hv) (hYW hw) hrv (hbad v hv w hw) hwr
  by_cases hRR : R ⊆ R'
  · -- Case `R' = R`: CH(3) on `T = Y ∪ R`
    have hTW : Y ∪ R ⊆ W := Finset.union_subset hYW hRW
    have hmin : ∀ t ∈ Y ∪ R, 3 ≤ (outN D (Y ∪ R) t).card := by
      intro t ht
      have hs := out_split (U := Y ∪ R) (S := {y}) (v := t) (fun b hb htb => by
        rcases Finset.mem_union.mp ht with htY | htR
        · rcases F1 t htY b hb htb with h | h
          · exact Or.inl (Finset.mem_union_left _ h)
          · exact Or.inl (Finset.mem_union_right _ h)
        · rcases hsplit b hb with rfl | hbV | hbY | hbR
          · exact Or.inr (Finset.mem_singleton_self _)
          · exact absurd htb (F3 t (hRR htR) b hbV)
          · exact Or.inl (Finset.mem_union_left _ hbY)
          · exact Or.inl (Finset.mem_union_right _ hbR))
      have h1 : (outN D {y} t).card ≤ 1 := (Finset.card_le_card outN_subset).trans (by simp)
      rw [hout t (hTW ht)] at hs
      omega
    have := ch3_set (q := 3) (by omega) (hfree.mono_set hTW) hmin
      ⟨w3, Finset.mem_union_left _ hw3⟩
    have := Finset.card_union_le Y R
    omega
  · -- Case `R' ≠ R`
    have hlt : R'.card < R.card := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hR'R, fun h => hRR (h ▸ subset_rfl)⟩)
    have hR'c : R'.card = 4 := by omega
    have hRm : (R \ R').card ≤ 1 := by rw [Finset.card_sdiff_of_subset hR'R]; omega
    have hw3eq : outN D W w3 = R' := Finset.eq_of_subset_of_card_le hw3R (by rw [hout w3 (hYW hw3)]; omega)
    -- Claim A
    have claimA : ∀ r ∈ R', ∀ w ∈ Y, D r w = true → w ≠ w3 ∧ (∀ r' ∈ R', r' ≠ r → D w r' = true) ∧
        (∀ w' ∈ Y, w' ≠ w → w' ≠ w3 → D w w' = true) := by
      intro r hr w hw hrw
      have hrW := hRW (hR'R hr)
      have hw3r : D w3 r = true := by rw [← hw3eq] at hr; exact (mem_outN.mp hr).2
      have hww3 : w ≠ w3 := by
        rintro rfl; exact digonfree hfree (by omega) hrW (hYW hw) hrw hw3r
      have hnww3 : ¬ D w w3 = true := fun h => tri3 hfree hrW (hYW hw) (hYW hw3) hrw h hw3r
      have hnwr : ¬ D w r = true := fun h => digonfree hfree (by omega) hrW (hYW hw) hrw h
      have hsub : outN D W w ⊆ (Y.erase w).erase w3 ∪ R'.erase r := by
        intro b hb
        obtain ⟨hbW, hwb⟩ := mem_outN.mp hb
        rcases F1 w hw b hbW hwb with hbY | hbR
        · refine Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨?_, Finset.mem_erase.mpr ⟨?_, hbY⟩⟩)
          · rintro rfl; exact hnww3 hwb
          · rintro rfl; exact loopfree hfree (by omega) hbW hwb
        · refine Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨?_, Finset.mem_filter.mpr ⟨hbR, w, hw, hwb⟩⟩)
          rintro rfl; exact hnwr hwb
      have hc1 : ((Y.erase w).erase w3).card = 1 := by
        rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨Ne.symm hww3, hw3⟩), Finset.card_erase_of_mem hw]
        omega
      have hc2 : (R'.erase r).card = 3 := by rw [Finset.card_erase_of_mem hr]; omega
      have heq := Finset.eq_of_subset_of_card_le hsub (by
        rw [hout w (hYW hw)]
        have := Finset.card_union_le ((Y.erase w).erase w3) (R'.erase r)
        omega)
      refine ⟨hww3, fun r' hr' hne => ?_, fun w' hw' hne hne3 => ?_⟩
      · have : r' ∈ outN D W w := by rw [heq]; exact Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hne, hr'⟩)
        exact (mem_outN.mp this).2
      · have : w' ∈ outN D W w := by
          rw [heq]; exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hne3, Finset.mem_erase.mpr ⟨hne, hw'⟩⟩)
        exact (mem_outN.mp this).2
    -- Claim B: at most one vertex of `R'` has an arc into `Y`
    have claimB : ∀ r1 ∈ R', ∀ r2 ∈ R', ∀ w1 ∈ Y, ∀ w2 ∈ Y, D r1 w1 = true → D r2 w2 = true → r1 = r2 := by
      intro r1 hr1 r2 hr2 w1 hw1 w2 hw2 h1 h2
      by_contra hne
      obtain ⟨hw13, hA1, hB1⟩ := claimA r1 hr1 w1 hw1 h1
      obtain ⟨hw23, hA2, hB2⟩ := claimA r2 hr2 w2 hw2 h2
      by_cases hw : w1 = w2
      · subst hw
        exact digonfree hfree (by omega) (hYW hw1) (hRW (hR'R hr2)) (hA1 r2 hr2 (Ne.symm hne)) h2
      · exact digonfree hfree (by omega) (hYW hw1) (hYW hw2) (hB1 w2 hw2 (Ne.symm hw) hw23) (hB2 w1 hw1 hw hw13)
    obtain ⟨r1, hr1, hr1p⟩ : ∃ r1 ∈ R', ∀ r ∈ R', r ≠ r1 → ∀ w ∈ Y, ¬ D r w = true := by
      by_cases hex : ∃ r ∈ R', ∃ w ∈ Y, D r w = true
      · obtain ⟨r, hr, w, hw, hrw⟩ := hex
        exact ⟨r, hr, fun r' hr' hne w' hw' h => hne (claimB r' hr' r hr w' hw' w hw h hrw)⟩
      · push Not at hex
        obtain ⟨r, hr⟩ : R'.Nonempty := by rw [← Finset.card_pos]; omega
        exact ⟨r, hr, fun r' hr' _ w hw => hex r' hr' w hw⟩
    -- the other three vertices of `R'` form a 3-free set with min out `≥ 1`
    have hR''W : R'.erase r1 ⊆ W := (Finset.erase_subset _ _).trans (hR'R.trans hRW)
    have hmin1 : ∀ r ∈ R'.erase r1, ∃ t ∈ R'.erase r1, D r t = true := by
      intro r hr
      obtain ⟨hrr1, hrR'⟩ := Finset.mem_erase.mp hr
      have hs := out_split (U := R'.erase r1) (S := insert y (insert r1 (R \ R'))) (v := r) (fun b hb hrb => by
        rcases hsplit b hb with rfl | hbV | hbY | hbR
        · exact Or.inr (Finset.mem_insert_self _ _)
        · exact absurd hrb (F3 r hrR' b hbV)
        · exact absurd hrb (hr1p r hrR' hrr1 b hbY)
        · by_cases hbR' : b ∈ R'
          · by_cases hb1 : b = r1
            · exact Or.inr (Finset.mem_insert_of_mem (hb1 ▸ Finset.mem_insert_self _ _))
            · exact Or.inl (Finset.mem_erase.mpr ⟨hb1, hbR'⟩)
          · exact Or.inr (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_sdiff.mpr ⟨hbR, hbR'⟩))))
      have hS3 : (outN D (insert y (insert r1 (R \ R'))) r).card ≤ 3 := by
        refine (Finset.card_le_card outN_subset).trans ?_
        refine (Finset.card_insert_le _ _).trans ?_
        have := Finset.card_insert_le r1 (R \ R')
        omega
      rw [hout r (hRW (hR'R hrR'))] at hs
      obtain ⟨t, ht⟩ : (outN D (R'.erase r1) r).Nonempty := by rw [← Finset.card_pos]; omega
      exact ⟨t, (mem_outN.mp ht).1, (mem_outN.mp ht).2⟩
    have hc3 : (R'.erase r1).card = 3 := by rw [Finset.card_erase_of_mem hr1]; omega
    obtain ⟨t, ht, hsink⟩ := exists_sink (hfree.mono_set hR''W) (Finset.card_pos.mp (by omega)) (by omega)
    obtain ⟨t', ht', htt'⟩ := hmin1 t ht
    exact hsink t' ht' htt'

/-- **Lemma 17.** `BallSmall 3 4`: every 3-free out-4 digraph on at most 13 vertices has `|B_2(y)| ≥ 9`. -/
theorem lemma17 : BallSmall 3 4 := by
  intro D W hfree hout hcard y hy
  change 9 ≤ (ball D W y 2).card
  classical
  have hV4 : (outN D W y).card = 4 := hout y hy
  have hyV : y ∉ outN D W y := fun h => loopfree hfree (by omega) hy (mem_outN.mp h).2
  have hb1 : (ball D W y 1).card = 5 := by rw [ball_one_eq hy, Finset.card_insert_of_notMem hyV, hV4]
  have e2 := Finset.card_sdiff_add_card_eq_card (ball_mono_radius (D := D) (W := W) (u := y) (by omega : 1 ≤ 2))
  by_contra hlt
  have hY : (ball D W y 2 \ ball D W y 1).card ≤ 3 := by omega
  have hVW : outN D W y ⊆ W := outN_subset
  have hVout : ∀ v ∈ outN D W y, ∀ b ∈ W, D v b = true → b ∈ ball D W y 2 \ ball D W y 1 ∨ b ∈ outN D W y := by
    intro v hv b hb hvb
    have hb2 : b ∈ ball D W y 2 := ball_step (mem_ball_one_of_out hv) hb hvb
    by_cases hb1 : b ∈ ball D W y 1
    · rcases (mem_ball_one hy).mp hb1 with rfl | h
      · exact absurd hvb (fun h' => digonfree hfree (by omega) hy (hVW hv) (mem_outN.mp hv).2 h')
      · exact Or.inr h
    · exact Or.inl (Finset.mem_sdiff.mpr ⟨hb2, hb1⟩)
  by_cases hsink : ∃ v ∈ outN D W y, ∀ w ∈ outN D W y, ¬ D v w = true
  · -- `D[N_1]` has a sink `v`: `O(v) ⊆ N_2`
    obtain ⟨v, hv, hvs⟩ := hsink
    have hsub : outN D W v ⊆ ball D W y 2 \ ball D W y 1 := by
      intro b hb
      obtain ⟨hbW, hvb⟩ := mem_outN.mp hb
      rcases hVout v hv b hbW hvb with h | h
      · exact h
      · exact absurd hvb (hvs b h)
    have := Finset.card_le_card hsub
    rw [hout v (hVW hv)] at this
    omega
  · -- `D[N_1]` has min out `≥ 1`, so out-degree exactly one in `N_1` (`unique_succ`): a bad root
    push Not at hsink
    have huniq : ∀ v ∈ outN D W y, (outN D (outN D W y) v).card ≤ 1 := by
      intro v hv
      refine Finset.card_le_one.mpr (fun a ha b hb => ?_)
      exact unique_succ (q := 3) (by omega) (hfree.mono_set hVW) (by omega) hsink hv (mem_outN.mp ha).1
        (mem_outN.mp hb).1 (mem_outN.mp ha).2 (mem_outN.mp hb).2
    have hY3 : ∀ v ∈ outN D W y, 3 ≤ (outN D (ball D W y 2 \ ball D W y 1) v).card := by
      intro v hv
      have hs := out_split (hVout v hv)
      rw [hout v (hVW hv)] at hs
      have := huniq v hv
      omega
    obtain ⟨v1, hv1⟩ : (outN D W y).Nonempty := by rw [← Finset.card_pos]; omega
    have hYc : (ball D W y 2 \ ball D W y 1).card = 3 := by
      have := hY3 v1 hv1
      have := Finset.card_le_card (outN_subset (D := D) (W := ball D W y 2 \ ball D W y 1) (y := v1))
      omega
    refine bad_root hfree hout hcard hy hYc (fun v hv w hw => ?_)
    have heq := Finset.eq_of_subset_of_card_le (outN_subset (D := D) (W := ball D W y 2 \ ball D W y 1) (y := v))
      (by have := hY3 v hv; omega)
    have : w ∈ outN D (ball D W y 2 \ ball D W y 1) v := by rw [heq]; exact hw
    exact (mem_outN.mp this).2

end LeanCH.BR.BRq4
