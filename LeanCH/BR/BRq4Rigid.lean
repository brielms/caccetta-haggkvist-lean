import LeanCH.BR.BRq3Util

/-!
# `Ball(4,4)`: the rigid second layer (Lean 4.35.0)

Paper: `checkpoints/boundary_20261111/BallQ4_attempt_subagent.md`, §2, Lemma 3(iv) and Lemma 4.

`D` is `4`-free with out-degree exactly four on `W`, `u ∈ W`, `N_1 = O(u)`, `N_2 = lay2`, `N_3 = lay3`.

* `out_N1`, `out_N2`: arcs out of `N_1` land in `N_1 ∪ N_2`; if `|N_3| ≤ 3`, every `b ∈ N_2` has an arc into
  `N_1 ∪ N_2`.
* `n2_ge_four` (Lemma 3(iv), (P1)): a sink of `D[N_1]` sends all four arcs into `N_2`, so `|N_2| ≥ 4`.
* `rigid` (**Lemma 4**): `|N_2| = 4` forces `|N_3| ≥ 4`.

The paper's topological order `a_1, …, a_4` of `N_1` is replaced by three successive sinks `t_1, t_2, t_3`
(`t_1` a sink of `D[N_1]`, `t_2` of `D[N_1 ∖ {t_1}]`, `t_3` of `D[N_1 ∖ {t_1, t_2}]`), i.e. `t_i = a_{5-i}`. `Reach j a`
says that `a` reaches every vertex of `N_2` by a walk of length `1..j`; `t_i` has `Reach i` (`reach_step`), so no arc
of `N_2` enters `t_1, t_2, t_3`.
-/

set_option linter.style.longLine false

namespace LeanCH.BR.BRq4

open LeanCH.BR.BRq2 LeanCH.BR.BRq3

/-- The second layer `N_2 = B_2 ∖ B_1`. -/
noncomputable def lay2 (D : CH.Digraph) (W : Finset ℕ) (u : ℕ) : Finset ℕ := ball D W u 2 \ ball D W u 1

/-- The third layer `N_3 = B_3 ∖ B_2`. -/
noncomputable def lay3 (D : CH.Digraph) (W : Finset ℕ) (u : ℕ) : Finset ℕ := ball D W u 3 \ ball D W u 2

/-- `a` reaches every vertex of `N_2` by a walk of length `1..j`. -/
def Reach (D : CH.Digraph) (W : Finset ℕ) (u j a : ℕ) : Prop :=
  ∀ b ∈ lay2 D W u, ∃ m, 1 ≤ m ∧ m ≤ j ∧ Walk D W a b m

variable {D : CH.Digraph} {W : Finset ℕ} {u : ℕ}

/-- Arcs out of `N_1` land in `N_1 ∪ N_2`. -/
theorem out_N1 (hfree : QFree D W 4) (hu : u ∈ W) {y c : ℕ} (hy : y ∈ outN D W u) (hc : c ∈ outN D W y) :
    c ∈ outN D W u ∨ c ∈ lay2 D W u := by
  obtain ⟨hcW, hyc⟩ := mem_outN.mp hc
  have hy1 : y ∈ ball D W u 1 := mem_ball_one_of_out hy
  have hc2 : c ∈ ball D W u 2 := ball_step hy1 hcW hyc
  by_cases hc1 : c ∈ ball D W u 1
  · rcases (mem_ball_one hu).mp hc1 with h | h
    · rw [h] at hyc; exact absurd hyc (no_back_arc hfree hu hy1 (by omega))
    · exact Or.inl h
  · exact Or.inr (Finset.mem_sdiff.mpr ⟨hc2, hc1⟩)

/-- If `|N_3| ≤ 3`, every `y ∈ N_2` has an arc into `N_1 ∪ N_2`. -/
theorem out_N2 (hfree : QFree D W 4) (hout : OutEq 4 D W) (hu : u ∈ W) (h3 : (lay3 D W u).card ≤ 3)
    {y : ℕ} (hy : y ∈ lay2 D W u) : ∃ c, D y c = true ∧ (c ∈ outN D W u ∨ c ∈ lay2 D W u) := by
  have hy2 : y ∈ ball D W u 2 := (Finset.mem_sdiff.mp hy).1
  have hyW : y ∈ W := ball_subset hy2
  obtain ⟨c, hc, hcN3⟩ : ∃ c ∈ outN D W y, c ∉ lay3 D W u := by
    by_contra h
    push Not at h
    have := Finset.card_le_card (show outN D W y ⊆ lay3 D W u from fun c hc => h c hc)
    rw [hout y hyW] at this
    omega
  obtain ⟨hcW, hyc⟩ := mem_outN.mp hc
  have hc3 : c ∈ ball D W u 3 := ball_step hy2 hcW hyc
  have hc2 : c ∈ ball D W u 2 := by
    by_contra h
    exact hcN3 (Finset.mem_sdiff.mpr ⟨hc3, h⟩)
  refine ⟨c, hyc, ?_⟩
  by_cases hc1 : c ∈ ball D W u 1
  · rcases (mem_ball_one hu).mp hc1 with h | h
    · rw [h] at hyc; exact absurd hyc (no_back_arc hfree hu hy2 (by omega))
    · exact Or.inl h
  · exact Or.inr (Finset.mem_sdiff.mpr ⟨hc2, hc1⟩)

/-- A sink of `D[N_1]` sends all four arcs into `N_2`. -/
theorem sink_sub (hfree : QFree D W 4) (hu : u ∈ W) {t : ℕ} (ht : t ∈ outN D W u)
    (hsink : ∀ c ∈ outN D W u, ¬ D t c = true) : outN D W t ⊆ lay2 D W u :=
  fun c hc => (out_N1 hfree hu ht hc).resolve_left (fun h => hsink c h (mem_outN.mp hc).2)

/-- **Lemma 3(iv), (P1).** `|N_2| ≥ 4`. -/
theorem n2_ge_four (hfree : QFree D W 4) (hout : OutEq 4 D W) (hu : u ∈ W) : 4 ≤ (lay2 D W u).card := by
  have hN1W : outN D W u ⊆ W := outN_subset
  obtain ⟨t, ht, hs⟩ := exists_sink (hfree.mono_set hN1W)
    (by rw [← Finset.card_pos, hout u hu]; omega) (by rw [hout u hu])
  have := Finset.card_le_card (sink_sub hfree hu ht hs)
  rwa [hout t (hN1W ht)] at this

/-- With `|N_2| = 4`, a sink of `D[N_1]` points to all of `N_2`. -/
theorem sink_all (hfree : QFree D W 4) (hout : OutEq 4 D W) (hu : u ∈ W) (h2 : (lay2 D W u).card = 4) {t : ℕ}
    (ht : t ∈ outN D W u) (hsink : ∀ c ∈ outN D W u, ¬ D t c = true) : ∀ b ∈ lay2 D W u, D t b = true := by
  have heq := Finset.eq_of_subset_of_card_le (sink_sub hfree hu ht hsink)
    (by rw [h2, hout t (outN_subset ht)])
  intro b hb
  rw [← heq] at hb
  exact (mem_outN.mp hb).2

theorem reach_mono {j j' a : ℕ} (h : Reach D W u j a) (hj : j ≤ j') : Reach D W u j' a := by
  intro b hb
  obtain ⟨m, h1, h2, w⟩ := h b hb
  exact ⟨m, h1, by omega, w⟩

/-- If every out-neighbour of `a ∈ N_1` inside `N_1` has `Reach j`, then `a` has `Reach (j+1)`. -/
theorem reach_step (hfree : QFree D W 4) (hout : OutEq 4 D W) (hu : u ∈ W) (h2 : (lay2 D W u).card = 4)
    {j a : ℕ} (ha : a ∈ outN D W u) (h : ∀ c ∈ outN D W u, D a c = true → Reach D W u j c) :
    Reach D W u (j + 1) a := by
  by_cases hc : ∃ c ∈ outN D W u, D a c = true
  · obtain ⟨c, hc, hac⟩ := hc
    intro b hb
    obtain ⟨m, h1, h2, w⟩ := h c hc hac b hb
    exact ⟨m + 1, by omega, by omega, .step (outN_subset hc) hac w⟩
  · intro b hb
    have hab := sink_all hfree hout hu h2 ha (fun c hc' hac => hc ⟨c, hc', hac⟩) b hb
    exact ⟨1, le_rfl, by omega, .step (ball_subset (Finset.mem_sdiff.mp hb).1) hab (.refl b)⟩

/-- No arc of `N_2` enters a vertex with `Reach 3`. -/
theorem no_in (hfree : QFree D W 4) {a b : ℕ} (ha : a ∈ W) (hr : Reach D W u 3 a) (hb : b ∈ lay2 D W u) :
    ¬ D b a = true := by
  intro hba
  obtain ⟨m, h1, h2, w⟩ := hr b hb
  exact hfree a (m + 1) (by omega) (by omega) (w.snoc ha hba)

/-- **Lemma 4 (rigid second layer, `s = q = 4`).** In a `4`-free digraph with out-degree four, `|N_2| = 4` implies
`|N_3| ≥ 4`. -/
theorem rigid (hfree : QFree D W 4) (hout : OutEq 4 D W) (hu : u ∈ W) (h2 : (lay2 D W u).card = 4) :
    4 ≤ (lay3 D W u).card := by
  classical
  by_contra h3'
  have h3 : (lay3 D W u).card ≤ 3 := by omega
  have hN1W : outN D W u ⊆ W := outN_subset
  have hN1c : (outN D W u).card = 4 := hout u hu
  have hN2W : lay2 D W u ⊆ W := fun b hb => ball_subset (Finset.mem_sdiff.mp hb).1
  -- three successive sinks of `D[N_1]`
  obtain ⟨t1, ht1, hs1⟩ := exists_sink (hfree.mono_set hN1W)
    (by rw [← Finset.card_pos]; omega) (by omega)
  obtain ⟨t2, ht2, hs2⟩ := exists_sink (T := (outN D W u).erase t1)
    (hfree.mono_set ((Finset.erase_subset _ _).trans hN1W))
    (by rw [← Finset.card_pos, Finset.card_erase_of_mem ht1]; omega)
    (by rw [Finset.card_erase_of_mem ht1]; omega)
  obtain ⟨t3, ht3, hs3⟩ := exists_sink (T := ((outN D W u).erase t1).erase t2)
    (hfree.mono_set (((Finset.erase_subset _ _).trans (Finset.erase_subset _ _)).trans hN1W))
    (by rw [← Finset.card_pos, Finset.card_erase_of_mem ht2, Finset.card_erase_of_mem ht1]; omega)
    (by rw [Finset.card_erase_of_mem ht2, Finset.card_erase_of_mem ht1]; omega)
  obtain ⟨ht21, ht2'⟩ := Finset.mem_erase.mp ht2
  obtain ⟨ht32, ht3'⟩ := Finset.mem_erase.mp ht3
  obtain ⟨ht31, ht3''⟩ := Finset.mem_erase.mp ht3'
  -- `t_i` reaches all of `N_2` within `i` steps
  have r1 : Reach D W u 1 t1 :=
    reach_step (j := 0) hfree hout hu h2 ht1 (fun c hc hac => absurd hac (hs1 c hc))
  have r2 : Reach D W u 2 t2 := by
    refine reach_step (j := 1) hfree hout hu h2 ht2' (fun c hc hac => ?_)
    have e : c = t1 := by
      by_contra hne
      exact hs2 c (Finset.mem_erase.mpr ⟨hne, hc⟩) hac
    rw [e]; exact r1
  have r3 : Reach D W u 3 t3 := by
    refine reach_step (j := 2) hfree hout hu h2 ht3'' (fun c hc hac => ?_)
    by_cases e1 : c = t1
    · rw [e1]; exact reach_mono r1 (by omega)
    by_cases e2 : c = t2
    · rw [e2]; exact r2
    exact absurd hac (hs3 c (Finset.mem_erase.mpr ⟨e2, Finset.mem_erase.mpr ⟨e1, hc⟩⟩))
  -- `N_1 ∖ {t_1, t_2, t_3}` has one vertex
  have hU : ∀ c ∈ outN D W u, c ≠ t1 → c ≠ t2 → c ≠ t3 →
      ∀ c' ∈ outN D W u, c' ≠ t1 → c' ≠ t2 → c' ≠ t3 → c = c' := by
    intro c hc hc1 hc2 hc3 c' hc' hc1' hc2' hc3'
    have hcard : ((((outN D W u).erase t1).erase t2).erase t3).card = 1 := by
      rw [Finset.card_erase_of_mem ht3, Finset.card_erase_of_mem ht2, Finset.card_erase_of_mem ht1]
      omega
    have m1 : c ∈ (((outN D W u).erase t1).erase t2).erase t3 :=
      Finset.mem_erase.mpr ⟨hc3, Finset.mem_erase.mpr ⟨hc2, Finset.mem_erase.mpr ⟨hc1, hc⟩⟩⟩
    have m2 : c' ∈ (((outN D W u).erase t1).erase t2).erase t3 :=
      Finset.mem_erase.mpr ⟨hc3', Finset.mem_erase.mpr ⟨hc2', Finset.mem_erase.mpr ⟨hc1', hc'⟩⟩⟩
    exact Finset.card_le_one.mp hcard.le c m1 c' m2
  by_cases hbad : ∃ b ∈ lay2 D W u, ∃ a ∈ outN D W u, D b a = true
  · -- an arc `b* → a` from `N_2` into `N_1`
    obtain ⟨bs, hbs, a, ha, hba⟩ := hbad
    have haW := hN1W ha
    have hbsW := hN2W hbs
    have ha1 : a ≠ t1 := by
      intro e; rw [e] at hba; exact no_in hfree (hN1W ht1) (reach_mono r1 (by omega)) hbs hba
    have ha2 : a ≠ t2 := by
      intro e; rw [e] at hba; exact no_in hfree (hN1W ht2') (reach_mono r2 (by omega)) hbs hba
    have ha3 : a ≠ t3 := by
      intro e; rw [e] at hba; exact no_in hfree (hN1W ht3'') r3 hbs hba
    -- `a` does not point to a vertex with `Reach 2`
    have hreach2 : ∀ c, Reach D W u 2 c → c ∈ W → ¬ D a c = true := by
      intro c hc hcW hac
      obtain ⟨m, h1, h2, w⟩ := hc bs hbs
      exact hfree a (m + 1 + 1) (by omega) (by omega) ((Walk.step hcW hac w).snoc haW hba)
    -- so the only out-neighbour of `a` in `N_1` is `t_3`
    have hO1 : ∀ c ∈ outN D W u, D a c = true → c = t3 := by
      intro c hc hac
      by_contra hc3
      have hc1 : c ≠ t1 := by
        intro e; rw [e] at hac; exact hreach2 _ (reach_mono r1 (by omega)) (hN1W ht1) hac
      have hc2 : c ≠ t2 := by
        intro e; rw [e] at hac; exact hreach2 _ r2 (hN1W ht2') hac
      have e := hU c hc hc1 hc2 hc3 a ha ha1 ha2 ha3
      rw [e] at hac
      exact loopfree hfree (by omega) haW hac
    -- hence `O(a) ∩ N_2 = N_2 ∖ {b*}`
    have hsub : (outN D W a).erase t3 ⊆ (lay2 D W u).erase bs := by
      intro c hc
      obtain ⟨hct3, hc'⟩ := Finset.mem_erase.mp hc
      refine Finset.mem_erase.mpr ⟨?_, ?_⟩
      · intro e
        rw [e] at hc'
        exact digonfree hfree (by omega) haW hbsW (mem_outN.mp hc').2 hba
      · rcases out_N1 hfree hu ha hc' with h | h
        · exact absurd (hO1 c h (mem_outN.mp hc').2) hct3
        · exact h
    have hcard : ((lay2 D W u).erase bs).card ≤ ((outN D W a).erase t3).card := by
      rw [Finset.card_erase_of_mem hbs, h2]
      have := Finset.pred_card_le_card_erase (s := outN D W a) (a := t3)
      rw [hout a haW] at this
      omega
    have heq := Finset.eq_of_subset_of_card_le hsub hcard
    have haT : ∀ b' ∈ (lay2 D W u).erase bs, D a b' = true := by
      intro b' hb'
      rw [← heq] at hb'
      exact (mem_outN.mp (Finset.mem_of_mem_erase hb')).2
    -- `D[N_2 ∖ {b*}]` has min out `≥ 1` on three vertices
    obtain ⟨t, ht, hst⟩ := exists_sink (T := (lay2 D W u).erase bs)
      (hfree.mono_set ((Finset.erase_subset _ _).trans hN2W))
      (by rw [← Finset.card_pos, Finset.card_erase_of_mem hbs]; omega)
      (by rw [Finset.card_erase_of_mem hbs]; omega)
    have htN2 := Finset.mem_of_mem_erase ht
    have htW := hN2W htN2
    obtain ⟨c, htc, hc⟩ := out_N2 hfree hout hu h3 htN2
    rcases hc with hc | hc
    · -- `c ∈ N_1` receives an arc from `N_2`, so `c = a`: a digon
      have hcW := hN1W hc
      have hc1 : c ≠ t1 := by
        intro e; rw [e] at htc; exact no_in hfree (hN1W ht1) (reach_mono r1 (by omega)) htN2 htc
      have hc2 : c ≠ t2 := by
        intro e; rw [e] at htc; exact no_in hfree (hN1W ht2') (reach_mono r2 (by omega)) htN2 htc
      have hc3 : c ≠ t3 := by
        intro e; rw [e] at htc; exact no_in hfree (hN1W ht3'') r3 htN2 htc
      have e := hU c hc hc1 hc2 hc3 a ha ha1 ha2 ha3
      rw [e] at htc
      exact digonfree hfree (by omega) haW htW (haT t ht) htc
    · -- `c ∈ N_2`, `c ≠ b*` (else `a → t → b* → a`)
      have hcbs : c ≠ bs := by
        intro e
        rw [e] at htc
        exact hfree a 3 (by omega) (by omega) (.step htW (haT t ht) (.step hbsW htc (.step haW hba (.refl a))))
      exact hst c (Finset.mem_erase.mpr ⟨hcbs, hc⟩) htc
  · -- no arc from `N_2` into `N_1`: `D[N_2]` has min out `≥ 1` on four vertices
    obtain ⟨t, ht, hst⟩ := exists_sink (T := lay2 D W u) (hfree.mono_set hN2W)
      (by rw [← Finset.card_pos]; omega) (by omega)
    obtain ⟨c, htc, hc⟩ := out_N2 hfree hout hu h3 ht
    rcases hc with hc | hc
    · exact hbad ⟨t, ht, c, hc, htc⟩
    · exact hst c hc htc

end LeanCH.BR.BRq4
