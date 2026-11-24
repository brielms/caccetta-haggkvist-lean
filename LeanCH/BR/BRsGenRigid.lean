import LeanCH.BR.BRq4Rigid

/-!
# Rigidity of the second layer for every out-degree `s` (Lean 4.35.0)

Paper: `checkpoints/boundary_20261111/BallQ5_attempt_subagent.md`, §2, Lemma Q1; the `s = 4` case is
`BRq4Rigid.lean` (`n2_ge_four`, `rigid`). No existing file is changed.

`D` is `s`-free with out-degree exactly `s` on `W`, `u ∈ W`, `N_1 = O(u)`, `N_2 = lay2`, `N_3 = lay3`.

* `n2_ge_s` (`2 ≤ s`): `|N_2| ≥ s`.
* `rigid_s` (**Lemma Q1**, `3 ≤ s`): `|N_2| = s` forces `|N_3| ≥ s`.

The paper's topological order of `N_1` is replaced by `chain_s`: for every `j ≤ s` there is `S ⊆ N_1` with
`|S| = j` all of whose vertices reach every vertex of `N_2` within `j` steps (`Reach j`). It is built by
successive sinks of `D[N_1 ∖ S]` (`chain_step`).

**`s ≥ 3` is needed.** The paper states Q1 for `s ≥ 2`, but at `s = 2` the arc `N_2 → u` is not excluded and the
statement is false: `u → a, a*`; `a → b*, b'`; `a* → a, b'`; `b* → a*, u`; `b' → u, x`; `x → u, a` is loopless,
digon-free, out-2, with `N_2 = {b*, b'}` and `N_3 = {x}`.
-/

set_option linter.style.longLine false

namespace LeanCH.BR.BRsGen

open LeanCH.BR.BRq2 LeanCH.BR.BRq3 LeanCH.BR.BRq4

variable {D : CH.Digraph} {W : Finset ℕ} {u s : ℕ}

/-- Arcs out of `N_1` land in `N_1 ∪ N_2` (`2 ≤ s`). -/
theorem out_N1_s (hs : 2 ≤ s) (hfree : QFree D W s) (hu : u ∈ W) {y c : ℕ} (hy : y ∈ outN D W u)
    (hc : c ∈ outN D W y) : c ∈ outN D W u ∨ c ∈ lay2 D W u := by
  obtain ⟨hcW, hyc⟩ := mem_outN.mp hc
  have hy1 : y ∈ ball D W u 1 := mem_ball_one_of_out hy
  have hc2 : c ∈ ball D W u 2 := ball_step hy1 hcW hyc
  by_cases hc1 : c ∈ ball D W u 1
  · rcases (mem_ball_one hu).mp hc1 with h | h
    · rw [h] at hyc; exact absurd hyc (no_back_arc hfree hu hy1 (by omega))
    · exact Or.inl h
  · exact Or.inr (Finset.mem_sdiff.mpr ⟨hc2, hc1⟩)

/-- If `|N_3| ≤ s - 1` (`3 ≤ s`), every `y ∈ N_2` has an arc into `N_1 ∪ N_2`. -/
theorem out_N2_s (hs : 3 ≤ s) (hfree : QFree D W s) (hout : OutEq s D W) (hu : u ∈ W)
    (h3 : (lay3 D W u).card ≤ s - 1) {y : ℕ} (hy : y ∈ lay2 D W u) :
    ∃ c, D y c = true ∧ (c ∈ outN D W u ∨ c ∈ lay2 D W u) := by
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

/-- A sink of `D[N_1]` sends all `s` arcs into `N_2`. -/
theorem sink_sub_s (hs : 2 ≤ s) (hfree : QFree D W s) (hu : u ∈ W) {t : ℕ} (ht : t ∈ outN D W u)
    (hsink : ∀ c ∈ outN D W u, ¬ D t c = true) : outN D W t ⊆ lay2 D W u :=
  fun c hc => (out_N1_s hs hfree hu ht hc).resolve_left (fun h => hsink c h (mem_outN.mp hc).2)

/-- **`n2_ge_four` for every `s ≥ 2`.** `|N_2| ≥ s`. -/
theorem n2_ge_s (hs : 2 ≤ s) (hfree : QFree D W s) (hout : OutEq s D W) (hu : u ∈ W) :
    s ≤ (lay2 D W u).card := by
  have hN1W : outN D W u ⊆ W := outN_subset
  obtain ⟨t, ht, hsn⟩ := exists_sink (hfree.mono_set hN1W)
    (by rw [← Finset.card_pos, hout u hu]; omega) (by rw [hout u hu])
  have := Finset.card_le_card (sink_sub_s hs hfree hu ht hsn)
  rwa [hout t (hN1W ht)] at this

/-- With `|N_2| = s`, a sink of `D[N_1]` points to all of `N_2`. -/
theorem sink_all_s (hs : 2 ≤ s) (hfree : QFree D W s) (hout : OutEq s D W) (hu : u ∈ W)
    (h2 : (lay2 D W u).card = s) {t : ℕ} (ht : t ∈ outN D W u) (hsink : ∀ c ∈ outN D W u, ¬ D t c = true) :
    ∀ b ∈ lay2 D W u, D t b = true := by
  have heq := Finset.eq_of_subset_of_card_le (sink_sub_s hs hfree hu ht hsink)
    (by rw [h2, hout t (outN_subset ht)])
  intro b hb
  rw [← heq] at hb
  exact (mem_outN.mp hb).2

/-- If every out-neighbour of `a ∈ N_1` inside `N_1` has `Reach j`, then `a` has `Reach (j+1)`. -/
theorem reach_step_s (hs : 2 ≤ s) (hfree : QFree D W s) (hout : OutEq s D W) (hu : u ∈ W)
    (h2 : (lay2 D W u).card = s) {j a : ℕ} (ha : a ∈ outN D W u)
    (h : ∀ c ∈ outN D W u, D a c = true → Reach D W u j c) : Reach D W u (j + 1) a := by
  by_cases hc : ∃ c ∈ outN D W u, D a c = true
  · obtain ⟨c, hc, hac⟩ := hc
    intro b hb
    obtain ⟨m, h1, h2, w⟩ := h c hc hac b hb
    exact ⟨m + 1, by omega, by omega, .step (outN_subset hc) hac w⟩
  · intro b hb
    have hab := sink_all_s hs hfree hout hu h2 ha (fun c hc' hac => hc ⟨c, hc', hac⟩) b hb
    exact ⟨1, le_rfl, by omega, .step (ball_subset (Finset.mem_sdiff.mp hb).1) hab (.refl b)⟩

/-- No arc of `N_2` enters a vertex with `Reach (s-1)`. -/
theorem no_in_s (hfree : QFree D W s) {a b : ℕ} (ha : a ∈ W) (hr : Reach D W u (s - 1) a)
    (hb : b ∈ lay2 D W u) : ¬ D b a = true := by
  intro hba
  obtain ⟨m, h1, h2, w⟩ := hr b hb
  exact hfree a (m + 1) (by omega) (by omega) (w.snoc ha hba)

/-- One more sink: given `S ⊆ N_1` with `|S| = j < s`, all of `Reach j`, a sink of `D[N_1 ∖ S]` has `Reach (j+1)`. -/
theorem chain_step (hs : 2 ≤ s) (hfree : QFree D W s) (hout : OutEq s D W) (hu : u ∈ W)
    (h2 : (lay2 D W u).card = s) {S : Finset ℕ} {j : ℕ} (hSN : S ⊆ outN D W u) (hSc : S.card = j) (hj : j < s)
    (hSr : ∀ a ∈ S, Reach D W u j a) : ∃ t ∈ outN D W u, t ∉ S ∧ Reach D W u (j + 1) t := by
  classical
  have hN1W : outN D W u ⊆ W := outN_subset
  have hTc : (outN D W u \ S).card = s - j := by rw [Finset.card_sdiff_of_subset hSN, hout u hu, hSc]
  obtain ⟨t, ht, hst⟩ := exists_sink (T := outN D W u \ S)
    (hfree.mono_set ((Finset.sdiff_subset).trans hN1W))
    (by rw [← Finset.card_pos, hTc]; omega) (by rw [hTc]; omega)
  obtain ⟨ht1, htS⟩ := Finset.mem_sdiff.mp ht
  refine ⟨t, ht1, htS, reach_step_s hs hfree hout hu h2 ht1 (fun c hc htc => ?_)⟩
  by_cases hcS : c ∈ S
  · exact hSr c hcS
  · exact absurd htc (hst c (Finset.mem_sdiff.mpr ⟨hc, hcS⟩))

/-- Successive sinks: for every `j ≤ s` some `j` vertices of `N_1` have `Reach j`. -/
theorem chain_s (hs : 2 ≤ s) (hfree : QFree D W s) (hout : OutEq s D W) (hu : u ∈ W)
    (h2 : (lay2 D W u).card = s) :
    ∀ j, j ≤ s → ∃ S ⊆ outN D W u, S.card = j ∧ ∀ a ∈ S, Reach D W u j a := by
  classical
  intro j
  induction j with
  | zero => intro _; exact ⟨∅, Finset.empty_subset _, rfl, fun a ha => absurd ha (Finset.notMem_empty a)⟩
  | succ j ih =>
    intro hj
    obtain ⟨S, hSN, hSc, hSr⟩ := ih (by omega)
    obtain ⟨t, ht, htS, htr⟩ := chain_step hs hfree hout hu h2 hSN hSc (by omega) hSr
    refine ⟨insert t S, Finset.insert_subset ht hSN, by rw [Finset.card_insert_of_notMem htS, hSc], fun a ha => ?_⟩
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact htr
    · exact reach_mono (hSr a ha) (by omega)

/-- **Lemma Q1 (rigid second layer, every `s ≥ 3`).** In an `s`-free digraph with out-degree exactly `s`,
`|N_2| = s` implies `|N_3| ≥ s`. -/
theorem rigid_s (hs : 3 ≤ s) (hfree : QFree D W s) (hout : OutEq s D W) (hu : u ∈ W)
    (h2 : (lay2 D W u).card = s) : s ≤ (lay3 D W u).card := by
  classical
  by_contra h3'
  have h3 : (lay3 D W u).card ≤ s - 1 := by omega
  have hN1W : outN D W u ⊆ W := outN_subset
  have hN1c : (outN D W u).card = s := hout u hu
  have hN2W : lay2 D W u ⊆ W := fun b hb => ball_subset (Finset.mem_sdiff.mp hb).1
  -- `S' ⊆ N_1`, `|S'| = s-2`, all `Reach (s-2)`; one more sink `t` with `Reach (s-1)`
  obtain ⟨S', hS'N, hS'c, hS'r⟩ := chain_s (by omega) hfree hout hu h2 (s - 2) (by omega)
  obtain ⟨t, ht, htS', htr⟩ := chain_step (by omega) hfree hout hu h2 hS'N hS'c (by omega) hS'r
  rw [show s - 2 + 1 = s - 1 by omega] at htr
  have hSN : insert t S' ⊆ outN D W u := Finset.insert_subset ht hS'N
  have hSc : (insert t S').card = s - 1 := by rw [Finset.card_insert_of_notMem htS', hS'c]; omega
  have hSr : ∀ a ∈ insert t S', Reach D W u (s - 1) a := by
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact htr
    · exact reach_mono (hS'r a ha) (by omega)
  -- `N_1 ∖ S` is a single vertex
  have hRc : (outN D W u \ insert t S').card = 1 := by
    rw [Finset.card_sdiff_of_subset hSN, hN1c, hSc]; omega
  have hU : ∀ c ∈ outN D W u, c ∉ insert t S' → ∀ c' ∈ outN D W u, c' ∉ insert t S' → c = c' :=
    fun c hc hcS c' hc' hc'S =>
      Finset.card_le_one.mp hRc.le c (Finset.mem_sdiff.mpr ⟨hc, hcS⟩) c' (Finset.mem_sdiff.mpr ⟨hc', hc'S⟩)
  -- arcs from `N_2` into `N_1` avoid `S`
  have hnoS : ∀ b ∈ lay2 D W u, ∀ a ∈ insert t S', ¬ D b a = true := fun b hb a ha =>
    no_in_s hfree (hN1W (hSN ha)) (hSr a ha) hb
  by_cases hbad : ∃ b ∈ lay2 D W u, ∃ a ∈ outN D W u, D b a = true
  · -- an arc `b* → a*` from `N_2` into `N_1`
    obtain ⟨bs, hbs, a, ha, hba⟩ := hbad
    have haW := hN1W ha
    have hbsW := hN2W hbs
    have haS : a ∉ insert t S' := fun h => hnoS bs hbs a h hba
    -- the only out-neighbour of `a*` in `N_1` is `t`
    have hO1 : ∀ c ∈ outN D W u, D a c = true → c = t := by
      intro c hc hac
      by_contra hct
      by_cases hcS' : c ∈ S'
      · obtain ⟨m, h1, h2', w⟩ := hS'r c hcS' bs hbs
        exact hfree a (m + 1 + 1) (by omega) (by omega) ((Walk.step (hN1W hc) hac w).snoc haW hba)
      · have hcS : c ∉ insert t S' := by
          intro h
          rcases Finset.mem_insert.mp h with h | h
          · exact hct h
          · exact hcS' h
        have e := hU c hc hcS a ha haS
        rw [e] at hac
        exact loopfree hfree (by omega) haW hac
    -- hence `O(a*) ∖ {t} = N_2 ∖ {b*}`
    have hsub : (outN D W a).erase t ⊆ (lay2 D W u).erase bs := by
      intro c hc
      obtain ⟨hct, hc'⟩ := Finset.mem_erase.mp hc
      refine Finset.mem_erase.mpr ⟨?_, ?_⟩
      · rintro rfl
        exact digonfree hfree (by omega) haW hbsW (mem_outN.mp hc').2 hba
      · rcases out_N1_s (by omega) hfree hu ha hc' with h | h
        · exact absurd (hO1 c h (mem_outN.mp hc').2) hct
        · exact h
    have hcard : ((lay2 D W u).erase bs).card ≤ ((outN D W a).erase t).card := by
      rw [Finset.card_erase_of_mem hbs, h2]
      have := Finset.pred_card_le_card_erase (s := outN D W a) (a := t)
      rw [hout a haW] at this
      omega
    have heq := Finset.eq_of_subset_of_card_le hsub hcard
    have haT : ∀ b' ∈ (lay2 D W u).erase bs, D a b' = true := by
      intro b' hb'
      rw [← heq] at hb'
      exact (mem_outN.mp (Finset.mem_of_mem_erase hb')).2
    -- `D[N_2 ∖ {b*}]` has min out `≥ 1` on `s - 1` vertices
    obtain ⟨t', ht', hst⟩ := exists_sink (T := (lay2 D W u).erase bs)
      (hfree.mono_set ((Finset.erase_subset _ _).trans hN2W))
      (by rw [← Finset.card_pos, Finset.card_erase_of_mem hbs]; omega)
      (by rw [Finset.card_erase_of_mem hbs]; omega)
    have ht'N2 := Finset.mem_of_mem_erase ht'
    have ht'W := hN2W ht'N2
    obtain ⟨c, htc, hc⟩ := out_N2_s hs hfree hout hu h3 ht'N2
    rcases hc with hc | hc
    · -- `c ∈ N_1` receives an arc from `N_2`, so `c = a*`: a digon
      have hcS : c ∉ insert t S' := fun h => hnoS t' ht'N2 c h htc
      have e := hU c hc hcS a ha haS
      rw [e] at htc
      exact digonfree hfree (by omega) haW ht'W (haT t' ht') htc
    · -- `c ∈ N_2`, `c ≠ b*` (else `a* → t' → b* → a*`, length `3 ≤ s`)
      have hcbs : c ≠ bs := by
        rintro rfl
        exact hfree a 3 (by omega) hs (.step ht'W (haT t' ht') (.step hbsW htc (.step haW hba (.refl a))))
      exact hst c (Finset.mem_erase.mpr ⟨hcbs, hc⟩) htc
  · -- no arc from `N_2` into `N_1`: `D[N_2]` has min out `≥ 1` on `s` vertices
    obtain ⟨t', ht', hst⟩ := exists_sink (T := lay2 D W u) (hfree.mono_set hN2W)
      (by rw [← Finset.card_pos]; omega) (by omega)
    obtain ⟨c, htc, hc⟩ := out_N2_s hs hfree hout hu h3 ht'
    rcases hc with hc | hc
    · exact hbad ⟨t', ht', c, hc, htc⟩
    · exact hst c hc htc

end LeanCH.BR.BRsGen
