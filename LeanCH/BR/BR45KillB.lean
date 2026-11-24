import LeanCH.BR.BR45KillA

/-!
# BR(4,5), profile kills, part B: Lemmas 6, 7 and the local half of Lemma 8 (Lean 4.35.0)

Paper: `checkpoints/boundary_20261111/BR45_attempt_subagent.md` §3–§4; audit `BR45_audit_subagent.md` §3.
Setting: `XY D X Y c` of `BR45KillA`.

Tools.
* `reach`: in a `4`-free `T` with `|T| ≤ 4` where every vertex has a head in `T ∪ S`, some vertex of `T` heads `S`.
* `XY.chain2`: if every `y ≠ y_0` of `Y` has a `Y`-head (`3 ≤ |Y| ≤ 5`), there are `y_1 → y_0` and `y_2 ∉ {y_0, y_1}`
  heading `{y_0, y_1}`.
* `XY.back2`, `XY.back3`: `XY.back_arc` (**Lemma 3**) with `D_1 = D_2 = {y_0, y_1}`, resp. `D_1 = {y_0, y_1}`,
  `D_2 = {y_0, y_1, y_2}`: `16 ≤ |X| + 2|Y|`, resp. `17 ≤ |X| + 2|Y|`.
* `XY.pair` (pair test): two `y ≠ y'` with `w ≥ 2` force `|X| ≥ 7` when `|Y| ≤ 5` (`CH(2)` on `X ∪ {y, y'}`).

Kills.
* `XY.kill644` (**Lemma 6**, `(6,4,4)`, `c = 1`). `X_1 = {inner ≤ 1}` heads all of `Y` and is nonempty (`CH(2)`);
  the sink `y_0` of `D[Y]` heads some `x_0 ∉ X_1`; `P = N⁺_X(x_0)` avoids `X_1`, `|P| ≥ 2`.
  If `|X_1| = 1`, `F = X ∖ X_1` has 5 vertices with min out `≥ 1` in `F`, so `BR(4,1)` gives out-degree 1 in `F`,
  against `P ⊆ F`. If `|X_1| ≥ 2`, the last vertex of `P` has two `X`-heads in `F ∖ ({x_0} ∪ P)`, of size `≤ 1`.
  (This replaces the note's `c, d` argument; same strategy.)
* `XY.kill653` (**Lemma 7**, `(6,5,3)`, `c = 2`). There is `y_0` with an `X`-head such that every other `y` has a
  `Y`-head (if `D[Y]` has no sink, `BR(4,1)` makes it `C_5`; otherwise the sink is unique by the pair test). Then
  `chain2` and `back3` give `17 ≤ 16`.
* `XY.loc554` (**Lemma 8**, local half, `(5,5)`, `c = 1`). `D[Y]` has no sink, and no `y` heads `X`.
  If every `y` has a `Y`-head: `chain2` and `back3` (`17 ≤ 15`) exclude every back arc. Otherwise: `back2`
  (`16 ≤ 15`) shows sinks have no `Y`-in-neighbour, so `D[Y]` has no arc (`CH(1)` on the vertices with a
  `Y`-in-neighbour); every `y` is missed by `x_y` and an `X`-head of `x_y`, so `Σ_x |miss(x)| ≥ 10`, while
  `|miss(x)| ≤ inner(x)` and `out_X + in_X ≤ 4` force every `out_X + in_X = 4`; then `D[X]` has a sink (`BR(4,1)`),
  which heads all of `Y` and is headed by all of `X`, so no `y` can head `X`.
-/

set_option linter.style.longLine false

namespace LeanCH.BR.BR45

open LeanCH.BR.BRq2 LeanCH.BR.BRq3 CH

variable {D : CH.Digraph}

/-- In a `4`-free `T`, `|T| ≤ 4`, where every vertex has a head in `T ∪ S`, some vertex of `T` heads `S`. -/
theorem reach {T S : Finset ℕ} (hfree : QFree D T 4) (hne : T.Nonempty) (hc : T.card ≤ 4)
    (hout : ∀ y ∈ T, ∃ z, (z ∈ T ∨ z ∈ S) ∧ D y z = true) : ∃ y ∈ T, ∃ s ∈ S, D y s = true := by
  by_contra hno
  push Not at hno
  obtain ⟨t, ht, hs⟩ := exists_sink hfree hne hc
  obtain ⟨z, hz | hz, htz⟩ := hout t ht
  · exact hs z hz htz
  · exact hno t ht z hz htz

namespace XY

variable {X Y : Finset ℕ} {c : ℕ}

/-- Two steps back from `y_0` inside `Y`. -/
theorem chain2 (H : XY D X Y c) (hY3 : 3 ≤ Y.card) (hY5 : Y.card ≤ 5) {y0 : ℕ} (hy0 : y0 ∈ Y)
    (hrest : ∀ y ∈ Y, y ≠ y0 → ∃ z ∈ Y, D y z = true) :
    ∃ y1 ∈ Y, ∃ y2 ∈ Y, D y1 y0 = true ∧ (D y2 y1 = true ∨ D y2 y0 = true) ∧ y2 ≠ y1 ∧ y2 ≠ y0 := by
  classical
  have hc1 := Finset.card_erase_of_mem hy0
  obtain ⟨y1, hy1T, s, hs, h1s⟩ := reach (S := {y0}) (H.freeY.mono_set (Finset.erase_subset y0 Y))
    (Finset.card_pos.mp (by omega)) (by omega) (fun y hy => by
      obtain ⟨hne, hyY⟩ := Finset.mem_erase.mp hy
      obtain ⟨z, hz, hyz⟩ := hrest y hyY hne
      refine ⟨z, ?_, hyz⟩
      by_cases hz0 : z = y0
      · exact Or.inr (Finset.mem_singleton.mpr hz0)
      · exact Or.inl (Finset.mem_erase.mpr ⟨hz0, hz⟩))
  have hs' : s = y0 := Finset.mem_singleton.mp hs
  rw [hs'] at h1s
  obtain ⟨hy10, hy1⟩ := Finset.mem_erase.mp hy1T
  have hc2 := Finset.card_erase_of_mem hy1T
  obtain ⟨y2, hy2T, s2, hs2, h2s⟩ := reach (S := {y0, y1})
    (H.freeY.mono_set ((Finset.erase_subset y1 _).trans (Finset.erase_subset y0 Y)))
    (Finset.card_pos.mp (by omega)) (by omega) (fun y hy => by
      obtain ⟨hne1, hy'⟩ := Finset.mem_erase.mp hy
      obtain ⟨hne0, hyY⟩ := Finset.mem_erase.mp hy'
      obtain ⟨z, hz, hyz⟩ := hrest y hyY hne0
      refine ⟨z, ?_, hyz⟩
      by_cases hz0 : z = y0
      · exact Or.inr (by rw [hz0]; exact Finset.mem_insert_self _ _)
      · by_cases hz1 : z = y1
        · exact Or.inr (by rw [hz1]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
        · exact Or.inl (Finset.mem_erase.mpr ⟨hz1, Finset.mem_erase.mpr ⟨hz0, hz⟩⟩))
  obtain ⟨hne21, hy2'⟩ := Finset.mem_erase.mp hy2T
  obtain ⟨hne20, hy2⟩ := Finset.mem_erase.mp hy2'
  refine ⟨y1, hy1, y2, hy2, h1s, ?_, hne21, hne20⟩
  rcases Finset.mem_insert.mp hs2 with h | h
  · rw [h] at h2s
    exact Or.inr h2s
  · rw [Finset.mem_singleton.mp h] at h2s
    exact Or.inl h2s

/-- **Lemma 3** with `D_1 = D_2 = {y_0, y_1}`. -/
theorem back2 (H : XY D X Y c) (hX6 : X.card ≤ 6) (hY6 : Y.card ≤ 6) {y0 y1 x : ℕ} (hy0 : y0 ∈ Y)
    (hy1 : y1 ∈ Y) (hx : x ∈ X) (hyx : D y0 x = true) (h10 : D y1 y0 = true) :
    16 ≤ X.card + 2 * Y.card := by
  classical
  have hne10 : y1 ≠ y0 := ne_of_arc H.free (H.mY hy0) h10
  have hc1 : ({y0, y1} : Finset ℕ).card = 2 := Finset.card_pair hne10.symm
  have hsub : ({y0, y1} : Finset ℕ) ⊆ Y := by
    intro z hz
    rcases Finset.mem_insert.mp hz with h | h
    · rw [h]; exact hy0
    · rw [Finset.mem_singleton.mp h]; exact hy1
  have hD1 : ∀ y ∈ ({y0, y1} : Finset ℕ), y = y0 ∨ D y y0 = true := by
    intro y hy
    rcases Finset.mem_insert.mp hy with h | h
    · exact Or.inl h
    · rw [Finset.mem_singleton.mp h]; exact Or.inr h10
  have := H.back_arc hX6 hy0 hx hyx hsub hsub hD1 (fun y hy => Or.inl hy) (by rw [hc1]; omega)
  rw [hc1] at this
  omega

/-- **Lemma 3** with `D_1 = {y_0, y_1}`, `D_2 = {y_0, y_1, y_2}`. -/
theorem back3 (H : XY D X Y c) (hX6 : X.card ≤ 6) (hY7 : Y.card ≤ 7) {y0 y1 y2 x : ℕ} (hy0 : y0 ∈ Y)
    (hy1 : y1 ∈ Y) (hy2 : y2 ∈ Y) (hx : x ∈ X) (hyx : D y0 x = true) (h10 : D y1 y0 = true)
    (h2 : D y2 y1 = true ∨ D y2 y0 = true) (hne21 : y2 ≠ y1) (hne20 : y2 ≠ y0) :
    17 ≤ X.card + 2 * Y.card := by
  classical
  have hne10 : y1 ≠ y0 := ne_of_arc H.free (H.mY hy0) h10
  have hc1 : ({y0, y1} : Finset ℕ).card = 2 := Finset.card_pair hne10.symm
  have hc2 : ({y2, y0, y1} : Finset ℕ).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hne20, hne21]), hc1]
  have hsub1 : ({y0, y1} : Finset ℕ) ⊆ Y := by
    intro z hz
    rcases Finset.mem_insert.mp hz with h | h
    · rw [h]; exact hy0
    · rw [Finset.mem_singleton.mp h]; exact hy1
  have hsub2 : ({y2, y0, y1} : Finset ℕ) ⊆ Y := by
    intro z hz
    rcases Finset.mem_insert.mp hz with h | h
    · rw [h]; exact hy2
    · exact hsub1 h
  have hD1 : ∀ y ∈ ({y0, y1} : Finset ℕ), y = y0 ∨ D y y0 = true := by
    intro y hy
    rcases Finset.mem_insert.mp hy with h | h
    · exact Or.inl h
    · rw [Finset.mem_singleton.mp h]; exact Or.inr h10
  have hD2 : ∀ y ∈ ({y2, y0, y1} : Finset ℕ), y ∈ ({y0, y1} : Finset ℕ) ∨
      ∃ y' ∈ ({y0, y1} : Finset ℕ), D y y' = true := by
    intro y hy
    rcases Finset.mem_insert.mp hy with h | h
    · rw [h]
      right
      rcases h2 with h2 | h2
      · exact ⟨y1, Finset.mem_insert_of_mem (Finset.mem_singleton_self _), h2⟩
      · exact ⟨y0, Finset.mem_insert_self _ _, h2⟩
    · exact Or.inl h
  have := H.back_arc hX6 hy0 hx hyx hsub1 hsub2 hD1 hD2 (by rw [hc2]; omega)
  rw [hc1, hc2] at this
  omega

/-- Pair test: two `y ≠ y'` with at least two `X`-heads each force `|X| ≥ 7` (when `|Y| ≤ 5`). -/
theorem pair (H : XY D X Y c) (hY : Y.card ≤ 5) {y y' : ℕ} (hy : y ∈ Y) (hy' : y' ∈ Y) (hne : y ≠ y')
    (hw : 2 ≤ (outN D X y).card) (hw' : 2 ≤ (outN D X y').card) : 7 ≤ X.card := by
  classical
  have hyX : y ∉ X := fun h => Finset.disjoint_left.mp H.disj h hy
  have hy'X : y' ∉ X := fun h => Finset.disjoint_left.mp H.disj h hy'
  have hTW : insert y (insert y' X) ⊆ X ∪ Y :=
    Finset.insert_subset (H.mY hy) (Finset.insert_subset (H.mY hy') Finset.subset_union_left)
  have hXT : X ⊆ insert y (insert y' X) := (Finset.subset_insert y' X).trans (Finset.subset_insert y _)
  have hmin : ∀ t ∈ insert y (insert y' X), 2 ≤ (outN D (insert y (insert y' X)) t).card := by
    intro t ht
    rcases Finset.mem_insert.mp ht with h | h
    · rw [h]
      exact hw.trans (Finset.card_le_card (outN_mono hXT y))
    · rcases Finset.mem_insert.mp h with h | h
      · rw [h]
        exact hw'.trans (Finset.card_le_card (outN_mono hXT y'))
      · have hsub : outN D (X ∪ Y) t ⊆ outN D (insert y (insert y' X)) t ∪ (Y.erase y).erase y' := by
          intro z hz
          obtain ⟨hzW, htz⟩ := mem_outN.mp hz
          by_cases hzy : z = y
          · exact Finset.mem_union_left _ (mem_outN.mpr ⟨by rw [hzy]; exact Finset.mem_insert_self _ _, htz⟩)
          · by_cases hzy' : z = y'
            · exact Finset.mem_union_left _ (mem_outN.mpr
                ⟨by rw [hzy']; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _), htz⟩)
            · rcases Finset.mem_union.mp hzW with hz' | hz'
              · exact Finset.mem_union_left _ (mem_outN.mpr ⟨hXT hz', htz⟩)
              · exact Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hzy', Finset.mem_erase.mpr ⟨hzy, hz'⟩⟩)
        have h1 := (H.outX t h).trans (Finset.card_le_card hsub)
        have h2 := Finset.card_union_le (outN D (insert y (insert y' X)) t) ((Y.erase y).erase y')
        have h3 := Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hne.symm, hy'⟩)
        have h4 := Finset.card_erase_of_mem hy
        omega
  have h9 := ch2 (H.free.mono_set hTW) hmin ⟨y, Finset.mem_insert_self _ _⟩
  rw [Finset.card_insert_of_notMem (by simp [hne, hyX]), Finset.card_insert_of_notMem hy'X] at h9
  omega

/-- **Lemma 6.** `(|X|, |Y|) = (6, 4)` with `c = 1` is impossible: kills `(6,4,4)`. -/
theorem kill644 (H : XY D X Y 1) (hX : X.card = 6) (hY : Y.card = 4) : False := by
  classical
  set X1 := X.filter (fun x => (outN D X x).card ≤ 1) with hX1
  have hX1Y : ∀ x ∈ X1, ∀ y ∈ Y, D x y = true := by
    intro x hx y hy
    obtain ⟨hxX, hx1⟩ := Finset.mem_filter.mp hx
    have h1 := H.rowX hxX
    have heq : outN D Y x = Y := Finset.eq_of_subset_of_card_le outN_subset (by omega)
    have : y ∈ outN D Y x := by rw [heq]; exact hy
    exact (mem_outN.mp this).2
  have hX1ne : X1.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    have hmin : ∀ x ∈ X, 2 ≤ (outN D X x).card := by
      intro x hx
      by_contra hlt
      have : x ∈ X1 := Finset.mem_filter.mpr ⟨hx, by omega⟩
      rw [h] at this
      exact Finset.notMem_empty _ this
    have := ch2 H.freeX hmin (Finset.card_pos.mp (by omega))
    omega
  obtain ⟨y0, hy0, hs⟩ := H.sinkY (Finset.card_pos.mp (by omega)) (by omega)
  obtain ⟨x0, hx0, hyx⟩ : ∃ x0 ∈ X, D y0 x0 = true := by
    have h1 := H.rowY hy0
    have h0 : (outN D Y y0).card = 0 := by
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro z hz
      exact hs z (mem_outN.mp hz).1 (mem_outN.mp hz).2
    obtain ⟨x0, hx0⟩ := Finset.card_pos.mp (show 0 < (outN D X y0).card by omega)
    exact ⟨x0, (mem_outN.mp hx0).1, (mem_outN.mp hx0).2⟩
  have hx0W := H.mX hx0
  have hy0W := H.mY hy0
  have hx0F : 2 ≤ (outN D X x0).card := by
    by_contra hlt
    have : x0 ∈ X1 := Finset.mem_filter.mpr ⟨hx0, by omega⟩
    exact n2 H.free hx0W hy0W (hX1Y x0 this y0 hy0) hyx
  have hPX1 : ∀ a ∈ outN D X x0, a ∉ X1 := by
    intro a ha haX1
    obtain ⟨haX, hxa⟩ := mem_outN.mp ha
    exact n3 H.free hx0W (H.mX haX) hy0W hxa (hX1Y a haX1 y0 hy0) hyx
  have hFc : (X \ X1).card + X1.card = X.card := Finset.card_sdiff_add_card_eq_card (Finset.filter_subset _ _)
  have hPF : outN D X x0 ⊆ X \ X1 := fun a ha => Finset.mem_sdiff.mpr ⟨(mem_outN.mp ha).1, hPX1 a ha⟩
  have hx0F' : x0 ∈ X \ X1 := Finset.mem_sdiff.mpr ⟨hx0, fun h => by
    have := (Finset.mem_filter.mp h).2
    omega⟩
  by_cases h1 : X1.card = 1
  · -- `BR(4,1)` on `F = X ∖ X_1`
    have hFfree : QFree D (X \ X1) 4 := H.freeX.mono_set Finset.sdiff_subset
    have hFmin : ∀ f ∈ X \ X1, 1 ≤ (outN D (X \ X1) f).card := by
      intro f hf
      obtain ⟨hfX, hfX1⟩ := Finset.mem_sdiff.mp hf
      have h2 : 2 ≤ (outN D X f).card := by
        by_contra hlt
        exact hfX1 (Finset.mem_filter.mpr ⟨hfX, by omega⟩)
      have hsub : outN D X f ⊆ outN D (X \ X1) f ∪ X1 := by
        intro z hz
        by_cases hzX1 : z ∈ X1
        · exact Finset.mem_union_right _ hzX1
        · exact Finset.mem_union_left _
            (mem_outN.mpr ⟨Finset.mem_sdiff.mpr ⟨(mem_outN.mp hz).1, hzX1⟩, (mem_outN.mp hz).2⟩)
      have h3 := Finset.card_le_card hsub
      have h4 := Finset.card_union_le (outN D (X \ X1) f) X1
      omega
    have h5 := (reg1 hFfree hFmin (by omega)).1 x0 hx0F'
    have hsub : outN D X x0 ⊆ outN D (X \ X1) x0 := fun a ha => mem_outN.mpr ⟨hPF ha, (mem_outN.mp ha).2⟩
    have := Finset.card_le_card hsub
    omega
  · -- `|X_1| ≥ 2`: the last vertex of `P` has no room
    have hX1c : 2 ≤ X1.card := by
      have := Finset.card_pos.mpr hX1ne
      omega
    have hGc : ((X \ X1).erase x0).card + 1 = (X \ X1).card := Finset.card_erase_add_one hx0F'
    have hPG : outN D X x0 ⊆ (X \ X1).erase x0 := fun a ha =>
      Finset.mem_erase.mpr ⟨(ne_of_arc H.free (H.mX (mem_outN.mp ha).1) (mem_outN.mp ha).2).symm, hPF ha⟩
    have hPc := Finset.card_le_card hPG
    obtain ⟨a, ha, has⟩ := exists_sink (D := D) (T := outN D X x0) (q := 4)
      (H.freeX.mono_set outN_subset) (Finset.card_pos.mp (by omega)) (by omega)
    obtain ⟨haX, hxa⟩ := mem_outN.mp ha
    have ha2 : 2 ≤ (outN D X a).card := by
      by_contra hlt
      exact hPX1 a ha (Finset.mem_filter.mpr ⟨haX, by omega⟩)
    have hsub : outN D X a ⊆ ((X \ X1).erase x0) \ outN D X x0 := by
      intro z hz
      obtain ⟨hzX, haz⟩ := mem_outN.mp hz
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_erase.mpr ⟨?_, Finset.mem_sdiff.mpr ⟨hzX, ?_⟩⟩,
        fun hzP => has z hzP haz⟩
      · rintro rfl
        exact n2 H.free hx0W (H.mX haX) hxa haz
      · intro hz1
        exact n4 H.free hx0W (H.mX haX) (H.mX hzX) hy0W hxa haz (hX1Y z hz1 y0 hy0) hyx
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_sdiff_add_card_eq_card hPG
    omega

/-- **Lemma 7.** `(|X|, |Y|) = (6, 5)` with `c = 2` is impossible: kills `(6,5,3)`. -/
theorem kill653 (H : XY D X Y 2) (hX : X.card = 6) (hY : Y.card = 5) : False := by
  classical
  obtain ⟨y0, hy0, x, hx, hyx, hrest⟩ : ∃ y0 ∈ Y, ∃ x ∈ X, D y0 x = true ∧
      ∀ y ∈ Y, y ≠ y0 → ∃ z ∈ Y, D y z = true := by
    by_cases hall : ∀ y ∈ Y, ∃ z ∈ Y, D y z = true
    · obtain ⟨y0, hy0⟩ := Finset.card_pos.mp (by omega : 0 < Y.card)
      have hmin : ∀ y ∈ Y, 1 ≤ (outN D Y y).card := fun y hy => by
        obtain ⟨z, hz, hyz⟩ := hall y hy
        exact Finset.card_pos.mpr ⟨z, mem_outN.mpr ⟨hz, hyz⟩⟩
      have h1 := (reg1 H.freeY hmin hY).1 y0 hy0
      have h2 := H.rowY hy0
      obtain ⟨x, hx⟩ := Finset.card_pos.mp (show 0 < (outN D X y0).card by omega)
      exact ⟨y0, hy0, x, (mem_outN.mp hx).1, (mem_outN.mp hx).2, fun y hy _ => hall y hy⟩
    · push Not at hall
      obtain ⟨y0, hy0, hs⟩ := hall
      have hw : ∀ y ∈ Y, (∀ z ∈ Y, ¬ D y z = true) → 2 ≤ (outN D X y).card := by
        intro y hy hsy
        have h1 := H.rowY hy
        have h0 : (outN D Y y).card = 0 := by
          rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
          intro z hz
          exact hsy z (mem_outN.mp hz).1 (mem_outN.mp hz).2
        omega
      have hw0 := hw y0 hy0 hs
      obtain ⟨x, hx⟩ := Finset.card_pos.mp (show 0 < (outN D X y0).card by omega)
      refine ⟨y0, hy0, x, (mem_outN.mp hx).1, (mem_outN.mp hx).2, fun y hy hne => ?_⟩
      by_contra hno
      push Not at hno
      have := H.pair (by omega) hy hy0 hne (hw y hy hno) hw0
      omega
  obtain ⟨y1, hy1, y2, hy2, h10, h2, hne21, hne20⟩ := H.chain2 (by omega) (by omega) hy0 hrest
  have := H.back3 (by omega) (by omega) hy0 hy1 hy2 hx hyx h10 h2 hne21 hne20
  omega

/-- **Lemma 8, local half.** At `(|X|, |Y|) = (5, 5)` with `c = 1`, every `y` has a `Y`-head and no `y` heads `X`. -/
theorem loc554 (H : XY D X Y 1) (hX : X.card = 5) (hY : Y.card = 5) :
    (∀ y ∈ Y, ∃ z ∈ Y, D y z = true) ∧ ∀ y ∈ Y, ∀ x ∈ X, ¬ D y x = true := by
  classical
  by_cases hall : ∀ y ∈ Y, ∃ z ∈ Y, D y z = true
  · refine ⟨hall, fun y0 hy0 x hx hyx => ?_⟩
    obtain ⟨y1, hy1, y2, hy2, h10, h2, hne21, hne20⟩ :=
      H.chain2 (by omega) (by omega) hy0 (fun y hy _ => hall y hy)
    have := H.back3 (by omega) (by omega) hy0 hy1 hy2 hx hyx h10 h2 hne21 hne20
    omega
  · exfalso
    push Not at hall
    obtain ⟨y0, hy0, hs0⟩ := hall
    have hsinkX : ∀ s ∈ Y, (∀ z ∈ Y, ¬ D s z = true) → ∃ x ∈ X, D s x = true := by
      intro s hs hss
      have h1 := H.rowY hs
      have h0 : (outN D Y s).card = 0 := by
        rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
        intro z hz
        exact hss z (mem_outN.mp hz).1 (mem_outN.mp hz).2
      obtain ⟨x, hx⟩ := Finset.card_pos.mp (show 0 < (outN D X s).card by omega)
      exact ⟨x, (mem_outN.mp hx).1, (mem_outN.mp hx).2⟩
    have hsinkIn : ∀ s ∈ Y, (∀ z ∈ Y, ¬ D s z = true) → ∀ y ∈ Y, ¬ D y s = true := by
      intro s hs hss y hy hys
      obtain ⟨x, hx, hsx⟩ := hsinkX s hs hss
      have := H.back2 (by omega) (by omega) hs hy hx hsx hys
      omega
    -- `D[Y]` has no arc
    have hnoarc : ∀ y ∈ Y, ∀ z ∈ Y, ¬ D y z = true := by
      by_contra hcon
      push Not at hcon
      obtain ⟨y, hy, z, hz, hyz⟩ := hcon
      have hSmin : ∀ s ∈ Y.filter (fun t => ∃ y ∈ Y, D y t = true),
          1 ≤ (outN D (Y.filter (fun t => ∃ y ∈ Y, D y t = true)) s).card := by
        intro s hs
        obtain ⟨hsY, y', hy', hys⟩ := Finset.mem_filter.mp hs
        have hns : ¬ ∀ z ∈ Y, ¬ D s z = true := fun hss => hsinkIn s hsY hss y' hy' hys
        push Not at hns
        obtain ⟨z', hz', hsz⟩ := hns
        exact Finset.card_pos.mpr ⟨z', mem_outN.mpr ⟨Finset.mem_filter.mpr ⟨hz', s, hsY, hsz⟩, hsz⟩⟩
      have hSne : (Y.filter (fun t => ∃ y ∈ Y, D y t = true)).Nonempty :=
        ⟨z, Finset.mem_filter.mpr ⟨hz, y, hy, hyz⟩⟩
      have h5 := ch1 (H.freeY.mono_set (Finset.filter_subset _ _)) hSmin hSne
      have hSY : Y.filter (fun t => ∃ y ∈ Y, D y t = true) = Y :=
        Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _) (by omega)
      have hy0S : y0 ∈ Y.filter (fun t => ∃ y ∈ Y, D y t = true) := by rw [hSY]; exact hy0
      obtain ⟨-, y', hy', hy'0⟩ := Finset.mem_filter.mp hy0S
      exact hsinkIn y0 hy0 hs0 y' hy' hy'0
    -- every `y` is missed by at least two vertices of `X`
    have hm2 : ∀ y ∈ Y, 2 ≤ (X.filter (fun x => ¬ D x y = true)).card := by
      intro y hy
      obtain ⟨x, hx, hyx⟩ := hsinkX y hy (hnoarc y hy)
      have hxW := H.mX hx
      have hyW := H.mY hy
      have hsub : outN D Y x ⊆ Y.erase y := fun z hz => Finset.mem_erase.mpr
        ⟨by rintro rfl; exact n2 H.free hxW hyW (mem_outN.mp hz).2 hyx, (mem_outN.mp hz).1⟩
      have h1 := Finset.card_le_card hsub
      rw [Finset.card_erase_of_mem hy] at h1
      have h2 := H.rowX hx
      obtain ⟨x', hx'⟩ := Finset.card_pos.mp (show 0 < (outN D X x).card by omega)
      obtain ⟨hx'X, hxx'⟩ := mem_outN.mp hx'
      have m1 : x ∈ X.filter (fun x => ¬ D x y = true) :=
        Finset.mem_filter.mpr ⟨hx, fun h => n2 H.free hxW hyW h hyx⟩
      have m2 : x' ∈ X.filter (fun x => ¬ D x y = true) :=
        Finset.mem_filter.mpr ⟨hx'X, fun h => n3 H.free hxW (H.mX hx'X) hyW hxx' h hyx⟩
      exact two_le m1 m2 (ne_of_arc H.free (H.mX hx'X) hxx')
    have hdc : ∑ x ∈ X, (miss D Y x).card = ∑ y ∈ Y, (X.filter (fun x => ¬ D x y = true)).card :=
      dcount X Y (fun x y => ¬ D x y = true)
    have hM : ∑ _y ∈ Y, 2 ≤ ∑ y ∈ Y, (X.filter (fun x => ¬ D x y = true)).card := Finset.sum_le_sum hm2
    rw [sum_const', hY] at hM
    have hmissle : ∀ x ∈ X, (miss D Y x).card ≤ (outN D X x).card := fun x hx => by
      have := card_miss D Y x
      have := H.rowX hx
      omega
    have hinner := Finset.sum_le_sum hmissle
    have hoi : ∀ x ∈ X, (outN D X x).card + (inN D X x).card ≤ 4 := fun x hx => by
      have := out_in_le H.freeX hx
      omega
    have hall4 : ∀ x ∈ X, (outN D X x).card + (inN D X x).card = 4 := by
      have h1 := Finset.sum_le_sum hoi
      have h2 : ∑ x ∈ X, ((outN D X x).card + (inN D X x).card) = 2 * ∑ x ∈ X, (outN D X x).card := by
        rw [Finset.sum_add_distrib, ← sum_out_in]
        omega
      rw [sum_const', hX] at h1
      have heq : ∑ x ∈ X, ((outN D X x).card + (inN D X x).card) = ∑ _x ∈ X, 4 := by
        rw [sum_const', hX]
        omega
      exact (Finset.sum_eq_sum_iff_of_le hoi).mp heq
    -- `D[X]` has a sink
    obtain ⟨σ, hσ, hσs⟩ : ∃ σ ∈ X, ∀ z ∈ X, ¬ D σ z = true := by
      by_contra hno
      push Not at hno
      have hmin : ∀ x ∈ X, 1 ≤ (outN D X x).card := fun x hx => by
        obtain ⟨z, hz, hxz⟩ := hno x hx
        exact Finset.card_pos.mpr ⟨z, mem_outN.mpr ⟨hz, hxz⟩⟩
      obtain ⟨ho, hi⟩ := reg1 H.freeX hmin hX
      obtain ⟨x, hx⟩ := Finset.card_pos.mp (show 0 < X.card by omega)
      have := hall4 x hx
      rw [ho x hx, hi x hx] at this
      omega
    have h0 : (outN D X σ).card = 0 := by
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro z hz
      exact hσs z (mem_outN.mp hz).1 (mem_outN.mp hz).2
    have hσY : ∀ y ∈ Y, D σ y = true := by
      have h1 := H.rowX hσ
      have heq : outN D Y σ = Y := Finset.eq_of_subset_of_card_le outN_subset (by omega)
      intro y hy
      have : y ∈ outN D Y σ := by rw [heq]; exact hy
      exact (mem_outN.mp this).2
    have hinX : ∀ x ∈ X, x ≠ σ → D x σ = true := by
      have hsub : inN D X σ ⊆ X.erase σ := fun z hz =>
        Finset.mem_erase.mpr ⟨ne_of_arc H.freeX hσ (mem_inN.mp hz).2, (mem_inN.mp hz).1⟩
      have h4 := hall4 σ hσ
      have heq := Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_erase_of_mem hσ]; omega)
      intro x hx hne
      have : x ∈ inN D X σ := by rw [heq]; exact Finset.mem_erase.mpr ⟨hne, hx⟩
      exact (mem_inN.mp this).2
    obtain ⟨x, hx, hyx⟩ := hsinkX y0 hy0 hs0
    by_cases hxσ : x = σ
    · rw [hxσ] at hyx
      exact n2 H.free (H.mX hσ) (H.mY hy0) (hσY y0 hy0) hyx
    · exact n3 H.free (H.mX hx) (H.mX hσ) (H.mY hy0) (hinX x hx hxσ) (hσY y0 hy0) hyx

end XY

end LeanCH.BR.BR45
