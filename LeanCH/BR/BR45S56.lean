import LeanCH.BR.BR45Base

/-!
# BR(4,5), Lemma 9: `S(5,6)` (Lean 4.35.0)

Paper: `checkpoints/boundary_20261111/BR45_attempt_subagent.md` §4 (Lemma 9), with the repairs of
`BR45_audit_subagent.md` §3.

**`s56`.** There is no `4`-free digraph on `X ⊔ Y`, `|X| = 5`, `|Y| = 6`, in which every `x ∈ X` has at least 5 heads
in `X ∪ Y` and every `y ∈ Y` has at least 2 heads in `X ∪ Y`.

The case split is restructured (same statement, shorter in Lean; the `(★)` test and the sub-cases on the number of
sinks are not needed).

* **No sink in `D[X]`** (`S56.no_cyc`). `BR(4,1)` on the 5-set `X` (`reg1`) gives exactly one `X`-head per `x`, so
  every `x` misses at most 2 vertices of `Y`. If `y → x` then `x, x⁺, x⁺⁺` are distinct and all miss `y`; counting
  misses, `B = {y : y heads X}` has `|B| ≤ 3`. For `y ∈ B` with `y → x`, `x` misses the `Y`-in-ball of radius 2 of
  `y`, so `y` has at most one `Y`-in-neighbour and that one is a `Y`-source. The non-sources of `Y ∖ B` are closed
  with min out 2, hence empty (`ch2`). So `Y ∖ B` consists of sources whose `≥ 2` heads lie in `B`:
  `2 (6 − |B|) ≤ |B| ≤ 3`, a contradiction.
* **A sink in `D[X]`** (`S56.no_acyc`). `Σ` = sinks of `D[X]` (each misses at most one vertex of `Y`);
  `Near` = vertices of `X` with a sink in their closed `X`-out-neighbourhood; `Far = X ∖ Near`;
  `B_near = {y : y heads Near}`. By (K) every `y ∈ B_near` is a `Y`-source and the miss of a sink, so
  `|B_near| ≤ |Σ|`. Put `Q = Y ∖ B_near`, `T = Q ∪ Far`. `Q`-rows keep all their heads in `T`; a `Far`-row loses only
  heads in `Near ∖ Σ` and `B_near`, so it keeps at least `5 − |Near| = |Far|`.
  - `Far = ∅`: `Q` is closed with min out 2, so `Q = ∅` and `6 = |B_near| ≤ |Σ| ≤ 5`.
  - `|Far| ≥ 2`: all rows of `T` keep `≥ 2`, so `|T| ≥ 9`; as `|Far| ≤ 3` (the sink of `D[X ∖ Σ]` is near),
    `|T| = 9`, `|Far| = 3`, and `BR(4,2)` (`reg2`) contradicts the `Far`-rows keeping 3.
  - `Far = {x}`: `|T| ≤ 7`, so `x` keeps `≤ 1`, forcing `|B_near| = |Σ|`, i.e. `B_near` is the set of all sink
    misses. `x` heads some `n ∈ Near ∖ Σ`, `n → σ ∈ Σ`; a `y ∈ Q` heading `x` would be missed by `σ` (4-cycle), so
    it would lie in `B_near`. Hence `Q` is closed with min out 2, `Q = ∅`, and again `6 ≤ |Σ| ≤ 5`.
-/

set_option linter.style.longLine false

namespace LeanCH.BR.BR45

open LeanCH.BR.BRq2 LeanCH.BR.BRq3 CH

/-- The vertices of `Y` not headed by `x`. -/
def miss (D : CH.Digraph) (Y : Finset ℕ) (x : ℕ) : Finset ℕ := Y.filter (fun y => ¬ D x y = true)

theorem card_miss (D : CH.Digraph) (Y : Finset ℕ) (x : ℕ) :
    (miss D Y x).card + (outN D Y x).card = Y.card := by
  classical
  unfold miss outN
  rw [add_comm]
  exact Finset.card_filter_add_card_filter_not (s := Y) (fun y => D x y = true)

/-- The hypotheses of `S(5,6)`. -/
structure S56 (D : CH.Digraph) (X Y : Finset ℕ) : Prop where
  disj : Disjoint X Y
  cX : X.card = 5
  cY : Y.card = 6
  free : QFree D (X ∪ Y) 4
  outX : ∀ x ∈ X, 5 ≤ (outN D (X ∪ Y) x).card
  outY : ∀ y ∈ Y, 2 ≤ (outN D (X ∪ Y) y).card

namespace S56

variable {D : CH.Digraph} {X Y : Finset ℕ}

theorem mX (_H : S56 D X Y) {x : ℕ} (hx : x ∈ X) : x ∈ X ∪ Y := Finset.mem_union_left _ hx

theorem mY (_H : S56 D X Y) {y : ℕ} (hy : y ∈ Y) : y ∈ X ∪ Y := Finset.mem_union_right _ hy

theorem miss_le (H : S56 D X Y) {x : ℕ} (hx : x ∈ X) : (miss D Y x).card ≤ 1 + (outN D X x).card := by
  have h1 := H.outX x hx
  rw [card_outN_union H.disj] at h1
  have h2 := card_miss D Y x
  have := H.cY
  omega

/-- `D[X]` has no sink: contradiction. -/
theorem no_cyc (H : S56 D X Y) (hns : ∀ x ∈ X, ∃ z ∈ X, D x z = true) : False := by
  classical
  have hfX : QFree D X 4 := H.free.mono_set Finset.subset_union_left
  have hpos : ∀ x ∈ X, 1 ≤ (outN D X x).card := fun x hx => by
    obtain ⟨z, hz, hxz⟩ := hns x hx
    exact Finset.card_pos.mpr ⟨z, mem_outN.mpr ⟨hz, hxz⟩⟩
  obtain ⟨hout1, -⟩ := reg1 hfX hpos H.cX
  have hm2 : ∀ x ∈ X, (miss D Y x).card ≤ 2 := fun x hx => by
    have := H.miss_le hx
    have := hout1 x hx
    omega
  set B := Y.filter (fun y => ∃ x ∈ X, D y x = true)
  have hBY : B ⊆ Y := Finset.filter_subset _ _
  have hB3 : ∀ y ∈ B, 3 ≤ (X.filter (fun x => ¬ D x y = true)).card := by
    intro y hy
    obtain ⟨hyY, x, hx, hyx⟩ := Finset.mem_filter.mp hy
    obtain ⟨x1, hx1, hxx1⟩ := hns x hx
    obtain ⟨x2, hx2, hx1x2⟩ := hns x1 hx1
    have hyW := H.mY hyY
    refine three_le (a := x) (b := x1) (c := x2) ?_ ?_ ?_ ?_ ?_ ?_
    · exact Finset.mem_filter.mpr ⟨hx, fun h => n2 H.free (H.mX hx) hyW h hyx⟩
    · exact Finset.mem_filter.mpr ⟨hx1, fun h => n3 H.free (H.mX hx) (H.mX hx1) hyW hxx1 h hyx⟩
    · exact Finset.mem_filter.mpr
        ⟨hx2, fun h => n4 H.free (H.mX hx) (H.mX hx1) (H.mX hx2) hyW hxx1 hx1x2 h hyx⟩
    · exact ne_of_arc H.free (H.mX hx1) hxx1
    · rintro rfl; exact n2 H.free (H.mX hx) (H.mX hx1) hxx1 hx1x2
    · exact ne_of_arc H.free (H.mX hx2) hx1x2
  have hBcard : B.card ≤ 3 := by
    have h1 : ∑ _y ∈ B, 3 ≤ ∑ y ∈ B, (X.filter (fun x => ¬ D x y = true)).card := Finset.sum_le_sum hB3
    have h2 : ∑ x ∈ X, (B.filter (fun y => ¬ D x y = true)).card ≤ ∑ _x ∈ X, 2 :=
      Finset.sum_le_sum (fun x hx =>
        (Finset.card_le_card (Finset.filter_subset_filter _ hBY)).trans (hm2 x hx))
    rw [dcount X B (fun x y => ¬ D x y = true)] at h2
    rw [sum_const'] at h1 h2
    have := H.cX
    omega
  have hBin : ∀ y ∈ B, (inN D Y y).card ≤ 1 ∧ ∀ y' ∈ inN D Y y, inN D Y y' = ∅ := by
    intro y hy
    obtain ⟨hyY, x, hx, hyx⟩ := Finset.mem_filter.mp hy
    have hyW := H.mY hyY
    have hxW := H.mX hx
    have m0 : y ∈ miss D Y x := Finset.mem_filter.mpr ⟨hyY, fun h => n2 H.free hxW hyW h hyx⟩
    have m1 : ∀ y' ∈ inN D Y y, y' ∈ miss D Y x := fun y' hy' => by
      obtain ⟨hy'Y, hy'y⟩ := mem_inN.mp hy'
      exact Finset.mem_filter.mpr ⟨hy'Y, fun h => n3 H.free hxW (H.mY hy'Y) hyW h hy'y hyx⟩
    have d1 : ∀ y' ∈ inN D Y y, y' ≠ y := fun y' hy' => ne_of_arc H.free hyW (mem_inN.mp hy').2
    constructor
    · rw [Finset.card_le_one]
      intro a ha b hb
      by_contra hab
      have := three_le m0 (m1 a ha) (m1 b hb) (d1 a ha).symm (d1 b hb).symm hab
      have := hm2 x hx
      omega
    · intro y' hy'
      rw [Finset.eq_empty_iff_forall_notMem]
      intro y'' hy''
      obtain ⟨hy'Y, hy'y⟩ := mem_inN.mp hy'
      obtain ⟨hy''Y, hy''y'⟩ := mem_inN.mp hy''
      have m2 : y'' ∈ miss D Y x := Finset.mem_filter.mpr
        ⟨hy''Y, fun h => n4 H.free hxW (H.mY hy''Y) (H.mY hy'Y) hyW h hy''y' hy'y hyx⟩
      have e1 : y'' ≠ y' := ne_of_arc H.free (H.mY hy'Y) hy''y'
      have e2 : y'' ≠ y := by rintro rfl; exact n2 H.free (H.mY hy'Y) hyW hy'y hy''y'
      have := three_le m0 (m1 y' hy') m2 (d1 y' hy').symm e2.symm e1.symm
      have := hm2 x hx
      omega
  -- the non-sources outside `B` are closed with min out 2
  set S := Y.filter (fun y => y ∉ B ∧ (inN D Y y).Nonempty)
  have hS : S = ∅ := by
    by_contra hne
    have hSY : S ⊆ Y := Finset.filter_subset _ _
    have hfS : QFree D S 4 := H.free.mono_set (hSY.trans Finset.subset_union_right)
    have hmin : ∀ y ∈ S, 2 ≤ (outN D S y).card := by
      intro y hy
      obtain ⟨hyY, hyB, hyin⟩ := Finset.mem_filter.mp hy
      refine (H.outY y hyY).trans (Finset.card_le_card ?_)
      intro z hz
      obtain ⟨hzW, hyz⟩ := mem_outN.mp hz
      rcases Finset.mem_union.mp hzW with hzX | hzY
      · exact absurd (Finset.mem_filter.mpr ⟨hyY, z, hzX, hyz⟩) hyB
      · refine mem_outN.mpr ⟨Finset.mem_filter.mpr ⟨hzY, ?_, ⟨y, mem_inN.mpr ⟨hyY, hyz⟩⟩⟩, hyz⟩
        intro hzB
        have := (hBin z hzB).2 y (mem_inN.mpr ⟨hyY, hyz⟩)
        rw [this] at hyin
        exact Finset.not_nonempty_empty hyin
    have h9 := ch2 hfS hmin (Finset.nonempty_iff_ne_empty.mpr hne)
    have := Finset.card_le_card hSY
    have := H.cY
    omega
  have hsrc : ∀ y ∈ Y, y ∉ B → inN D Y y = ∅ := by
    intro y hyY hyB
    by_contra hne
    have : y ∈ S := Finset.mem_filter.mpr ⟨hyY, hyB, Finset.nonempty_iff_ne_empty.mpr hne⟩
    rw [hS] at this
    exact Finset.notMem_empty _ this
  have hY0 : ∀ y ∈ Y \ B, 2 ≤ (B.filter (fun b => D y b = true)).card := by
    intro y hy
    obtain ⟨hyY, hyB⟩ := Finset.mem_sdiff.mp hy
    refine (H.outY y hyY).trans (Finset.card_le_card ?_)
    intro z hz
    obtain ⟨hzW, hyz⟩ := mem_outN.mp hz
    rcases Finset.mem_union.mp hzW with hzX | hzY
    · exact absurd (Finset.mem_filter.mpr ⟨hyY, z, hzX, hyz⟩) hyB
    · refine Finset.mem_filter.mpr ⟨?_, hyz⟩
      by_contra hzB
      have := hsrc z hzY hzB
      have hin : y ∈ inN D Y z := mem_inN.mpr ⟨hyY, hyz⟩
      rw [this] at hin
      exact Finset.notMem_empty _ hin
  have h1 : ∑ _y ∈ Y \ B, 2 ≤ ∑ y ∈ Y \ B, (B.filter (fun b => D y b = true)).card :=
    Finset.sum_le_sum hY0
  have h2 : ∑ b ∈ B, ((Y \ B).filter (fun y => D y b = true)).card ≤ ∑ _b ∈ B, 1 :=
    Finset.sum_le_sum (fun b hb =>
      (Finset.card_le_card (Finset.filter_subset_filter _ Finset.sdiff_subset)).trans (hBin b hb).1)
  rw [dcount (Y \ B) B (fun y b => D y b = true)] at h1
  rw [sum_const'] at h1 h2
  have h3 := Finset.card_sdiff_of_subset hBY
  have h4 := Finset.card_le_card hBY
  have := H.cY
  omega

/-- `D[X]` has a sink: contradiction. -/
theorem no_acyc (H : S56 D X Y) {σ0 : ℕ} (hσ0 : σ0 ∈ X) (hsink0 : ∀ z ∈ X, ¬ D σ0 z = true) : False := by
  classical
  have hfX : QFree D X 4 := H.free.mono_set Finset.subset_union_left
  set Sg := X.filter (fun x => ∀ z ∈ X, ¬ D x z = true)
  set Near := X.filter (fun x => x ∈ Sg ∨ ∃ σ ∈ Sg, D x σ = true)
  set Far := X \ Near
  have hSgX : Sg ⊆ X := Finset.filter_subset _ _
  have hσ0S : σ0 ∈ Sg := Finset.mem_filter.mpr ⟨hσ0, hsink0⟩
  have hSgNear : Sg ⊆ Near := fun x hx => Finset.mem_filter.mpr ⟨hSgX hx, Or.inl hx⟩
  have hNearX : Near ⊆ X := Finset.filter_subset _ _
  have hFarX : Far ⊆ X := Finset.sdiff_subset
  have hmiss1 : ∀ σ ∈ Sg, (miss D Y σ).card ≤ 1 := by
    intro σ hσ
    obtain ⟨hσX, hs⟩ := Finset.mem_filter.mp hσ
    have := H.miss_le hσX
    have h0 : (outN D X σ).card = 0 := by
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro z hz
      exact hs z (mem_outN.mp hz).1 (mem_outN.mp hz).2
    omega
  set Bn := Y.filter (fun y => ∃ x ∈ Near, D y x = true)
  -- (K)
  have hK : ∀ y ∈ Bn, (∃ σ ∈ Sg, y ∈ miss D Y σ) ∧ inN D Y y = ∅ := by
    intro y hy
    obtain ⟨hyY, x, hxN, hyx⟩ := Finset.mem_filter.mp hy
    obtain ⟨hxX, hx⟩ := Finset.mem_filter.mp hxN
    have hyW := H.mY hyY
    have hxW := H.mX hxX
    obtain ⟨σ, hσ, hxσ⟩ : ∃ σ ∈ Sg, x = σ ∨ D x σ = true := by
      rcases hx with h | ⟨σ, hσ, h⟩
      · exact ⟨x, h, Or.inl rfl⟩
      · exact ⟨σ, hσ, Or.inr h⟩
    have hσW := H.mX (hSgX hσ)
    have hσy : ¬ D σ y = true := by
      intro h
      rcases hxσ with hxσ | hxσ
      · rw [← hxσ] at h; exact n2 H.free hxW hyW h hyx
      · exact n3 H.free hxW hσW hyW hxσ h hyx
    have hym : y ∈ miss D Y σ := Finset.mem_filter.mpr ⟨hyY, hσy⟩
    refine ⟨⟨σ, hσ, hym⟩, ?_⟩
    rw [Finset.eq_empty_iff_forall_notMem]
    intro y' hy'
    obtain ⟨hy'Y, hy'y⟩ := mem_inN.mp hy'
    have hne : y' ≠ y := ne_of_arc H.free hyW hy'y
    have hσy' : D σ y' = true := by
      by_contra h
      have hy'm : y' ∈ miss D Y σ := Finset.mem_filter.mpr ⟨hy'Y, h⟩
      exact hne (Finset.card_le_one.mp (hmiss1 σ hσ) y' hy'm y hym)
    rcases hxσ with hxσ | hxσ
    · rw [← hxσ] at hσy'; exact n3 H.free hxW (H.mY hy'Y) hyW hσy' hy'y hyx
    · exact n4 H.free hxW hσW (H.mY hy'Y) hyW hxσ hσy' hy'y hyx
  set MS := Sg.biUnion (fun σ => miss D Y σ)
  have hBnMS : Bn ⊆ MS := fun y hy => by
    obtain ⟨⟨σ, hσ, hm⟩, -⟩ := hK y hy
    exact Finset.mem_biUnion.mpr ⟨σ, hσ, hm⟩
  have hMScard : MS.card ≤ Sg.card := by
    refine Finset.card_biUnion_le.trans ?_
    calc ∑ σ ∈ Sg, (miss D Y σ).card ≤ ∑ _σ ∈ Sg, 1 := Finset.sum_le_sum hmiss1
      _ = Sg.card := by simp
  have hBncard : Bn.card ≤ Sg.card := (Finset.card_le_card hBnMS).trans hMScard
  have hSgc := Finset.card_le_card hSgX
  have hcX := H.cX
  have hcY := H.cY
  set Q := Y \ Bn
  have hQY : Q ⊆ Y := Finset.sdiff_subset
  set T := Q ∪ Far
  have hTW : T ⊆ X ∪ Y :=
    Finset.union_subset (hQY.trans Finset.subset_union_right) (hFarX.trans Finset.subset_union_left)
  have hfT : QFree D T 4 := H.free.mono_set hTW
  have hdQF : Disjoint Q Far := (H.disj.mono hFarX hQY).symm
  have hTc : T.card = Q.card + Far.card := Finset.card_union_of_disjoint hdQF
  have hQc := Finset.card_le_card hQY
  have hQrow : ∀ y ∈ Q, outN D (X ∪ Y) y ⊆ outN D T y := by
    intro y hy z hz
    obtain ⟨hyY, hyB⟩ := Finset.mem_sdiff.mp hy
    obtain ⟨hzW, hyz⟩ := mem_outN.mp hz
    refine mem_outN.mpr ⟨?_, hyz⟩
    rcases Finset.mem_union.mp hzW with hzX | hzY
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr
        ⟨hzX, fun hzN => hyB (Finset.mem_filter.mpr ⟨hyY, z, hzN, hyz⟩)⟩)
    · refine Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hzY, fun hzB => ?_⟩)
      have := (hK z hzB).2
      have hin : y ∈ inN D Y z := mem_inN.mpr ⟨hyY, hyz⟩
      rw [this] at hin
      exact Finset.notMem_empty _ hin
  have hQkeep : ∀ y ∈ Q, 2 ≤ (outN D T y).card := fun y hy =>
    (H.outY y (hQY hy)).trans (Finset.card_le_card (hQrow y hy))
  have hNF : Near.card + Far.card = 5 := by
    have h1 : Far.card = X.card - Near.card := Finset.card_sdiff_of_subset hNearX
    have h2 := Finset.card_le_card hNearX
    omega
  have hSN := Finset.card_le_card hSgNear
  have hFkeep : ∀ x ∈ Far, 5 ≤ (outN D T x).card + (Near.card - Sg.card) + Bn.card := by
    intro x hx
    obtain ⟨hxX, hxN⟩ := Finset.mem_sdiff.mp hx
    have hsub : outN D (X ∪ Y) x ⊆ outN D T x ∪ ((Near \ Sg) ∪ Bn) := by
      intro z hz
      obtain ⟨hzW, hxz⟩ := mem_outN.mp hz
      by_cases hzT : z ∈ T
      · exact Finset.mem_union_left _ (mem_outN.mpr ⟨hzT, hxz⟩)
      · refine Finset.mem_union_right _ ?_
        rcases Finset.mem_union.mp hzW with hzX | hzY
        · refine Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨?_, ?_⟩)
          · by_contra hzN
            exact hzT (Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hzX, hzN⟩))
          · intro hzS
            exact hxN (Finset.mem_filter.mpr ⟨hxX, Or.inr ⟨z, hzS, hxz⟩⟩)
        · refine Finset.mem_union_right _ ?_
          by_contra hzB
          exact hzT (Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hzY, hzB⟩))
    have h1 := (H.outX x hxX).trans (Finset.card_le_card hsub)
    have h2 := Finset.card_union_le (outN D T x) ((Near \ Sg) ∪ Bn)
    have h3 := Finset.card_union_le (Near \ Sg) Bn
    have h4 := Finset.card_sdiff_of_subset hSgNear
    omega
  -- `Q = ∅` is impossible
  have hQne : Q ≠ ∅ := by
    intro hQe
    have h1 : Y ⊆ Bn := Finset.sdiff_eq_empty_iff_subset.mp hQe
    have := Finset.card_le_card h1
    omega
  rcases (by omega : Far.card = 0 ∨ Far.card = 1 ∨ 2 ≤ Far.card) with h0 | h1 | h2
  · -- `Far = ∅`
    have hFe : Far = ∅ := Finset.card_eq_zero.mp h0
    have hmin : ∀ y ∈ T, 2 ≤ (outN D T y).card := by
      intro y hy
      rcases Finset.mem_union.mp hy with h | h
      · exact hQkeep y h
      · rw [hFe] at h
        exact absurd h (Finset.notMem_empty _)
    obtain ⟨y, hy⟩ := Finset.nonempty_iff_ne_empty.mpr hQne
    have h9 := ch2 hfT hmin ⟨y, Finset.mem_union_left _ hy⟩
    omega
  · -- `Far = {x}`
    obtain ⟨x, hFx⟩ := Finset.card_eq_one.mp h1
    have hxF : x ∈ Far := by rw [hFx]; exact Finset.mem_singleton_self x
    obtain ⟨hxX, hxN⟩ := Finset.mem_sdiff.mp hxF
    have hx1 : (outN D T x).card ≤ 1 := by
      by_contra hgt
      have hmin : ∀ y ∈ T, 2 ≤ (outN D T y).card := by
        intro y hy
        rcases Finset.mem_union.mp hy with h | h
        · exact hQkeep y h
        · rw [hFx, Finset.mem_singleton] at h
          rw [h]; omega
      have h9 := ch2 hfT hmin ⟨x, Finset.mem_union_right _ hxF⟩
      omega
    have hBS : Sg.card ≤ Bn.card := by
      have := hFkeep x hxF
      omega
    have hBnMSeq : Bn = MS := Finset.eq_of_subset_of_card_le hBnMS (by omega)
    have hxS : x ∉ Sg := fun h => hxN (hSgNear h)
    obtain ⟨n, hnX, hxn⟩ : ∃ n ∈ X, D x n = true := by
      by_contra hcon
      push Not at hcon
      exact hxS (Finset.mem_filter.mpr ⟨hxX, fun z hz => hcon z hz⟩)
    have hnS : n ∉ Sg := fun h => hxN (Finset.mem_filter.mpr ⟨hxX, Or.inr ⟨n, h, hxn⟩⟩)
    have hnx : n ≠ x := (ne_of_arc H.free (H.mX hnX) hxn).symm
    have hnN : n ∈ Near := by
      by_contra h
      have hnF : n ∈ Far := Finset.mem_sdiff.mpr ⟨hnX, h⟩
      rw [hFx, Finset.mem_singleton] at hnF
      exact hnx hnF
    obtain ⟨σ, hσ, hnσ⟩ : ∃ σ ∈ Sg, D n σ = true := by
      rcases (Finset.mem_filter.mp hnN).2 with h | h
      · exact absurd h hnS
      · exact h
    have hQx : ∀ y ∈ Q, ¬ D y x = true := by
      intro y hy hyx
      obtain ⟨hyY, hyB⟩ := Finset.mem_sdiff.mp hy
      apply hyB
      rw [hBnMSeq]
      refine Finset.mem_biUnion.mpr ⟨σ, hσ, Finset.mem_filter.mpr ⟨hyY, fun h => ?_⟩⟩
      exact n4 H.free (H.mX hxX) (H.mX hnX) (H.mX (hSgX hσ)) (H.mY hyY) hxn hnσ h hyx
    have hfQ : QFree D Q 4 := H.free.mono_set (hQY.trans Finset.subset_union_right)
    have hmin : ∀ y ∈ Q, 2 ≤ (outN D Q y).card := by
      intro y hy
      refine (hQkeep y hy).trans (Finset.card_le_card ?_)
      intro z hz
      obtain ⟨hzT, hyz⟩ := mem_outN.mp hz
      rcases Finset.mem_union.mp hzT with h | h
      · exact mem_outN.mpr ⟨h, hyz⟩
      · rw [hFx, Finset.mem_singleton] at h
        rw [h] at hyz
        exact absurd hyz (hQx y hy)
    have := ch2 hfQ hmin (Finset.nonempty_iff_ne_empty.mpr hQne)
    omega
  · -- `|Far| ≥ 2`
    have hmin : ∀ y ∈ T, 2 ≤ (outN D T y).card := by
      intro y hy
      rcases Finset.mem_union.mp hy with h | h
      · exact hQkeep y h
      · have := hFkeep y h
        omega
    obtain ⟨x, hx⟩ : Far.Nonempty := Finset.card_pos.mp (by omega)
    have h9 := ch2 hfT hmin ⟨x, Finset.mem_union_right _ hx⟩
    -- the sink of `D[X ∖ Σ]` is near, so `|Far| ≤ 3`
    have hF3 : Far.card ≤ 3 := by
      have hNne : (X \ Sg).Nonempty :=
        ⟨x, Finset.mem_sdiff.mpr ⟨hFarX hx, fun h => (Finset.mem_sdiff.mp hx).2 (hSgNear h)⟩⟩
      have hNc := Finset.card_sdiff_of_subset hSgX
      have hSpos : 1 ≤ Sg.card := Finset.card_pos.mpr ⟨σ0, hσ0S⟩
      obtain ⟨t, ht, hts⟩ := exists_sink (D := D) (T := X \ Sg) (q := 4)
        (hfX.mono_set Finset.sdiff_subset) hNne (by omega)
      obtain ⟨htX, htS⟩ := Finset.mem_sdiff.mp ht
      obtain ⟨z, hzX, htz⟩ : ∃ z ∈ X, D t z = true := by
        by_contra hcon
        push Not at hcon
        exact htS (Finset.mem_filter.mpr ⟨htX, fun z hz => hcon z hz⟩)
      have hzS : z ∈ Sg := by
        by_contra h
        exact hts z (Finset.mem_sdiff.mpr ⟨hzX, h⟩) htz
      have htN : t ∈ Near := Finset.mem_filter.mpr ⟨htX, Or.inr ⟨z, hzS, htz⟩⟩
      have hsub : Far ⊆ (X \ Sg).erase t := by
        intro a ha
        obtain ⟨haX, haN⟩ := Finset.mem_sdiff.mp ha
        refine Finset.mem_erase.mpr ⟨?_, Finset.mem_sdiff.mpr ⟨haX, fun h => haN (hSgNear h)⟩⟩
        rintro rfl
        exact haN htN
      have := Finset.card_le_card hsub
      rw [Finset.card_erase_of_mem ht] at this
      omega
    have hT9 : T.card = 9 := by omega
    have h2' := (reg2 hfT hmin hT9).1 x (Finset.mem_union_right _ hx)
    have := hFkeep x hx
    omega

theorem false_of (H : S56 D X Y) : False := by
  classical
  by_cases h : ∃ σ ∈ X, ∀ z ∈ X, ¬ D σ z = true
  · obtain ⟨σ, hσ, hs⟩ := h
    exact H.no_acyc hσ hs
  · push Not at h
    exact H.no_cyc h

end S56

/-- **Lemma 9, `S(5,6)`.** No `4`-free digraph on `X ⊔ Y` with `|X| = 5`, `|Y| = 6` has at least 5 heads (in
`X ∪ Y`) on every `X`-row and at least 2 on every `Y`-row. -/
theorem s56 {D : CH.Digraph} {X Y : Finset ℕ} (hdisj : Disjoint X Y) (hX : X.card = 5) (hY : Y.card = 6)
    (hfree : QFree D (X ∪ Y) 4) (hXout : ∀ x ∈ X, 5 ≤ (outN D (X ∪ Y) x).card)
    (hYout : ∀ y ∈ Y, 2 ≤ (outN D (X ∪ Y) y).card) : False :=
  S56.false_of ⟨hdisj, hX, hY, hfree, hXout, hYout⟩

end LeanCH.BR.BR45
