import LeanCH.BR.BR45S56

/-!
# BR(4,5), profile kills, part A: the local `X ⊔ Y` setting (Lean 4.35.0)

Paper: `checkpoints/boundary_20261111/BR45_attempt_subagent.md` §2–§4; audit `BR45_audit_subagent.md` §2–§3.

`XY D X Y c`: `X = N_1(u)`, `Y = N_2(u)` seen locally. `D` is `4`-free on `X ⊔ Y`, every `X`-row has at least 5 heads
in `X ∪ Y`, every `Y`-row at least `c` (in the application `c = 5 − n_3`), and every `y ∈ Y` has a parent in `X`.

* `XY.tight54` (**Lemma 2, item 5**): at `(|X|, |Y|) = (5, 4)`, `D[X]` is 1-regular (out and in) and every `x` heads
  all of `Y`.
* `XY.kill54` (**Lemma 2, item 6**): at `(5, 4)`, `c = 0` (so `n_3 ≥ 5`): kills `(5,4,3)`, `(5,4,4)`.
* `XY.kill10` (**Lemma 4**, restructured): `|X| + |Y| = 10`, `|X| ≥ 4`, `c = 2` is impossible: kills `(5,5,3)` and
  `(6,4,3)`. Every `a ∈ X ∪ Y` has an in-neighbour in `Y` (9-vertex `BR(4,2)` test on `(X ∪ Y) ∖ {a}`), so every
  `x` misses three vertices `y → x`, `y′ → y`, `y″ → y′` of `Y`, giving `inner(x) ≥ |X| − 2`, against
  `inner + in_X ≤ |X| − 1`. (The Hamiltonian-cycle step of the note is not needed.)
* `XY.kill_n4` (**Lemma 5**): `|Y| = 4`, `|X| ≤ 7`, `c = 2` is impossible: kills `(7,4,3)` (and `(6,4,3)`).
* `XY.kill56` (**Lemma 9 applied**): `(5, 6)` with `c = 2` is impossible: kills `(5,6,3)`.
* `XY.back_arc` (**Lemma 3**, in the form used): for a back arc `y_0 → x` and sets `D_1 ⊆ D_2 ⊆ Y` inside the
  `Y`-in-balls of radius 1 and 2 of `y_0`, `12 + |D_1| + |D_2| ≤ |X| + 2|Y|` (when `|X| ≤ 6` and `|Y| < 5 + |D_2|`).
-/

set_option linter.style.longLine false

namespace LeanCH.BR.BR45

open LeanCH.BR.BRq2 LeanCH.BR.BRq3 CH

variable {D : CH.Digraph}

theorem outN_erase (S : Finset ℕ) (a x : ℕ) : outN D (S.erase a) x = (outN D S x).erase a := by
  classical
  unfold outN
  exact Finset.filter_erase _ _ _

/-- In a `4`-free set, out- and in-neighbourhoods of `x` are disjoint and avoid `x`. -/
theorem out_in_le {S : Finset ℕ} (hfree : QFree D S 4) {x : ℕ} (hx : x ∈ S) :
    (outN D S x).card + (inN D S x).card + 1 ≤ S.card := by
  classical
  have hd : Disjoint (outN D S x) (inN D S x) := by
    rw [Finset.disjoint_left]
    intro z hz hz'
    exact n2 hfree hx (mem_outN.mp hz).1 (mem_outN.mp hz).2 (mem_inN.mp hz').2
  have hsub : outN D S x ∪ inN D S x ⊆ S.erase x := by
    intro z hz
    rcases Finset.mem_union.mp hz with h | h
    · exact Finset.mem_erase.mpr
        ⟨(ne_of_arc hfree (mem_outN.mp h).1 (mem_outN.mp h).2).symm, (mem_outN.mp h).1⟩
    · exact Finset.mem_erase.mpr ⟨ne_of_arc hfree hx (mem_inN.mp h).2, (mem_inN.mp h).1⟩
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hd, Finset.card_erase_of_mem hx] at h1
  have := Finset.card_pos.mpr ⟨x, hx⟩
  omega

theorem sum_out_in (D : CH.Digraph) (S : Finset ℕ) :
    ∑ x ∈ S, (outN D S x).card = ∑ x ∈ S, (inN D S x).card :=
  Compose.ThinRigid.sum_out_eq_sum_in D S

/-- The local `X ⊔ Y` setting. -/
structure XY (D : CH.Digraph) (X Y : Finset ℕ) (c : ℕ) : Prop where
  disj : Disjoint X Y
  free : QFree D (X ∪ Y) 4
  outX : ∀ x ∈ X, 5 ≤ (outN D (X ∪ Y) x).card
  outY : ∀ y ∈ Y, c ≤ (outN D (X ∪ Y) y).card
  par : ∀ y ∈ Y, ∃ x ∈ X, D x y = true

namespace XY

variable {X Y : Finset ℕ} {c : ℕ}

theorem mX (_H : XY D X Y c) {x : ℕ} (hx : x ∈ X) : x ∈ X ∪ Y := Finset.mem_union_left _ hx

theorem mY (_H : XY D X Y c) {y : ℕ} (hy : y ∈ Y) : y ∈ X ∪ Y := Finset.mem_union_right _ hy

theorem freeX (H : XY D X Y c) : QFree D X 4 := H.free.mono_set Finset.subset_union_left

theorem freeY (H : XY D X Y c) : QFree D Y 4 := H.free.mono_set Finset.subset_union_right

theorem mono (H : XY D X Y c) {c' : ℕ} (h : c' ≤ c) : XY D X Y c' :=
  ⟨H.disj, H.free, H.outX, fun y hy => h.trans (H.outY y hy), H.par⟩

theorem rowX (H : XY D X Y c) {x : ℕ} (hx : x ∈ X) : 5 ≤ (outN D X x).card + (outN D Y x).card := by
  have := H.outX x hx
  rwa [card_outN_union H.disj] at this

theorem rowY (H : XY D X Y c) {y : ℕ} (hy : y ∈ Y) : c ≤ (outN D X y).card + (outN D Y y).card := by
  have := H.outY y hy
  rwa [card_outN_union H.disj] at this

theorem outY_le (_H : XY D X Y c) (x : ℕ) : (outN D Y x).card ≤ Y.card :=
  Finset.card_le_card outN_subset

theorem card_W (H : XY D X Y c) : (X ∪ Y).card = X.card + Y.card :=
  Finset.card_union_of_disjoint H.disj

/-- A sink of `D[Y]` exists when `|Y| ≤ 4`. -/
theorem sinkY (H : XY D X Y c) (hne : Y.Nonempty) (h4 : Y.card ≤ 4) :
    ∃ y ∈ Y, ∀ z ∈ Y, ¬ D y z = true :=
  exists_sink H.freeY hne h4

/-- **Lemma 2, item 5.** At `(5,4)`, `D[X]` is 1-regular and every `x ∈ X` heads all of `Y`. -/
theorem tight54 (H : XY D X Y c) (hX : X.card = 5) (hY : Y.card = 4) :
    ∀ x ∈ X, (outN D X x).card = 1 ∧ (inN D X x).card = 1 ∧ ∀ y ∈ Y, D x y = true := by
  classical
  have hpos : ∀ x ∈ X, 1 ≤ (outN D X x).card := fun x hx => by
    have := H.rowX hx
    have := H.outY_le x
    omega
  obtain ⟨ho, hi⟩ := reg1 H.freeX hpos hX
  intro x hx
  refine ⟨ho x hx, hi x hx, fun y hy => ?_⟩
  have h1 := H.rowX hx
  have h2 := ho x hx
  have heq : outN D Y x = Y := Finset.eq_of_subset_of_card_le outN_subset (by omega)
  have : y ∈ outN D Y x := by rw [heq]; exact hy
  exact (mem_outN.mp this).2

/-- **Lemma 2, item 6.** At `(5,4)` a sink of `D[Y]` has no head in `X ∪ Y`. -/
theorem kill54 (H : XY D X Y c) (hX : X.card = 5) (hY : Y.card = 4) : c = 0 := by
  classical
  have hT := H.tight54 hX hY
  obtain ⟨y0, hy0, hs⟩ := H.sinkY (Finset.card_pos.mp (by omega)) (by omega)
  have h0 : (outN D (X ∪ Y) y0).card = 0 := by
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro z hz
    obtain ⟨hzW, hyz⟩ := mem_outN.mp hz
    rcases Finset.mem_union.mp hzW with h | h
    · exact n2 H.free (H.mX h) (H.mY hy0) ((hT z h).2.2 y0 hy0) hyz
    · exact hs z h hyz
  have := H.outY y0 hy0
  omega

/-- **Lemma 4.** `|X| + |Y| = 10` with `c = 2` is impossible. -/
theorem kill10 (H : XY D X Y 2) (h10 : X.card + Y.card = 10) (hX4 : 4 ≤ X.card) : False := by
  classical
  have hW := H.card_W
  -- every vertex has an in-neighbour in `Y`
  have hcov : ∀ a ∈ X ∪ Y, ∃ y ∈ Y, D y a = true := by
    intro a ha
    by_contra hno
    push Not at hno
    have hfT : QFree D ((X ∪ Y).erase a) 4 := H.free.mono_set (Finset.erase_subset _ _)
    have hTc : ((X ∪ Y).erase a).card = 9 := by
      rw [Finset.card_erase_of_mem ha]
      omega
    have hXrow : ∀ x ∈ X, 4 ≤ (outN D ((X ∪ Y).erase a) x).card := by
      intro x hx
      rw [outN_erase]
      have h1 := Finset.pred_card_le_card_erase (s := outN D (X ∪ Y) x) (a := a)
      have h2 := H.outX x hx
      omega
    have hmin : ∀ t ∈ (X ∪ Y).erase a, 2 ≤ (outN D ((X ∪ Y).erase a) t).card := by
      intro t ht
      rcases Finset.mem_union.mp (Finset.mem_of_mem_erase ht) with h | h
      · exact le_trans (by omega) (hXrow t h)
      · rw [outN_erase, Finset.erase_eq_of_notMem (fun hm => hno t h (mem_outN.mp hm).2)]
        exact H.outY t h
    obtain ⟨x, hx⟩ : (X.erase a).Nonempty := by
      refine Finset.card_pos.mp ?_
      have := Finset.pred_card_le_card_erase (s := X) (a := a)
      omega
    obtain ⟨hxa, hxX⟩ := Finset.mem_erase.mp hx
    have h2 := (reg2 hfT hmin hTc).1 x (Finset.mem_erase.mpr ⟨hxa, H.mX hxX⟩)
    have := hXrow x hxX
    omega
  -- every `x` has at least `|X| - 2` heads in `X`
  have hinner : ∀ x ∈ X, 2 ≤ (outN D X x).card ∧ (inN D X x).card ≤ 1 := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := hcov x (H.mX hx)
    obtain ⟨y', hy', hy'y⟩ := hcov y (H.mY hy)
    obtain ⟨y'', hy'', hy''y'⟩ := hcov y' (H.mY hy')
    have hxW := H.mX hx
    have m0 : y ∈ miss D Y x := Finset.mem_filter.mpr ⟨hy, fun h => n2 H.free hxW (H.mY hy) h hyx⟩
    have m1 : y' ∈ miss D Y x :=
      Finset.mem_filter.mpr ⟨hy', fun h => n3 H.free hxW (H.mY hy') (H.mY hy) h hy'y hyx⟩
    have m2 : y'' ∈ miss D Y x := Finset.mem_filter.mpr
      ⟨hy'', fun h => n4 H.free hxW (H.mY hy'') (H.mY hy') (H.mY hy) h hy''y' hy'y hyx⟩
    have d1 : y ≠ y' := (ne_of_arc H.free (H.mY hy) hy'y).symm
    have d2 : y' ≠ y'' := (ne_of_arc H.free (H.mY hy') hy''y').symm
    have d3 : y ≠ y'' := by
      rintro rfl
      exact n2 H.free (H.mY hy') (H.mY hy) hy'y hy''y'
    have h3 := three_le m0 m1 m2 d1 d3 d2
    have h4 := card_miss D Y x
    have h5 := H.rowX hx
    have h6 := out_in_le H.freeX hx
    constructor <;> omega
  have h1 : ∑ _x ∈ X, 2 ≤ ∑ x ∈ X, (outN D X x).card := Finset.sum_le_sum (fun x hx => (hinner x hx).1)
  have h2 : ∑ x ∈ X, (inN D X x).card ≤ ∑ _x ∈ X, 1 := Finset.sum_le_sum (fun x hx => (hinner x hx).2)
  rw [sum_out_in, sum_const'] at h1
  rw [sum_const'] at h2
  omega

/-- **Lemma 5.** `|Y| = 4`, `|X| ≤ 7`, `c = 2` is impossible. -/
theorem kill_n4 (H : XY D X Y 2) (hY : Y.card = 4) (hX : X.card ≤ 7) : False := by
  classical
  have hw : ∀ y ∈ Y, (outN D X y).card ≤ 1 := by
    intro y hy
    by_contra hgt
    have hyX : y ∉ X := fun h => (Finset.disjoint_left.mp H.disj h hy)
    have hTW : insert y X ⊆ X ∪ Y :=
      Finset.insert_subset (H.mY hy) Finset.subset_union_left
    have hfT : QFree D (insert y X) 4 := H.free.mono_set hTW
    have hmin : ∀ t ∈ insert y X, 2 ≤ (outN D (insert y X) t).card := by
      intro t ht
      rcases Finset.mem_insert.mp ht with h | h
      · rw [h]
        exact le_trans (by omega) (Finset.card_le_card (outN_mono (Finset.subset_insert y X) y))
      · have hsub : outN D (X ∪ Y) t ⊆ outN D (insert y X) t ∪ Y.erase y := by
          intro z hz
          obtain ⟨hzW, htz⟩ := mem_outN.mp hz
          by_cases hzy : z = y
          · exact Finset.mem_union_left _ (mem_outN.mpr ⟨hzy ▸ Finset.mem_insert_self y X, htz⟩)
          · rcases Finset.mem_union.mp hzW with hz' | hz'
            · exact Finset.mem_union_left _ (mem_outN.mpr ⟨Finset.mem_insert_of_mem hz', htz⟩)
            · exact Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hzy, hz'⟩)
        have h1 := (H.outX t h).trans (Finset.card_le_card hsub)
        have h2 := Finset.card_union_le (outN D (insert y X) t) (Y.erase y)
        have h3 := Finset.card_erase_of_mem hy
        omega
    have h9 := ch2 hfT hmin ⟨y, Finset.mem_insert_self y X⟩
    rw [Finset.card_insert_of_notMem hyX] at h9
    omega
  obtain ⟨y0, hy0, hs⟩ := H.sinkY (Finset.card_pos.mp (by omega)) (by omega)
  have h0 : (outN D Y y0).card = 0 := by
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro z hz
    exact hs z (mem_outN.mp hz).1 (mem_outN.mp hz).2
  have := H.rowY hy0
  have := hw y0 hy0
  omega

/-- **Lemma 9 applied.** `(5,6)` with `c = 2` is impossible. -/
theorem kill56 (H : XY D X Y 2) (hX : X.card = 5) (hY : Y.card = 6) : False :=
  s56 H.disj hX hY H.free H.outX H.outY

/-- **Lemma 3 (back-arc lemma)**, in the form used. -/
theorem back_arc (H : XY D X Y c) (hX6 : X.card ≤ 6) {y0 x : ℕ} (hy0 : y0 ∈ Y) (hx : x ∈ X)
    (hyx : D y0 x = true) {D1 D2 : Finset ℕ} (hD1Y : D1 ⊆ Y) (hD2Y : D2 ⊆ Y)
    (hD1 : ∀ y ∈ D1, y = y0 ∨ D y y0 = true)
    (hD2 : ∀ y ∈ D2, y ∈ D1 ∨ ∃ y' ∈ D1, D y y' = true)
    (hpos : Y.card < 5 + D2.card) : 12 + D1.card + D2.card ≤ X.card + 2 * Y.card := by
  classical
  have hxW := H.mX hx
  have hy0W := H.mY hy0
  obtain ⟨j, hjX, hjy⟩ := H.par y0 hy0
  have hjW := H.mX hjX
  have hjx : j ≠ x := by
    rintro rfl
    exact n2 H.free hjW hy0W hjy hyx
  -- a walk `v → y0` of length `≤ 2` from `D1`, `≤ 3` from `D2`, closes with `y0 → x`
  have c1 : ∀ {p y : ℕ}, p ∈ X ∪ Y → y ∈ D1 → D p y = true →
      (p = x → False) ∧ (D x p = true → False) := by
    intro p y hp hy hpy
    have hyW := H.mY (hD1Y hy)
    rcases hD1 y hy with h | h
    · rw [h] at hpy
      exact ⟨fun e => by rw [e] at hpy; exact n2 H.free hxW hy0W hpy hyx,
        fun hxp => n3 H.free hxW hp hy0W hxp hpy hyx⟩
    · exact ⟨fun e => by rw [e] at hpy; exact n3 H.free hxW hyW hy0W hpy h hyx,
        fun hxp => n4 H.free hxW hp hyW hy0W hxp hpy h hyx⟩
  set G := (X.erase x).erase j
  have hGc : G.card + 2 = X.card := by
    have h1 := Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hjx, hjX⟩)
    have h2 := Finset.card_erase_of_mem hx
    have h3 : 0 < ((X.erase x)).card := Finset.card_pos.mpr ⟨j, Finset.mem_erase.mpr ⟨hjx, hjX⟩⟩
    have h4 : G.card = (X.erase x).card - 1 := h1
    omega
  set A := outN D X x
  have hAG : A ⊆ G := by
    intro a ha
    obtain ⟨haX, hxa⟩ := mem_outN.mp ha
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_erase.mpr ⟨(ne_of_arc H.free (H.mX haX) hxa).symm, haX⟩⟩
    rintro rfl
    exact n3 H.free hxW hjW hy0W hxa hjy hyx
  have hAA : ∀ a ∈ A, outN D X a ⊆ G := by
    intro a ha a' ha'
    obtain ⟨haX, hxa⟩ := mem_outN.mp ha
    obtain ⟨ha'X, haa'⟩ := mem_outN.mp ha'
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_erase.mpr ⟨?_, ha'X⟩⟩
    · rintro rfl
      exact n4 H.free hxW (H.mX haX) hjW hy0W hxa haa' hjy hyx
    · rintro rfl
      exact n2 H.free hxW (H.mX haX) hxa haa'
  have hxY : outN D Y x ⊆ Y \ D2 := by
    intro y hy
    obtain ⟨hyY, hxy⟩ := mem_outN.mp hy
    refine Finset.mem_sdiff.mpr ⟨hyY, fun hy2 => ?_⟩
    rcases hD2 y hy2 with h | ⟨y', hy', h⟩
    · exact (c1 hxW h hxy).1 rfl
    · exact (c1 (H.mY hyY) hy' h).2 hxy
  have hA1 : 5 + D2.card ≤ A.card + Y.card := by
    have h1 : 5 ≤ A.card + (outN D Y x).card := H.rowX hx
    have h2 := Finset.card_le_card hxY
    have h3 := Finset.card_sdiff_add_card_eq_card hD2Y
    omega
  have hAne : A.Nonempty := Finset.card_pos.mp (by omega)
  have hAc := Finset.card_le_card hAG
  obtain ⟨a, ha, has⟩ := exists_sink (D := D) (T := A) (q := 4)
    (H.freeX.mono_set outN_subset) hAne (by omega)
  obtain ⟨haX, hxa⟩ := mem_outN.mp ha
  have haY : outN D Y a ⊆ Y \ D1 := by
    intro y hy
    obtain ⟨hyY, hay⟩ := mem_outN.mp hy
    exact Finset.mem_sdiff.mpr ⟨hyY, fun hy1 => (c1 (H.mX haX) hy1 hay).2 hxa⟩
  have ha1 : 5 + D1.card ≤ (outN D X a).card + Y.card := by
    have h1 := H.rowX haX
    have h2 := Finset.card_le_card haY
    have h3 := Finset.card_sdiff_add_card_eq_card hD1Y
    omega
  have ha2 : (outN D X a).card + A.card ≤ G.card := by
    have hsub : outN D X a ⊆ G \ A := by
      intro z hz
      exact Finset.mem_sdiff.mpr ⟨hAA a ha hz, fun hzA => has z hzA (mem_outN.mp hz).2⟩
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_sdiff_of_subset hAG] at h1
    omega
  omega

end XY

end LeanCH.BR.BR45
