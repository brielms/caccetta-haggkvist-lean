import LeanCH.BR.BR45KillB
import LeanCH.BR.BR45Disc

/-!
# BR(4,5), profile kills, part C: BFS layers and Lemma 8 (Lean 4.35.0)

Paper: `checkpoints/boundary_20261111/BR45_attempt_subagent.md` §1 (BFS facts), §4 (Lemma 8); audit
`BR45_audit_subagent.md` §1–§3.

Global setting: `E` is `4`-free on `V`, min out `≥ 5`, `u ∈ V`. Layers: `X = O(u)`, `Y = N2 E V u = B_2 ∖ B_1`,
`Z = N3 E V u = B_3 ∖ B_2`, `R = V ∖ B_3`.

* `card_B1`, `card_B2`, `card_B3`: `|B_1| = |X| + 1`, `|B_2| = |B_1| + |Y|`, `|B_3| = |B_2| + |Z|`.
* `split4`: every `w ∈ V` is `u` or in `X`, `Y`, `Z`, or outside `B_3`.
* `headX`, `headY`: `O(x) ⊆ X ∪ Y`, `O(y) ⊆ X ∪ Y ∪ Z` (BFS, and no cycle of length `≤ 4` back to `u`).
* `parY`: every `y` has a parent in `X`.
* `lay_XY` (**the global-to-local bridge**): `XY E X Y (5 − |Z|)`.
* `outN_X_eq`: `O(x) = O_{X ∪ Y}(x)`.
* `kill554` (**Lemma 8**, `(5,5,4)`, `C_5` branch global). By `XY.loc554` no `y` heads `X` and every `y` has one
  `Y`-head, so `y` heads all of `Z`. Then `Z`-rows head only `Z ∪ R` (no `u`; `X`: triangle through a `Y`-head of
  `x`; `Y`: digon). The sink of `D[Z]` puts `≥ 5` vertices into `R_Z = {r ∈ R : I(r) ∩ Z ≠ ∅}`, and `|R| = 6`. An
  `R_Z`-row avoids `X` (4-cycle `x → y → z → r → x`) and `Y` (triangle), so it keeps `≥ 5 − 1 − 1 = 3` heads in
  `Z ∪ R_Z` (lost: `u`, and the `≤ 1` vertex of `R ∖ R_Z`). `Z`-rows keep all their heads there. `CH(3)` needs 13
  vertices, but `|Z ∪ R_Z| ≤ 10`.
-/

set_option linter.style.longLine false

namespace LeanCH.BR.BR45

open LeanCH.BR.BRq2 LeanCH.BR.BRq3 CH

variable {E : CH.Digraph} {V : Finset ℕ} {u : ℕ}

/-- `N_2(u) = B_2(u) ∖ B_1(u)`. -/
noncomputable def N2 (E : CH.Digraph) (V : Finset ℕ) (u : ℕ) : Finset ℕ := ball E V u 2 \ ball E V u 1

/-- `N_3(u) = B_3(u) ∖ B_2(u)`. -/
noncomputable def N3 (E : CH.Digraph) (V : Finset ℕ) (u : ℕ) : Finset ℕ := ball E V u 3 \ ball E V u 2

theorem mem_N2 {y : ℕ} : y ∈ N2 E V u ↔ y ∈ ball E V u 2 ∧ y ∉ ball E V u 1 := Finset.mem_sdiff

theorem mem_N3 {z : ℕ} : z ∈ N3 E V u ↔ z ∈ ball E V u 3 ∧ z ∉ ball E V u 2 := Finset.mem_sdiff

theorem N2_subV {y : ℕ} (hy : y ∈ N2 E V u) : y ∈ V := ball_subset (mem_N2.mp hy).1

theorem N3_subV {z : ℕ} (hz : z ∈ N3 E V u) : z ∈ V := ball_subset (mem_N3.mp hz).1

theorem X_B1 {x : ℕ} (hx : x ∈ outN E V u) : x ∈ ball E V u 1 :=
  ball_of_adj (mem_outN.mp hx).1 (mem_outN.mp hx).2

theorem ball1_eq (hu : u ∈ V) : ball E V u 1 = insert u (outN E V u) := by
  ext v
  rw [mem_ball_one hu, Finset.mem_insert]

theorem card_B1 (hfree : QFree E V 4) (hu : u ∈ V) : (ball E V u 1).card = (outN E V u).card + 1 := by
  rw [ball1_eq hu, Finset.card_insert_of_notMem (fun h => n1 hfree hu (mem_outN.mp h).2)]

theorem card_B2 : (ball E V u 2).card = (ball E V u 1).card + (N2 E V u).card := by
  have := Finset.card_sdiff_add_card_eq_card (ball_mono_radius (D := E) (W := V) (u := u) (by omega : 1 ≤ 2))
  unfold N2
  omega

theorem card_B3 : (ball E V u 3).card = (ball E V u 2).card + (N3 E V u).card := by
  have := Finset.card_sdiff_add_card_eq_card (ball_mono_radius (D := E) (W := V) (u := u) (by omega : 2 ≤ 3))
  unfold N3
  omega

theorem disjXY : Disjoint (outN E V u) (N2 E V u) :=
  Finset.disjoint_left.mpr (fun _ hx hy => (mem_N2.mp hy).2 (X_B1 hx))

theorem split4 (hu : u ∈ V) (w : ℕ) :
    w = u ∨ w ∈ outN E V u ∨ w ∈ N2 E V u ∨ w ∈ N3 E V u ∨ w ∉ ball E V u 3 := by
  by_cases h3 : w ∈ ball E V u 3
  · by_cases h2 : w ∈ ball E V u 2
    · by_cases h1 : w ∈ ball E V u 1
      · rcases (mem_ball_one hu).mp h1 with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl (mem_N2.mpr ⟨h2, h1⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (mem_N3.mpr ⟨h3, h2⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h3)))

/-- Heads of `X`-rows lie in `X ∪ Y`. -/
theorem headX (hfree : QFree E V 4) (hu : u ∈ V) {x w : ℕ} (hx : x ∈ outN E V u) (hw : w ∈ V)
    (hxw : E x w = true) : w ∈ outN E V u ∪ N2 E V u := by
  have hb := X_B1 hx
  rcases split4 hu w with h | h | h | h | h
  · rw [h] at hxw
    exact absurd hxw (no_back_arc hfree hu hb (by omega))
  · exact Finset.mem_union_left _ h
  · exact Finset.mem_union_right _ h
  · exact absurd (ball_step hb hw hxw) (mem_N3.mp h).2
  · exact absurd (ball_mono_radius (by omega : 2 ≤ 3) (ball_step hb hw hxw)) h

/-- Heads of `Y`-rows lie in `X ∪ Y ∪ Z`. -/
theorem headY (hfree : QFree E V 4) (hu : u ∈ V) {y w : ℕ} (hy : y ∈ N2 E V u) (hw : w ∈ V)
    (hyw : E y w = true) : w ∈ outN E V u ∪ N2 E V u ∨ w ∈ N3 E V u := by
  have hb := (mem_N2.mp hy).1
  rcases split4 hu w with h | h | h | h | h
  · rw [h] at hyw
    exact absurd hyw (no_back_arc hfree hu hb (by omega))
  · exact Or.inl (Finset.mem_union_left _ h)
  · exact Or.inl (Finset.mem_union_right _ h)
  · exact Or.inr h
  · exact absurd (ball_step hb hw hyw) h

/-- Every `y ∈ Y` has a parent in `X`. -/
theorem parY (hu : u ∈ V) {y : ℕ} (hy : y ∈ N2 E V u) : ∃ x ∈ outN E V u, E x y = true := by
  obtain ⟨p, hp, hpy⟩ := ball_succ_pred hu (mem_N2.mp hy).1 (mem_N2.mp hy).2
  rcases (mem_ball_one hu).mp hp with h | h
  · rw [h] at hpy
    exact absurd (ball_of_adj (N2_subV hy) hpy) (mem_N2.mp hy).2
  · exact ⟨p, h, hpy⟩

theorem XY_subV : outN E V u ∪ N2 E V u ⊆ V :=
  Finset.union_subset outN_subset (fun _ hy => N2_subV hy)

/-- `O(x) = O_{X ∪ Y}(x)` for `x ∈ X`. -/
theorem outN_X_eq (hfree : QFree E V 4) (hu : u ∈ V) {x : ℕ} (hx : x ∈ outN E V u) :
    outN E V x = outN E (outN E V u ∪ N2 E V u) x := by
  ext w
  rw [mem_outN, mem_outN]
  exact ⟨fun ⟨hw, hxw⟩ => ⟨headX hfree hu hx hw hxw, hxw⟩, fun ⟨hw, hxw⟩ => ⟨XY_subV hw, hxw⟩⟩

/-- **The bridge.** The layers `X = N_1(u)`, `Y = N_2(u)` form an `XY` instance with `c = 5 − |N_3(u)|`. -/
theorem lay_XY (hfree : QFree E V 4) (hout : ∀ v ∈ V, 5 ≤ (outN E V v).card) (hu : u ∈ V) :
    XY E (outN E V u) (N2 E V u) (5 - (N3 E V u).card) := by
  classical
  refine ⟨disjXY, hfree.mono_set XY_subV, fun x hx => ?_, fun y hy => ?_, fun y hy => parY hu hy⟩
  · rw [← outN_X_eq hfree hu hx]
    exact hout x (mem_outN.mp hx).1
  · have hsub : outN E V y ⊆ outN E (outN E V u ∪ N2 E V u) y ∪ N3 E V u := by
      intro w hw
      obtain ⟨hwV, hyw⟩ := mem_outN.mp hw
      rcases headY hfree hu hy hwV hyw with h | h
      · exact Finset.mem_union_left _ (mem_outN.mpr ⟨h, hyw⟩)
      · exact Finset.mem_union_right _ h
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_union_le (outN E (outN E V u ∪ N2 E V u) y) (N3 E V u)
    have h3 := hout y (N2_subV hy)
    omega

/-- **Lemma 8.** The profile `(5,5,4)` is impossible on 21 vertices. -/
theorem kill554 (hV : V.card = 21) (hfree : QFree E V 4) (hout : ∀ v ∈ V, 5 ≤ (outN E V v).card)
    (hu : u ∈ V) (h1 : (outN E V u).card = 5) (h2 : (N2 E V u).card = 5) (h3 : (N3 E V u).card = 4) :
    False := by
  classical
  have H : XY E (outN E V u) (N2 E V u) 1 := (lay_XY hfree hout hu).mono (by omega)
  obtain ⟨hcyc, hw0⟩ := H.loc554 h1 h2
  have hYmin : ∀ y ∈ N2 E V u, 1 ≤ (outN E (N2 E V u) y).card := fun y hy => by
    obtain ⟨z, hz, hyz⟩ := hcyc y hy
    exact Finset.card_pos.mpr ⟨z, mem_outN.mpr ⟨hz, hyz⟩⟩
  have hY1 := (reg1 H.freeY hYmin h2).1
  -- every `y` heads all of `Z`
  have hYZ : ∀ y ∈ N2 E V u, ∀ z ∈ N3 E V u, E y z = true := by
    intro y hy
    have hsub : outN E V y ⊆ outN E (N2 E V u) y ∪ outN E (N3 E V u) y := by
      intro w hw
      obtain ⟨hwV, hyw⟩ := mem_outN.mp hw
      rcases headY hfree hu hy hwV hyw with h | h
      · rcases Finset.mem_union.mp h with h | h
        · exact absurd hyw (hw0 y hy w h)
        · exact Finset.mem_union_left _ (mem_outN.mpr ⟨h, hyw⟩)
      · exact Finset.mem_union_right _ (mem_outN.mpr ⟨h, hyw⟩)
    have c1 := Finset.card_le_card hsub
    have c2 := Finset.card_union_le (outN E (N2 E V u) y) (outN E (N3 E V u) y)
    have c3 := hout y (N2_subV hy)
    have c4 := hY1 y hy
    have heq : outN E (N3 E V u) y = N3 E V u := Finset.eq_of_subset_of_card_le outN_subset (by omega)
    intro z hz
    have : z ∈ outN E (N3 E V u) y := by rw [heq]; exact hz
    exact (mem_outN.mp this).2
  -- every `x` has a `Y`-head
  have hXY : ∀ x ∈ outN E V u, ∃ y ∈ N2 E V u, E x y = true := by
    intro x hx
    have c1 := H.rowX hx
    have c2 := out_in_le H.freeX hx
    obtain ⟨y, hy⟩ := Finset.card_pos.mp (show 0 < (outN E (N2 E V u) x).card by omega)
    exact ⟨y, (mem_outN.mp hy).1, (mem_outN.mp hy).2⟩
  -- `Z`-rows head only `Z ∪ R`
  have hZhead : ∀ z ∈ N3 E V u, ∀ w ∈ V, E z w = true → w ∈ N3 E V u ∨ w ∉ ball E V u 3 := by
    intro z hz w hw hzw
    have hzV := N3_subV hz
    rcases split4 hu w with h | h | h | h | h
    · rw [h] at hzw
      exact absurd hzw (no_back_arc hfree hu (mem_N3.mp hz).1 (by omega))
    · exfalso
      obtain ⟨y, hy, hwy⟩ := hXY w h
      exact n3 hfree hw (N2_subV hy) hzV hwy (hYZ y hy z hz) hzw
    · exact (n2 hfree hw hzV (hYZ w h z hz) hzw).elim
    · exact Or.inl h
    · exact Or.inr h
  obtain ⟨z0, hz0, hs0⟩ := exists_sink (D := E) (T := N3 E V u) (q := 4)
    (hfree.mono_set (fun _ hz => N3_subV hz)) (Finset.card_pos.mp (by omega)) (by omega)
  have hRc : (V \ ball E V u 3).card = 6 := by
    have c1 := Finset.card_sdiff_add_card_eq_card (ball_subset (D := E) (W := V) (u := u) (k := 3))
    have c2 := card_B3 (E := E) (V := V) (u := u)
    have c3 := card_B2 (E := E) (V := V) (u := u)
    have c4 := card_B1 hfree hu
    omega
  set RZ := (V \ ball E V u 3).filter (fun r => ∃ z ∈ N3 E V u, E z r = true) with hRZ
  have hRZR : RZ ⊆ V \ ball E V u 3 := Finset.filter_subset _ _
  have hRZ5 : 5 ≤ RZ.card := by
    have hsub : outN E V z0 ⊆ RZ := by
      intro w hw
      obtain ⟨hwV, hzw⟩ := mem_outN.mp hw
      rcases hZhead z0 hz0 w hwV hzw with h | h
      · exact absurd hzw (hs0 w h)
      · exact Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hwV, h⟩, z0, hz0, hzw⟩
    exact (hout z0 (N3_subV hz0)).trans (Finset.card_le_card hsub)
  have hR0 : ((V \ ball E V u 3) \ RZ).card ≤ 1 := by
    have := Finset.card_sdiff_add_card_eq_card hRZR
    omega
  have hTV : N3 E V u ∪ RZ ⊆ V :=
    Finset.union_subset (fun _ hz => N3_subV hz) (fun _ hr => (Finset.mem_sdiff.mp (hRZR hr)).1)
  have hTmin : ∀ t ∈ N3 E V u ∪ RZ, 3 ≤ (outN E (N3 E V u ∪ RZ) t).card := by
    intro t ht
    rcases Finset.mem_union.mp ht with hz | hr
    · have hsub : outN E V t ⊆ outN E (N3 E V u ∪ RZ) t := by
        intro w hw
        obtain ⟨hwV, htw⟩ := mem_outN.mp hw
        refine mem_outN.mpr ⟨?_, htw⟩
        rcases hZhead t hz w hwV htw with h | h
        · exact Finset.mem_union_left _ h
        · exact Finset.mem_union_right _
            (Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hwV, h⟩, t, hz, htw⟩)
      have c1 := hout t (N3_subV hz)
      have c2 := Finset.card_le_card hsub
      omega
    · obtain ⟨hrR, z, hz, hzr⟩ := Finset.mem_filter.mp hr
      have hrV := (Finset.mem_sdiff.mp hrR).1
      have hzV := N3_subV hz
      have hsub : outN E V t ⊆ insert u (outN E (N3 E V u ∪ RZ) t ∪ ((V \ ball E V u 3) \ RZ)) := by
        intro w hw
        obtain ⟨hwV, htw⟩ := mem_outN.mp hw
        rcases split4 hu w with h | h | h | h | h
        · rw [h]
          exact Finset.mem_insert_self _ _
        · exfalso
          obtain ⟨y, hy, hwy⟩ := hXY w h
          exact n4 hfree hwV (N2_subV hy) hzV hrV hwy (hYZ y hy z hz) hzr htw
        · exact (n3 hfree hwV hzV hrV (hYZ w h z hz) hzr htw).elim
        · exact Finset.mem_insert_of_mem (Finset.mem_union_left _
            (mem_outN.mpr ⟨Finset.mem_union_left _ h, htw⟩))
        · by_cases hwRZ : w ∈ RZ
          · exact Finset.mem_insert_of_mem (Finset.mem_union_left _
              (mem_outN.mpr ⟨Finset.mem_union_right _ hwRZ, htw⟩))
          · exact Finset.mem_insert_of_mem (Finset.mem_union_right _
              (Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨hwV, h⟩, hwRZ⟩))
      have c1 := Finset.card_le_card hsub
      have c2 := Finset.card_insert_le u (outN E (N3 E V u ∪ RZ) t ∪ ((V \ ball E V u 3) \ RZ))
      have c3 := Finset.card_union_le (outN E (N3 E V u ∪ RZ) t) ((V \ ball E V u 3) \ RZ)
      have c4 := hout t hrV
      omega
  have h13 := ch3 (hfree.mono_set hTV) hTmin ⟨z0, Finset.mem_union_left _ hz0⟩
  have c1 := Finset.card_union_le (N3 E V u) RZ
  have c2 := Finset.card_le_card hRZR
  omega

end LeanCH.BR.BR45
