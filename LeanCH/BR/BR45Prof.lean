import LeanCH.BR.BR45KillC

/-!
# BR(4,5): the profile list, the strict cap and the tight profile (Lean 4.35.0)

Paper: `checkpoints/boundary_20261111/BR45_attempt_subagent.md` §2 (Lemma 2), Corollary 10; the derivation follows
`BR45_audit_subagent.md` §2 (from `CH(c)`, `BR(4,c)`, `c ≤ 4`, only).

Let `E` be `4`-free on `V`, `|V| = 21`, min out `≥ 5`, `u ∈ V`, `n_1 = |X|`, `n_2 = |Y|`, `n_3 = |Z|`, so
`b_3 = 1 + n_1 + n_2 + n_3` (`card_B1..3`), and `XY E X Y (5 − n_3)` (`lay_XY`).

* `prof`: if `b_3 ≤ 15` then `(n_1, n_2, n_3) = (5, 4, 5)`.
  - `n_3 ≥ 3`: otherwise `CH(4)` (`n_3 ≤ 1`) or `CH(3)` (`n_3 = 2`) on `X ∪ Y`.
  - `n_2 ≥ 4`: otherwise `CH(3)` (`n_2 ≤ 2`) or `CH(2)` (`n_2 = 3`) on `X`.
  - The remaining nine profiles are killed: `(5,4,3)`, `(5,4,4)` by `XY.kill54`; `(6,4,3)`, `(7,4,3)` by
    `XY.kill_n4`; `(6,4,4)` by `XY.kill644`; `(5,5,3)` by `XY.kill10`; `(5,5,4)` by `kill554`; `(6,5,3)` by
    `XY.kill653`; `(5,6,3)` by `XY.kill56`.
* `tight_of`: at `(5,4,·)` the vertex has the tight profile `TightAt` (`XY.tight54`).
* `cap45 : Cap45`, `tight45 : Tight45`.
-/

set_option linter.style.longLine false

namespace LeanCH.BR.BR45

open LeanCH.BR.BRq2 LeanCH.BR.BRq3 CH

variable {E : CH.Digraph} {V : Finset ℕ} {u : ℕ}

/-- The local profile kills leave two possibilities when `b_3 ≤ 15`. -/
theorem prof_local (hfree : QFree E V 4) (hout : ∀ v ∈ V, 5 ≤ (outN E V v).card)
    (hu : u ∈ V) (hb : (ball E V u 3).card ≤ 15) :
    (outN E V u).card = 5 ∧
      (((N2 E V u).card = 4 ∧ (N3 E V u).card = 5) ∨
       ((N2 E V u).card = 5 ∧ (N3 E V u).card = 4)) := by
  classical
  have H0 := lay_XY hfree hout hu
  have e1 := card_B1 hfree hu
  have e2 := card_B2 (E := E) (V := V) (u := u)
  have e3 := card_B3 (E := E) (V := V) (u := u)
  have hn1 := hout u hu
  have hW := H0.card_W
  have hXne : (outN E V u).Nonempty := Finset.card_pos.mp (by omega)
  have hWne : (outN E V u ∪ N2 E V u).Nonempty := hXne.mono Finset.subset_union_left
  -- `n_3 ≥ 3`
  have hn3 : 3 ≤ (N3 E V u).card := by
    by_contra hlt
    by_cases h1 : (N3 E V u).card ≤ 1
    · have := ch4 H0.free (fun t ht => ?_) hWne
      · omega
      · rcases Finset.mem_union.mp ht with h | h
        · exact le_trans (by omega) (H0.outX t h)
        · exact le_trans (by omega) (H0.outY t h)
    · have := ch3 H0.free (fun t ht => ?_) hWne
      · omega
      · rcases Finset.mem_union.mp ht with h | h
        · exact le_trans (by omega) (H0.outX t h)
        · exact le_trans (by omega) (H0.outY t h)
  -- `n_2 ≥ 4`
  have hn2 : 4 ≤ (N2 E V u).card := by
    by_contra hlt
    have hrow : ∀ x ∈ outN E V u, 5 ≤ (outN E (outN E V u) x).card + (N2 E V u).card := fun x hx => by
      have := H0.rowX hx
      have := H0.outY_le x
      omega
    by_cases h2 : (N2 E V u).card ≤ 2
    · have := ch3 H0.freeX (fun x hx => by have := hrow x hx; omega) hXne
      omega
    · have := ch2 H0.freeX (fun x hx => by have := hrow x hx; omega) hXne
      omega
  -- the ten profiles
  have hcases : ((N2 E V u).card = 4 ∧ (outN E V u).card = 5 ∧ (N3 E V u).card = 5) ∨
      ((N2 E V u).card = 4 ∧ (outN E V u).card = 5 ∧ (N3 E V u).card ≤ 4) ∨
      ((N2 E V u).card = 4 ∧ (N3 E V u).card = 3 ∧ (outN E V u).card ≤ 7) ∨
      ((N2 E V u).card = 4 ∧ (outN E V u).card = 6 ∧ (N3 E V u).card = 4) ∨
      ((N2 E V u).card = 5 ∧ (outN E V u).card = 5 ∧ (N3 E V u).card = 3) ∨
      ((N2 E V u).card = 5 ∧ (outN E V u).card = 5 ∧ (N3 E V u).card = 4) ∨
      ((N2 E V u).card = 5 ∧ (outN E V u).card = 6 ∧ (N3 E V u).card = 3) ∨
      ((N2 E V u).card = 6 ∧ (outN E V u).card = 5 ∧ (N3 E V u).card = 3) := by
    omega
  rcases hcases with ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩ | ⟨a, b, c⟩ |
      ⟨a, b, c⟩
  · exact ⟨b, Or.inl ⟨a, c⟩⟩
  · -- `(5,4,3)`, `(5,4,4)`
    have := H0.kill54 b a
    omega
  · -- `(6,4,3)`, `(7,4,3)`
    exact (H0.mono (by omega : 2 ≤ 5 - (N3 E V u).card) |>.kill_n4 a c).elim
  · -- `(6,4,4)`
    exact (H0.mono (by omega : 1 ≤ 5 - (N3 E V u).card) |>.kill644 b a).elim
  · -- `(5,5,3)`
    exact (H0.mono (by omega : 2 ≤ 5 - (N3 E V u).card) |>.kill10 (by omega) (by omega)).elim
  · -- `(5,5,4)`
    exact ⟨b, Or.inr ⟨a, c⟩⟩
  · -- `(6,5,3)`
    exact (H0.mono (by omega : 2 ≤ 5 - (N3 E V u).card) |>.kill653 b a).elim
  · -- `(5,6,3)`
    exact (H0.mono (by omega : 2 ≤ 5 - (N3 E V u).card) |>.kill56 b a).elim

/-- **Lemma 2 and the kills.** A boundary vertex with `b_3 ≤ 15` has profile `(5,4,5)`. -/
theorem prof (hV : V.card = 21) (hfree : QFree E V 4) (hout : ∀ v ∈ V, 5 ≤ (outN E V v).card)
    (hu : u ∈ V) (hb : (ball E V u 3).card ≤ 15) :
    (outN E V u).card = 5 ∧ (N2 E V u).card = 4 ∧ (N3 E V u).card = 5 := by
  obtain ⟨h1, h45 | h54⟩ := prof_local hfree hout hu hb
  · exact ⟨h1, h45⟩
  · exact (kill554 hV hfree hout hu h1 h54.1 h54.2).elim

/-- A radius-three ball in a 5-free digraph of minimum out-degree five
has at least 16 vertices. This bound has no host-order restriction. -/
theorem card_ball_three_ge_sixteen (hfree : QFree E V 5)
    (hout : ∀ v ∈ V, 5 ≤ (outN E V v).card) (hu : u ∈ V) :
    16 ≤ (ball E V u 3).card := by
  by_contra hsmall
  have hf4 : QFree E V 4 := hfree.mono_bound (by decide)
  obtain ⟨h1, h45 | h54⟩ := prof_local hf4 hout hu (by omega)
  · have H := lay_XY hf4 hout hu
    have ht := H.tight54 h1 h45.1
    have hX := outN_subset (D := E) (W := V) (y := u)
    have hXne : (outN E V u).Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨x, hx, hsink⟩ := exists_sink (hfree.mono_set hX)
      hXne (by omega)
    obtain ⟨z, hz⟩ := Finset.card_pos.mp (by rw [(ht x hx).1]; decide)
    exact hsink z (mem_outN.mp hz).1 (mem_outN.mp hz).2
  · have H : XY E (outN E V u) (N2 E V u) 1 := (lay_XY hf4 hout hu).mono (by omega)
    obtain ⟨hcyc, _⟩ := H.loc554 h1 h54.1
    have hYne : (N2 E V u).Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨y, hy, hsink⟩ := exists_sink
      (hfree.mono_set (fun _ hy => N2_subV hy)) hYne (by omega)
    obtain ⟨z, hz, hyz⟩ := hcyc y hy
    exact hsink z hz hyz

/-- At profile `(5,4,·)` the vertex has the tight profile. -/
theorem tight_of (hfree : QFree E V 4) (hout : ∀ v ∈ V, 5 ≤ (outN E V v).card) (hu : u ∈ V)
    (h1 : (outN E V u).card = 5) (h2 : (N2 E V u).card = 4) : TightAt E V u := by
  classical
  have H0 := lay_XY hfree hout hu
  have hT := H0.tight54 h1 h2
  have e1 := card_B1 hfree hu
  have e2 := card_B2 (E := E) (V := V) (u := u)
  refine ⟨h1, by omega, fun x hx => ⟨?_, (hT x hx).1, (hT x hx).2.1,
    fun y hy2 hy1 => (hT x hx).2.2 y (mem_N2.mpr ⟨hy2, hy1⟩)⟩⟩
  have hY : outN E (N2 E V u) x = N2 E V u :=
    Finset.eq_of_subset_of_card_le outN_subset
      (Finset.card_le_card (fun y hy => mem_outN.mpr ⟨hy, (hT x hx).2.2 y hy⟩))
  rw [outN_X_eq hfree hu hx, card_outN_union disjXY, hY]
  have := (hT x hx).1
  omega

/-- **The strict cap** (hypothesis (i) of the discharging step). -/
theorem cap45 : Cap45 := by
  intro E hfree hout u hu
  by_contra hlt
  obtain ⟨h1, h2, h3⟩ := prof (V := V45) (Finset.card_range 21) hfree hout hu (by omega)
  have e1 := card_B1 hfree hu
  have e2 := card_B2 (E := E) (V := V45) (u := u)
  have e3 := card_B3 (E := E) (V := V45) (u := u)
  omega

/-- **The tight profile** (hypothesis (ii) of the discharging step). -/
theorem tight45 : Tight45 := by
  intro E hfree hout u hu hb
  obtain ⟨h1, h2, -⟩ := prof (V := V45) (Finset.card_range 21) hfree hout hu (by omega)
  exact tight_of hfree hout hu h1 h2

end LeanCH.BR.BR45
