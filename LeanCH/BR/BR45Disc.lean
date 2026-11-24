import LeanCH.BR.BR45Sat
import Mathlib.Tactic.Linarith

/-!
# BR(4,5), the discharging step (Lemma 10′, Lemma 10″, Theorem 11), conditional (Lean 4.35.0)

Paper: `checkpoints/boundary_20261111/BR45_attempt_subagent.md` §5, audited in `BR45_audit_subagent.md` §4.

The two inputs from the profile kills are kept as named hypotheses:

* `Cap45` (i): in every `4`-free digraph on `range 21` with min out `≥ 5`, `|B_3(u)| ≥ 15` for every `u`.
* `Tight45` (ii): at a vertex with `|B_3(u)| = 15` the profile is `(5,4,5)` (`TightAt`): `out(u) = 5`,
  `|B_2(u)| = 10`, and every `x ∈ X = O(u)` has `out(x) = 5`, exactly one head and exactly one in-neighbour in `X`
  (`D[X] = C_5`), and heads all of `N_2(u)`.

`br45_of_cap_tight : Cap45 → Tight45 → BoundaryRegular 4 5`.

For a saturated boundary graph (`DHyp`), a *root* is a vertex of in-degree 6 (then `|B_3| = 15`, so `TightAt`, so
out-degree 5). `HS u = {η ∈ I(u) : η heads all of O(u)}`.

* `root_in` (**Lemma 10′(i)**): `I(x) ⊆ {u} ∪ (I(x) ∩ X) ∪ H(u)` for `x ∈ O(u)`; so `in(x) ≤ 2 + h(u)`.
* `H_in` (**Lemma 10′(ii)**): `I(η) ⊆ I(u) ∖ {η}` for `η ∈ H(u)`; so `in(η) ≤ 5`, and `out(η) ≥ 6`.
* `X_disj` (**Lemma 10′(iii)**): distinct roots have disjoint out-neighbourhoods.
* `H_excess` (**Lemma 10″**): if `η ∈ H(u)` for every `u` in a nonempty set `R` of roots, then
  `in(η) + |R| ≤ out(η)`. (Summing `in(η) + a_j ≤ 5` over `j ∈ R` and `|R| + 5 ≤ out_R(i) + out(η)` over `i ∈ R`.)
* `no_root` (**Theorem 11**): `Σ_{non-roots} (out − in) = #roots`, while `H* ∪ X′` (`X′` the union of `O(u)` over
  roots with `h(u) ≤ 3`) consists of non-roots and carries at least `Σ_u (h(u) + 5 (3 − h(u))⁺) ≥ 3 · #roots`.
* `regular`: with no root, `in ≤ 5` everywhere and `Σ in = Σ out ≥ 105`.
-/

set_option linter.style.longLine false

namespace LeanCH.BR.BR45

open LeanCH.BR.BRq2 LeanCH.BR.BRq3 CH Compose.Boundary Compose.FloorSix

/-- The boundary vertex set at `(q, s) = (4, 5)`. -/
abbrev V45 : Finset ℕ := Finset.range 21

/-- The tight profile `(5,4,5)` at `u`. -/
def TightAt (E : CH.Digraph) (V : Finset ℕ) (u : ℕ) : Prop :=
  (outN E V u).card = 5 ∧ (ball E V u 2).card = 10 ∧
  ∀ x ∈ outN E V u, (outN E V x).card = 5 ∧ (outN E (outN E V u) x).card = 1 ∧
    (inN E (outN E V u) x).card = 1 ∧ ∀ y ∈ ball E V u 2, y ∉ ball E V u 1 → E x y = true

/-- Hypothesis (i): the strict cap `b_3 ≥ 15` in every `(4,5)` boundary graph. -/
def Cap45 : Prop :=
  ∀ E : CH.Digraph, QFree E V45 4 → (∀ v ∈ V45, 5 ≤ (outN E V45 v).card) →
    ∀ u ∈ V45, 15 ≤ (ball E V45 u 3).card

/-- Hypothesis (ii): a vertex with `b_3 = 15` has the tight profile `(5,4,5)`. -/
def Tight45 : Prop :=
  ∀ E : CH.Digraph, QFree E V45 4 → (∀ v ∈ V45, 5 ≤ (outN E V45 v).card) →
    ∀ u ∈ V45, (ball E V45 u 3).card = 15 → TightAt E V45 u

/-- `H(u)`: in-neighbours of `u` heading all of `O(u)`. -/
noncomputable def HS (E : CH.Digraph) (V : Finset ℕ) (u : ℕ) : Finset ℕ :=
  open Classical in (inN E V u).filter (fun η => ∀ x ∈ outN E V u, E η x = true)

/-- A saturated `(4,5)` boundary graph with the strict cap and the tight profile. -/
structure DHyp (E : CH.Digraph) (V : Finset ℕ) : Prop where
  cV : V.card = 21
  free : QFree E V 4
  out : ∀ v ∈ V, 5 ≤ (outN E V v).card
  sat : Sat E V
  cap : ∀ u ∈ V, 15 ≤ (ball E V u 3).card
  tight : ∀ u ∈ V, (ball E V u 3).card = 15 → TightAt E V u

variable {E : CH.Digraph} {V : Finset ℕ}

theorem mem_HS {u η : ℕ} : η ∈ HS E V u ↔ η ∈ inN E V u ∧ ∀ x ∈ outN E V u, E η x = true := by
  classical
  unfold HS
  exact Finset.mem_filter

/-- A vertex of `N_3(u)` has an in-neighbour in `N_2(u)`. -/
theorem layer3 {u z : ℕ} (hu : u ∈ V) (hz3 : z ∈ ball E V u 3) (hz2 : z ∉ ball E V u 2) :
    ∃ y, y ∈ ball E V u 2 ∧ y ∉ ball E V u 1 ∧ E y z = true := by
  obtain ⟨y, hy, hyz⟩ := ball_succ_pred hu hz3 hz2
  exact ⟨y, hy, fun h1 => hz2 (ball_step h1 (ball_subset hz3) hyz), hyz⟩

namespace DHyp

theorem in_add (H : DHyp E V) {v : ℕ} (hv : v ∈ V) : (inN E V v).card + (ball E V v 3).card = 21 := by
  rw [card_inN_of_sat H.free H.sat hv, H.cV]

theorem in_le (H : DHyp E V) {v : ℕ} (hv : v ∈ V) : (inN E V v).card ≤ 6 := by
  have := H.in_add hv
  have := H.cap v hv
  omega

theorem tightAt (H : DHyp E V) {u : ℕ} (hu : u ∈ V) (hr : (inN E V u).card = 6) : TightAt E V u := by
  have := H.in_add hu
  exact H.tight u hu (by omega)

/-- **Lemma 10′(i).** -/
theorem root_in (H : DHyp E V) {u x : ℕ} (hu : u ∈ V) (hr : (inN E V u).card = 6)
    (hx : x ∈ outN E V u) : inN E V x ⊆ insert u (inN E (outN E V u) x ∪ HS E V u) := by
  classical
  have hT := H.tightAt hu hr
  obtain ⟨hxV, hux⟩ := mem_outN.mp hx
  obtain ⟨-, -, -, hxY⟩ := hT.2.2 x hx
  intro p hp
  obtain ⟨hpV, hpx⟩ := mem_inN.mp hp
  by_cases hp3 : p ∈ ball E V u 3
  · by_cases hp2 : p ∈ ball E V u 2
    · by_cases hp1 : p ∈ ball E V u 1
      · rcases (mem_ball_one hu).mp hp1 with h | h
        · rw [h]
          exact Finset.mem_insert_self _ _
        · exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (mem_inN.mpr ⟨h, hpx⟩))
      · exact (n2 H.free hxV hpV (hxY p hp2 hp1) hpx).elim
    · obtain ⟨y, hy2, hy1, hyp⟩ := layer3 hu hp3 hp2
      exact (n3 H.free hxV (ball_subset hy2) hpV (hxY y hy2 hy1) hyp hpx).elim
  · have hpI : p ∈ inN E V u := by
      rw [inN_eq_of_sat H.free H.sat hu]
      exact Finset.mem_sdiff.mpr ⟨hpV, hp3⟩
    refine Finset.mem_insert_of_mem (Finset.mem_union_right _ (mem_HS.mpr ⟨hpI, fun x' hx' => ?_⟩))
    by_contra hpx'
    obtain ⟨z, hz, hz3, hz2⟩ := sat_d2 H.free H.sat hu hpI hx' hpx'
    obtain ⟨y, hy2, hy1, hyz⟩ := layer3 hu hz3 hz2
    exact n4 H.free hxV (ball_subset hy2) (ball_subset hz3) hpV (hxY y hy2 hy1) hyz (mem_inN.mp hz).2 hpx

theorem root_in_card (H : DHyp E V) {u x : ℕ} (hu : u ∈ V) (hr : (inN E V u).card = 6)
    (hx : x ∈ outN E V u) : (inN E V x).card ≤ 2 + (HS E V u).card := by
  classical
  have h1 := Finset.card_le_card (H.root_in hu hr hx)
  have h2 := Finset.card_insert_le u (inN E (outN E V u) x ∪ HS E V u)
  have h3 := Finset.card_union_le (inN E (outN E V u) x) (HS E V u)
  have h4 := ((H.tightAt hu hr).2.2 x hx).2.2.1
  omega

/-- **Lemma 10′(ii).** -/
theorem H_in (H : DHyp E V) {u η : ℕ} (hu : u ∈ V) (hr : (inN E V u).card = 6) (hη : η ∈ HS E V u) :
    inN E V η ⊆ (inN E V u).erase η := by
  classical
  obtain ⟨hηI, hηX⟩ := mem_HS.mp hη
  obtain ⟨hηV, hηu⟩ := mem_inN.mp hηI
  have hT := H.tightAt hu hr
  obtain ⟨x, hx⟩ : (outN E V u).Nonempty := Finset.card_pos.mp (by rw [hT.1]; omega)
  obtain ⟨hxV, hux⟩ := mem_outN.mp hx
  obtain ⟨-, -, -, hxY⟩ := hT.2.2 x hx
  intro p hp
  obtain ⟨hpV, hpη⟩ := mem_inN.mp hp
  refine Finset.mem_erase.mpr ⟨ne_of_arc H.free hηV hpη, ?_⟩
  rw [inN_eq_of_sat H.free H.sat hu]
  refine Finset.mem_sdiff.mpr ⟨hpV, fun hp3 => ?_⟩
  have hp2 := sat_d1 H.free hu hηI hp
  obtain ⟨y, hy2, hy1, hyp⟩ := layer3 hu hp3 hp2
  exact n4 H.free hxV (ball_subset hy2) hpV hηV (hxY y hy2 hy1) hyp hpη (hηX x hx)

theorem H_in_card (H : DHyp E V) {u η : ℕ} (hu : u ∈ V) (hr : (inN E V u).card = 6)
    (hη : η ∈ HS E V u) : (inN E V η).card ≤ 5 := by
  classical
  have h1 := Finset.card_le_card (H.H_in hu hr hη)
  rw [Finset.card_erase_of_mem (mem_HS.mp hη).1, hr] at h1
  exact h1

theorem H_out_card (H : DHyp E V) {u η : ℕ} (hu : u ∈ V) (hr : (inN E V u).card = 6)
    (hη : η ∈ HS E V u) : 6 ≤ (outN E V η).card := by
  classical
  obtain ⟨hηI, hηX⟩ := mem_HS.mp hη
  have hsub : insert u (outN E V u) ⊆ outN E V η := by
    intro z hz
    rcases Finset.mem_insert.mp hz with h | h
    · rw [h]
      exact mem_outN.mpr ⟨hu, (mem_inN.mp hηI).2⟩
    · exact mem_outN.mpr ⟨(mem_outN.mp h).1, hηX z h⟩
  have hnot : u ∉ outN E V u := fun h => n1 H.free hu (mem_outN.mp h).2
  have := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hnot, (H.tightAt hu hr).1] at this
  exact this

/-- **Lemma 10′(iii).** -/
theorem X_disj (H : DHyp E V) {u u' : ℕ} (hu : u ∈ V) (hu' : u' ∈ V) (hr : (inN E V u).card = 6)
    (hr' : (inN E V u').card = 6) (hne : u ≠ u') : Disjoint (outN E V u) (outN E V u') := by
  classical
  have key : ∀ {a b : ℕ}, a ∈ V → b ∈ V → (inN E V a).card = 6 → (inN E V b).card = 6 → a ≠ b →
      ∀ x, x ∈ outN E V a → x ∈ outN E V b → E a b = true := by
    intro a b ha hb hra hrb hab x hxa hxb
    have hbI : b ∈ inN E V x := mem_inN.mpr ⟨hb, (mem_outN.mp hxb).2⟩
    rcases Finset.mem_insert.mp (H.root_in ha hra hxa hbI) with h | h
    · exact absurd h.symm hab
    · rcases Finset.mem_union.mp h with h | h
      · exact (mem_outN.mp (mem_inN.mp h).1).2
      · have := H.H_in_card ha hra h
        omega
  rw [Finset.disjoint_left]
  intro x hx hx'
  exact n2 H.free hu hu' (key hu hu' hr hr' hne x hx hx') (key hu' hu hr' hr hne.symm x hx' hx)

/-- **Lemma 10″.** -/
theorem H_excess (H : DHyp E V) {η : ℕ} {R : Finset ℕ} (hne : R.Nonempty)
    (hR : ∀ u ∈ R, u ∈ V ∧ (inN E V u).card = 6 ∧ η ∈ HS E V u) :
    (inN E V η).card + R.card ≤ (outN E V η).card := by
  classical
  obtain ⟨u0, hu0⟩ := hne
  obtain ⟨hu0V, hr0, hη0⟩ := hR u0 hu0
  have hηV : η ∈ V := (mem_inN.mp (mem_HS.mp hη0).1).1
  have hηarc : ∀ i ∈ R, E η i = true := fun i hi => (mem_inN.mp (mem_HS.mp (hR i hi).2.2).1).2
  have hA : ∀ j ∈ R, (inN E V η).card + (R.filter (fun i => E i j = true)).card ≤ 5 := by
    intro j hj
    obtain ⟨hjV, hrj, hηj⟩ := hR j hj
    have hsub : inN E V η ∪ R.filter (fun i => E i j = true) ⊆ (inN E V j).erase η := by
      intro p hp
      rcases Finset.mem_union.mp hp with h | h
      · exact H.H_in hjV hrj hηj h
      · obtain ⟨hpR, hpj⟩ := Finset.mem_filter.mp h
        refine Finset.mem_erase.mpr ⟨?_, mem_inN.mpr ⟨(hR p hpR).1, hpj⟩⟩
        rintro rfl
        exact n1 H.free hηV (hηarc p hpR)
    have hdisj : Disjoint (inN E V η) (R.filter (fun i => E i j = true)) := by
      rw [Finset.disjoint_left]
      intro p hp1 hp2
      obtain ⟨hpV, hpη⟩ := mem_inN.mp hp1
      exact n2 H.free hpV hηV hpη (hηarc p (Finset.mem_filter.mp hp2).1)
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdisj, Finset.card_erase_of_mem (mem_HS.mp hηj).1, hrj] at h1
    exact h1
  have hB : ∀ i ∈ R, R.card + 5 ≤ (R.filter (fun j => E i j = true)).card + (outN E V η).card := by
    intro i hi
    obtain ⟨hiV, hri, hηi⟩ := hR i hi
    have hiO : i ∈ outN E V η := mem_outN.mpr ⟨hiV, hηarc i hi⟩
    have hsub1 : outN E V i ⊆ (outN E V η).erase i := by
      intro x hx
      refine Finset.mem_erase.mpr ⟨?_, mem_outN.mpr ⟨(mem_outN.mp hx).1, (mem_HS.mp hηi).2 x hx⟩⟩
      rintro rfl
      exact n1 H.free hiV (mem_outN.mp hx).2
    have hsub2 : R.erase i ⊆ R.filter (fun j => E i j = true) ∪ ((outN E V η).erase i \ outN E V i) := by
      intro j hj
      obtain ⟨hji, hjR⟩ := Finset.mem_erase.mp hj
      by_cases hij : E i j = true
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hjR, hij⟩)
      · refine Finset.mem_union_right _ (Finset.mem_sdiff.mpr
          ⟨Finset.mem_erase.mpr ⟨hji, mem_outN.mpr ⟨(hR j hjR).1, hηarc j hjR⟩⟩, fun h => hij (mem_outN.mp h).2⟩)
    have h1 := Finset.card_le_card hsub2
    have h2 := Finset.card_union_le (R.filter (fun j => E i j = true)) ((outN E V η).erase i \ outN E V i)
    have h3 := Finset.card_sdiff_of_subset hsub1
    have h4 := Finset.card_erase_of_mem hiO
    have h5 := Finset.card_erase_of_mem hi
    have h6 := (H.tightAt hiV hri).1
    have h7 := Finset.card_le_card hsub1
    have h8 : 0 < R.card := Finset.card_pos.mpr ⟨i, hi⟩
    omega
  have sA := Finset.sum_le_sum hA
  have sB := Finset.sum_le_sum hB
  rw [Finset.sum_add_distrib, sum_const', sum_const'] at sA
  rw [sum_const', Finset.sum_add_distrib, sum_const'] at sB
  have hd := dcount R R (fun i j => E i j = true)
  rw [hd] at sB
  have hmul : R.card * ((inN E V η).card + R.card) ≤ R.card * (outN E V η).card := by nlinarith
  exact Nat.le_of_mul_le_mul_left hmul (Finset.card_pos.mpr ⟨u0, hu0⟩)

/-- **Theorem 11.** A saturated `(4,5)` boundary graph has no root. -/
theorem no_root (H : DHyp E V) : ∀ u ∈ V, (inN E V u).card ≠ 6 := by
  classical
  set Zr := V.filter (fun u => (inN E V u).card = 6) with hZr
  have hZV : Zr ⊆ V := Finset.filter_subset _ _
  have hZ : ∀ {u : ℕ}, u ∈ Zr → u ∈ V ∧ (inN E V u).card = 6 := fun h => Finset.mem_filter.mp h
  set Hs := Zr.biUnion (fun u => HS E V u) with hHs
  set Zr' := Zr.filter (fun u => (HS E V u).card ≤ 3) with hZr'
  set Xs := Zr'.biUnion (fun u => outN E V u) with hXs
  -- non-roots
  have hNR : ∀ v ∈ V \ Zr, (inN E V v).card ≤ 5 ∧ 5 ≤ (outN E V v).card := by
    intro v hv
    obtain ⟨hvV, hvZ⟩ := Finset.mem_sdiff.mp hv
    have h1 := H.in_le hvV
    have h2 : (inN E V v).card ≠ 6 := fun h => hvZ (Finset.mem_filter.mpr ⟨hvV, h⟩)
    exact ⟨by omega, H.out v hvV⟩
  have hHsub : Hs ⊆ V \ Zr := by
    intro η hη
    obtain ⟨u, hu, hηu⟩ := Finset.mem_biUnion.mp hη
    obtain ⟨huV, hr⟩ := hZ hu
    refine Finset.mem_sdiff.mpr ⟨(mem_inN.mp (mem_HS.mp hηu).1).1, fun h => ?_⟩
    have := H.H_in_card huV hr hηu
    have := (hZ h).2
    omega
  have hXsub : Xs ⊆ V \ Zr := by
    intro x hx
    obtain ⟨u, hu, hxu⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨huZ, hh⟩ := Finset.mem_filter.mp hu
    obtain ⟨huV, hr⟩ := hZ huZ
    refine Finset.mem_sdiff.mpr ⟨(mem_outN.mp hxu).1, fun h => ?_⟩
    have := H.root_in_card huV hr hxu
    have := (hZ h).2
    omega
  have hdisj : Disjoint Hs Xs := by
    rw [Finset.disjoint_left]
    intro η hη hx
    obtain ⟨u, hu, hηu⟩ := Finset.mem_biUnion.mp hη
    obtain ⟨u', hu', hxu'⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨huV, hr⟩ := hZ hu
    obtain ⟨hu'V, hr'⟩ := hZ (Finset.mem_filter.mp hu').1
    have h1 := H.H_out_card huV hr hηu
    have h2 := ((H.tightAt hu'V hr').2.2 η hxu').1
    omega
  -- the excess on `H*`
  have hH : ∑ u ∈ Zr, (HS E V u).card ≤ ∑ η ∈ Hs, ((outN E V η).card - (inN E V η).card) := by
    have h1 : ∑ η ∈ Hs, (Zr.filter (fun u => η ∈ HS E V u)).card ≤
        ∑ η ∈ Hs, ((outN E V η).card - (inN E V η).card) := by
      refine Finset.sum_le_sum (fun η hη => ?_)
      obtain ⟨u, hu, hηu⟩ := Finset.mem_biUnion.mp hη
      have := H.H_excess (η := η) (R := Zr.filter (fun u => η ∈ HS E V u))
        ⟨u, Finset.mem_filter.mpr ⟨hu, hηu⟩⟩
        (fun u' hu' => ⟨(hZ (Finset.mem_filter.mp hu').1).1, (hZ (Finset.mem_filter.mp hu').1).2,
          (Finset.mem_filter.mp hu').2⟩)
      omega
    rw [dcount Hs Zr (fun η u => η ∈ HS E V u)] at h1
    refine le_trans (le_of_eq (Finset.sum_congr rfl (fun u hu => ?_))) h1
    congr 1
    ext η
    rw [Finset.mem_filter]
    exact ⟨fun h => ⟨Finset.mem_biUnion.mpr ⟨u, hu, h⟩, h⟩, fun h => h.2⟩
  -- the excess on `X′`
  have hX : ∑ u ∈ Zr', 5 * (3 - (HS E V u).card) ≤ ∑ x ∈ Xs, ((outN E V x).card - (inN E V x).card) := by
    have hpd : ∀ u ∈ Zr', ∀ u' ∈ Zr', u ≠ u' → Disjoint (outN E V u) (outN E V u') := by
      intro u hu u' hu' hne
      obtain ⟨huV, hr⟩ := hZ (Finset.mem_filter.mp hu).1
      obtain ⟨hu'V, hr'⟩ := hZ (Finset.mem_filter.mp hu').1
      exact H.X_disj huV hu'V hr hr' hne
    rw [hXs, Finset.sum_biUnion hpd]
    refine Finset.sum_le_sum (fun u hu => ?_)
    obtain ⟨huV, hr⟩ := hZ (Finset.mem_filter.mp hu).1
    have hT := H.tightAt huV hr
    have h1 : ∑ _x ∈ outN E V u, (3 - (HS E V u).card) ≤
        ∑ x ∈ outN E V u, ((outN E V x).card - (inN E V x).card) := by
      refine Finset.sum_le_sum (fun x hx => ?_)
      have := H.root_in_card huV hr hx
      have := (hT.2.2 x hx).1
      omega
    rw [sum_const', hT.1] at h1
    exact h1
  -- the total excess on the non-roots
  have hTot : ∑ v ∈ V \ Zr, ((outN E V v).card - (inN E V v).card) = Zr.card := by
    have hsum : ∑ y ∈ V, (outN E V y).card = ∑ z ∈ V, (inN E V z).card :=
      Compose.ThinRigid.sum_out_eq_sum_in E V
    rw [← Finset.sum_sdiff hZV, ← Finset.sum_sdiff (f := fun z => (inN E V z).card) hZV] at hsum
    have ho : ∑ u ∈ Zr, (outN E V u).card = Zr.card * 5 := by
      rw [← sum_const']
      exact Finset.sum_congr rfl (fun u hu => (H.tightAt (hZ hu).1 (hZ hu).2).1)
    have hi : ∑ u ∈ Zr, (inN E V u).card = Zr.card * 6 := by
      rw [← sum_const']
      exact Finset.sum_congr rfl (fun u hu => (hZ hu).2)
    have hs : ∑ v ∈ V \ Zr, (outN E V v).card =
        ∑ v ∈ V \ Zr, (inN E V v).card + ∑ v ∈ V \ Zr, ((outN E V v).card - (inN E V v).card) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun v hv => ?_)
      have := hNR v hv
      omega
    omega
  have hsub : ∑ v ∈ Hs ∪ Xs, ((outN E V v).card - (inN E V v).card) ≤
      ∑ v ∈ V \ Zr, ((outN E V v).card - (inN E V v).card) :=
    Finset.sum_le_sum_of_subset (Finset.union_subset hHsub hXsub)
  rw [Finset.sum_union hdisj, hTot] at hsub
  have h3 : ∑ _u ∈ Zr, 3 ≤ ∑ u ∈ Zr, (HS E V u).card + ∑ u ∈ Zr', 5 * (3 - (HS E V u).card) := by
    have e : ∑ u ∈ Zr', 5 * (3 - (HS E V u).card) =
        ∑ u ∈ Zr, if (HS E V u).card ≤ 3 then 5 * (3 - (HS E V u).card) else 0 :=
      Finset.sum_filter _ _
    rw [e, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum (fun u _ => ?_)
    split_ifs <;> omega
  rw [sum_const'] at h3
  have hZ0 : Zr.card = 0 := by omega
  intro u hu hr
  have : u ∈ Zr := Finset.mem_filter.mpr ⟨hu, hr⟩
  rw [Finset.card_eq_zero.mp hZ0] at this
  exact Finset.notMem_empty _ this

/-- With no root, a saturated `(4,5)` boundary graph is in-regular. -/
theorem regular (H : DHyp E V) : ∀ v ∈ V, (inN E V v).card = 5 := by
  classical
  have hle : ∀ v ∈ V, (inN E V v).card ≤ 5 := fun v hv => by
    have := H.in_le hv
    have := H.no_root v hv
    omega
  have hsum : ∑ y ∈ V, (outN E V y).card = ∑ z ∈ V, (inN E V z).card :=
    Compose.ThinRigid.sum_out_eq_sum_in E V
  have h1 : ∑ _y ∈ V, 5 ≤ ∑ y ∈ V, (outN E V y).card := Finset.sum_le_sum H.out
  have h2 : ∑ z ∈ V, (inN E V z).card ≤ ∑ _y ∈ V, 5 := Finset.sum_le_sum hle
  have heq : ∑ z ∈ V, (inN E V z).card = ∑ _y ∈ V, 5 := le_antisymm h2 (hsum ▸ h1)
  exact (Finset.sum_eq_sum_iff_of_le hle).mp heq

end DHyp

/-- **Theorem 11, conditional form.** The strict cap and the tight profile give `BR(4,5)`. -/
theorem br45_of_cap_tight (hc : Cap45) (ht : Tight45) : BoundaryRegular 4 5 :=
  br45_of_sat (fun E hfree hout hsat =>
    DHyp.regular ⟨Finset.card_range 21, hfree, hout, hsat, hc E hfree hout, ht E hfree hout⟩)

end LeanCH.BR.BR45
