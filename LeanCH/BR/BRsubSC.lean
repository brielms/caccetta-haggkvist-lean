import LeanCH.BR.BRsubSat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The sub-diagonal family: `SC(s) ⇒ BR(s-1, s)` for every `s ≥ 4` (Lean 4.35.0)

Paper: `checkpoints/boundary_20261111/BRsubdiag_attempt_subagent.md` §1 (Lemma 1), §2 (definitions), §3 (Lemma 10′,
Lemma 10″, Theorem 11). Generalises `LeanCH/BR/BR45Disc.lean` (the case `s = 5`) to every `s ≥ 4`, `q = s - 1`.

* `TightRoot E V s u`: `out(u) = s`, `|N_2(u)| = s - 1`, and every `x ∈ X = O(u)` has `out(x) = s`, exactly one head
  and exactly one in-neighbour in `X` (`D[X] = C_s`), and heads every vertex of `N_2(u)`.
* `SC s` (the strict cap, saturated form): in every `(s-1)`-free digraph on `range ((s-1)s+1)` with min out `≥ s`
  that is saturated (`Sat (s-1)`), every `u` has `|B_{s-2}(u)| ≥ (s-2)s`, and equality makes `u` a tight root.
* `br_of_sc : 4 ≤ s → SC s → BoundaryRegular (s - 1) s`.

Inside the proof (`SHyp q s E V`, with `q + 1 = s`): a *root* is a vertex of in-degree `s + 1` (by Lemma 1(b) this is
`|B_{q-1}(u)| = (q-1)s`, so a tight root).

* `root_in` (**Lemma 10′(i)**): `I(x) ⊆ {u} ∪ (I(x) ∩ X) ∪ H(u)`; so `in(x) ≤ 2 + h(u)`.
* `H_in` (**Lemma 10′(ii)**): `I(η) ⊆ I(u) ∖ {η}`; so `in(η) ≤ s`, and `out(η) ≥ s + 1`.
* `X_disj` (**Lemma 10′(iii)**): distinct roots have disjoint out-neighbourhoods.
* `H_excess` (**Lemma 10″**): `in(η) + |R| ≤ out(η)` if `η ∈ H(u)` for every `u` in a nonempty set `R` of roots.
* `no_root` (**Theorem 11**): per root `f(h) = h + s(s-2-h)⁺ ≥ s - 2 ≥ 2` units of excess, cost `1`.
* `regular`: no root, so `in ≤ s` everywhere and `Σ in = Σ out ≥ s|V|`.
-/

set_option linter.style.longLine false

namespace LeanCH.BR.BRsub

open LeanCH.BR.BRq2 LeanCH.BR.BRq3 LeanCH.BR.BR45 CH Compose.Boundary Compose.FloorSix

/-- A tight root at out-degree `s`: `out(u) = s`, `|N_2(u)| = s - 1`, and every `x ∈ O(u)` has `out(x) = s`, one head
and one tail in `O(u)` (so `D[O(u)]` is a directed `s`-cycle), and heads every vertex of `N_2(u)`. -/
def TightRoot (E : CH.Digraph) (V : Finset ℕ) (s u : ℕ) : Prop :=
  (outN E V u).card = s ∧ (ball E V u 2 \ ball E V u 1).card = s - 1 ∧
  ∀ x ∈ outN E V u, (outN E V x).card = s ∧ (outN E (outN E V u) x).card = 1 ∧
    (inN E (outN E V u) x).card = 1 ∧ ∀ y ∈ ball E V u 2, y ∉ ball E V u 1 → E x y = true

/-- **SC(s)**, the strict cap at `(q, s) = (s - 1, s)` on saturated boundary graphs. -/
def SC (s : ℕ) : Prop :=
  ∀ E : CH.Digraph, QFree E (Finset.range ((s - 1) * s + 1)) (s - 1) →
    (∀ v ∈ Finset.range ((s - 1) * s + 1), s ≤ (outN E (Finset.range ((s - 1) * s + 1)) v).card) →
    Sat (s - 1) E (Finset.range ((s - 1) * s + 1)) →
    ∀ u ∈ Finset.range ((s - 1) * s + 1),
      (s - 2) * s ≤ (ball E (Finset.range ((s - 1) * s + 1)) u (s - 2)).card ∧
      ((ball E (Finset.range ((s - 1) * s + 1)) u (s - 2)).card = (s - 2) * s →
        TightRoot E (Finset.range ((s - 1) * s + 1)) s u)

/-- A saturated `(q, s)` boundary graph, `q = s - 1`, with the strict cap and tight roots. -/
structure SHyp (q s : ℕ) (E : CH.Digraph) (V : Finset ℕ) : Prop where
  hs : 4 ≤ s
  hq : q + 1 = s
  cV : V.card = q * s + 1
  free : QFree E V q
  out : ∀ v ∈ V, s ≤ (outN E V v).card
  sat : Sat q E V
  cap : ∀ u ∈ V, (q - 1) * s ≤ (ball E V u (q - 1)).card
  tight : ∀ u ∈ V, (ball E V u (q - 1)).card = (q - 1) * s → TightRoot E V s u

/-- `H(u)`: in-neighbours of `u` heading all of `O(u)`. -/
noncomputable def HS (E : CH.Digraph) (V : Finset ℕ) (u : ℕ) : Finset ℕ :=
  open Classical in (inN E V u).filter (fun η => ∀ x ∈ outN E V u, E η x = true)

theorem mem_HS {E : CH.Digraph} {V : Finset ℕ} {u η : ℕ} :
    η ∈ HS E V u ↔ η ∈ inN E V u ∧ ∀ x ∈ outN E V u, E η x = true := by
  classical
  unfold HS
  exact Finset.mem_filter

theorem pred_mul_add {q s : ℕ} (hq : 1 ≤ q) : (q - 1) * s + s = q * s := by
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  ring

variable {q s : ℕ} {E : CH.Digraph} {V : Finset ℕ}

namespace SHyp

theorem q3 (H : SHyp q s E V) : 3 ≤ q := by
  have := H.hq
  have := H.hs
  omega

theorem in_add (H : SHyp q s E V) {v : ℕ} (hv : v ∈ V) :
    (inN E V v).card + (ball E V v (q - 1)).card = q * s + 1 := by
  have := H.q3
  rw [card_inN_of_satQ (by omega) H.free H.sat hv, H.cV]

theorem in_le (H : SHyp q s E V) {v : ℕ} (hv : v ∈ V) : (inN E V v).card ≤ s + 1 := by
  have h1 := H.in_add hv
  have h2 := H.cap v hv
  have h3 := pred_mul_add (q := q) (s := s) (by have := H.q3; omega)
  omega

theorem tightAt (H : SHyp q s E V) {u : ℕ} (hu : u ∈ V) (hr : (inN E V u).card = s + 1) :
    TightRoot E V s u := by
  have h1 := H.in_add hu
  have h3 := pred_mul_add (q := q) (s := s) (by have := H.q3; omega)
  exact H.tight u hu (by omega)

/-- **Lemma 10′(i).** -/
theorem root_in (H : SHyp q s E V) {u x : ℕ} (hu : u ∈ V) (hr : (inN E V u).card = s + 1)
    (hx : x ∈ outN E V u) : inN E V x ⊆ insert u (inN E (outN E V u) x ∪ HS E V u) := by
  classical
  have hq3 := H.q3
  have hT := H.tightAt hu hr
  obtain ⟨hxV, hux⟩ := mem_outN.mp hx
  obtain ⟨-, -, -, hxY⟩ := hT.2.2 x hx
  intro p hp
  obtain ⟨hpV, hpx⟩ := mem_inN.mp hp
  by_cases hp1 : p ∈ ball E V u 1
  · rcases (mem_ball_one hu).mp hp1 with h | h
    · rw [h]
      exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (mem_inN.mpr ⟨h, hpx⟩))
  by_cases hpq : p ∈ ball E V u (q - 1)
  · exact (no_back_arc H.free hxV (reach_of_heads hu hxY (by omega) hpq hp1) (by omega) hpx).elim
  · have hpI : p ∈ inN E V u := by
      rw [inN_eq_of_satQ (by omega) H.free H.sat hu]
      exact Finset.mem_sdiff.mpr ⟨hpV, hpq⟩
    refine Finset.mem_insert_of_mem (Finset.mem_union_right _ (mem_HS.mpr ⟨hpI, fun x' hx' => ?_⟩))
    by_contra hpx'
    obtain ⟨z, hz, hzq, hzq2⟩ := sat_d2Q (by omega) H.free H.sat hu hpI hx' hpx'
    have hz1 : z ∉ ball E V u 1 := fun h => hzq2 (ball_mono_radius (by omega) h)
    have hzx := reach_of_heads hu hxY (by omega) hzq hz1
    have hpx2 := ball_step hzx hpV (mem_inN.mp hz).2
    exact no_back_arc H.free hxV hpx2 (by omega) hpx

theorem root_in_card (H : SHyp q s E V) {u x : ℕ} (hu : u ∈ V) (hr : (inN E V u).card = s + 1)
    (hx : x ∈ outN E V u) : (inN E V x).card ≤ 2 + (HS E V u).card := by
  classical
  have h1 := Finset.card_le_card (H.root_in hu hr hx)
  have h2 := Finset.card_insert_le u (inN E (outN E V u) x ∪ HS E V u)
  have h3 := Finset.card_union_le (inN E (outN E V u) x) (HS E V u)
  have h4 := ((H.tightAt hu hr).2.2 x hx).2.2.1
  omega

/-- **Lemma 10′(ii).** -/
theorem H_in (H : SHyp q s E V) {u η : ℕ} (hu : u ∈ V) (hr : (inN E V u).card = s + 1)
    (hη : η ∈ HS E V u) : inN E V η ⊆ (inN E V u).erase η := by
  classical
  have hq3 := H.q3
  obtain ⟨hηI, hηX⟩ := mem_HS.mp hη
  obtain ⟨hηV, hηu⟩ := mem_inN.mp hηI
  have hT := H.tightAt hu hr
  obtain ⟨x, hx⟩ : (outN E V u).Nonempty := Finset.card_pos.mp (by rw [hT.1]; have := H.hs; omega)
  obtain ⟨hxV, hux⟩ := mem_outN.mp hx
  obtain ⟨-, -, -, hxY⟩ := hT.2.2 x hx
  intro p hp
  obtain ⟨hpV, hpη⟩ := mem_inN.mp hp
  refine Finset.mem_erase.mpr ⟨fun h => ?_, ?_⟩
  · rw [h] at hpη
    exact loopfree H.free (by omega) hηV hpη
  · rw [inN_eq_of_satQ (by omega) H.free H.sat hu]
    refine Finset.mem_sdiff.mpr ⟨hpV, fun hpq => ?_⟩
    have hp2 := sat_d1Q (by omega) H.free hu hηI hp
    have hp1 : p ∉ ball E V u 1 := fun h => hp2 (ball_mono_radius (by omega) h)
    have hpx := reach_of_heads hu hxY (by omega) hpq hp1
    have hηx := ball_step hpx hηV hpη
    exact no_back_arc H.free hxV hηx (by omega) (hηX x hx)

theorem H_in_card (H : SHyp q s E V) {u η : ℕ} (hu : u ∈ V) (hr : (inN E V u).card = s + 1)
    (hη : η ∈ HS E V u) : (inN E V η).card ≤ s := by
  classical
  have h1 := Finset.card_le_card (H.H_in hu hr hη)
  rw [Finset.card_erase_of_mem (mem_HS.mp hη).1, hr] at h1
  omega

theorem H_out_card (H : SHyp q s E V) {u η : ℕ} (hu : u ∈ V) (hr : (inN E V u).card = s + 1)
    (hη : η ∈ HS E V u) : s + 1 ≤ (outN E V η).card := by
  classical
  have hq3 := H.q3
  obtain ⟨hηI, hηX⟩ := mem_HS.mp hη
  have hsub : insert u (outN E V u) ⊆ outN E V η := by
    intro z hz
    rcases Finset.mem_insert.mp hz with h | h
    · rw [h]
      exact mem_outN.mpr ⟨hu, (mem_inN.mp hηI).2⟩
    · exact mem_outN.mpr ⟨(mem_outN.mp h).1, hηX z h⟩
  have hnot : u ∉ outN E V u := fun h => loopfree H.free (by omega) hu (mem_outN.mp h).2
  have := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hnot, (H.tightAt hu hr).1] at this
  exact this

/-- **Lemma 10′(iii).** -/
theorem X_disj (H : SHyp q s E V) {u u' : ℕ} (hu : u ∈ V) (hu' : u' ∈ V) (hr : (inN E V u).card = s + 1)
    (hr' : (inN E V u').card = s + 1) (hne : u ≠ u') : Disjoint (outN E V u) (outN E V u') := by
  classical
  have hq3 := H.q3
  have key : ∀ {a b : ℕ}, a ∈ V → b ∈ V → (inN E V a).card = s + 1 → (inN E V b).card = s + 1 → a ≠ b →
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
  exact digonfree H.free (by omega) hu hu' (key hu hu' hr hr' hne x hx hx') (key hu' hu hr' hr hne.symm x hx' hx)

/-- **Lemma 10″.** -/
theorem H_excess (H : SHyp q s E V) {η : ℕ} {R : Finset ℕ} (hne : R.Nonempty)
    (hR : ∀ u ∈ R, u ∈ V ∧ (inN E V u).card = s + 1 ∧ η ∈ HS E V u) :
    (inN E V η).card + R.card ≤ (outN E V η).card := by
  classical
  have hq3 := H.q3
  obtain ⟨u0, hu0⟩ := hne
  obtain ⟨hu0V, hr0, hη0⟩ := hR u0 hu0
  have hηV : η ∈ V := (mem_inN.mp (mem_HS.mp hη0).1).1
  have hηarc : ∀ i ∈ R, E η i = true := fun i hi => (mem_inN.mp (mem_HS.mp (hR i hi).2.2).1).2
  have hA : ∀ j ∈ R, (inN E V η).card + (R.filter (fun i => E i j = true)).card ≤ s := by
    intro j hj
    obtain ⟨hjV, hrj, hηj⟩ := hR j hj
    have hsub : inN E V η ∪ R.filter (fun i => E i j = true) ⊆ (inN E V j).erase η := by
      intro p hp
      rcases Finset.mem_union.mp hp with h | h
      · exact H.H_in hjV hrj hηj h
      · obtain ⟨hpR, hpj⟩ := Finset.mem_filter.mp h
        refine Finset.mem_erase.mpr ⟨?_, mem_inN.mpr ⟨(hR p hpR).1, hpj⟩⟩
        rintro rfl
        exact loopfree H.free (by omega) hηV (hηarc p hpR)
    have hdisj : Disjoint (inN E V η) (R.filter (fun i => E i j = true)) := by
      rw [Finset.disjoint_left]
      intro p hp1 hp2
      obtain ⟨hpV, hpη⟩ := mem_inN.mp hp1
      exact digonfree H.free (by omega) hpV hηV hpη (hηarc p (Finset.mem_filter.mp hp2).1)
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdisj, Finset.card_erase_of_mem (mem_HS.mp hηj).1, hrj] at h1
    omega
  have hB : ∀ i ∈ R, R.card + s ≤ (R.filter (fun j => E i j = true)).card + (outN E V η).card := by
    intro i hi
    obtain ⟨hiV, hri, hηi⟩ := hR i hi
    have hiO : i ∈ outN E V η := mem_outN.mpr ⟨hiV, hηarc i hi⟩
    have hsub1 : outN E V i ⊆ (outN E V η).erase i := by
      intro x hx
      refine Finset.mem_erase.mpr ⟨?_, mem_outN.mpr ⟨(mem_outN.mp hx).1, (mem_HS.mp hηi).2 x hx⟩⟩
      rintro rfl
      exact loopfree H.free (by omega) hiV (mem_outN.mp hx).2
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
    have hs4 := H.hs
    omega
  have sA := Finset.sum_le_sum hA
  have sB := Finset.sum_le_sum hB
  rw [Finset.sum_add_distrib, sum_const', sum_const'] at sA
  rw [sum_const', Finset.sum_add_distrib, sum_const'] at sB
  have hd := dcount R R (fun i j => E i j = true)
  rw [hd] at sB
  have hmul : R.card * ((inN E V η).card + R.card) ≤ R.card * (outN E V η).card := by nlinarith
  exact Nat.le_of_mul_le_mul_left hmul (Finset.card_pos.mpr ⟨u0, hu0⟩)

/-- **Theorem 11.** A saturated `(s-1, s)` boundary graph with the strict cap has no root. -/
theorem no_root (H : SHyp q s E V) : ∀ u ∈ V, (inN E V u).card ≠ s + 1 := by
  classical
  have hs4 := H.hs
  set Zr := V.filter (fun u => (inN E V u).card = s + 1) with hZr
  have hZV : Zr ⊆ V := Finset.filter_subset _ _
  have hZ : ∀ {u : ℕ}, u ∈ Zr → u ∈ V ∧ (inN E V u).card = s + 1 := fun h => Finset.mem_filter.mp h
  set Hs := Zr.biUnion (fun u => HS E V u) with hHs
  set Zr' := Zr.filter (fun u => (HS E V u).card ≤ s - 2) with hZr'
  set Xs := Zr'.biUnion (fun u => outN E V u) with hXs
  -- non-roots
  have hNR : ∀ v ∈ V \ Zr, (inN E V v).card ≤ s ∧ s ≤ (outN E V v).card := by
    intro v hv
    obtain ⟨hvV, hvZ⟩ := Finset.mem_sdiff.mp hv
    have h1 := H.in_le hvV
    have h2 : (inN E V v).card ≠ s + 1 := fun h => hvZ (Finset.mem_filter.mpr ⟨hvV, h⟩)
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
  have hX : ∑ u ∈ Zr', s * (s - 2 - (HS E V u).card) ≤
      ∑ x ∈ Xs, ((outN E V x).card - (inN E V x).card) := by
    have hpd : ∀ u ∈ Zr', ∀ u' ∈ Zr', u ≠ u' → Disjoint (outN E V u) (outN E V u') := by
      intro u hu u' hu' hne
      obtain ⟨huV, hr⟩ := hZ (Finset.mem_filter.mp hu).1
      obtain ⟨hu'V, hr'⟩ := hZ (Finset.mem_filter.mp hu').1
      exact H.X_disj huV hu'V hr hr' hne
    rw [hXs, Finset.sum_biUnion hpd]
    refine Finset.sum_le_sum (fun u hu => ?_)
    obtain ⟨huV, hr⟩ := hZ (Finset.mem_filter.mp hu).1
    have hT := H.tightAt huV hr
    have h1 : ∑ _x ∈ outN E V u, (s - 2 - (HS E V u).card) ≤
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
    have ho : ∑ u ∈ Zr, (outN E V u).card = Zr.card * s := by
      rw [← sum_const']
      exact Finset.sum_congr rfl (fun u hu => (H.tightAt (hZ hu).1 (hZ hu).2).1)
    have hi : ∑ u ∈ Zr, (inN E V u).card = Zr.card * s + Zr.card := by
      rw [show Zr.card * s + Zr.card = Zr.card * (s + 1) by ring, ← sum_const']
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
  -- each root certifies `f(h) = h + s(s-2-h)⁺ ≥ s - 2` units
  have h3 : ∑ _u ∈ Zr, (s - 2) ≤ ∑ u ∈ Zr, (HS E V u).card + ∑ u ∈ Zr', s * (s - 2 - (HS E V u).card) := by
    have e : ∑ u ∈ Zr', s * (s - 2 - (HS E V u).card) =
        ∑ u ∈ Zr, if (HS E V u).card ≤ s - 2 then s * (s - 2 - (HS E V u).card) else 0 :=
      Finset.sum_filter _ _
    rw [e, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum (fun u _ => ?_)
    split_ifs with hle
    · have : s - 2 - (HS E V u).card ≤ s * (s - 2 - (HS E V u).card) :=
        Nat.le_mul_of_pos_left _ (by omega)
      omega
    · omega
  rw [sum_const'] at h3
  have h4 : Zr.card * 2 ≤ Zr.card * (s - 2) := Nat.mul_le_mul_left _ (by omega)
  have hZ0 : Zr.card = 0 := by omega
  intro u hu hr
  have : u ∈ Zr := Finset.mem_filter.mpr ⟨hu, hr⟩
  rw [Finset.card_eq_zero.mp hZ0] at this
  exact Finset.notMem_empty _ this

/-- With no root, a saturated `(s-1, s)` boundary graph is in-regular. -/
theorem regular (H : SHyp q s E V) : ∀ v ∈ V, (inN E V v).card = s := by
  classical
  have hle : ∀ v ∈ V, (inN E V v).card ≤ s := fun v hv => by
    have := H.in_le hv
    have := H.no_root v hv
    omega
  have hsum : ∑ y ∈ V, (outN E V y).card = ∑ z ∈ V, (inN E V z).card :=
    Compose.ThinRigid.sum_out_eq_sum_in E V
  have h1 : ∑ _y ∈ V, s ≤ ∑ y ∈ V, (outN E V y).card := Finset.sum_le_sum H.out
  have h2 : ∑ z ∈ V, (inN E V z).card ≤ ∑ _y ∈ V, s := Finset.sum_le_sum hle
  have heq : ∑ z ∈ V, (inN E V z).card = ∑ _y ∈ V, s := le_antisymm h2 (hsum ▸ h1)
  exact (Finset.sum_eq_sum_iff_of_le hle).mp heq

end SHyp

/-- **Theorem 11, general form (Theorem A of the note).** For every `s ≥ 4`, the strict cap `SC(s)` gives
`BR(s-1, s)`. -/
theorem br_of_sc {s : ℕ} (hs : 4 ≤ s) (hsc : SC s) : BoundaryRegular (s - 1) s :=
  br_of_satQ (fun E hfree hout hsat => by
    have e : s - 1 - 1 = s - 2 := by omega
    refine SHyp.regular (q := s - 1) ⟨hs, by omega, Finset.card_range _, hfree, hout, hsat, ?_, ?_⟩
    · intro u hu
      rw [e]
      exact (hsc E hfree hout hsat u hu).1
    · intro u hu hb
      rw [e] at hb
      exact (hsc E hfree hout hsat u hu).2 hb)

end LeanCH.BR.BRsub
