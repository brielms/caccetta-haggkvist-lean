import LeanCH.BR.WeakCap
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Large outgoing modules are terminal at the boundary (q = 3), Lean 4.35.0

Paper source: `checkpoints/boundary_20261112/LargeBoundaryModule_Exclusion_20261112.md`, Sections 1-6
(independently audited in `..._IndependentAudit.md`).

**Theorem (`exterior_empty`).** Let `s ≥ 2`, `G` loopless on `3s+1` labels, minimum out-degree `≥ s`, no directed
cycle of length `≤ 3`, and `BR(3,t)` for every `1 ≤ t < s`. Let `T` be a set with `|T| ≥ s` and `U` a set disjoint
from `T` such that every `T`-row heads every member of `U` and has no other head outside `T` (an outgoing module with
common exterior `U`). Then `U = ∅`.

Proof (the paper's argument, with the per-vertex cap kept in integer form).

* Banks. `R = V \ (T ∪ U)`, `P` = members of `R` heading some `T` vertex, `L = R \ P`. So
  `|T| + |U| + |P| + |L| = 3s+1`. Write `m = |T|`, `k = |U| ≥ 1`, `p = |P|`, `ℓ = |L|`.
* `U`-rows. A `U`-row has no head in `T` (digon with `T → U`) and none in `P` (`u → w → t → u` triangle), so all its
  heads lie in `U ∪ L`.
* Per `u ∈ U` (weak cap `LeanCH.BR.WeakCap.weak_cap` at `u`, whose in-neighbourhood contains `T`, the `U`-parents
  and the `L`-parents of `u`): `3m + 3h_u + 3b_u + 2o_u + 1 ≤ 6s`, `s ≤ o_u ≤ h⁺_u + λ_u` and `λ_u + b_u ≤ ℓ`
  (no digon between `u` and `L`), where `o_u` is the out-degree, `h_u`/`h⁺_u` the in/out-degree inside `U`, `b_u`
  the number of `L`-parents and `λ_u` the number of `L`-heads of `u`.
* Summing over `U` (with `Σ h_u = Σ h⁺_u = H`, `B = Σ b_u = e(L,U)`, `O = Σ o_u`, `Λ = Σ λ_u`):
  `3km + 3H + 3B + 2O + k ≤ 6ks`, `ks ≤ O ≤ H + Λ`, `Λ + B ≤ kℓ`. These give the paper's (6)-(7):
  `6B ≤ k(3ℓ - 2s - 3e - 1)` with `e = m - s`.
* `L`-rows have no head in `T`, so `ℓ s ≤ e(L) + ℓ p + B`, and `2 e(L) + ℓ ≤ ℓ²` (no digon). This is (8).
* Combining and eliminating `p` gives the paper's quadratic (10), times three:
  `G(ℓ,e) = 3ℓ² + 3ℓ(2e + k - 2s - 1) + k(2s + 3e + 1) ≤ 0`.
* Side facts: `3m + 1 ≤ 4s` (cap at one `u`, i.e. `3e ≤ s - 1`); if `k < s`, the `T`-rows keep `s - k` heads in `T`
  and `LeanCH.BR.ModuleSize.module_size` gives `3(s-k) + 1 ≤ m`; if `0 < ℓ < s`, the `U`-rows keep `s - ℓ` heads in
  `U`, so `3(s-ℓ) + 1 ≤ k`.
* Cases on `3k` versus `S = 2s+1` (the paper's `k` versus `K = 2c+1`, since `3k - S = k - K`):
  - `3k > S` (Case A): `12G = (6ℓ + 3(k-S))² + 3(3k-S)(3S-k) + 12e(6ℓ+3k) > 0`.
  - `3k < S` (Case B): `e ≥ S - 3k > 0` and `9k ≥ 5s + 4`, and
    `12G = (6ℓ + 3(S-5k))² + 3(37k-3S)(S-3k) + 12(e-(S-3k))(6ℓ+3k) > 0`.
  - `3k = S` (Case C): `G = 3(ℓ-k)² + e(6ℓ+3k)`, so `ℓ = k`; then `0 < ℓ < s` and `3(s-ℓ)+1 ≤ k` contradict
    `3k = 2s+1`, `s ≥ 2`.

`module_terminal` restates the theorem in the paper's form: a set of size `≥ s` whose rows share the same exterior
head set has no exterior heads at all.
-/

namespace LeanCH.BR.LargeModule

open CH Compose.Boundary Compose.FloorSix

/-- Arc double counting between two sets. -/
theorem swap_count (G : CH.Digraph) (A B : Finset Nat) :
    ∑ a ∈ A, (B.filter (fun w => G a w = true)).card =
      ∑ b ∈ B, (A.filter (fun u => G u b = true)).card := by
  classical
  rw [Finset.sum_congr rfl (fun a _ => Finset.card_filter (fun w => G a w = true) B),
    Finset.sum_congr rfl (fun b _ => Finset.card_filter (fun u => G u b = true) A)]
  exact Finset.sum_comm

/-- No-digon edge bound inside a set: `2 e(A) + |A| ≤ |A|²`. -/
theorem edge_bound {G : CH.Digraph} {n : Nat} {A : Finset Nat} (hA : A ⊆ Finset.range n)
    (loopless : CH.Loopless G n) (noShort : ¬ CH.HasDirectedCycleAtMost G n 3) :
    2 * ∑ x ∈ A, (A.filter (fun w => G x w = true)).card + A.card ≤ A.card * A.card := by
  classical
  have hloc : ∀ x ∈ A, (A.filter (fun w => G x w = true)).card +
      (A.filter (fun u => G u x = true)).card + 1 ≤ A.card := by
    intro x hx
    have hxn : x < n := Finset.mem_range.mp (hA hx)
    have hsub : A.filter (fun w => G x w = true) ∪ A.filter (fun u => G u x = true) ⊆ A.erase x := by
      intro w hw
      rcases Finset.mem_union.mp hw with hw | hw
      · obtain ⟨hwA, hG⟩ := Finset.mem_filter.mp hw
        refine Finset.mem_erase.mpr ⟨?_, hwA⟩
        intro hwx; rw [hwx, loopless x hxn] at hG; exact Bool.false_ne_true hG
      · obtain ⟨hwA, hG⟩ := Finset.mem_filter.mp hw
        refine Finset.mem_erase.mpr ⟨?_, hwA⟩
        intro hwx; rw [hwx, loopless x hxn] at hG; exact Bool.false_ne_true hG
    have hdisj : Disjoint (A.filter (fun w => G x w = true)) (A.filter (fun u => G u x = true)) := by
      rw [Finset.disjoint_left]
      intro w h1 h2
      exact no2 loopless noShort hxn (Finset.mem_range.mp (hA (Finset.mem_filter.mp h1).1))
        (Finset.mem_filter.mp h1).2 (Finset.mem_filter.mp h2).2
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_union_of_disjoint hdisj, Finset.card_erase_of_mem hx] at h1
    have : 0 < A.card := Finset.card_pos.mpr ⟨x, hx⟩
    omega
  have hsum := Finset.sum_le_sum hloc
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Compose.ThinRigid.sum_out_eq_sum_in G A] at hsum
  simp only [Finset.sum_const, Nat.nsmul_eq_mul, mul_one] at hsum
  linarith

/-- No-digon cross bound: for every `u ∈ U`, out-heads and in-parents of `u` inside `L` are disjoint. -/
theorem cross_bound {G : CH.Digraph} {n : Nat} {U L : Finset Nat} (hU : U ⊆ Finset.range n)
    (hL : L ⊆ Finset.range n) (loopless : CH.Loopless G n)
    (noShort : ¬ CH.HasDirectedCycleAtMost G n 3) :
    ∑ u ∈ U, (L.filter (fun w => G u w = true)).card +
      ∑ u ∈ U, (L.filter (fun w => G w u = true)).card ≤ U.card * L.card := by
  classical
  have hloc : ∀ u ∈ U, (L.filter (fun w => G u w = true)).card +
      (L.filter (fun w => G w u = true)).card ≤ L.card := by
    intro u hu
    have hun : u < n := Finset.mem_range.mp (hU hu)
    have hdisj : Disjoint (L.filter (fun w => G u w = true)) (L.filter (fun w => G w u = true)) := by
      rw [Finset.disjoint_left]
      intro w h1 h2
      exact no2 loopless noShort hun (Finset.mem_range.mp (hL (Finset.mem_filter.mp h1).1))
        (Finset.mem_filter.mp h1).2 (Finset.mem_filter.mp h2).2
    rw [← Finset.card_union_of_disjoint hdisj]
    exact Finset.card_le_card (Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _))
  have hsum := Finset.sum_le_sum hloc
  rw [Finset.sum_add_distrib, Finset.sum_const, Nat.nsmul_eq_mul] at hsum
  exact hsum

/-- Three pairwise disjoint subsets of `D`. -/
theorem card_three_le {A B C D : Finset Nat} (hAB : Disjoint A B) (hAC : Disjoint A C)
    (hBC : Disjoint B C) (hA : A ⊆ D) (hB : B ⊆ D) (hC : C ⊆ D) :
    A.card + B.card + C.card ≤ D.card := by
  classical
  rw [← Finset.card_union_of_disjoint hAB,
    ← Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hAC, hBC⟩)]
  exact Finset.card_le_card (Finset.union_subset (Finset.union_subset hA hB) hC)

/-- The closing arithmetic (paper Sections 5-6). All quantities are the actual counts of `exterior_empty`. -/
theorem arith {s m k p l H B O Λ E : Nat} (hs : 2 ≤ s) (hk : 1 ≤ k) (hm : s ≤ m)
    (hsize : m + k + p + l = 3 * s + 1)
    (hcap : 3 * (k * m) + 3 * H + 3 * B + 2 * O + k ≤ 6 * (k * s))
    (hO1 : k * s ≤ O) (hO2 : O ≤ H + Λ) (hcross : Λ + B ≤ k * l)
    (hLrow : l * s ≤ E + l * p + B) (hE : 2 * E + l ≤ l * l)
    (hcap1 : 3 * m + 1 ≤ 4 * s)
    (hTlow : k < s → 3 * s + 1 ≤ m + 3 * k)
    (hUlow : 0 < l → l < s → 3 * s + 1 ≤ k + 3 * l) : False := by
  -- the paper's quadratic (10), multiplied by three
  have hp : (p : ℤ) = 3 * s + 1 - m - k - l := by omega
  have key : 3 * (l : ℤ) ^ 2 + 3 * l * (2 * ((m : ℤ) - s) + k - 2 * s - 1) +
      k * (2 * s + 3 * ((m : ℤ) - s) + 1) ≤ 0 := by
    have h1 : (3 * (k * m) + 3 * H + 3 * B + 2 * O + k : ℤ) ≤ 6 * (k * s) := by exact_mod_cast hcap
    have h2 : (k * s : ℤ) ≤ O := by exact_mod_cast hO1
    have h3 : (O : ℤ) ≤ H + Λ := by exact_mod_cast hO2
    have h4 : (Λ + B : ℤ) ≤ k * l := by exact_mod_cast hcross
    have h5 : (l * s : ℤ) ≤ E + l * p + B := by exact_mod_cast hLrow
    have h6 : (2 * E + l : ℤ) ≤ l * l := by exact_mod_cast hE
    rw [hp] at h5
    nlinarith
  have hl0 : (0 : ℤ) ≤ 6 * l + 3 * k := by omega
  rcases lt_trichotomy (3 * k) (2 * s + 1) with hlt | heq | hgt
  · -- Case B: k < K
    have hT := hTlow (by omega)
    have e0 : (0 : ℤ) ≤ ((m : ℤ) - s) - (2 * s + 1 - 3 * k) := by omega
    have pos1 : (0 : ℤ) < 37 * k - 3 * (2 * s + 1) := by omega
    have pos2 : (0 : ℤ) < 2 * s + 1 - 3 * k := by omega
    nlinarith [sq_nonneg (6 * (l : ℤ) + 3 * (2 * s + 1 - 5 * k)), mul_pos pos1 pos2,
      mul_nonneg e0 hl0]
  · -- Case C: k = K, the zero-discriminant case
    have hS : (2 * s + 1 : ℤ) = 3 * k := by omega
    have e0 : (0 : ℤ) ≤ (m : ℤ) - s := by omega
    have hSl : (2 * s + 1 : ℤ) * l = 3 * k * l := by rw [hS]
    have hSk : (2 * s + 1 : ℤ) * k = 3 * k * k := by rw [hS]
    have hsq : ((l : ℤ) - k) ^ 2 = 0 :=
      le_antisymm (by nlinarith [mul_nonneg e0 hl0]) (sq_nonneg _)
    have hlk' : (l : ℤ) = k := by
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq
      linarith
    have hlk : l = k := by exact_mod_cast hlk'
    have := hUlow (by omega) (by omega)
    omega
  · -- Case A: k > K
    have e0 : (0 : ℤ) ≤ (m : ℤ) - s := by omega
    have pos1 : (0 : ℤ) < 3 * k - (2 * s + 1) := by omega
    have pos2 : (0 : ℤ) < 3 * (2 * s + 1) - k := by omega
    nlinarith [sq_nonneg (6 * (l : ℤ) + 3 * (k - (2 * s + 1))), mul_pos pos1 pos2,
      mul_nonneg e0 hl0]

/-- **Large-module exclusion (paper Sections 1-6).** On `3s+1` labels, `s ≥ 2`, with lower BR, an outgoing module
`T` of size at least `s` (every `T`-row heads all of `U` and has no other head outside `T`) has empty common
exterior `U`. -/
theorem exterior_empty {G : CH.Digraph} {s : Nat} (hs : 2 ≤ s)
    (brs : ∀ t, 1 ≤ t → t < s → BoundaryRegular 3 t)
    (loopless : CH.Loopless G (3 * s + 1)) (deg : CH.MinOutdegreeAtLeast G (3 * s + 1) s)
    (noShort : ¬ CH.HasDirectedCycleAtMost G (3 * s + 1) 3)
    {T U : Finset Nat} (hT : T ⊆ Finset.range (3 * s + 1)) (hTs : s ≤ T.card)
    (hU : U ⊆ Finset.range (3 * s + 1)) (hUT : ∀ u ∈ U, u ∉ T)
    (hmod : ∀ x ∈ T, ∀ w, w < 3 * s + 1 → w ∉ T → G x w = true → w ∈ U)
    (hcomp : ∀ x ∈ T, ∀ u ∈ U, G x u = true) :
    U = ∅ := by
  classical
  by_contra hne
  have hUne : U.Nonempty := Finset.nonempty_iff_ne_empty.mpr hne
  have hk : 0 < U.card := Finset.card_pos.mpr hUne
  obtain ⟨u0, hu0⟩ := hUne
  -- the four banks T, U, P, L
  set R : Finset Nat := (Finset.range (3 * s + 1) \ T) \ U with hR
  set L : Finset Nat := R.filter (fun w => ∀ t ∈ T, G w t = false) with hL
  set P : Finset Nat := R.filter (fun w => ¬ ∀ t ∈ T, G w t = false) with hP
  have memR : ∀ w, w ∈ R ↔ w < 3 * s + 1 ∧ w ∉ T ∧ w ∉ U := by
    intro w
    simp only [hR, Finset.mem_sdiff, Finset.mem_range, and_assoc]
  have memL : ∀ w, w ∈ L ↔ w ∈ R ∧ ∀ t ∈ T, G w t = false := fun w => Finset.mem_filter
  have hLR : L ⊆ R := Finset.filter_subset _ _
  have hRsub : R ⊆ Finset.range (3 * s + 1) := fun w hw => Finset.mem_range.mpr ((memR w).mp hw).1
  have hLsub : L ⊆ Finset.range (3 * s + 1) := hLR.trans hRsub
  have hUsub' : U ⊆ Finset.range (3 * s + 1) \ T := fun u hu =>
    Finset.mem_sdiff.mpr ⟨hU hu, hUT u hu⟩
  have hRcard : R.card = 3 * s + 1 - T.card - U.card := by
    rw [hR, Finset.card_sdiff_of_subset hUsub', Finset.card_sdiff_of_subset hT, Finset.card_range]
  have hTle : T.card ≤ 3 * s + 1 := by simpa using Finset.card_le_card hT
  have hUle : U.card ≤ 3 * s + 1 - T.card := by
    have := Finset.card_le_card hUsub'
    rwa [Finset.card_sdiff_of_subset hT, Finset.card_range] at this
  have hLP : L.card + P.card = R.card := Finset.card_filter_add_card_filter_not _
  have hsize : T.card + U.card + P.card + L.card = 3 * s + 1 := by omega
  -- U-rows head only U ∪ L
  have Urow : ∀ u ∈ U, ∀ w, w < 3 * s + 1 → G u w = true → w ∈ U ∨ w ∈ L := by
    intro u hu w hw huw
    have hun : u < 3 * s + 1 := Finset.mem_range.mp (hU hu)
    by_cases hwU : w ∈ U
    · exact Or.inl hwU
    · right
      have hwT : w ∉ T := fun hwT => no2 loopless noShort hun hw huw (hcomp w hwT u hu)
      refine (memL w).mpr ⟨(memR w).mpr ⟨hw, hwT, hwU⟩, fun t ht => ?_⟩
      cases hwt : G w t
      · rfl
      · exact (no3 loopless noShort hun hw (Finset.mem_range.mp (hT ht)) huw hwt
          (hcomp t ht u hu)).elim
  -- L-rows head only L ∪ P ∪ U
  have Lrow : ∀ w ∈ L, ((Finset.range (3 * s + 1)).filter (fun y => G w y = true)).card ≤
      (L.filter (fun y => G w y = true)).card + P.card + (U.filter (fun y => G w y = true)).card := by
    intro w hw
    have hwT := ((memL w).mp hw).2
    have hsub : (Finset.range (3 * s + 1)).filter (fun y => G w y = true) ⊆
        L.filter (fun y => G w y = true) ∪ P ∪ U.filter (fun y => G w y = true) := by
      intro y hy
      obtain ⟨hyn, hwy⟩ := Finset.mem_filter.mp hy
      have hyT : y ∉ T := by
        intro hyT; rw [hwT y hyT] at hwy; exact Bool.false_ne_true hwy
      by_cases hyU : y ∈ U
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hyU, hwy⟩)
      · have hyR : y ∈ R := (memR y).mpr ⟨Finset.mem_range.mp hyn, hyT, hyU⟩
        by_cases hyL : ∀ t ∈ T, G y t = false
        · exact Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_filter.mpr ⟨(memL y).mpr ⟨hyR, hyL⟩, hwy⟩))
        · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hyR, hyL⟩))
    exact (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
      (Nat.add_le_add_right (Finset.card_union_le _ _) _))
  -- per-vertex facts at U
  have perU : ∀ u ∈ U,
      3 * T.card + 3 * (U.filter (fun x => G x u = true)).card +
          3 * (L.filter (fun x => G x u = true)).card +
          2 * ((Finset.range (3 * s + 1)).filter (fun w => G u w = true)).card + 1 ≤ 6 * s ∧
        s ≤ ((Finset.range (3 * s + 1)).filter (fun w => G u w = true)).card ∧
        ((Finset.range (3 * s + 1)).filter (fun w => G u w = true)).card ≤
          (U.filter (fun w => G u w = true)).card + (L.filter (fun w => G u w = true)).card := by
    intro u hu
    have hun : u < 3 * s + 1 := Finset.mem_range.mp (hU hu)
    have hin : T.card + (U.filter (fun x => G x u = true)).card +
        (L.filter (fun x => G x u = true)).card ≤ (par G (3 * s + 1) u).card := by
      apply card_three_le
      · exact Finset.disjoint_left.mpr (fun x hxT hxU => hUT x (Finset.mem_filter.mp hxU).1 hxT)
      · exact Finset.disjoint_left.mpr (fun x hxT hxL =>
          ((memR x).mp (hLR (Finset.mem_filter.mp hxL).1)).2.1 hxT)
      · exact Finset.disjoint_left.mpr (fun x hxU hxL =>
          ((memR x).mp (hLR (Finset.mem_filter.mp hxL).1)).2.2 (Finset.mem_filter.mp hxU).1)
      · intro x hx; exact Finset.mem_filter.mpr ⟨hT hx, hcomp x hx u hu⟩
      · intro x hx
        obtain ⟨hxU, hG⟩ := Finset.mem_filter.mp hx
        exact Finset.mem_filter.mpr ⟨hU hxU, hG⟩
      · intro x hx
        obtain ⟨hxL, hG⟩ := Finset.mem_filter.mp hx
        exact Finset.mem_filter.mpr ⟨hLsub hxL, hG⟩
    have hcap := LeanCH.BR.WeakCap.weak_cap (by omega) brs loopless deg noShort hun (by omega)
    have hout := out_card deg hun
    have hsplit : ((Finset.range (3 * s + 1)).filter (fun w => G u w = true)).card ≤
        (U.filter (fun w => G u w = true)).card + (L.filter (fun w => G u w = true)).card := by
      have hsub : (Finset.range (3 * s + 1)).filter (fun w => G u w = true) ⊆
          U.filter (fun w => G u w = true) ∪ L.filter (fun w => G u w = true) := by
        intro w hw
        obtain ⟨hwn, huw⟩ := Finset.mem_filter.mp hw
        rcases Urow u hu w (Finset.mem_range.mp hwn) huw with h | h
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨h, huw⟩)
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨h, huw⟩)
      exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    exact ⟨by omega, hout, hsplit⟩
  -- the local cap at one U vertex: 3e ≤ s - 1
  have cap1 : 3 * T.card + 1 ≤ 4 * s := by
    have h := perU u0 hu0
    omega
  -- lower BR on the actual induced T
  have Tlow : U.card < s → 3 * s + 1 ≤ T.card + 3 * U.card := by
    intro hks
    have keep : ∀ x ∈ T, s - U.card ≤ (T.filter (fun w => G x w = true)).card := by
      intro x hx
      have hxn : x < 3 * s + 1 := Finset.mem_range.mp (hT hx)
      have hsub : (Finset.range (3 * s + 1)).filter (fun w => G x w = true) ⊆
          T.filter (fun w => G x w = true) ∪ U := by
        intro w hw
        obtain ⟨hwn, hxw⟩ := Finset.mem_filter.mp hw
        by_cases hwT : w ∈ T
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hwT, hxw⟩)
        · exact Finset.mem_union_right _ (hmod x hx w (Finset.mem_range.mp hwn) hwT hxw)
      have h1 := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
      have h2 := out_card deg hxn
      omega
    have := LeanCH.BR.ModuleSize.module_size (q := 3) (c := s - U.card) (by omega)
      (brs _ (by omega) (by omega)) hT (by omega) loopless noShort keep
    omega
  -- lower BR on the actual induced U
  have Ulow : 0 < L.card → L.card < s → 3 * s + 1 ≤ U.card + 3 * L.card := by
    intro hl hls
    have keep : ∀ u ∈ U, s - L.card ≤ (U.filter (fun w => G u w = true)).card := by
      intro u hu
      have h := perU u hu
      have : (L.filter (fun w => G u w = true)).card ≤ L.card :=
        Finset.card_le_card (Finset.filter_subset _ _)
      omega
    have := LeanCH.BR.ModuleSize.module_size (q := 3) (c := s - L.card) (by omega)
      (brs _ (by omega) (by omega)) hU hk loopless noShort keep
    omega
  -- summed U facts
  have sum1 : ∑ u ∈ U, (3 * T.card + 3 * (U.filter (fun x => G x u = true)).card +
          3 * (L.filter (fun x => G x u = true)).card +
          2 * ((Finset.range (3 * s + 1)).filter (fun w => G u w = true)).card + 1) ≤
        ∑ _u ∈ U, 6 * s := Finset.sum_le_sum (fun u hu => (perU u hu).1)
  have sum2 : ∑ _u ∈ U, s ≤ ∑ u ∈ U, ((Finset.range (3 * s + 1)).filter (fun w => G u w = true)).card :=
    Finset.sum_le_sum (fun u hu => (perU u hu).2.1)
  have sum3 : ∑ u ∈ U, ((Finset.range (3 * s + 1)).filter (fun w => G u w = true)).card ≤
      ∑ u ∈ U, ((U.filter (fun w => G u w = true)).card + (L.filter (fun w => G u w = true)).card) :=
    Finset.sum_le_sum (fun u hu => (perU u hu).2.2)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Nat.nsmul_eq_mul, ← Finset.mul_sum] at sum1 sum2 sum3
  have hH := Compose.ThinRigid.sum_out_eq_sum_in G U
  have hcross := cross_bound hU hLsub loopless noShort
  -- summed L facts
  have sumL : ∑ w ∈ L, ((Finset.range (3 * s + 1)).filter (fun y => G w y = true)).card ≤
      ∑ w ∈ L, ((L.filter (fun y => G w y = true)).card + P.card +
        (U.filter (fun y => G w y = true)).card) := Finset.sum_le_sum Lrow
  have sumL2 : ∑ _w ∈ L, s ≤ ∑ w ∈ L, ((Finset.range (3 * s + 1)).filter (fun y => G w y = true)).card :=
    Finset.sum_le_sum (fun w hw => out_card deg (Finset.mem_range.mp (hLsub hw)))
  simp only [Finset.sum_add_distrib, Finset.sum_const, Nat.nsmul_eq_mul] at sumL sumL2
  have hB := swap_count G L U
  have hE := edge_bound hLsub loopless noShort
  exact arith (s := s) (m := T.card) (k := U.card) (p := P.card) (l := L.card)
    (H := ∑ u ∈ U, (U.filter (fun x => G x u = true)).card)
    (B := ∑ u ∈ U, (L.filter (fun x => G x u = true)).card)
    (O := ∑ u ∈ U, ((Finset.range (3 * s + 1)).filter (fun w => G u w = true)).card)
    (Λ := ∑ u ∈ U, (L.filter (fun w => G u w = true)).card)
    (E := ∑ w ∈ L, (L.filter (fun y => G w y = true)).card)
    hs hk hTs (by omega) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) hE cap1
    Tlow Ulow

/-- **Paper form.** A set `T` with `|T| ≥ s` whose rows all have the same exterior head set is terminal. -/
theorem module_terminal {G : CH.Digraph} {s : Nat} (hs : 2 ≤ s)
    (brs : ∀ t, 1 ≤ t → t < s → BoundaryRegular 3 t)
    (loopless : CH.Loopless G (3 * s + 1)) (deg : CH.MinOutdegreeAtLeast G (3 * s + 1) s)
    (noShort : ¬ CH.HasDirectedCycleAtMost G (3 * s + 1) 3)
    {T : Finset Nat} (hT : T ⊆ Finset.range (3 * s + 1)) (hTs : s ≤ T.card)
    (hsame : ∀ x ∈ T, ∀ y ∈ T, ∀ w, w < 3 * s + 1 → w ∉ T → G x w = G y w) :
    ∀ x ∈ T, ∀ w, w < 3 * s + 1 → w ∉ T → G x w = false := by
  classical
  intro x hx w hw hwT
  set U : Finset Nat := (Finset.range (3 * s + 1) \ T).filter (fun y => G x y = true) with hUdef
  have hU : U ⊆ Finset.range (3 * s + 1) := fun y hy =>
    (Finset.mem_sdiff.mp (Finset.mem_filter.mp hy).1).1
  have hUT : ∀ u ∈ U, u ∉ T := fun y hy => (Finset.mem_sdiff.mp (Finset.mem_filter.mp hy).1).2
  have hmod : ∀ z ∈ T, ∀ y, y < 3 * s + 1 → y ∉ T → G z y = true → y ∈ U := by
    intro z hz y hy hyT hzy
    refine Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_range.mpr hy, hyT⟩, ?_⟩
    rw [hsame x hx z hz y hy hyT]; exact hzy
  have hcomp : ∀ z ∈ T, ∀ u ∈ U, G z u = true := by
    intro z hz u hu
    obtain ⟨hu1, hxu⟩ := Finset.mem_filter.mp hu
    obtain ⟨hun, huT⟩ := Finset.mem_sdiff.mp hu1
    rw [hsame z hz x hx u (Finset.mem_range.mp hun) huT]; exact hxu
  have hempty := exterior_empty hs brs loopless deg noShort hT hTs hU hUT hmod hcomp
  cases hxw : G x w
  · rfl
  · have : w ∈ U := hmod x hx w hw hwT hxw
    rw [hempty] at this
    exact absurd this (Finset.notMem_empty w)

end LeanCH.BR.LargeModule
