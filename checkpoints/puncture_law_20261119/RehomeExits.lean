import checkpoints.puncture_law_20261119.HeirExit
import LeanCH.BR.BRCommonParentTransferGeometry

/-! Rehome exits. (1) Star heir exit: the heir exit with a set B of new heads at the tail a.
(2) Far exit: an out-neighbour v of a whose other parents all also point to some z ≠ v
cannot be lighter than the new heads; its weight is moved to z. (3) Flat-branch wrappers and
their duals by reversal. (4) Joint safety of a tail star by reversal of the head-star result. -/
namespace LeanCH.BR.Closure.RehomeExits
open Finset FiniteCutInverse WeightedSD BRq2 BRq3 LeanCH.BR.Closure.HeirExit

/-! ### Row of a star extension -/

/-- The new heads B at a raise the out-weight of a by at least Σ_B w. -/
theorem outW_star_le {E J : CH.Digraph} {V B : Finset ℕ} {a : ℕ} {w : ℕ → ℚ}
    (wn : ∀ i ∈ V, 0 ≤ w i) (hJE : ∀ x y, E x y = true → J x y = true)
    (hB : ∀ y ∈ B, y ∈ V ∧ E a y = false ∧ J a y = true) :
    outW E V w a + ∑ y ∈ B, w y ≤ outW J V w a := by
  have hBV : B ⊆ V := fun y hy => (hB y hy).1
  have h1 : ∑ y ∈ B, w y = ∑ y ∈ B,
      ((if J a y = true then w y else 0) - (if E a y = true then w y else 0)) :=
    Finset.sum_congr rfl fun y hy => by simp [(hB y hy).2.1, (hB y hy).2.2]
  have h2 : ∑ y ∈ B, ((if J a y = true then w y else 0) - (if E a y = true then w y else 0)) ≤
      ∑ y ∈ V, ((if J a y = true then w y else 0) - (if E a y = true then w y else 0)) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hBV
    intro u hu _
    by_cases hE : E a u = true
    · simp [hE, hJE a u hE]
    · by_cases hJ : J a u = true
      · simp [hE, hJ, wn u hu]
      · simp [hE, hJ]
  have h3 : ∑ y ∈ V, ((if J a y = true then w y else 0) - (if E a y = true then w y else 0)) =
      outW J V w a - outW E V w a := by
    unfold outW; rw [Finset.sum_sub_distrib]
  linarith

theorem row_star_le {q : ℕ} {E J : CH.Digraph} {V B : Finset ℕ} {a : ℕ} {w : ℕ → ℚ}
    (ha : a ∈ V) (wn : ∀ i ∈ V, 0 ≤ w i) (hJE : ∀ x y, E x y = true → J x y = true)
    (hB : ∀ y ∈ B, y ∈ V ∧ E a y = false ∧ J a y = true)
    (hr : ∀ i ∈ V, mass V w ≤ WeightedSD.row q E V w i) :
    mass V w + (q : ℚ) * ∑ y ∈ B, w y ≤ WeightedSD.row q J V w a := by
  have h := hr a ha
  have hs := outW_star_le wn hJE hB
  have hm := mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg (α := ℚ) q)
  rw [mul_add] at hm
  unfold WeightedSD.row at h ⊢
  linarith

/-- A nonempty set of new heads makes the positive feasible extension J not SmallRow. -/
theorem star_not_smallRow {q : ℕ} (hq : 2 ≤ q) {E J : CH.Digraph} {V B : Finset ℕ} {a : ℕ}
    (ha : a ∈ V) (hJE : ∀ x y, E x y = true → J x y = true)
    (hB : ∀ y ∈ B, y ∈ V ∧ E a y = false ∧ J a y = true) (hBne : B.Nonempty)
    {w : ℕ → ℚ} (hw : ∀ i ∈ V, 0 < w i) (hr : ∀ i ∈ V, mass V w ≤ WeightedSD.row q E V w i) :
    ¬ SmallRow q J V := by
  obtain ⟨b, hbB⟩ := hBne
  exact positive_feasible_extension_not_smallRow hq (fun i _ j _ h => hJE i j h) w hw hr ha
    (hB b hbB).1 (by simp [(hB b hbB).2.1]) (hB b hbB).2.2

/-! ### Item 1. Star heir exit -/

theorem star_heir_exit_general {q : ℕ} (hq : 2 ≤ q) {E J : CH.Digraph} {V : Finset ℕ}
    (small : SmallerSmallRow q V.card) {a v : ℕ} (ha : a ∈ V) (hvV : v ∈ V)
    (hJE : ∀ x y, E x y = true → J x y = true)
    (hJi : ∀ i, i ≠ a → ∀ y, J i y = E i y) (safe : QFree J V q)
    {B : Finset ℕ} (hB : ∀ y ∈ B, y ∈ V ∧ E a y = false ∧ J a y = true)
    {w : ℕ → ℚ} (hw : ∀ i ∈ V, 0 < w i) (hr : ∀ i ∈ V, mass V w ≤ WeightedSD.row q E V w i)
    (hav : E a v = true) (heir : ∀ i ∈ V, i ≠ a → E i v = true → E i a = true)
    (light : ((q : ℚ) - 1) * w v < (q : ℚ) * ∑ y ∈ B, w y) : False := by
  have hq1 : 1 ≤ q := by omega
  have hJaa : ¬ J a a = true := loopfree safe hq1 ha
  have hva : v ≠ a := by rintro rfl; exact hJaa (hJE _ _ hav)
  have hJav : J a v = true := hJE _ _ hav
  have wn : ∀ i ∈ V, 0 ≤ w i := fun i hi => (hw i hi).le
  have q1 : (1 : ℚ) ≤ (q : ℚ) - 1 := by
    have : (2 : ℚ) ≤ q := by exact_mod_cast hq
    linarith
  have hBne : B.Nonempty := by
    rcases B.eq_empty_or_nonempty with h | h
    · rw [h, Finset.sum_empty, mul_zero] at light
      have := mul_pos (by linarith : (0 : ℚ) < (q : ℚ) - 1) (hw v hvV)
      linarith
    · exact h
  have bad := star_not_smallRow hq ha hJE hB hBne hw hr
  obtain ⟨x, xn, _, xh⟩ := strict_witness_of_not_smallRow bad
  have rowJ : ∀ i ∈ V, mass V w ≤ WeightedSD.row q J V w i := fun i hi =>
    (hr i hi).trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left
      (outW_mono_graph (fun x _ y _ h => hJE x y h) wn hi) (Nat.cast_nonneg q)))
  have rowJa := row_star_le (q := q) ha wn hJE hB hr
  obtain ⟨S, hS⟩ : ∃ S : ℚ, S = ∑ y ∈ B, w y := ⟨_, rfl⟩
  rw [← hS] at light rowJa
  obtain ⟨G, hG⟩ : ∃ G : ℚ, G = WeightedSD.row q J V w a - mass V w - ((q : ℚ) - 1) * w v :=
    ⟨_, rfl⟩
  have Gpos : 0 < G := by rw [hG]; linarith
  have xv0 : 0 ≤ x v := xn v hvV
  have den : 0 < ((q : ℚ) - 1) * x v + 1 := by
    have := mul_nonneg (by linarith : (0 : ℚ) ≤ (q : ℚ) - 1) xv0
    linarith
  obtain ⟨ε, hε⟩ : ∃ ε : ℚ, ε = G / (((q : ℚ) - 1) * x v + 1) := ⟨_, rfl⟩
  have εpos : 0 < ε := by rw [hε]; exact div_pos Gpos den
  have εeq : ε * (((q : ℚ) - 1) * x v + 1) = G := by rw [hε]; exact div_mul_cancel₀ G den.ne'
  let K := V.erase v
  let z := transferWeight (fun u => w u + ε * x u) v a
  have haK : a ∈ K := Finset.mem_erase.mpr ⟨hva.symm, ha⟩
  have hKV : K ⊆ V := Finset.erase_subset _ _
  have hKne : K ≠ V := by
    intro he
    have hh : v ∈ K := by rw [he]; exact hvV
    exact Finset.notMem_erase v V hh
  have yn : ∀ u ∈ V, 0 ≤ w u + ε * x u := fun u hu =>
    add_nonneg (wn u hu) (mul_nonneg εpos.le (xn u hu))
  have hz : ∀ u ∈ K, 0 ≤ z u := by
    intro u hu
    dsimp [z, transferWeight]
    have := yn u (hKV hu)
    have := yn v hvV
    split_ifs <;> linarith
  apply (small.induced safe K hKV hKne).no_strict ⟨a, haK⟩ z hz
  intro i hi
  have hiV : i ∈ V := hKV hi
  have e1 := row_transfer (J := J) (q := q) hvV ha hva (fun u => w u + ε * x u) i
  have e2 := mass_transfer hvV ha hva (fun u => w u + ε * x u)
  have e3 := row_add (q := q) (J := J) (V := V) w x ε i
  have e4 := mass_add V w x ε
  show mass (V.erase v) (transferWeight (fun u => w u + ε * x u) v a) <
    WeightedSD.row q J (V.erase v) (transferWeight (fun u => w u + ε * x u) v a) i
  rw [e1, e2, e3, e4]
  have hxi := mul_pos εpos (sub_pos.mpr (xh i hiV))
  by_cases hia : i = a
  · rw [hia] at hxi ⊢
    simp only [ite_true, hJaa, hJav, ite_false, Bool.false_eq_true]
    linarith
  · have hyv := yn v hvV
    have hw0 := rowJ i hiV
    simp only [hia, ite_false, hJi i hia]
    by_cases hEv : E i v = true
    · have hEa := heir i hiV hia hEv
      simp only [hEv, hEa, ite_true]
      linarith
    · by_cases hEa : E i a = true
      · simp only [hEv, hEa, ite_true, ite_false, Bool.false_eq_true]
        have := mul_nonneg hyv (Nat.cast_nonneg (α := ℚ) q)
        linarith
      · simp only [hEv, hEa, ite_false, Bool.false_eq_true]
        linarith

/-- The single-head heir exit is the case B = {b}. -/
theorem heir_exit_general_of_star {q : ℕ} (hq : 2 ≤ q) {E J : CH.Digraph} {V : Finset ℕ}
    (small : SmallerSmallRow q V.card) {a b v : ℕ} (ha : a ∈ V) (hb : b ∈ V) (hvV : v ∈ V)
    (off : E a b = false) (hJE : ∀ x y, E x y = true → J x y = true) (hJab : J a b = true)
    (hJi : ∀ i, i ≠ a → ∀ y, J i y = E i y) (safe : QFree J V q)
    {w : ℕ → ℚ} (hw : ∀ i ∈ V, 0 < w i) (hr : ∀ i ∈ V, mass V w ≤ WeightedSD.row q E V w i)
    (hav : E a v = true) (heir : ∀ i ∈ V, i ≠ a → E i v = true → E i a = true)
    (light : ((q : ℚ) - 1) * w v < (q : ℚ) * w b) : False :=
  star_heir_exit_general hq small ha hvV hJE hJi safe (B := {b})
    (fun y hy => by rw [Finset.mem_singleton.mp hy]; exact ⟨hb, off, hJab⟩) hw hr hav heir
    (by rw [Finset.sum_singleton]; exact light)

/-! ### Item 2. Far exit -/

/-- Far exit. The hypotheses `z ≠ a` and `E z v = false` of the paper statement are not
needed: the bracket [i = z] is never negative, and z = a is harmless. -/
theorem far_exit_general {q : ℕ} (hq : 2 ≤ q) {E J : CH.Digraph} {V : Finset ℕ}
    (small : SmallerSmallRow q V.card) {a v z : ℕ} (ha : a ∈ V) (hvV : v ∈ V) (hzV : z ∈ V)
    (hJE : ∀ x y, E x y = true → J x y = true)
    (hJi : ∀ i, i ≠ a → ∀ y, J i y = E i y) (safe : QFree J V q)
    {B : Finset ℕ} (hB : ∀ y ∈ B, y ∈ V ∧ E a y = false ∧ J a y = true)
    {w : ℕ → ℚ} (hw : ∀ i ∈ V, 0 < w i) (hr : ∀ i ∈ V, mass V w ≤ WeightedSD.row q E V w i)
    (hav : E a v = true) (hzv : z ≠ v)
    (dom : ∀ i ∈ V, i ≠ a → E i v = true → E i z = true)
    (light : w v < ∑ y ∈ B, w y) : False := by
  have hq1 : 1 ≤ q := by omega
  have hJaa : ¬ J a a = true := loopfree safe hq1 ha
  have hva : v ≠ a := by rintro rfl; exact hJaa (hJE _ _ hav)
  have hJav : J a v = true := hJE _ _ hav
  have wn : ∀ i ∈ V, 0 ≤ w i := fun i hi => (hw i hi).le
  have hq0 : (0 : ℚ) ≤ q := Nat.cast_nonneg q
  have hBne : B.Nonempty := by
    rcases B.eq_empty_or_nonempty with h | h
    · rw [h, Finset.sum_empty] at light
      have := hw v hvV
      linarith
    · exact h
  have bad := star_not_smallRow hq ha hJE hB hBne hw hr
  obtain ⟨x, xn, _, xh⟩ := strict_witness_of_not_smallRow bad
  have rowJ : ∀ i ∈ V, mass V w ≤ WeightedSD.row q J V w i := fun i hi =>
    (hr i hi).trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left
      (outW_mono_graph (fun x _ y _ h => hJE x y h) wn hi) (Nat.cast_nonneg q)))
  have rowJa := row_star_le (q := q) ha wn hJE hB hr
  obtain ⟨S, hS⟩ : ∃ S : ℚ, S = ∑ y ∈ B, w y := ⟨_, rfl⟩
  rw [← hS] at light rowJa
  have xv0 : 0 ≤ x v := xn v hvV
  have den : 0 < x v + 1 := by linarith
  obtain ⟨ε, hε⟩ : ∃ ε : ℚ, ε = (S - w v) / (x v + 1) := ⟨_, rfl⟩
  have εpos : 0 < ε := by rw [hε]; exact div_pos (by linarith) den
  have εeq : ε * (x v + 1) = S - w v := by rw [hε]; exact div_mul_cancel₀ _ den.ne'
  have εq : (q : ℚ) * (ε * (x v + 1)) = (q : ℚ) * (S - w v) := by rw [εeq]
  let K := V.erase v
  let t := transferWeight (fun u => w u + ε * x u) v z
  have hzK : z ∈ K := Finset.mem_erase.mpr ⟨hzv, hzV⟩
  have hKV : K ⊆ V := Finset.erase_subset _ _
  have hKne : K ≠ V := by
    intro he
    have hh : v ∈ K := by rw [he]; exact hvV
    exact Finset.notMem_erase v V hh
  have yn : ∀ u ∈ V, 0 ≤ w u + ε * x u := fun u hu =>
    add_nonneg (wn u hu) (mul_nonneg εpos.le (xn u hu))
  have ht : ∀ u ∈ K, 0 ≤ t u := by
    intro u hu
    dsimp [t, transferWeight]
    have := yn u (hKV hu)
    have := yn v hvV
    split_ifs <;> linarith
  apply (small.induced safe K hKV hKne).no_strict ⟨z, hzK⟩ t ht
  intro i hi
  have hiV : i ∈ V := hKV hi
  have e1 := row_transfer (J := J) (q := q) hvV hzV hzv.symm (fun u => w u + ε * x u) i
  have e2 := mass_transfer hvV hzV hzv.symm (fun u => w u + ε * x u)
  have e3 := row_add (q := q) (J := J) (V := V) w x ε i
  have e4 := mass_add V w x ε
  show mass (V.erase v) (transferWeight (fun u => w u + ε * x u) v z) <
    WeightedSD.row q J (V.erase v) (transferWeight (fun u => w u + ε * x u) v z) i
  rw [e1, e2, e3, e4]
  have hxi := mul_pos εpos (sub_pos.mpr (xh i hiV))
  have hyv := yn v hvV
  have hyq := mul_nonneg hyv hq0
  have hqε := mul_nonneg hq0 εpos.le
  by_cases hia : i = a
  · have hJiv : J i v = true := by rw [hia]; exact hJav
    have rowJi : mass V w + (q : ℚ) * S ≤ WeightedSD.row q J V w i := by rw [hia]; exact rowJa
    rw [if_pos hJiv]
    split_ifs <;> linarith
  · have hw0 := rowJ i hiV
    rw [hJi i hia v, hJi i hia z]
    by_cases hEv : E i v = true
    · have hEz := dom i hiV hia hEv
      rw [if_pos hEv, if_pos hEz]
      split_ifs <;> linarith
    · rw [if_neg hEv]
      split_ifs <;> linarith

/-! ### Item 3. Flat-branch corollaries -/

/-- 3a. An heir v of the tail a is strictly heavier than the head: w v > w b. -/
theorem heir_no_heavier {q : ℕ} (hq : 2 ≤ q) {E : CH.Digraph} {V : Finset ℕ}
    (small : SmallerSmallRow q V.card) (a b : V) (off : E a b = false)
    (safe : QFree (insertArc E a b) V q) {w p : ℕ → ℚ}
    (wp : ∀ i ∈ V, 0 < w i ∧ 0 < p i) (wm : mass V w = 1)
    (wr : ∀ i ∈ V, WeightedSD.row q E V w i = 1) (pc : ∀ i ∈ V, WeightedSD.col q E V p i = 1)
    (v : V) (hav : E a v = true)
    (heir : ∀ i ∈ V, i ≠ (a : ℕ) → E i v = true → E i a = true)
    (heavy : w v ≤ w b) : False := by
  refine heir_exit hq small a b off safe wp wm wr pc v hav heir ?_
  have h1 := (wp v v.property).1
  have h2 := mul_le_mul_of_nonneg_left heavy (Nat.cast_nonneg (α := ℚ) q)
  linarith

/-- 3b. Far exit on the flat branch (J = E + a→b, B = {b}). -/
theorem far_exit {q : ℕ} (hq : 2 ≤ q) {E : CH.Digraph} {V : Finset ℕ}
    (small : SmallerSmallRow q V.card) (a b : V) (off : E a b = false)
    (safe : QFree (insertArc E a b) V q) {w p : ℕ → ℚ}
    (wp : ∀ i ∈ V, 0 < w i ∧ 0 < p i) (wm : mass V w = 1)
    (wr : ∀ i ∈ V, WeightedSD.row q E V w i = 1) (pc : ∀ i ∈ V, WeightedSD.col q E V p i = 1)
    (v z : V) (hav : E a v = true) (hzv : (z : ℕ) ≠ v)
    (dom : ∀ i ∈ V, i ≠ (a : ℕ) → E i v = true → E i z = true)
    (light : w v < w b) : False :=
  far_exit_general hq small a.property v.property z.property
    (fun x y h => insertArc_mono E a b x y h) (fun i hi y => by simp [insertArc, hi]) safe
    (B := {(b : ℕ)})
    (fun y hy => by
      rw [Finset.mem_singleton.mp hy]; exact ⟨b.property, off, by simp [insertArc]⟩)
    (fun i hi => (wp i hi).1) (fun i hi => by rw [wm, wr i hi]) hav hzv dom
    (by rw [Finset.sum_singleton]; exact light)

/-- 3c, dual of 3a in general form: co-heir k of the head b has p k > p a. -/
theorem coheir_no_heavier {q : ℕ} (hq : 2 ≤ q) {E : CH.Digraph} {V : Finset ℕ}
    (small : SmallerSmallRow q V.card) (a b : V) (off : E a b = false)
    (safe : QFree (insertArc E a b) V q) {w p : ℕ → ℚ}
    (wp : ∀ i ∈ V, 0 < w i ∧ 0 < p i) (wm : mass V w = 1)
    (wr : ∀ i ∈ V, WeightedSD.row q E V w i = 1) (pc : ∀ i ∈ V, WeightedSD.col q E V p i = 1)
    (k : V) (hkb : E k b = true)
    (coheir : ∀ j ∈ V, j ≠ (b : ℕ) → E k j = true → E b j = true)
    (heavy : p k ≤ p a) : False := by
  refine coheir_exit hq small a b off safe wp wm wr pc k hkb coheir ?_
  have h1 := (wp k k.property).2
  have h2 := mul_le_mul_of_nonneg_left heavy (Nat.cast_nonneg (α := ℚ) q)
  linarith

/-- 3c, dual of 3b in general form (column-feasible p), by reversing the graph. -/
theorem cofar_exit_general {q : ℕ} (hq : 2 ≤ q) {E : CH.Digraph} {V : Finset ℕ}
    (small : SmallerSmallRow q V.card) {a b k z : ℕ} (ha : a ∈ V) (hb : b ∈ V) (hkV : k ∈ V)
    (hzV : z ∈ V) (off : E a b = false) (safe : QFree (insertArc E a b) V q)
    {p : ℕ → ℚ} (hp : ∀ i ∈ V, 0 < p i) (hc : ∀ i ∈ V, mass V p ≤ WeightedSD.col q E V p i)
    (hkb : E k b = true) (hzk : z ≠ k)
    (codom : ∀ j ∈ V, j ≠ b → E k j = true → E z j = true)
    (light : p k < p a) : False := by
  have safeR : QFree (insertArc (fun x y => E y x) b a) V q := by
    have h := safe.reverse
    rwa [insertArc_reverse] at h
  exact far_exit_general (E := fun x y => E y x) (J := insertArc (fun x y => E y x) b a)
    hq small hb hkV hzV (fun x y h => insertArc_mono _ b a x y h)
    (fun i hi y => by simp [insertArc, hi]) safeR (B := {a})
    (fun y hy => by rw [Finset.mem_singleton.mp hy]; exact ⟨ha, off, by simp [insertArc]⟩)
    hp hc hkb hzk codom (by rw [Finset.sum_singleton]; exact light)

/-- 3c, dual of 3b on the flat branch. -/
theorem cofar_exit {q : ℕ} (hq : 2 ≤ q) {E : CH.Digraph} {V : Finset ℕ}
    (small : SmallerSmallRow q V.card) (a b : V) (off : E a b = false)
    (safe : QFree (insertArc E a b) V q) {w p : ℕ → ℚ}
    (wp : ∀ i ∈ V, 0 < w i ∧ 0 < p i) (wm : mass V w = 1)
    (wr : ∀ i ∈ V, WeightedSD.row q E V w i = 1) (pc : ∀ i ∈ V, WeightedSD.col q E V p i = 1)
    (k z : V) (hkb : E k b = true) (hzk : (z : ℕ) ≠ k)
    (codom : ∀ j ∈ V, j ≠ (b : ℕ) → E k j = true → E z j = true)
    (light : p k < p a) : False := by
  have pm := mass_col_of_flat wm wr pc
  exact cofar_exit_general hq small a.property b.property k.property z.property off safe
    (fun i hi => (wp i hi).2) (fun i hi => by rw [pm, pc i hi]) hkb hzk codom light

/-! ### Item 4. Joint safety of a tail star -/

/-- Insert every arc a→y with y ∈ B. -/
def insertTailStar (E : CH.Digraph) (a : ℕ) (B : Finset ℕ) : CH.Digraph :=
  fun x y => if x = a ∧ y ∈ B then true else E x y

/-- If each head y ∈ B is individually safe for the tail a (a is outside the (q-1)-ball of
y, the condition of `qfree_insertArc`), the whole tail star is jointly safe. -/
theorem qfree_insertTailStar {q : ℕ} {E : CH.Digraph} {V : Finset ℕ} (hf : QFree E V q)
    {a : ℕ} (ha : a ∈ V) {B : Finset ℕ} (hBV : ∀ y ∈ B, y ∈ V)
    (hsafe : ∀ y ∈ B, a ∉ ball E V y (q - 1)) : QFree (insertTailStar E a B) V q := by
  have hR : QFree (fun x y => insertTailStar E a B y x) V q := by
    refine qfree_common_head_additions (D := fun x y => E y x) (P := fun x => x ∈ B) (y := a)
      hf.reverse hBV ?_ ?_
    · intro x y h
      by_cases e : y = a ∧ x ∈ B
      · exact Or.inr ⟨e.2, e.1⟩
      · have h' : insertTailStar E a B y x = true := h
        unfold insertTailStar at h'
        rw [if_neg e] at h'
        exact Or.inl h'
    · intro x hx hball
      obtain ⟨_, j, hj, wk⟩ := mem_ball.mp hball
      exact hsafe x hx (mem_ball.mpr ⟨ha, j, hj, wk.reverse_of_mem ha⟩)
  exact hR.reverse

#print axioms star_heir_exit_general
#print axioms heir_exit_general_of_star
#print axioms far_exit_general
#print axioms heir_no_heavier
#print axioms far_exit
#print axioms coheir_no_heavier
#print axioms cofar_exit_general
#print axioms cofar_exit
#print axioms qfree_insertTailStar

end LeanCH.BR.Closure.RehomeExits
