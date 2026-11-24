import checkpoints.puncture_law_20261119.DeckFactorization

/-! Heir exit. In a flat graph E with a safe insertion a→b, an old out-neighbour v of the
tail a whose other parents all point to a cannot be light: (q-1) w_v < q w_b is impossible.
Proof: perturb the flat law by a strict witness of the child E + a→b, delete v and move its
weight to a; the child would then fail SmallRow on V \ {v}. The dual (co-heir) exit follows
by reversal. -/
namespace LeanCH.BR.Closure.HeirExit
open Finset FiniteCutInverse WeightedSD BRq2 BRq3
open scoped Matrix

/-- Row after deleting v and transferring its weight to a. -/
theorem row_transfer {q : ℕ} {J : CH.Digraph} {V : Finset ℕ} {v a : ℕ}
    (hv : v ∈ V) (ha : a ∈ V) (hva : v ≠ a) (y : ℕ → ℚ) (i : ℕ) :
    WeightedSD.row q J (V.erase v) (transferWeight y v a) i =
      WeightedSD.row q J V y i + y v * ((if i = a then (1 : ℚ) else 0) +
        (q : ℚ) * (if J i a = true then (1 : ℚ) else 0) -
        (q : ℚ) * (if J i v = true then (1 : ℚ) else 0)) := by
  have haK : a ∈ V.erase v := Finset.mem_erase.mpr ⟨hva.symm, ha⟩
  unfold WeightedSD.row
  rw [outW_transfer haK, outW_erase hv y i]
  simp only [transferWeight]
  split_ifs <;> ring

theorem row_add {q : ℕ} {J : CH.Digraph} {V : Finset ℕ} (y x : ℕ → ℚ) (ε : ℚ) (i : ℕ) :
    WeightedSD.row q J V (fun u => y u + ε * x u) i =
      WeightedSD.row q J V y i + ε * WeightedSD.row q J V x i := by
  have h : (∑ u ∈ V, if J i u = true then y u + ε * x u else 0) =
      (∑ u ∈ V, if J i u = true then y u else 0) +
        ε * ∑ u ∈ V, if J i u = true then x u else 0 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun u _ => by split_ifs <;> ring
  simp only [WeightedSD.row, outW, h]
  ring

theorem mass_add (V : Finset ℕ) (y x : ℕ → ℚ) (ε : ℚ) :
    mass V (fun u => y u + ε * x u) = mass V y + ε * mass V x := by
  unfold mass
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]

/-- General form of the heir exit. J is any graph that contains E, adds the arc a→b, agrees
with E on rows other than a, and is q-free on V. The weight w only needs to be positive and
feasible for E (mass ≤ every row). -/
theorem heir_exit_general {q : ℕ} (hq : 2 ≤ q) {E J : CH.Digraph} {V : Finset ℕ}
    (small : SmallerSmallRow q V.card) {a b v : ℕ} (ha : a ∈ V) (hb : b ∈ V) (hvV : v ∈ V)
    (off : E a b = false) (hJE : ∀ x y, E x y = true → J x y = true) (hJab : J a b = true)
    (hJi : ∀ i, i ≠ a → ∀ y, J i y = E i y) (safe : QFree J V q)
    {w : ℕ → ℚ} (hw : ∀ i ∈ V, 0 < w i) (hr : ∀ i ∈ V, mass V w ≤ WeightedSD.row q E V w i)
    (hav : E a v = true) (heir : ∀ i ∈ V, i ≠ a → E i v = true → E i a = true)
    (light : ((q : ℚ) - 1) * w v < (q : ℚ) * w b) : False := by
  have hq1 : 1 ≤ q := by omega
  have hJaa : ¬ J a a = true := loopfree safe hq1 ha
  have hab : a ≠ b := by rintro rfl; exact hJaa hJab
  have hva : v ≠ a := by rintro rfl; exact hJaa (hJE _ _ hav)
  have hJav : J a v = true := hJE _ _ hav
  have wn : ∀ i ∈ V, 0 ≤ w i := fun i hi => (hw i hi).le
  -- the child has a strict rational witness
  have bad : ¬ SmallRow q J V := positive_feasible_extension_not_smallRow hq
    (fun i _ j _ h => hJE i j h) w hw hr ha hb (by simp [off]) hJab
  obtain ⟨x, xn, _, xh⟩ := strict_witness_of_not_smallRow bad
  -- rows of J at w
  have rowJ : ∀ i ∈ V, mass V w ≤ WeightedSD.row q J V w i := fun i hi =>
    (hr i hi).trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left
      (outW_mono_graph (fun x _ y _ h => hJE x y h) wn hi) (Nat.cast_nonneg q)))
  have rowJa : mass V w + (q : ℚ) * w b ≤ WeightedSD.row q J V w a := by
    have haB : a ∈ V.erase b := Finset.mem_erase.mpr ⟨hab, ha⟩
    have e1 := outW_erase (D := J) hb w a
    have e2 := outW_erase (D := E) hb w a
    have m : outW E (V.erase b) w a ≤ outW J (V.erase b) w a :=
      outW_mono_graph (fun x _ y _ h => hJE x y h)
        (fun i hi => wn i (Finset.mem_of_mem_erase hi)) haB
    simp only [hJab, off, ite_true, Bool.false_eq_true, ite_false, add_zero] at e1 e2
    have hout : outW E V w a + w b ≤ outW J V w a := by rw [e1, e2]; linarith
    have hm := mul_le_mul_of_nonneg_left hout (Nat.cast_nonneg (α := ℚ) q)
    rw [mul_add] at hm
    have h := hr a ha
    unfold WeightedSD.row at h ⊢
    linarith
  -- the perturbation size
  obtain ⟨G, hG⟩ : ∃ G : ℚ, G = WeightedSD.row q J V w a - mass V w - ((q : ℚ) - 1) * w v :=
    ⟨_, rfl⟩
  have Gpos : 0 < G := by rw [hG]; linarith
  have q1 : (1 : ℚ) ≤ (q : ℚ) - 1 := by
    have : (2 : ℚ) ≤ q := by exact_mod_cast hq
    linarith
  have xv0 : 0 ≤ x v := xn v hvV
  have den : 0 < ((q : ℚ) - 1) * x v + 1 := by
    have := mul_nonneg (by linarith : (0 : ℚ) ≤ (q : ℚ) - 1) xv0
    linarith
  obtain ⟨ε, hε⟩ : ∃ ε : ℚ, ε = G / (((q : ℚ) - 1) * x v + 1) := ⟨_, rfl⟩
  have εpos : 0 < ε := by rw [hε]; exact div_pos Gpos den
  have εeq : ε * (((q : ℚ) - 1) * x v + 1) = G := by rw [hε]; exact div_mul_cancel₀ G den.ne'
  -- delete v, move its weight to a
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

/-- Item 1. Heir exit for a safe insertion a→b in a flat graph. -/
theorem heir_exit {q : ℕ} (hq : 2 ≤ q) {E : CH.Digraph} {V : Finset ℕ}
    (small : SmallerSmallRow q V.card) (a b : V) (off : E a b = false)
    (safe : QFree (insertArc E a b) V q) {w p : ℕ → ℚ}
    (wp : ∀ i ∈ V, 0 < w i ∧ 0 < p i) (wm : mass V w = 1)
    (wr : ∀ i ∈ V, WeightedSD.row q E V w i = 1) (pc : ∀ i ∈ V, WeightedSD.col q E V p i = 1)
    (v : V) (hav : E a v = true)
    (heir : ∀ i ∈ V, i ≠ (a : ℕ) → E i v = true → E i a = true)
    (light : ((q : ℚ) - 1) * w v < (q : ℚ) * w b) : False :=
  heir_exit_general hq small a.property b.property v.property off
    (fun x y h => insertArc_mono E a b x y h) (by simp [insertArc])
    (fun i hi y => by simp [insertArc, hi]) safe (fun i hi => (wp i hi).1)
    (fun i hi => by rw [wm, wr i hi]) hav heir light

/-- The column law has the same mass as the row law: Σ p = Σ p·row(w) = Σ w·col(p) = Σ w. -/
theorem mass_col_of_flat {q : ℕ} {E : CH.Digraph} {V : Finset ℕ} {w p : ℕ → ℚ}
    (wm : mass V w = 1) (wr : ∀ i ∈ V, WeightedSD.row q E V w i = 1)
    (pc : ∀ i ∈ V, WeightedSD.col q E V p i = 1) : mass V p = 1 := by
  have bal : ∑ i ∈ V, p i * WeightedSD.row q E V w i =
      ∑ u ∈ V, w u * WeightedSD.col q E V p u := by
    simp only [WeightedSD.row, WeightedSD.col, outW, inW, mul_add, Finset.sum_add_distrib,
      Finset.mul_sum]
    congr 1
    · exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    · rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun i _ => by
        split_ifs <;> ring
  calc
    mass V p = ∑ i ∈ V, p i * WeightedSD.row q E V w i :=
      Finset.sum_congr rfl fun i hi => by rw [wr i hi, mul_one]
    _ = ∑ u ∈ V, w u * WeightedSD.col q E V p u := bal
    _ = mass V w := Finset.sum_congr rfl fun u hu => by rw [pc u hu, mul_one]
    _ = 1 := wm

/-- Item 2, general form: the co-heir exit, by reversing the graph. -/
theorem coheir_exit_general {q : ℕ} (hq : 2 ≤ q) {E : CH.Digraph} {V : Finset ℕ}
    (small : SmallerSmallRow q V.card) {a b k : ℕ} (ha : a ∈ V) (hb : b ∈ V) (hkV : k ∈ V)
    (off : E a b = false) (safe : QFree (insertArc E a b) V q)
    {p : ℕ → ℚ} (hp : ∀ i ∈ V, 0 < p i) (hc : ∀ i ∈ V, mass V p ≤ WeightedSD.col q E V p i)
    (hkb : E k b = true) (coheir : ∀ j ∈ V, j ≠ b → E k j = true → E b j = true)
    (light : ((q : ℚ) - 1) * p k < (q : ℚ) * p a) : False := by
  have safeR : QFree (insertArc (fun x y => E y x) b a) V q := by
    have h := safe.reverse
    rwa [insertArc_reverse] at h
  exact heir_exit_general (E := fun x y => E y x) hq small hb ha hkV off
    (fun x y h => insertArc_mono _ b a x y h) (by simp [insertArc])
    (fun i hi y => by simp [insertArc, hi]) safeR hp hc hkb coheir light

/-- Item 2. Co-heir exit for a safe insertion a→b in a flat graph. -/
theorem coheir_exit {q : ℕ} (hq : 2 ≤ q) {E : CH.Digraph} {V : Finset ℕ}
    (small : SmallerSmallRow q V.card) (a b : V) (off : E a b = false)
    (safe : QFree (insertArc E a b) V q) {w p : ℕ → ℚ}
    (wp : ∀ i ∈ V, 0 < w i ∧ 0 < p i) (wm : mass V w = 1)
    (wr : ∀ i ∈ V, WeightedSD.row q E V w i = 1) (pc : ∀ i ∈ V, WeightedSD.col q E V p i = 1)
    (k : V) (hkb : E k b = true)
    (coheir : ∀ j ∈ V, j ≠ (b : ℕ) → E k j = true → E b j = true)
    (light : ((q : ℚ) - 1) * p k < (q : ℚ) * p a) : False := by
  have pm := mass_col_of_flat wm wr pc
  exact coheir_exit_general hq small a.property b.property k.property off safe
    (fun i hi => (wp i hi).2) (fun i hi => by rw [pm, pc i hi]) hkb coheir light

section MatrixLevel
open DeckFactorization
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Item 3, matrix level: a deck and positive row sums force H ≥ 0. -/
theorem nonneg_of_deck {N H P : Matrix I I ℝ} (inv : N * H = 1) (deck : Deck N P)
    (rpos : ∀ i, 0 < ∑ k, H i k) : ∀ i j, 0 ≤ H i j := by
  intro i j
  rw [factor inv deck rpos, Matrix.mul_apply]
  exact Finset.sum_nonneg fun m _ =>
    mul_nonneg (theta_inv_nonneg inv deck rpos i m) (deck.nonneg m j)

end MatrixLevel

open DeckFactorization PunctureLaw in
/-- Item 3, graph level: SmallRow on every single deletion, at least two vertices, and
positive row sums of a right inverse of the excess matrix force that inverse to be ≥ 0. -/
theorem graph_nonneg {q : ℕ} {G : CH.Digraph} {V : Finset ℕ} {H : Matrix V V ℝ}
    (inv : excess (realMatrix q G V) * H = 1) (rpos : ∀ i, 0 < ∑ k, H i k)
    (small : ∀ m ∈ V, SmallRow q G (V.erase m)) (two : ∃ i j : V, i ≠ j) :
    ∀ i j, 0 ≤ H i j := by
  obtain ⟨i0, j0, hij⟩ := two
  have each : ∀ m : V, ∃ p : V → ℝ, (∀ i, 0 ≤ p i) ∧ p m = 0 ∧ (∑ i, p i) = 1 ∧
      ∀ i, i ≠ m → (p ᵥ* excess (realMatrix q G V)) i ≤ 0 := by
    intro m
    have other : ∃ j : V, j ≠ m := by
      by_cases h : m = i0
      · exact ⟨j0, by rw [h]; exact hij.symm⟩
      · exact ⟨i0, Ne.symm h⟩
    obtain ⟨j, hj⟩ := other
    exact certificate m (small m m.property) j hj
  choose P hP using each
  have deck : Deck (excess (realMatrix q G V)) P :=
    ⟨fun m k => (hP m).1 k, fun m => (hP m).2.1, fun m => (hP m).2.2.1,
      fun m j hj => (hP m).2.2.2 j hj⟩
  exact nonneg_of_deck inv deck rpos

#print axioms heir_exit_general
#print axioms heir_exit
#print axioms coheir_exit_general
#print axioms coheir_exit
#print axioms nonneg_of_deck
#print axioms graph_nonneg

end LeanCH.BR.Closure.HeirExit
