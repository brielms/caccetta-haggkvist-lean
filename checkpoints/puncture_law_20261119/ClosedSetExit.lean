import checkpoints.puncture_law_20261119.RehomeExits

/-! Closed-set exit. A nonempty set X of vertices other than the tail a, avoiding the new
heads B, whose parents outside X (other than a) are all parents of a, cannot be light:
q·Σ_{X ∩ N⁺(a)} w < q·Σ_B w + Σ_X w is impossible. Proof: perturb w by a strict witness of
the child J, delete X and move all of its weight to a; J would then fail SmallRow on V \ X.

Compared with the paper statement: `X.Nonempty` is needed (X = ∅ gives no contradiction);
the main theorem assumes `¬ SmallRow q J V` (automatic when B is nonempty, see
`closed_set_exit_general`); the hypothesis `∀ x ∈ X, J a x = E a x` is NOT needed — a new
head of a inside X adds to row a exactly what its deletion removes. -/
namespace LeanCH.BR.Closure.ClosedSetExit
open Finset FiniteCutInverse WeightedSD BRq2 BRq3 LeanCH.BR.Closure.HeirExit
  LeanCH.BR.Closure.RehomeExits

/-- Delete the set X and move all of its weight to a. -/
def setTransfer (y : ℕ → ℚ) (X : Finset ℕ) (a : ℕ) : ℕ → ℚ :=
  fun u => y u + if u = a then ∑ x ∈ X, y x else 0

theorem outW_setTransfer {J : CH.Digraph} {V X : Finset ℕ} {a : ℕ} (hXV : X ⊆ V)
    (haK : a ∈ V \ X) (y : ℕ → ℚ) (i : ℕ) :
    outW J (V \ X) (setTransfer y X a) i =
      outW J V y i - (∑ u ∈ X, if J i u = true then y u else 0) +
        (if J i a = true then ∑ x ∈ X, y x else 0) := by
  have h1 : outW J (V \ X) (setTransfer y X a) i = outW J (V \ X) y i +
      ∑ u ∈ V \ X, if u = a then (if J i a = true then ∑ x ∈ X, y x else 0) else 0 := by
    unfold outW setTransfer
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun u _ => ?_
    by_cases hu : u = a
    · rw [hu]; by_cases hJ : J i a = true <;> simp [hJ]
    · simp [hu]
  have h2 : outW J V y i = outW J (V \ X) y i + ∑ u ∈ X, if J i u = true then y u else 0 := by
    unfold outW; exact (Finset.sum_sdiff hXV).symm
  rw [h1, h2, Finset.sum_ite_eq', if_pos haK]
  ring

theorem mass_setTransfer {V X : Finset ℕ} {a : ℕ} (hXV : X ⊆ V) (haK : a ∈ V \ X)
    (y : ℕ → ℚ) : mass (V \ X) (setTransfer y X a) = mass V y := by
  unfold mass setTransfer
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq', if_pos haK]
  exact Finset.sum_sdiff hXV

theorem row_setTransfer {q : ℕ} {J : CH.Digraph} {V X : Finset ℕ} {a : ℕ} (hXV : X ⊆ V)
    (haK : a ∈ V \ X) (y : ℕ → ℚ) (i : ℕ) :
    WeightedSD.row q J (V \ X) (setTransfer y X a) i =
      WeightedSD.row q J V y i + (if i = a then ∑ x ∈ X, y x else 0) +
        (q : ℚ) * (if J i a = true then ∑ x ∈ X, y x else 0) -
        (q : ℚ) * ∑ u ∈ X, if J i u = true then y u else 0 := by
  unfold WeightedSD.row
  rw [outW_setTransfer hXV haK]
  simp only [setTransfer]
  ring

theorem sum_ite_add (X : Finset ℕ) (P : ℕ → Prop) [DecidablePred P] (w x : ℕ → ℚ) (ε : ℚ) :
    (∑ u ∈ X, if P u then w u + ε * x u else 0) =
      (∑ u ∈ X, if P u then w u else 0) + ε * ∑ u ∈ X, if P u then x u else 0 := by
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun u _ => by split_ifs <;> ring

/-! ### Item 1. Closed-set exit -/

theorem closed_set_exit_strict {q : ℕ} (hq : 2 ≤ q) {E J : CH.Digraph} {V : Finset ℕ}
    (small : SmallerSmallRow q V.card) {a : ℕ} (ha : a ∈ V)
    (hJE : ∀ x y, E x y = true → J x y = true)
    (hJi : ∀ i, i ≠ a → ∀ y, J i y = E i y) (safe : QFree J V q)
    {B : Finset ℕ} (hB : ∀ y ∈ B, y ∈ V ∧ E a y = false ∧ J a y = true)
    {w : ℕ → ℚ} (hw : ∀ i ∈ V, 0 < w i) (hr : ∀ i ∈ V, mass V w ≤ WeightedSD.row q E V w i)
    (strict : ¬ SmallRow q J V)
    {X : Finset ℕ} (hX : X.Nonempty) (hXV : X ⊆ V) (haX : a ∉ X) (hBX : ∀ y ∈ B, y ∉ X)
    (closed : ∀ i ∈ V, i ∉ X → i ≠ a → (∃ x ∈ X, E i x = true) → E i a = true)
    (light : (q : ℚ) * ∑ x ∈ X.filter (fun x => E a x = true), w x <
      (q : ℚ) * ∑ y ∈ B, w y + ∑ x ∈ X, w x) : False := by
  have hq1 : 1 ≤ q := by omega
  have hJaa : ¬ J a a = true := loopfree safe hq1 ha
  have wn : ∀ i ∈ V, 0 ≤ w i := fun i hi => (hw i hi).le
  have hq0 : (0 : ℚ) ≤ q := Nat.cast_nonneg q
  have haK : a ∈ V \ X := Finset.mem_sdiff.mpr ⟨ha, haX⟩
  obtain ⟨x, xn, _, xh⟩ := strict_witness_of_not_smallRow strict
  have rowJ : ∀ i ∈ V, mass V w ≤ WeightedSD.row q J V w i := fun i hi =>
    (hr i hi).trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left
      (outW_mono_graph (fun x _ y _ h => hJE x y h) wn hi) (Nat.cast_nonneg q)))
  -- the row of a at w: new heads in B count, new heads in X cancel against their deletion
  have key : outW E V w a + ∑ y ∈ B, w y + ∑ u ∈ X, (if J a u = true then w u else 0) ≤
      outW J V w a + ∑ u ∈ X, (if E a u = true then w u else 0) := by
    have hBV : B ⊆ V := fun y hy => (hB y hy).1
    have eB : ∑ y ∈ B, w y = ∑ u ∈ V, if u ∈ B then w u else 0 := by
      rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hBV]
    have eXJ : (∑ u ∈ X, if J a u = true then w u else 0) =
        ∑ u ∈ V, if u ∈ X then (if J a u = true then w u else 0) else 0 := by
      rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hXV]
    have eXE : (∑ u ∈ X, if E a u = true then w u else 0) =
        ∑ u ∈ V, if u ∈ X then (if E a u = true then w u else 0) else 0 := by
      rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hXV]
    rw [eB, eXJ, eXE]
    unfold outW
    simp only [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro u hu
    have wu := wn u hu
    by_cases huB : u ∈ B
    · obtain ⟨_, hE, hJ⟩ := hB u huB
      have huX := hBX u huB
      simp [huB, huX, hE, hJ]
    · by_cases hE : E a u = true
      · have hJ := hJE _ _ hE
        by_cases huX : u ∈ X <;> simp [huB, huX, hE, hJ]
      · by_cases hJ : J a u = true <;> by_cases huX : u ∈ X <;> simp [huB, huX, hE, hJ, wu]
  have keyq := mul_le_mul_of_nonneg_left key hq0
  have hra := hr a ha
  have rJa : WeightedSD.row q J V w a = w a + (q : ℚ) * outW J V w a := rfl
  have rEa : WeightedSD.row q E V w a = w a + (q : ℚ) * outW E V w a := rfl
  rw [Finset.sum_filter] at light
  -- the perturbation size
  obtain ⟨T, hT⟩ : ∃ T : ℚ, T = ∑ u ∈ X, if J a u = true then x u else 0 := ⟨_, rfl⟩
  have T0 : 0 ≤ T := by
    rw [hT]; exact Finset.sum_nonneg fun u hu => by
      split_ifs
      · exact xn u (hXV hu)
      · exact le_rfl
  obtain ⟨G, hG⟩ : ∃ G : ℚ, G = (q : ℚ) * ∑ y ∈ B, w y + ∑ u ∈ X, w u -
      (q : ℚ) * ∑ u ∈ X, (if E a u = true then w u else 0) := ⟨_, rfl⟩
  have Gpos : 0 < G := by rw [hG]; linarith
  have den : 0 < (q : ℚ) * T + 1 := by
    have := mul_nonneg hq0 T0
    linarith
  obtain ⟨ε, hε⟩ : ∃ ε : ℚ, ε = G / ((q : ℚ) * T + 1) := ⟨_, rfl⟩
  have εpos : 0 < ε := by rw [hε]; exact div_pos Gpos den
  have εeq : ε * ((q : ℚ) * T + 1) = G := by rw [hε]; exact div_mul_cancel₀ G den.ne'
  -- the perturbed weight
  obtain ⟨y, hy⟩ : ∃ y : ℕ → ℚ, y = fun u => w u + ε * x u := ⟨_, rfl⟩
  have yn : ∀ u ∈ V, 0 ≤ y u := fun u hu => by
    rw [hy]; exact add_nonneg (wn u hu) (mul_nonneg εpos.le (xn u hu))
  have eS : ∑ u ∈ X, y u = ∑ u ∈ X, w u + ε * ∑ u ∈ X, x u := by
    rw [hy, Finset.mul_sum, ← Finset.sum_add_distrib]
  have eD : ∀ (D : CH.Digraph) (i : ℕ), (∑ u ∈ X, if D i u = true then y u else 0) =
      (∑ u ∈ X, if D i u = true then w u else 0) +
        ε * ∑ u ∈ X, if D i u = true then x u else 0 := by
    intro D i; rw [hy]; exact sum_ite_add X (fun u => D i u = true) w x ε
  have erow : ∀ i, WeightedSD.row q J V y i =
      WeightedSD.row q J V w i + ε * WeightedSD.row q J V x i := by
    intro i; rw [hy]; exact row_add w x ε i
  have emass : mass V y = mass V w + ε * mass V x := by rw [hy]; exact mass_add V w x ε
  have xX : 0 ≤ ∑ u ∈ X, x u := Finset.sum_nonneg fun u hu => xn u (hXV hu)
  have yX : 0 ≤ ∑ u ∈ X, y u := Finset.sum_nonneg fun u hu => yn u (hXV hu)
  -- delete X, move its weight to a
  let K := V \ X
  let z := setTransfer y X a
  have hKV : K ⊆ V := Finset.sdiff_subset
  have hKne : K ≠ V := by
    obtain ⟨v, hv⟩ := hX
    intro he
    have hh : v ∈ K := by rw [he]; exact hXV hv
    exact (Finset.mem_sdiff.mp hh).2 hv
  have hz : ∀ u ∈ K, 0 ≤ z u := by
    intro u hu
    have := yn u (hKV hu)
    show 0 ≤ y u + if u = a then ∑ x ∈ X, y x else 0
    split_ifs <;> linarith
  apply (small.induced safe K hKV hKne).no_strict ⟨a, haK⟩ z hz
  intro i hi
  have hiV : i ∈ V := hKV hi
  have hiX : i ∉ X := (Finset.mem_sdiff.mp hi).2
  have e1 := row_setTransfer (q := q) (J := J) hXV haK y i
  have e2 := mass_setTransfer hXV haK y
  show mass (V \ X) (setTransfer y X a) < WeightedSD.row q J (V \ X) (setTransfer y X a) i
  rw [e1, e2, erow i, emass]
  have hxi := mul_pos εpos (sub_pos.mpr (xh i hiV))
  by_cases hia : i = a
  · rw [hia] at hxi ⊢
    rw [if_pos rfl, if_neg hJaa, eS, eD J a, ← hT]
    have := mul_nonneg εpos.le xX
    have εT : ε * ((q : ℚ) * T) + ε = G := by linarith
    linarith
  · have hw0 := rowJ i hiV
    rw [if_neg hia, hJi i hia a]
    have eJi : (∑ u ∈ X, if J i u = true then y u else 0) =
        ∑ u ∈ X, if E i u = true then y u else 0 :=
      Finset.sum_congr rfl fun u _ => by rw [hJi i hia u]
    rw [eJi]
    by_cases hEa : E i a = true
    · rw [if_pos hEa]
      have h1 : (∑ u ∈ X, if E i u = true then y u else 0) ≤ ∑ u ∈ X, y u :=
        Finset.sum_le_sum fun u hu => by
          split_ifs
          · exact le_rfl
          · exact yn u (hXV hu)
      have := mul_le_mul_of_nonneg_left h1 hq0
      linarith
    · rw [if_neg hEa]
      have h0 : (∑ u ∈ X, if E i u = true then y u else 0) = 0 :=
        Finset.sum_eq_zero fun u hu => by
          rw [if_neg]
          intro hE
          exact hEa (closed i hiV hiX hia ⟨u, hu, hE⟩)
      rw [h0]
      linarith

/-- Item 1 without the strictness hypothesis, for a nonempty set of new heads. -/
theorem closed_set_exit_general {q : ℕ} (hq : 2 ≤ q) {E J : CH.Digraph} {V : Finset ℕ}
    (small : SmallerSmallRow q V.card) {a : ℕ} (ha : a ∈ V)
    (hJE : ∀ x y, E x y = true → J x y = true)
    (hJi : ∀ i, i ≠ a → ∀ y, J i y = E i y) (safe : QFree J V q)
    {B : Finset ℕ} (hB : ∀ y ∈ B, y ∈ V ∧ E a y = false ∧ J a y = true) (hBne : B.Nonempty)
    {w : ℕ → ℚ} (hw : ∀ i ∈ V, 0 < w i) (hr : ∀ i ∈ V, mass V w ≤ WeightedSD.row q E V w i)
    {X : Finset ℕ} (hX : X.Nonempty) (hXV : X ⊆ V) (haX : a ∉ X) (hBX : ∀ y ∈ B, y ∉ X)
    (closed : ∀ i ∈ V, i ∉ X → i ≠ a → (∃ x ∈ X, E i x = true) → E i a = true)
    (light : (q : ℚ) * ∑ x ∈ X.filter (fun x => E a x = true), w x <
      (q : ℚ) * ∑ y ∈ B, w y + ∑ x ∈ X, w x) : False :=
  closed_set_exit_strict hq small ha hJE hJi safe hB hw hr
    (star_not_smallRow hq ha hJE hB hBne hw hr) hX hXV haX hBX closed light

/-! ### Item 2a. The star heir exit is the case X = {v} -/

theorem star_heir_exit_general' {q : ℕ} (hq : 2 ≤ q) {E J : CH.Digraph} {V : Finset ℕ}
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
  have hBne : B.Nonempty := by
    rcases B.eq_empty_or_nonempty with h | h
    · rw [h, Finset.sum_empty, mul_zero] at light
      have : (1 : ℚ) ≤ (q : ℚ) - 1 := by
        have : (2 : ℚ) ≤ q := by exact_mod_cast hq
        linarith
      have := mul_pos (by linarith : (0 : ℚ) < (q : ℚ) - 1) (hw v hvV)
      linarith
    · exact h
  refine closed_set_exit_general hq small ha hJE hJi safe hB hBne hw hr (X := {v})
    (Finset.singleton_nonempty v) (Finset.singleton_subset_iff.mpr hvV)
    (fun h => hva (Finset.mem_singleton.mp h).symm) ?_ ?_ ?_
  · intro y hy hyv
    rw [Finset.mem_singleton.mp hyv] at hy
    have := (hB v hy).2.1
    rw [hav] at this
    exact Bool.noConfusion this
  · rintro i hiV _ hia ⟨u, hu, hE⟩
    rw [Finset.mem_singleton.mp hu] at hE
    exact heir i hiV hia hE
  · rw [Finset.filter_singleton, if_pos hav, Finset.sum_singleton]
    linarith

/-! ### Item 2b. Flat-branch wrapper -/

theorem closed_set_exit {q : ℕ} (hq : 2 ≤ q) {E : CH.Digraph} {V : Finset ℕ}
    (small : SmallerSmallRow q V.card) (a b : V) (off : E a b = false)
    (safe : QFree (insertArc E a b) V q) {w p : ℕ → ℚ}
    (wp : ∀ i ∈ V, 0 < w i ∧ 0 < p i) (wm : mass V w = 1)
    (wr : ∀ i ∈ V, WeightedSD.row q E V w i = 1) (pc : ∀ i ∈ V, WeightedSD.col q E V p i = 1)
    {X : Finset ℕ} (hX : X.Nonempty) (hXV : X ⊆ V) (haX : (a : ℕ) ∉ X) (hbX : (b : ℕ) ∉ X)
    (closed : ∀ i ∈ V, i ∉ X → i ≠ (a : ℕ) → (∃ x ∈ X, E i x = true) → E i a = true)
    (light : (q : ℚ) * ∑ x ∈ X.filter (fun x => E a x = true), w x <
      (q : ℚ) * w b + ∑ x ∈ X, w x) : False :=
  closed_set_exit_general hq small a.property
    (fun x y h => insertArc_mono E a b x y h) (fun i hi y => by simp [insertArc, hi]) safe
    (B := {(b : ℕ)})
    (fun y hy => by
      rw [Finset.mem_singleton.mp hy]; exact ⟨b.property, off, by simp [insertArc]⟩)
    (Finset.singleton_nonempty _)
    (fun i hi => (wp i hi).1) (fun i hi => by rw [wm, wr i hi]) hX hXV haX
    (fun y hy => by rw [Finset.mem_singleton.mp hy]; exact hbX) closed
    (by rw [Finset.sum_singleton]; exact light)

/-! ### Item 2c. Module form: X inside the out-neighbourhood of a -/

theorem closed_module_exit {q : ℕ} (hq : 2 ≤ q) {E : CH.Digraph} {V : Finset ℕ}
    (small : SmallerSmallRow q V.card) (a b : V) (off : E a b = false)
    (safe : QFree (insertArc E a b) V q) {w p : ℕ → ℚ}
    (wp : ∀ i ∈ V, 0 < w i ∧ 0 < p i) (wm : mass V w = 1)
    (wr : ∀ i ∈ V, WeightedSD.row q E V w i = 1) (pc : ∀ i ∈ V, WeightedSD.col q E V p i = 1)
    {X : Finset ℕ} (hX : X.Nonempty) (hXV : X ⊆ V) (haX : (a : ℕ) ∉ X) (hbX : (b : ℕ) ∉ X)
    (hout : ∀ x ∈ X, E a x = true)
    (closed : ∀ i ∈ V, i ∉ X → i ≠ (a : ℕ) → (∃ x ∈ X, E i x = true) → E i a = true)
    (light : ((q : ℚ) - 1) * ∑ x ∈ X, w x < (q : ℚ) * w b) : False := by
  refine closed_set_exit hq small a b off safe wp wm wr pc hX hXV haX hbX closed ?_
  rw [Finset.filter_true_of_mem hout]
  linarith

#print axioms closed_set_exit_strict
#print axioms closed_set_exit_general
#print axioms star_heir_exit_general'
#print axioms closed_set_exit
#print axioms closed_module_exit

end LeanCH.BR.Closure.ClosedSetExit
