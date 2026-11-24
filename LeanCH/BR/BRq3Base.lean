import LeanCH.BR.BRq2

/-!
# Infrastructure for `BR(4,3)` and `BR(5,3)` (ball route, out-degree three), Lean 4.35.0

Paper: `checkpoints/boundary_20261111/BRq2_attempt_subagent.md`, §6.1 (Lemma 6.1, uniform reduction).

* `outN D W y`: out-neighbours of `y` inside `W`; `OutEq s D W`: every vertex of `W` has exactly `s` of them.
* `exists_outEq`: min out `≥ s` on `W` has a spanning sub-digraph with out-degree exactly `s` (paper: "we may
  assume out-degree exactly s").
* `exists_sink`: a nonempty `T` with no closed walk of length `1..|T|` inside `T` has a sink of `D[T]`.
* `reach_sink3`: in a 3-free `D[T]` with `|T| ≤ 3`, every `v ∈ T` reaches a sink of `D[T]` within two steps in `T`.
* `corB`: Corollary B (CH at `r = 2`) for a vertex set, from `ball_growth`.
* `card_ge_of_ball`: the degree sum of Lemma 6.1 on a vertex set: a ball bound `b` at radius `q-1` and min out `s`
  give `|U| ≥ b + s`.
* `br_of_ball`: Lemma 6.1, `Ball(q,s) ⇒ BR(q,s)`.
-/

set_option linter.style.longLine false

namespace LeanCH.BR.BRq3

open LeanCH.BR.BRq2 CH Compose.Boundary Compose.FloorSix

/-- Out-neighbours of `y` inside `W`. -/
def outN (D : CH.Digraph) (W : Finset ℕ) (y : ℕ) : Finset ℕ := W.filter (fun z => D y z = true)

/-- Every vertex of `W` has exactly `s` out-neighbours in `W`. -/
def OutEq (s : ℕ) (D : CH.Digraph) (W : Finset ℕ) : Prop := ∀ v ∈ W, (outN D W v).card = s

variable {D : CH.Digraph} {W : Finset ℕ}

theorem mem_outN {y z : ℕ} : z ∈ outN D W y ↔ z ∈ W ∧ D y z = true := Finset.mem_filter

theorem outN_subset {y : ℕ} : outN D W y ⊆ W := Finset.filter_subset _ _

theorem walk_sub {E : CH.Digraph} (h : ∀ a b, D a b = true → E a b = true) {a b m : ℕ}
    (w : Walk D W a b m) : Walk E W a b m := by
  induction w with
  | refl a => exact .refl a
  | step hb hab _ ih => exact .step hb (h _ _ hab) ih

theorem ball_sub {E : CH.Digraph} (h : ∀ a b, D a b = true → E a b = true) {u k : ℕ} :
    ball D W u k ⊆ ball E W u k := by
  intro v hv
  obtain ⟨hvW, j, hj, w⟩ := mem_ball.mp hv
  exact mem_ball.mpr ⟨hvW, j, hj, walk_sub h w⟩

theorem qfree_sub {E : CH.Digraph} {q : ℕ} (h : ∀ a b, D a b = true → E a b = true) (hf : QFree E W q) :
    QFree D W q :=
  fun a ℓ h1 h2 w => hf a ℓ h1 h2 (walk_sub h w)

/-! ### Short closed walks and balls -/

theorem loopfree {q a : ℕ} (hfree : QFree D W q) (hq : 1 ≤ q) (ha : a ∈ W) : ¬ D a a = true :=
  fun h => hfree a 1 le_rfl hq (.step ha h (.refl a))

theorem digonfree {q a b : ℕ} (hfree : QFree D W q) (hq : 2 ≤ q) (ha : a ∈ W) (hb : b ∈ W)
    (hab : D a b = true) (hba : D b a = true) : False :=
  hfree a 2 (by omega) hq (.step hb hab (.step ha hba (.refl a)))

theorem ball_of_adj {a b : ℕ} (hb : b ∈ W) (h : D a b = true) : b ∈ ball D W a 1 :=
  mem_ball.mpr ⟨hb, 1, le_rfl, .step hb h (.refl b)⟩

theorem mem_ball_one {u v : ℕ} (hu : u ∈ W) : v ∈ ball D W u 1 ↔ v = u ∨ v ∈ outN D W u := by
  constructor
  · intro hv
    obtain ⟨hvW, j, hj, w⟩ := mem_ball.mp hv
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hj with rfl | rfl
    · cases w; exact Or.inl rfl
    · cases w with
      | step hb hab w' => cases w'; exact Or.inr (mem_outN.mpr ⟨hb, hab⟩)
  · rintro (rfl | h)
    · exact self_mem_ball hu
    · exact ball_of_adj (mem_outN.mp h).1 (mem_outN.mp h).2

/-- A vertex first reached at radius `k+1` has an in-neighbour in `B_k`. -/
theorem ball_succ_pred {u k z : ℕ} (hu : u ∈ W) (hz : z ∈ ball D W u (k + 1)) (hzk : z ∉ ball D W u k) :
    ∃ y ∈ ball D W u k, D y z = true := by
  obtain ⟨hzW, j, hj, w⟩ := mem_ball.mp hz
  cases j with
  | zero => exact absurd (mem_ball.mpr ⟨hzW, 0, Nat.zero_le _, w⟩) hzk
  | succ j =>
    obtain ⟨y, wy, _, hyz⟩ := w.unsnoc
    refine ⟨y, mem_ball.mpr ⟨?_, j, by omega, wy⟩, hyz⟩
    rcases wy.end_mem_or with rfl | h
    · exact hu
    · exact h

/-- `B_1(u) = {u} ∪ O(u)` has four vertices when out-degrees are three. -/
theorem card_ball_one {u : ℕ} (hfree : QFree D W 1) (hout : OutEq 3 D W) (hu : u ∈ W) :
    (ball D W u 1).card = 4 := by
  classical
  have e : ball D W u 1 = insert u (outN D W u) := by
    ext v; rw [mem_ball_one hu, Finset.mem_insert]
  have hnot : u ∉ outN D W u := fun h => loopfree hfree le_rfl hu (mem_outN.mp h).2
  rw [e, Finset.card_insert_of_notMem hnot, hout u hu]

/-! ### Sinks -/

/-- A nonempty `T` with no closed walk of length `1..|T|` inside `T` has a vertex with no out-neighbour in `T`. -/
theorem exists_sink {T : Finset ℕ} {q : ℕ} (hfree : QFree D T q) (hne : T.Nonempty) (hq : T.card ≤ q) :
    ∃ t ∈ T, ∀ z ∈ T, ¬ D t z = true := by
  classical
  by_contra hcon
  push Not at hcon
  let nx : ℕ → ℕ := fun t => if h : ∃ z ∈ T, D t z = true then h.choose else t
  have hnx : ∀ t ∈ T, nx t ∈ T ∧ D t (nx t) = true := by
    intro t ht
    have h := hcon t ht
    simp only [nx]
    split
    · next h' => exact h'.choose_spec
    · next h' => exact absurd h h'
  obtain ⟨t0, ht0⟩ := hne
  have hg : ∀ i, nx^[i] t0 ∈ T := by
    intro i
    induction i with
    | zero => exact ht0
    | succ i ih => rw [Function.iterate_succ_apply']; exact (hnx _ ih).1
  have hw : ∀ i l, Walk D T (nx^[i] t0) (nx^[i + l] t0) l := by
    intro i l
    induction l with
    | zero => exact .refl _
    | succ l ih =>
      have e : nx^[i + (l + 1)] t0 = nx (nx^[i + l] t0) := by
        rw [← Nat.add_assoc, Function.iterate_succ_apply']
      rw [e]
      exact ih.snoc (hnx _ (hg _)).1 (hnx _ (hg _)).2
  obtain ⟨i, hi, j, hj, hij, heq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (s := Finset.range (T.card + 1)) (t := T) (f := fun i => nx^[i] t0) (by simp)
    (by intro i _; exact hg i)
  have heq' : nx^[i] t0 = nx^[j] t0 := heq
  simp only [Finset.mem_range] at hi hj
  rcases Nat.lt_or_gt_of_ne hij with h | h
  · have w := hw i (j - i)
    rw [Nat.add_sub_cancel' h.le, ← heq'] at w
    exact hfree _ (j - i) (by omega) (by omega) w
  · have w := hw j (i - j)
    rw [Nat.add_sub_cancel' h.le, heq'] at w
    exact hfree _ (i - j) (by omega) (by omega) w

/-- In a 3-free `D[T]` with `|T| ≤ 3`, every `v ∈ T` reaches a sink of `D[T]` within two steps inside `T`. -/
theorem reach_sink3 {T : Finset ℕ} {v : ℕ} (hfree : QFree D W 3) (hTW : T ⊆ W) (hT : T.card ≤ 3)
    (hv : v ∈ T) :
    ∃ s ∈ T, (∀ z ∈ T, ¬ D s z = true) ∧
      (s = v ∨ D v s = true ∨ ∃ x ∈ T, D v x = true ∧ D x s = true) := by
  classical
  by_cases h0 : ∀ z ∈ T, ¬ D v z = true
  · exact ⟨v, hv, h0, Or.inl rfl⟩
  push Not at h0
  obtain ⟨x, hx, hvx⟩ := h0
  by_cases h1 : ∀ z ∈ T, ¬ D x z = true
  · exact ⟨x, hx, h1, Or.inr (Or.inl hvx)⟩
  push Not at h1
  obtain ⟨y, hy, hxy⟩ := h1
  by_cases h2 : ∀ z ∈ T, ¬ D y z = true
  · exact ⟨y, hy, h2, Or.inr (Or.inr ⟨x, hx, hvx, hxy⟩)⟩
  push Not at h2
  obtain ⟨z, hz, hyz⟩ := h2
  exfalso
  have hvW := hTW hv
  have hxW := hTW hx
  have hyW := hTW hy
  have hzW := hTW hz
  have d1 : v ≠ x := by rintro rfl; exact loopfree hfree (by omega) hvW hvx
  have d2 : x ≠ y := by rintro rfl; exact loopfree hfree (by omega) hxW hxy
  have d3 : y ≠ z := by rintro rfl; exact loopfree hfree (by omega) hyW hyz
  have d4 : v ≠ y := by rintro rfl; exact digonfree hfree (by omega) hvW hxW hvx hxy
  have d5 : x ≠ z := by rintro rfl; exact digonfree hfree (by omega) hxW hyW hxy hyz
  have d6 : v ≠ z := by
    rintro rfl
    exact hfree v 3 (by omega) le_rfl (.step hxW hvx (.step hyW hxy (.step hvW hyz (.refl v))))
  have hsub : ({v, x, y, z} : Finset ℕ) ⊆ T := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl <;> assumption
  have hc := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem (by simp [d1, d4, d6]), Finset.card_insert_of_notMem (by simp [d2, d5]),
    Finset.card_pair d3] at hc
  omega

/-! ### Corollary B and the degree sum on a vertex set -/

/-- Corollary B (CH at `r = 2`) on a vertex set. -/
theorem corB {U : Finset ℕ} {q : ℕ} (hq : 1 ≤ q) (hfree : QFree D U q) (hmin : MinOut2 D U)
    (hne : U.Nonempty) : 2 * q + 1 ≤ U.card := by
  obtain ⟨z, hz⟩ := hne
  exact (ball_growth q hq D U hfree hmin z hz q le_rfl).trans (Finset.card_le_card ball_subset)

/-- Lemma 6.1 as a degree sum on a vertex set: in-neighbours of `z` avoid `B_{q-1}(z)`, so a radius-`(q-1)` ball
bound `b` and min out `s` give `s|U| ≤ Σ in ≤ |U|(|U| - b)`. -/
theorem card_ge_of_ball {U : Finset ℕ} {q s b : ℕ} (hq : 1 ≤ q) (hfree : QFree D U q)
    (hmin : ∀ y ∈ U, s ≤ (outN D U y).card) (hball : ∀ z ∈ U, b ≤ (ball D U z (q - 1)).card)
    (hne : U.Nonempty) : b + s ≤ U.card := by
  classical
  have hin : ∀ z ∈ U, (U.filter (fun y => D y z = true)).card ≤ U.card - b := by
    intro z hz
    have hsub : U.filter (fun y => D y z = true) ⊆ U \ ball D U z (q - 1) := by
      intro y hy
      obtain ⟨hyU, hyz⟩ := Finset.mem_filter.mp hy
      exact Finset.mem_sdiff.mpr ⟨hyU, fun hyb => no_back_arc hfree hz hyb (by omega) hyz⟩
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_sdiff_of_subset ball_subset] at h1
    have h2 := hball z hz
    omega
  have hsum : U.card * s ≤ U.card * (U.card - b) := by
    calc U.card * s = ∑ _y ∈ U, s := (Finset.sum_const_nat (fun _ _ => rfl)).symm
      _ ≤ ∑ y ∈ U, (outN D U y).card := Finset.sum_le_sum hmin
      _ = ∑ z ∈ U, (U.filter (fun y => D y z = true)).card := Compose.ThinRigid.sum_out_eq_sum_in D U
      _ ≤ ∑ _z ∈ U, (U.card - b) := Finset.sum_le_sum hin
      _ = U.card * (U.card - b) := Finset.sum_const_nat (fun _ _ => rfl)
  have hpos : 0 < U.card := Finset.card_pos.mpr hne
  have h3 := Nat.le_of_mul_le_mul_left hsum hpos
  obtain ⟨z, hz⟩ := hne
  have h4 := (hball z hz).trans (Finset.card_le_card (ball_subset (D := D) (W := U) (u := z) (k := q - 1)))
  omega

/-! ### Exact out-degree and Lemma 6.1 -/

/-- Min out `≥ s` on `V` has a spanning sub-digraph with out-degree exactly `s` on `V`. -/
theorem exists_outEq {G : CH.Digraph} {V : Finset ℕ} {s : ℕ} (h : ∀ v ∈ V, s ≤ (outN G V v).card) :
    ∃ G' : CH.Digraph, (∀ a b, G' a b = true → G a b = true) ∧ OutEq s G' V := by
  classical
  have hex : ∀ a, ∃ t ⊆ outN G V a, t.card = min s (outN G V a).card :=
    fun a => Finset.exists_subset_card_eq (min_le_right _ _)
  choose sel hsel hcard using hex
  refine ⟨fun a b => decide (b ∈ sel a), ?_, ?_⟩
  · intro a b hab
    exact (mem_outN.mp (hsel a (of_decide_eq_true hab))).2
  · intro v hv
    have e : outN (fun a b => decide (b ∈ sel a)) V v = sel v := by
      ext z
      rw [mem_outN, decide_eq_true_eq]
      constructor
      · exact fun hz => hz.2
      · exact fun hz => ⟨(mem_outN.mp (hsel v hz)).1, hz⟩
    rw [e, hcard, min_eq_left (h v hv)]

/-- **Lemma 6.1** (`Ball(q,s) ⇒ BR(q,s)`): a radius-`(q-1)` ball bound `s(q-1)+1` for every `q`-free digraph with
out-degree exactly `s` gives boundary regularity at `(q, s)`. -/
theorem br_of_ball {q s : ℕ} (hq : 1 ≤ q)
    (hball : ∀ (D : CH.Digraph) (W : Finset ℕ), QFree D W q → OutEq s D W →
      ∀ u ∈ W, s * (q - 1) + 1 ≤ (ball D W u (q - 1)).card) :
    BoundaryRegular q s := by
  intro G loopless deg noShort
  classical
  have hfree : QFree G (Finset.range (q * s + 1)) q := qfree_of_noShort loopless noShort
  obtain ⟨G', hsub, hout⟩ := exists_outEq (G := G) (V := Finset.range (q * s + 1)) (s := s)
    (fun v hv => out_card deg (Finset.mem_range.mp hv))
  have e : s * (q - 1) + s = q * s := by
    obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    rw [Nat.add_sub_cancel, Nat.succ_mul, Nat.mul_comm]
  have hle : ∀ u ∈ Finset.range (q * s + 1), (par G (q * s + 1) u).card ≤ s := by
    intro u hu
    have hA := hball G' _ (qfree_sub hsub hfree) hout u hu
    have hsub2 : par G (q * s + 1) u ⊆ Finset.range (q * s + 1) \ ball G (Finset.range (q * s + 1)) u (q - 1) := by
      intro y hy
      obtain ⟨hyV, hyu⟩ := Finset.mem_filter.mp hy
      exact Finset.mem_sdiff.mpr ⟨hyV, fun hyb => no_back_arc hfree hu hyb (by omega) hyu⟩
    have h1 := Finset.card_le_card hsub2
    have h2 := Finset.card_le_card (ball_sub (W := Finset.range (q * s + 1)) (u := u) (k := q - 1) hsub)
    rw [Finset.card_sdiff_of_subset ball_subset, Finset.card_range] at h1
    omega
  have hge : ∑ _u ∈ Finset.range (q * s + 1), s ≤
      ∑ u ∈ Finset.range (q * s + 1), (par G (q * s + 1) u).card :=
    calc ∑ _u ∈ Finset.range (q * s + 1), s
        ≤ ∑ x ∈ Finset.range (q * s + 1),
            ((Finset.range (q * s + 1)).filter (fun w => G x w = true)).card :=
          Finset.sum_le_sum (fun x hx => out_card deg (Finset.mem_range.mp hx))
      _ = ∑ v ∈ Finset.range (q * s + 1),
            ((Finset.range (q * s + 1)).filter (fun u => G u v = true)).card :=
          Compose.ThinRigid.sum_out_eq_sum_in G _
      _ = ∑ u ∈ Finset.range (q * s + 1), (par G (q * s + 1) u).card := rfl
  have heq := le_antisymm (Finset.sum_le_sum hle) hge
  have each := (Finset.sum_eq_sum_iff_of_le hle).mp heq
  intro v hv
  exact each v (Finset.mem_range.mpr hv)

end LeanCH.BR.BRq3
