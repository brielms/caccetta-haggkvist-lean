import LeanCH.BR.BRq4All
import LeanCH.BR.BRq3BallAll

/-!
# BR(4,5): shared tools (Lean 4.35.0)

Paper: `checkpoints/boundary_20261111/BR45_attempt_subagent.md` §1 ("Deletion test"), audited in
`BR45_audit_subagent.md` §1.

* `inN D W v`: in-neighbours of `v` inside `W`.
* `n1 … n4`: a `4`-free vertex set has no loop, digon, triangle or 4-cycle.
* `ball_q_one`: `Ball q 1` for every `q ≥ 1` (so `BR(q,1)` holds; a `4`-free digraph on 5 vertices with min out
  `≥ 1` is `C_5`).
* `dt_size`, `dt_reg` (**DT_c**): on a `q`-free vertex set `U` whose members keep `≥ s` heads in `U`, a ball
  statement `Ball q s` gives `|U| ≥ qs + 1`, and at `|U| = qs + 1` every member has exactly `s` heads and exactly
  `s` in-neighbours in `U`.
* `ch1 … ch4`, `reg1`, `reg2`: the instances at `q = 4` (from `ball_q_one`, `ball_growth`, `ball_all`, `ball44`).
* `dcount`: bipartite double counting.
-/

set_option linter.style.longLine false

namespace LeanCH.BR.BR45

open LeanCH.BR.BRq2 LeanCH.BR.BRq3 CH Compose.Boundary Compose.FloorSix

variable {D : CH.Digraph} {W : Finset ℕ}

/-- In-neighbours of `v` inside `W`. -/
def inN (D : CH.Digraph) (W : Finset ℕ) (v : ℕ) : Finset ℕ := W.filter (fun y => D y v = true)

theorem mem_inN {y v : ℕ} : y ∈ inN D W v ↔ y ∈ W ∧ D y v = true := Finset.mem_filter

/-! ### Short cycles -/

theorem n1 (hfree : QFree D W 4) {a : ℕ} (ha : a ∈ W) (h : D a a = true) : False :=
  hfree a 1 le_rfl (by omega) (.step ha h (.refl a))

theorem n2 (hfree : QFree D W 4) {a b : ℕ} (ha : a ∈ W) (hb : b ∈ W) (h1 : D a b = true)
    (h2 : D b a = true) : False :=
  hfree a 2 (by omega) (by omega) (.step hb h1 (.step ha h2 (.refl a)))

theorem n3 (hfree : QFree D W 4) {a b c : ℕ} (ha : a ∈ W) (hb : b ∈ W) (hc : c ∈ W) (h1 : D a b = true)
    (h2 : D b c = true) (h3 : D c a = true) : False :=
  hfree a 3 (by omega) (by omega) (.step hb h1 (.step hc h2 (.step ha h3 (.refl a))))

theorem n4 (hfree : QFree D W 4) {a b c d : ℕ} (ha : a ∈ W) (hb : b ∈ W) (hc : c ∈ W) (hd : d ∈ W)
    (h1 : D a b = true) (h2 : D b c = true) (h3 : D c d = true) (h4 : D d a = true) : False :=
  hfree a 4 (by omega) le_rfl (.step hb h1 (.step hc h2 (.step hd h3 (.step ha h4 (.refl a)))))

theorem ne_of_arc (hfree : QFree D W 4) {a b : ℕ} (hb : b ∈ W) (h : D a b = true) : a ≠ b := by
  rintro rfl; exact n1 hfree hb h

/-! ### Small counting tools -/

theorem three_le {S : Finset ℕ} {a b c : ℕ} (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c) : 3 ≤ S.card := by
  classical
  have hsub : ({a, b, c} : Finset ℕ) ⊆ S := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl <;> assumption
  have := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem (by simp [hab, hac]), Finset.card_pair hbc] at this
  exact this

theorem two_le {S : Finset ℕ} {a b : ℕ} (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b) : 2 ≤ S.card := by
  classical
  have hsub : ({a, b} : Finset ℕ) ⊆ S := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl <;> assumption
  have := Finset.card_le_card hsub
  rw [Finset.card_pair hab] at this
  exact this

theorem sum_const' (S : Finset ℕ) (c : ℕ) : ∑ _x ∈ S, c = S.card * c :=
  Finset.sum_const_nat (fun _ _ => rfl)

/-- Bipartite double counting. -/
theorem dcount (A B : Finset ℕ) (r : ℕ → ℕ → Prop) [∀ a b, Decidable (r a b)] :
    ∑ a ∈ A, (B.filter (fun b => r a b)).card = ∑ b ∈ B, (A.filter (fun a => r a b)).card := by
  classical
  have hc : ∀ (S : Finset ℕ) (p : ℕ → Prop) [DecidablePred p], (S.filter p).card = ∑ w ∈ S, if p w then 1 else 0 := by
    intro S p _; exact Finset.card_filter p S
  rw [Finset.sum_congr rfl (fun a _ => hc B (fun b => r a b)),
      Finset.sum_congr rfl (fun b _ => hc A (fun a => r a b))]
  exact Finset.sum_comm

/-- Out-neighbourhoods split over a disjoint union. -/
theorem outN_union (A B : Finset ℕ) (x : ℕ) : outN D (A ∪ B) x = outN D A x ∪ outN D B x := by
  classical
  unfold outN
  exact Finset.filter_union _ _ _

theorem card_outN_union {A B : Finset ℕ} (h : Disjoint A B) (x : ℕ) :
    (outN D (A ∪ B) x).card = (outN D A x).card + (outN D B x).card := by
  classical
  rw [outN_union]
  exact Finset.card_union_of_disjoint (Finset.disjoint_filter_filter h)

theorem outN_mono {A B : Finset ℕ} (h : A ⊆ B) (x : ℕ) : outN D A x ⊆ outN D B x :=
  Finset.filter_subset_filter _ h

/-! ### `Ball q 1` -/

theorem ball_one_growth {q : ℕ} (hfree : QFree D W q) (hout : ∀ v ∈ W, 1 ≤ (outN D W v).card) {u : ℕ}
    (hu : u ∈ W) : ∀ k, k + 1 ≤ q → k + 1 ≤ (ball D W u k).card := by
  classical
  intro k
  induction k with
  | zero => intro _; exact Finset.card_pos.mpr ⟨u, self_mem_ball hu⟩
  | succ k ih =>
    intro hk
    have h1 := ih (by omega)
    by_contra hlt
    have hsub : ball D W u k ⊆ ball D W u (k + 1) := ball_mono_radius (by omega)
    have hc := Finset.card_le_card hsub
    have heq : ball D W u k = ball D W u (k + 1) := Finset.eq_of_subset_of_card_le hsub (by omega)
    obtain ⟨t, ht, hsink⟩ := exists_sink (D := D) (T := ball D W u k) (q := q)
      (hfree.mono_set ball_subset) ⟨u, self_mem_ball hu⟩ (by omega)
    have htW : t ∈ W := ball_subset ht
    obtain ⟨z, hz⟩ := Finset.card_pos.mp (hout t htW)
    obtain ⟨hzW, htz⟩ := mem_outN.mp hz
    exact hsink z (heq ▸ ball_step ht hzW htz) htz

/-- `Ball q 1` for every `q ≥ 1`. -/
theorem ball_q_one : ∀ q, 1 ≤ q → Ball q 1 := by
  intro q hq D W hfree hout u hu
  have := ball_one_growth hfree (fun v hv => (hout v hv).ge) hu (q - 1) (by omega)
  omega

theorem ball42 : Ball 4 2 := by
  intro D W hfree hout u hu
  exact ball_growth 4 (by omega) D W hfree (fun v hv => (hout v hv).ge) u hu 3 (by omega)

/-! ### The deletion test -/

theorem ball_of_min {q s : ℕ} (hb : Ball q s) {U : Finset ℕ} (hfree : QFree D U q)
    (hmin : ∀ y ∈ U, s ≤ (outN D U y).card) : ∀ z ∈ U, s * (q - 1) + 1 ≤ (ball D U z (q - 1)).card := by
  intro z hz
  obtain ⟨G', hsub, hout⟩ := exists_outEq (G := D) (V := U) (s := s) hmin
  exact (hb G' U (qfree_sub hsub hfree) hout z hz).trans (Finset.card_le_card (ball_sub hsub))

theorem mul_pred_add {q s : ℕ} (hq : 1 ≤ q) : s * (q - 1) + 1 + s = q * s + 1 := by
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
  rw [Nat.add_sub_cancel, Nat.succ_mul, Nat.mul_comm]; omega

/-- **DT, size.** -/
theorem dt_size {q s : ℕ} (hq : 1 ≤ q) (hb : Ball q s) {U : Finset ℕ} (hfree : QFree D U q)
    (hmin : ∀ y ∈ U, s ≤ (outN D U y).card) (hne : U.Nonempty) : q * s + 1 ≤ U.card := by
  have := card_ge_of_ball hq hfree hmin (ball_of_min hb hfree hmin) hne
  have e := mul_pred_add (s := s) hq
  omega

/-- **DT, regularity.** -/
theorem dt_reg {q s : ℕ} (hq : 1 ≤ q) (hb : Ball q s) {U : Finset ℕ} (hfree : QFree D U q)
    (hmin : ∀ y ∈ U, s ≤ (outN D U y).card) (hcard : U.card = q * s + 1) :
    (∀ y ∈ U, (outN D U y).card = s) ∧ (∀ y ∈ U, (inN D U y).card = s) := by
  classical
  have hball := ball_of_min hb hfree hmin
  have e := mul_pred_add (s := s) hq
  have hin : ∀ z ∈ U, (inN D U z).card ≤ s := by
    intro z hz
    have hsub : inN D U z ⊆ U \ ball D U z (q - 1) := by
      intro y hy
      obtain ⟨hyU, hyz⟩ := mem_inN.mp hy
      exact Finset.mem_sdiff.mpr ⟨hyU, fun hyb => no_back_arc hfree hz hyb (by omega) hyz⟩
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_sdiff_of_subset ball_subset] at h1
    have h2 := hball z hz
    omega
  have hsum : ∑ y ∈ U, (outN D U y).card = ∑ z ∈ U, (inN D U z).card :=
    Compose.ThinRigid.sum_out_eq_sum_in D U
  have h1 : ∑ _y ∈ U, s ≤ ∑ y ∈ U, (outN D U y).card := Finset.sum_le_sum hmin
  have h2 : ∑ z ∈ U, (inN D U z).card ≤ ∑ _y ∈ U, s := Finset.sum_le_sum hin
  constructor
  · have heq : ∑ _y ∈ U, s = ∑ y ∈ U, (outN D U y).card := le_antisymm h1 (hsum ▸ h2)
    intro y hy
    exact ((Finset.sum_eq_sum_iff_of_le hmin).mp heq y hy).symm
  · have heq : ∑ z ∈ U, (inN D U z).card = ∑ _y ∈ U, s := le_antisymm h2 (hsum ▸ h1)
    exact (Finset.sum_eq_sum_iff_of_le hin).mp heq

/-! ### Instances at `q = 4` -/

theorem ch1 {T : Finset ℕ} (hfree : QFree D T 4) (hmin : ∀ y ∈ T, 1 ≤ (outN D T y).card)
    (hne : T.Nonempty) : 5 ≤ T.card :=
  dt_size (by omega) (ball_q_one 4 (by omega)) hfree hmin hne

theorem ch2 {T : Finset ℕ} (hfree : QFree D T 4) (hmin : ∀ y ∈ T, 2 ≤ (outN D T y).card)
    (hne : T.Nonempty) : 9 ≤ T.card :=
  dt_size (by omega) ball42 hfree hmin hne

theorem ch3 {T : Finset ℕ} (hfree : QFree D T 4) (hmin : ∀ y ∈ T, 3 ≤ (outN D T y).card)
    (hne : T.Nonempty) : 13 ≤ T.card :=
  dt_size (by omega) (ball_all 4 (by omega)) hfree hmin hne

theorem ch4 {T : Finset ℕ} (hfree : QFree D T 4) (hmin : ∀ y ∈ T, 4 ≤ (outN D T y).card)
    (hne : T.Nonempty) : 17 ≤ T.card :=
  dt_size (by omega) LeanCH.BR.BRq4.ball44 hfree hmin hne

theorem reg1 {T : Finset ℕ} (hfree : QFree D T 4) (hmin : ∀ y ∈ T, 1 ≤ (outN D T y).card)
    (hcard : T.card = 5) : (∀ y ∈ T, (outN D T y).card = 1) ∧ (∀ y ∈ T, (inN D T y).card = 1) :=
  dt_reg (by omega) (ball_q_one 4 (by omega)) hfree hmin (by omega)

theorem reg2 {T : Finset ℕ} (hfree : QFree D T 4) (hmin : ∀ y ∈ T, 2 ≤ (outN D T y).card)
    (hcard : T.card = 9) : (∀ y ∈ T, (outN D T y).card = 2) ∧ (∀ y ∈ T, (inN D T y).card = 2) :=
  dt_reg (by omega) ball42 hfree hmin (by omega)

/-- `BR(q,1)` for every `q ≥ 1`. -/
theorem br_q_one : ∀ q, 1 ≤ q → BoundaryRegular q 1 :=
  fun q hq => br_of_ball hq (ball_q_one q hq)

end LeanCH.BR.BR45
