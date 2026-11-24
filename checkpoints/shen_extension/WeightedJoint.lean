import checkpoints.shen_extension.LoneRow
import checkpoints.shen_extension.WeightedHost

/-!
# Weights and new arcs in one test

`WeightedHost.weighted_bound` pays rows by multiplicities on a safe digraph.
`JointShortcut.install_iff` decides exactly when a family of new arcs is safe, and that test does
not see multiplicities. Together:

* `weighted_exit`: under `NoHost q t`, no safe digraph on any carrier carries weights of total at
  most `q t` that pay every row of positive weight.
* `weighted_cycle`: for every retained graph, every family of new arcs and every such weighting
  that pays in the installed graph, the arc labels have a closed trail of cost at most `q`.
  Weight zero deletes a label, weight two copies it. Unit weights on `V \ B` give
  `joint_cycle_list`; no new arcs gives the copy allocation rule.
* `clone_bypass`: one use that neither parent rule gives. On a lone row, delete `x`, copy any
  surviving `k`, and let the tight parents that miss `k` take heads of `x`. So the tight parent
  that misses `k` and the tight parent whose missed heads all return can be taken to be the same.
-/

namespace LeanCH.BR.WeightedJoint
open Finset BRq2 BRq3 FundedCascade BypassRepair BypassBankReplay BypassTwoStepRow JointShortcut
  JointShortcutReplay LoneRow

variable {q t : ℕ}

/-- **Weights on any safe digraph.** -/
theorem weighted_exit (none : NoHost q t) {G : CH.Digraph} {W : Finset ℕ} (μ : ℕ → ℕ)
    (safe : QFree G W q) (pos : ∃ v ∈ W, 0 < μ v) (mass : ∑ v ∈ W, μ v ≤ q*t)
    (paid : ∀ v ∈ W, 0 < μ v → t ≤ ∑ w ∈ outN G W v, μ w) : False := by
  have order : ∀ (F : CH.Digraph) (U : Finset ℕ), QFree F U q →
      (∀ v ∈ U, t ≤ (outN F U v).card) → U.Nonempty → q*t+1 ≤ U.card := by
    intro F U hF deg ne
    by_contra small
    exact none F U ne (by omega) hF deg
  have := WeightedHost.weighted_bound order μ safe pos paid
  omega

/-- **Weights and new arcs together.** Any carrier `W`, any retained `q`-free graph `K` on it, any
family `F` of new arcs with heads in `W`, any weights of total at most `q t` that pay every row of
positive weight in the installed graph: the labels of `F` have a closed trail of cost at most
`q`, made of old walks of `K`. -/
theorem weighted_cycle (none : NoHost q t) {K : CH.Digraph} {W : Finset ℕ} {F : Finset Arc}
    (μ : ℕ → ℕ) (old : QFree K W q) (inW : ∀ j ∈ F, j.2 ∈ W)
    (pos : ∃ v ∈ W, 0 < μ v) (mass : ∑ v ∈ W, μ v ≤ q*t)
    (paid : ∀ v ∈ W, 0 < μ v → t ≤ ∑ w ∈ outN (install K F) W v, μ w) :
    ∃ (n : ℕ) (lab : ℕ → Arc) (len : ℕ → ℕ), 0 < n ∧ lab n = lab 0 ∧ (∀ l ≤ n, lab l ∈ F) ∧
      (∀ l < n, Walk K W (lab l).2 (lab (l + 1)).1 (len l)) ∧
      ∑ l ∈ range n, (len l + 1) ≤ q := by
  have trail : ∃ i ∈ F, ∃ c, 0 < c ∧ c ≤ q ∧ Trail K W F i i c := by
    by_contra no
    push Not at no
    exact weighted_exit none μ ((install_iff inW).mpr ⟨old, no⟩) pos mass paid
  obtain ⟨i, iF, c, cpos, le, tr⟩ := trail
  obtain ⟨n, lab, len, l0, ln, steps, sum⟩ := tr.cyclic
  have npos : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · simp at sum
      omega
    · exact h
  refine ⟨n, lab, len, npos, ln.trans l0.symm, ?_, fun l hl => (steps l hl).2, by omega⟩
  intro l hl
  rcases Nat.eq_zero_or_pos l with rfl | h
  · rw [l0]; exact iF
  · obtain ⟨m, rfl⟩ : ∃ m, l = m + 1 := ⟨l - 1, by omega⟩
    exact (steps m (by omega)).1

/-- Weight two on one label, one elsewhere. -/
theorem clone_sum (S : Finset ℕ) (k : ℕ) :
    ∑ w ∈ S, (if w = k then 2 else 1) = S.card + (if k ∈ S then 1 else 0) := by
  have split : ∀ w, (if w = k then 2 else 1 : ℕ) = 1 + (if w = k then 1 else 0) := fun w => by
    split_ifs <;> rfl
  simp [split, sum_add_distrib]

/-- **Copy one label and bypass the rest.** On a lone row, for every surviving `k ≠ x` and every
cut affordable without `x`, one tight parent both misses `k` and has an exact `(q-1)`-return from
every head of `x` it misses. -/
theorem clone_bypass {D : CH.Digraph} {V U : Finset ℕ} {x : ℕ} (L : Lone D V U q t x)
    (hq : 1 ≤ q) {k : ℕ} (ku : k ∈ U) (kx : k ≠ x) (C : ℕ → Finset ℕ)
    (budget : ∀ c ∈ U.erase x, (C c).card ≤ spare D (U.erase x) t c) :
    ∃ y, TightParent D U t x y ∧ D y k ≠ true ∧
      ∀ a ∈ U, D x a = true → D y a ≠ true → Walk (cut D C) (U.erase x) a y (q-1) := by
  classical
  by_contra no
  push Not at no
  choose! f hf using no
  have xv := L.uv L.xu
  have noloop : D x x ≠ true := loopfree L.free hq xv
  have kW : k ∈ U.erase x := mem_erase.mpr ⟨kx, ku⟩
  let FT : Finset Arc :=
    (U.filter (fun y => TightParent D U t x y ∧ D y k ≠ true)).image (fun y => (y, f y))
  have memFT : ∀ j, j ∈ FT → TightParent D U t x j.1 ∧ D j.1 k ≠ true ∧ j.2 = f j.1 := by
    intro j hj
    obtain ⟨y, yT, rfl⟩ := mem_image.mp hj
    exact ⟨(mem_filter.mp yT).2.1, (mem_filter.mp yT).2.2, rfl⟩
  have headW : ∀ y, TightParent D U t x y → D y k ≠ true → f y ∈ U.erase x := by
    intro y ty yk
    refine mem_erase.mpr ⟨fun e => ?_, (hf y ty yk).1⟩
    have arc := (hf y ty yk).2.1
    rw [e] at arc
    exact noloop arc
  have safe : QFree (install (cut D C) FT) (U.erase x) q := by
    apply safe_of_parent_order (par := fun _ => x) (ρ := fun _ => 0) L.free hq
      ((erase_subset _ _).trans L.uv) cut_sub
    · intro j hj
      obtain ⟨ty, yk, e⟩ := memFT j hj
      rw [e]
      exact headW _ ty yk
    · exact fun _ _ => xv
    · intro j hj
      obtain ⟨ty, yk, e⟩ := memFT j hj
      rw [e]
      exact (hf _ ty yk).2.1
    · exact fun _ _ j' hj' _ => (memFT j' hj').1.2.2.1
    · intro j hj
      obtain ⟨ty, yk, e⟩ := memFT j hj
      rw [e]
      exact (hf _ ty yk).2.2.2
  refine weighted_exit L.none (fun w => if w = k then 2 else 1) safe ⟨k, kW, by simp⟩ ?_ ?_
  · rw [clone_sum]
    simp only [kW, ↓reduceIte]
    have := card_erase_add_one L.xu
    have := L.small
    omega
  · intro c cW _
    rw [clone_sum]
    obtain ⟨cx, cu⟩ := mem_erase.mp cW
    have ge := L.other c cu cx
    have b : (C c).card ≤ (outN D (U.erase x) c).card - t := budget c cW
    have keep : outN D (U.erase x) c \ C c ⊆ outN (install (cut D C) FT) (U.erase x) c := by
      intro w hw
      obtain ⟨oldw, off⟩ := mem_sdiff.mp hw
      obtain ⟨ww, arc⟩ := mem_outN.mp oldw
      exact mem_outN.mpr ⟨ww, install_old (by simp [cut, arc, off])⟩
    have k1 := card_le_card keep
    have k2 := le_card_sdiff (C c) (outN D (U.erase x) c)
    have ec : (outN D (U.erase x) c).card = ((outN D U c).erase x).card := by
      congr 1
      ext j
      simp only [mem_outN, mem_erase]
      tauto
    by_cases cxarc : D c x = true
    · have one := card_erase_add_one (show x ∈ outN D U c from mem_outN.mpr ⟨L.xu, cxarc⟩)
      by_cases tight : (outN D U c).card = t
      · have ty : TightParent D U t x c := ⟨cu, cx, cxarc, tight⟩
        by_cases ck : D c k = true
        · have none' : C c = ∅ := card_eq_zero.mp (by omega)
          have kin : k ∈ outN (install (cut D C) FT) (U.erase x) c :=
            mem_outN.mpr ⟨kW, install_old (by simp [cut, ck, none'])⟩
          simp only [kin, ↓reduceIte]
          omega
        · have new : f c ∈ outN (install (cut D C) FT) (U.erase x) c :=
            mem_outN.mpr ⟨headW c ty ck,
              install_new (mem_image.mpr ⟨c, mem_filter.mpr ⟨cu, ty, ck⟩, rfl⟩)⟩
          have notold : f c ∉ outN D (U.erase x) c \ C c := fun hit =>
            (hf c ty ck).2.2.1 (mem_outN.mp (mem_sdiff.mp hit).1).2
          have big := card_le_card (insert_subset new keep)
          rw [card_insert_of_notMem notold] at big
          exact le_trans (by omega) (Nat.le_add_right _ _)
      · exact le_trans (by omega) (Nat.le_add_right _ _)
    · rw [erase_eq_of_notMem (fun hit => cxarc (mem_outN.mp hit).2)] at ec
      exact le_trans (by omega) (Nat.le_add_right _ _)

/-- The same on the live lone cell. It contains `CopySeparation.every_column` (drop the returns)
and, with `k` a head of the marked row or any column, sharpens the bypass packet. -/
theorem marked_clone_bypass {q r} {X : ShenMinimumOrder.Source q r} {m : Cell} (hq : 2 ≤ q)
    (none : NoHost q (r-1)) (cell : Marked X m) (lone : LoneBlocked X m) {k : ℕ}
    (ku : k ∈ X.V \ m.bank) (kx : k ≠ m.x) (C : ℕ → Finset ℕ)
    (budget : ∀ c ∈ (X.V \ m.bank).erase m.x,
      (C c).card ≤ spare X.D ((X.V \ m.bank).erase m.x) (r-1) c) :
    ∃ y, TightParent X.D (X.V \ m.bank) (r-1) m.x y ∧ X.D y k ≠ true ∧
      ∀ a ∈ X.V \ m.bank, X.D m.x a = true → X.D y a ≠ true →
        Walk (cut X.D C) ((X.V \ m.bank).erase m.x) a y (q-1) :=
  clone_bypass (on_cell none cell lone) (by omega) ku kx C budget

#print axioms weighted_exit
#print axioms weighted_cycle
#print axioms clone_bypass
#print axioms marked_clone_bypass
end LeanCH.BR.WeightedJoint
