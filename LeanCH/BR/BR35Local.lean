import LeanCH.BR.StrictCap
import LeanCH.BR.SmallBR
import Mathlib.Tactic.IntervalCases
import Mathlib.Algebra.Group.Action.Defs

/-!
# BR(3,5), part 1: counting tools and the local setup at a vertex of in-degree 6 (Lean 4.35.0)

Paper source: `checkpoints/boundary_20261111/BR35_attempt_subagent.md` (sections 1-2).

* `oc G A w` / `ic G A w`: number of heads / parents of `w` inside the set `A`.
* Generic lemmas (any order `n`, no loop, no directed cycle of length `≤ 3`):
  - `oc_ic_le`: heads and parents of `w` inside `A` are disjoint (no digon);
  - `small_out`: a nonempty set of at most three vertices in which every vertex has a head is impossible;
  - `tourn_source`: a tournament without directed triangles has a source (the vertex of largest out-degree);
  - `four_regular`: on four vertices, minimum internal out-degree `1` forces internal out-degree exactly `1`
    (`BR(3,1)` through `LeanCH.BR.StrictCap.induced_regular`).
* `Hyp G`: a boundary graph at `s = 5` (16 labels, minimum out-degree 5, no cycle of length `≤ 3`) whose
  in-degrees are at most 6 (the strict cap).
* `Root G u I O M`: `u` has in-degree 6 and out-degree 5; `I = I(u)`, `O = O(u)`, `M` = the 4 remaining labels.
  The partition gives the degree splits `split_out` / `split_in`, the local facts (L1), (L2), (L4) of the paper,
  and the budget (2.2) summed from the cap at the vertices of `M`.
-/

namespace LeanCH.BR.BR35

open CH Compose.Boundary Compose.FloorSix

/-- Number of heads of `w` inside `A`. -/
def oc (G : CH.Digraph) (A : Finset Nat) (w : Nat) : Nat := (A.filter (fun v => G w v = true)).card

/-- Number of parents of `w` inside `A`. -/
def ic (G : CH.Digraph) (A : Finset Nat) (w : Nat) : Nat := (A.filter (fun v => G v w = true)).card

section generic

variable {G : CH.Digraph}

theorem oc_le (A : Finset Nat) (w : Nat) : oc G A w ≤ A.card := Finset.card_filter_le _ _

theorem ic_le (A : Finset Nat) (w : Nat) : ic G A w ≤ A.card := Finset.card_filter_le _ _

theorem oc_union {A B : Finset Nat} (h : Disjoint A B) (w : Nat) :
    oc G (A ∪ B) w = oc G A w + oc G B w := by
  unfold oc
  rw [Finset.filter_union, Finset.card_union_of_disjoint (Finset.disjoint_filter_filter h)]

theorem ic_union {A B : Finset Nat} (h : Disjoint A B) (w : Nat) :
    ic G (A ∪ B) w = ic G A w + ic G B w := by
  unfold ic
  rw [Finset.filter_union, Finset.card_union_of_disjoint (Finset.disjoint_filter_filter h)]

theorem oc_mono {A B : Finset Nat} (h : A ⊆ B) (w : Nat) : oc G A w ≤ oc G B w :=
  Finset.card_le_card (Finset.filter_subset_filter _ h)

theorem ic_mono {A B : Finset Nat} (h : A ⊆ B) (w : Nat) : ic G A w ≤ ic G B w :=
  Finset.card_le_card (Finset.filter_subset_filter _ h)

theorem oc_sdiff {A B : Finset Nat} (h : B ⊆ A) (w : Nat) : oc G A w = oc G B w + oc G (A \ B) w := by
  rw [← oc_union Finset.disjoint_sdiff, Finset.union_sdiff_of_subset h]

theorem ic_sdiff {A B : Finset Nat} (h : B ⊆ A) (w : Nat) : ic G A w = ic G B w + ic G (A \ B) w := by
  rw [← ic_union Finset.disjoint_sdiff, Finset.union_sdiff_of_subset h]

theorem oc_insert {A : Finset Nat} {a : Nat} (ha : a ∉ A) (w : Nat) :
    oc G (insert a A) w = (if G w a = true then 1 else 0) + oc G A w := by
  unfold oc
  rw [Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (fun h' => ha (Finset.mem_filter.mp h').1)]; omega
  · omega

theorem ic_insert {A : Finset Nat} {a : Nat} (ha : a ∉ A) (w : Nat) :
    ic G (insert a A) w = (if G a w = true then 1 else 0) + ic G A w := by
  unfold ic
  rw [Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (fun h' => ha (Finset.mem_filter.mp h').1)]; omega
  · omega

theorem oc_pos {A : Finset Nat} {w v : Nat} (hv : v ∈ A) (h : G w v = true) : 1 ≤ oc G A w :=
  Finset.card_pos.mpr ⟨v, Finset.mem_filter.mpr ⟨hv, h⟩⟩

theorem ic_pos {A : Finset Nat} {w v : Nat} (hv : v ∈ A) (h : G v w = true) : 1 ≤ ic G A w :=
  Finset.card_pos.mpr ⟨v, Finset.mem_filter.mpr ⟨hv, h⟩⟩

theorem exists_of_oc {A : Finset Nat} {w : Nat} (h : 1 ≤ oc G A w) : ∃ v ∈ A, G w v = true := by
  obtain ⟨v, hv⟩ := Finset.card_pos.mp h
  exact ⟨v, (Finset.mem_filter.mp hv).1, (Finset.mem_filter.mp hv).2⟩

theorem exists_of_ic {A : Finset Nat} {w : Nat} (h : 1 ≤ ic G A w) : ∃ v ∈ A, G v w = true := by
  obtain ⟨v, hv⟩ := Finset.card_pos.mp h
  exact ⟨v, (Finset.mem_filter.mp hv).1, (Finset.mem_filter.mp hv).2⟩

theorem all_of_oc {A : Finset Nat} {w : Nat} (h : A.card ≤ oc G A w) : ∀ v ∈ A, G w v = true := by
  have heq := Finset.eq_of_subset_of_card_le (Finset.filter_subset (fun v => G w v = true) A) h
  intro v hv
  rw [← heq] at hv
  exact (Finset.mem_filter.mp hv).2

theorem all_of_ic {A : Finset Nat} {w : Nat} (h : A.card ≤ ic G A w) : ∀ v ∈ A, G v w = true := by
  have heq := Finset.eq_of_subset_of_card_le (Finset.filter_subset (fun v => G v w = true) A) h
  intro v hv
  rw [← heq] at hv
  exact (Finset.mem_filter.mp hv).2

theorem oc_eq_zero {A : Finset Nat} {w : Nat} (h : ∀ v ∈ A, G w v = false) : oc G A w = 0 := by
  unfold oc
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro v hv hG
  rw [h v hv] at hG
  exact Bool.false_ne_true hG

theorem ic_eq_zero {A : Finset Nat} {w : Nat} (h : ∀ v ∈ A, G v w = false) : ic G A w = 0 := by
  unfold ic
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro v hv hG
  rw [h v hv] at hG
  exact Bool.false_ne_true hG

/-- Removing a vertex that `w` does not head does not change the head count of `w`. -/
theorem oc_erase_eq {A : Finset Nat} {a w : Nat} (h : G w a = false) : oc G (A.erase a) w = oc G A w := by
  unfold oc
  congr 1
  ext v
  simp only [Finset.mem_filter, Finset.mem_erase]
  constructor
  · rintro ⟨⟨_, hv⟩, hG⟩
    exact ⟨hv, hG⟩
  · rintro ⟨hv, hG⟩
    refine ⟨⟨?_, hv⟩, hG⟩
    rintro rfl
    rw [h] at hG
    exact Bool.false_ne_true hG

/-- Removing a vertex that does not head `w` does not change the parent count of `w`. -/
theorem ic_erase_eq {A : Finset Nat} {a w : Nat} (h : G a w = false) : ic G (A.erase a) w = ic G A w := by
  unfold ic
  congr 1
  ext v
  simp only [Finset.mem_filter, Finset.mem_erase]
  constructor
  · rintro ⟨⟨_, hv⟩, hG⟩
    exact ⟨hv, hG⟩
  · rintro ⟨hv, hG⟩
    refine ⟨⟨?_, hv⟩, hG⟩
    rintro rfl
    rw [h] at hG
    exact Bool.false_ne_true hG

/-- Heads of `w` in `A` all lie in `B`. -/
theorem oc_le_of_sub {A B : Finset Nat} {w : Nat} (h : ∀ v ∈ A, G w v = true → v ∈ B) :
    oc G A w ≤ B.card := by
  apply Finset.card_le_card
  intro v hv
  exact h v (Finset.mem_filter.mp hv).1 (Finset.mem_filter.mp hv).2

theorem oc_full {A : Finset Nat} {w : Nat} (h : ∀ v ∈ A, G w v = true) : oc G A w = A.card := by
  unfold oc
  rw [Finset.filter_true_of_mem h]

theorem ic_full {A : Finset Nat} {w : Nat} (h : ∀ v ∈ A, G v w = true) : ic G A w = A.card := by
  unfold ic
  rw [Finset.filter_true_of_mem h]

/-- Arc double counting between two sets. -/
theorem swap (G : CH.Digraph) (A B : Finset Nat) : ∑ a ∈ A, oc G B a = ∑ b ∈ B, ic G A b :=
  LeanCH.BR.LargeModule.swap_count G A B

/-- One strict point in a pointwise inequality of sums. -/
theorem sum_add_one_le {s : Finset Nat} {f g : Nat → Nat} (h : ∀ x ∈ s, f x ≤ g x) {a : Nat} (ha : a ∈ s)
    (hlt : f a + 1 ≤ g a) : ∑ x ∈ s, f x + 1 ≤ ∑ x ∈ s, g x :=
  Finset.sum_lt_sum h ⟨a, ha, hlt⟩

/-- Two strict points in a pointwise inequality of sums. -/
theorem sum_add_two_le {s : Finset Nat} {f g : Nat → Nat} (h : ∀ x ∈ s, f x ≤ g x) {a b : Nat}
    (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b) (hfa : f a + 1 ≤ g a) (hfb : f b + 1 ≤ g b) :
    ∑ x ∈ s, f x + 2 ≤ ∑ x ∈ s, g x := by
  rw [← Finset.add_sum_erase s f ha, ← Finset.add_sum_erase s g ha]
  have := sum_add_one_le (s := s.erase a) (fun x hx => h x (Finset.mem_of_mem_erase hx))
    (Finset.mem_erase.mpr ⟨Ne.symm hab, hb⟩) hfb
  omega

theorem card_mul_le_sum {s : Finset Nat} {f : Nat → Nat} {c : Nat} (h : ∀ x ∈ s, c ≤ f x) :
    s.card * c ≤ ∑ x ∈ s, f x := by
  have := Finset.card_nsmul_le_sum s f c h
  rwa [smul_eq_mul] at this

theorem sum_le_card_mul {s : Finset Nat} {f : Nat → Nat} {c : Nat} (h : ∀ x ∈ s, f x ≤ c) :
    ∑ x ∈ s, f x ≤ s.card * c := by
  have := Finset.sum_le_card_nsmul s f c h
  rwa [smul_eq_mul] at this

variable {n : Nat}

/-- No digon: the heads and the parents of `w` inside `A` are disjoint; if both lie in `B`, they number at most
`|B|`. -/
theorem oc_ic_le (loopless : CH.Loopless G n) (noShort : ¬ CH.HasDirectedCycleAtMost G n 3)
    {A B : Finset Nat} (hA : A ⊆ Finset.range n) {w : Nat} (hw : w < n)
    (hsub : ∀ v ∈ A, (G w v = true ∨ G v w = true) → v ∈ B) :
    oc G A w + ic G A w ≤ B.card := by
  unfold oc ic
  rw [← Finset.card_union_of_disjoint]
  · apply Finset.card_le_card
    intro v hv
    rcases Finset.mem_union.mp hv with h | h
    · exact hsub v (Finset.mem_filter.mp h).1 (Or.inl (Finset.mem_filter.mp h).2)
    · exact hsub v (Finset.mem_filter.mp h).1 (Or.inr (Finset.mem_filter.mp h).2)
  · rw [Finset.disjoint_left]
    intro v h1 h2
    exact no2 loopless noShort hw (Finset.mem_range.mp (hA (Finset.mem_filter.mp h1).1))
      (Finset.mem_filter.mp h1).2 (Finset.mem_filter.mp h2).2

/-- Inside a set containing `w`: heads and parents of `w` number at most `|A| - 1`. -/
theorem oc_ic_le_mem (loopless : CH.Loopless G n) (noShort : ¬ CH.HasDirectedCycleAtMost G n 3)
    {A : Finset Nat} (hA : A ⊆ Finset.range n) {w : Nat} (hwA : w ∈ A) :
    oc G A w + ic G A w + 1 ≤ A.card := by
  have hw : w < n := Finset.mem_range.mp (hA hwA)
  have := oc_ic_le loopless noShort hA hw (B := A.erase w) (fun v hv hG => by
    refine Finset.mem_erase.mpr ⟨?_, hv⟩
    rintro rfl
    rcases hG with h | h <;> (rw [loopless v hw] at h; exact Bool.false_ne_true h))
  rw [Finset.card_erase_of_mem hwA] at this
  have := Finset.card_pos.mpr ⟨w, hwA⟩
  omega

/-- **Small sets.** A nonempty set of at most three vertices in which every vertex has a head inside the set
contains a loop, digon or triangle. -/
theorem small_out (loopless : CH.Loopless G n) (noShort : ¬ CH.HasDirectedCycleAtMost G n 3)
    {A : Finset Nat} (hA : A ⊆ Finset.range n) (hcard : A.card ≤ 3) (hne : A.Nonempty)
    (h : ∀ a ∈ A, ∃ b ∈ A, G a b = true) : False := by
  obtain ⟨a, ha⟩ := hne
  obtain ⟨b, hb, hab⟩ := h a ha
  obtain ⟨c, hc, hbc⟩ := h b hb
  obtain ⟨d, hd, hcd⟩ := h c hc
  have lt : ∀ x ∈ A, x < n := fun x hx => Finset.mem_range.mp (hA hx)
  have nab : a ≠ b := by rintro rfl; rw [loopless a (lt a ha)] at hab; exact Bool.false_ne_true hab
  have nbc : b ≠ c := by rintro rfl; rw [loopless b (lt b hb)] at hbc; exact Bool.false_ne_true hbc
  have ncd : c ≠ d := by rintro rfl; rw [loopless c (lt c hc)] at hcd; exact Bool.false_ne_true hcd
  have nac : a ≠ c := by rintro rfl; exact no2 loopless noShort (lt a ha) (lt b hb) hab hbc
  have nbd : b ≠ d := by rintro rfl; exact no2 loopless noShort (lt b hb) (lt c hc) hbc hcd
  have nad : a ≠ d := by
    rintro rfl; exact no3 loopless noShort (lt a ha) (lt b hb) (lt c hc) hab hbc hcd
  have hsub : ({a, b, c, d} : Finset Nat) ⊆ A := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> assumption
  have h4 : ({a, b, c, d} : Finset Nat).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [nab, nac, nad]),
      Finset.card_insert_of_notMem (by simp [nbc, nbd]), Finset.card_pair ncd]
  have := Finset.card_le_card hsub
  omega

/-- **Source of a tournament.** A tournament without directed triangles has a vertex with no parent: a vertex of
largest out-degree. -/
theorem tourn_source (loopless : CH.Loopless G n) (noShort : ¬ CH.HasDirectedCycleAtMost G n 3)
    {J : Finset Nat} (hJ : J ⊆ Finset.range n) (hne : J.Nonempty)
    (tour : ∀ a ∈ J, ∀ b ∈ J, a ≠ b → G a b = true ∨ G b a = true) :
    ∃ t ∈ J, ∀ v ∈ J, G v t = false := by
  obtain ⟨t, ht, hmax⟩ := J.exists_max_image (oc G J) hne
  refine ⟨t, ht, fun v hv => ?_⟩
  have lt : ∀ x ∈ J, x < n := fun x hx => Finset.mem_range.mp (hJ hx)
  by_contra hvt
  rw [Bool.not_eq_false] at hvt
  have hsub : insert t (J.filter (fun y => G t y = true)) ⊆ J.filter (fun y => G v y = true) := by
    intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact Finset.mem_filter.mpr ⟨ht, hvt⟩
    · obtain ⟨hyJ, hty⟩ := Finset.mem_filter.mp hy
      refine Finset.mem_filter.mpr ⟨hyJ, ?_⟩
      have hyv : y ≠ v := by rintro rfl; exact no2 loopless noShort (lt t ht) (lt y hyJ) hty hvt
      rcases tour v hv y hyJ (Ne.symm hyv) with h | h
      · exact h
      · exact (no3 loopless noShort (lt v hv) (lt t ht) (lt y hyJ) hvt hty h).elim
  have htn : t ∉ J.filter (fun y => G t y = true) := by
    intro h
    have := (Finset.mem_filter.mp h).2
    rw [loopless t (lt t ht)] at this
    exact Bool.false_ne_true this
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem htn] at h1
  have h2 := hmax v hv
  unfold oc at h2
  omega

/-- **Four vertices (`BR(3,1)`).** If every member of a 4-set keeps a head inside it, every member has exactly one
head inside it. -/
theorem four_regular (loopless : CH.Loopless G n) (noShort : ¬ CH.HasDirectedCycleAtMost G n 3)
    {T : Finset Nat} (hT : T ⊆ Finset.range n) (hcard : T.card = 4)
    (keep : ∀ x ∈ T, 1 ≤ oc G T x) : ∀ x ∈ T, oc G T x = 1 :=
  LeanCH.BR.StrictCap.induced_regular (q := 3) (c := 1) LeanCH.BR.SmallBR.br_one hT hcard loopless noShort
    keep

end generic

/-- The 16 labels. -/
abbrev V : Finset Nat := Finset.range 16

/-- A boundary graph at `s = 5` whose in-degrees are at most 6 (the strict cap). -/
structure Hyp (G : CH.Digraph) : Prop where
  loopless : CH.Loopless G 16
  deg : CH.MinOutdegreeAtLeast G 16 5
  noShort : ¬ CH.HasDirectedCycleAtMost G 16 3
  cap : ∀ v, v < 16 → ic G V v ≤ 6

namespace Hyp

variable {G : CH.Digraph} (H : Hyp G)
include H

theorem n2 {a b : Nat} (ha : a < 16) (hb : b < 16) (h1 : G a b = true) (h2 : G b a = true) : False :=
  no2 H.loopless H.noShort ha hb h1 h2

theorem n3 {a b c : Nat} (ha : a < 16) (hb : b < 16) (hc : c < 16)
    (h1 : G a b = true) (h2 : G b c = true) (h3 : G c a = true) : False :=
  no3 H.loopless H.noShort ha hb hc h1 h2 h3

theorem out {w : Nat} (hw : w < 16) : 5 ≤ oc G V w := out_card H.deg hw

theorem ne_of_arc {a b : Nat} (ha : a < 16) (h : G a b = true) : a ≠ b := by
  rintro rfl; rw [H.loopless a ha] at h; exact Bool.false_ne_true h

/-- `G c a = false` from `a → b → c` (no triangle). -/
theorem tri {a b c : Nat} (ha : a < 16) (hb : b < 16) (hc : c < 16) (h1 : G a b = true)
    (h2 : G b c = true) : G c a = false := by
  cases h' : G c a
  · rfl
  · exact (H.n3 ha hb hc h1 h2 h').elim

/-- `G b a = false` from `G a b = true` (no digon). -/
theorem back {a b : Nat} (ha : a < 16) (hb : b < 16) (h : G a b = true) : G b a = false := by
  cases h' : G b a
  · rfl
  · exact (H.n2 ha hb h h').elim

end Hyp

/-- The local picture at a vertex `u` of in-degree 6 and out-degree 5: `I = I(u)`, `O = O(u)`, and `M` the other
four labels. -/
structure Root (G : CH.Digraph) (u : Nat) (I O M : Finset Nat) : Prop where
  H : Hyp G
  hu : u < 16
  mI : ∀ v, v ∈ I ↔ v < 16 ∧ G v u = true
  mO : ∀ v, v ∈ O ↔ v < 16 ∧ G u v = true
  mM : ∀ v, v ∈ M ↔ v < 16 ∧ v ≠ u ∧ G v u = false ∧ G u v = false
  cI : I.card = 6
  cO : O.card = 5

/-- The root structure at `u`, from in-degree 6 and out-degree 5. -/
theorem root_of {G : CH.Digraph} (H : Hyp G) {u : Nat} (hu : u < 16) (hin : ic G V u = 6)
    (hout : oc G V u = 5) :
    Root G u (V.filter (fun v => G v u = true)) (V.filter (fun v => G u v = true))
      (V.filter (fun v => v ≠ u ∧ G v u = false ∧ G u v = false)) where
  H := H
  hu := hu
  mI := fun v => by simp [V]
  mO := fun v => by simp [V]
  mM := fun v => by simp [V]
  cI := hin
  cO := hout

namespace Root

variable {G : CH.Digraph} {u : Nat} {I O M : Finset Nat} (R : Root G u I O M)
include R

theorem ltI {w : Nat} (h : w ∈ I) : w < 16 := ((R.mI w).mp h).1
theorem ltO {w : Nat} (h : w ∈ O) : w < 16 := ((R.mO w).mp h).1
theorem ltM {w : Nat} (h : w ∈ M) : w < 16 := ((R.mM w).mp h).1
theorem subI : I ⊆ Finset.range 16 := fun _ h => Finset.mem_range.mpr (R.ltI h)
theorem subO : O ⊆ Finset.range 16 := fun _ h => Finset.mem_range.mpr (R.ltO h)
theorem subM : M ⊆ Finset.range 16 := fun _ h => Finset.mem_range.mpr (R.ltM h)
theorem arcI {w : Nat} (h : w ∈ I) : G w u = true := ((R.mI w).mp h).2
theorem arcO {w : Nat} (h : w ∈ O) : G u w = true := ((R.mO w).mp h).2
theorem Mnu {m : Nat} (h : m ∈ M) : G m u = false := ((R.mM m).mp h).2.2.1
theorem Mun {m : Nat} (h : m ∈ M) : G u m = false := ((R.mM m).mp h).2.2.2

theorem uI : u ∉ I := fun h => by
  have := R.arcI h; rw [R.H.loopless u R.hu] at this; exact Bool.false_ne_true this

theorem uO : u ∉ O := fun h => by
  have := R.arcO h; rw [R.H.loopless u R.hu] at this; exact Bool.false_ne_true this

theorem uM : u ∉ M := fun h => ((R.mM u).mp h).2.1 rfl

theorem dIO : Disjoint I O := by
  rw [Finset.disjoint_left]
  intro v h1 h2
  exact R.H.n2 (R.ltI h1) R.hu (R.arcI h1) (R.arcO h2)

theorem dIM : Disjoint I M := by
  rw [Finset.disjoint_left]
  intro v h1 h2
  have := R.arcI h1; rw [R.Mnu h2] at this; exact Bool.false_ne_true this

theorem dOM : Disjoint O M := by
  rw [Finset.disjoint_left]
  intro v h1 h2
  have := R.arcO h1; rw [R.Mun h2] at this; exact Bool.false_ne_true this

/-- The partition `V = {u} ⊔ I ⊔ O ⊔ M`. -/
theorem part (p : Nat → Prop) [DecidablePred p] :
    (V.filter p).card =
      (if p u then 1 else 0) + (I.filter p).card + (O.filter p).card + (M.filter p).card := by
  have hV : V = insert u (I ∪ O ∪ M) := by
    ext v
    simp only [V, Finset.mem_range, Finset.mem_insert, Finset.mem_union]
    constructor
    · intro hv
      by_cases h1 : v = u
      · exact Or.inl h1
      right
      cases h2 : G v u
      · cases h3 : G u v
        · exact Or.inr ((R.mM v).mpr ⟨hv, h1, h2, h3⟩)
        · exact Or.inl (Or.inr ((R.mO v).mpr ⟨hv, h3⟩))
      · exact Or.inl (Or.inl ((R.mI v).mpr ⟨hv, h2⟩))
    · rintro (rfl | (h | h) | h)
      · exact R.hu
      · exact R.ltI h
      · exact R.ltO h
      · exact R.ltM h
  have hun : u ∉ I ∪ O ∪ M := by
    simp only [Finset.mem_union, not_or]
    exact ⟨⟨R.uI, R.uO⟩, R.uM⟩
  have d1 : Disjoint (I.filter p) (O.filter p) := Finset.disjoint_filter_filter R.dIO
  have d2 : Disjoint (I.filter p ∪ O.filter p) (M.filter p) := by
    rw [Finset.disjoint_union_left]
    exact ⟨Finset.disjoint_filter_filter R.dIM, Finset.disjoint_filter_filter R.dOM⟩
  have hun' : u ∉ I.filter p ∪ O.filter p ∪ M.filter p := by
    intro h
    apply hun
    rcases Finset.mem_union.mp h with h | h
    · rcases Finset.mem_union.mp h with h | h
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_of_mem_filter u h))
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_of_mem_filter u h))
    · exact Finset.mem_union_right _ (Finset.mem_of_mem_filter u h)
  rw [hV, Finset.filter_insert, Finset.filter_union, Finset.filter_union]
  split_ifs with hp
  · rw [Finset.card_insert_of_notMem hun',
      Finset.card_union_of_disjoint d2, Finset.card_union_of_disjoint d1]
    omega
  · rw [Finset.card_union_of_disjoint d2, Finset.card_union_of_disjoint d1]
    omega

theorem cM : M.card = 4 := by
  have h := R.part (fun _ => True)
  simp only [Finset.filter_true_of_mem (fun _ _ => trivial), ite_true, Finset.card_range] at h
  rw [R.cI, R.cO] at h
  omega

theorem split_out (w : Nat) :
    oc G V w = (if G w u = true then 1 else 0) + oc G I w + oc G O w + oc G M w :=
  R.part (fun v => G w v = true)

theorem split_in (w : Nat) :
    ic G V w = (if G u w = true then 1 else 0) + ic G I w + ic G O w + ic G M w :=
  R.part (fun v => G v w = true)

/-- (L1) An out-neighbour of `u` heads no in-neighbour of `u`. -/
theorem O_noI {x w : Nat} (hx : x ∈ O) (hw : w ∈ I) : G x w = false := by
  cases h : G x w
  · rfl
  · exact (R.H.n3 R.hu (R.ltO hx) (R.ltI hw) (R.arcO hx) h (R.arcI hw)).elim

theorem O_nou {x : Nat} (hx : x ∈ O) : G x u = false := R.H.back R.hu (R.ltO hx) (R.arcO hx)

/-- (L1) Rows of `O` live in `O ∪ M`. -/
theorem O_out {x : Nat} (hx : x ∈ O) : 5 ≤ oc G O x + oc G M x := by
  have h1 := R.H.out (R.ltO hx)
  rw [R.split_out x, R.O_nou hx, oc_eq_zero (fun w hw => R.O_noI hx hw)] at h1
  simpa using h1

theorem O_inner {x : Nat} (hx : x ∈ O) : 1 ≤ oc G O x := by
  have h1 := R.O_out hx
  have h2 := oc_le (G := G) M x
  rw [R.cM] at h2
  omega

/-- Rows of `I`: `u` plus heads in `I`, `O`, `M`. -/
theorem I_out {w : Nat} (hw : w ∈ I) : 4 ≤ oc G I w + (oc G O w + oc G M w) := by
  have h1 := R.H.out (R.ltI hw)
  rw [R.split_out w, R.arcI hw] at h1
  split_ifs at h1 <;> omega

/-- (L4) Rows of `M` do not head `u`. -/
theorem M_out {m : Nat} (hm : m ∈ M) : 5 ≤ oc G I m + oc G O m + oc G M m := by
  have h1 := R.H.out (R.ltM hm)
  rw [R.split_out m, R.Mnu hm] at h1
  simpa using h1

/-- (L5) The cap at a vertex of `M`. -/
theorem M_in {m : Nat} (hm : m ∈ M) : ic G I m + ic G O m + ic G M m ≤ 6 := by
  have h1 := R.H.cap m (R.ltM hm)
  rw [R.split_in m, R.Mun hm] at h1
  simpa using h1

/-- (2.2) The budget, summed over `M`: `(I→M) + (O→M) + e(D[M]) ≤ 24`. -/
theorem budget : ∑ m ∈ M, ic G I m + ∑ m ∈ M, ic G O m + ∑ m ∈ M, ic G M m ≤ 24 := by
  have h := Finset.sum_le_sum (fun m hm => R.M_in (m := m) hm)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, R.cM, smul_eq_mul] at h
  exact h

end Root

end LeanCH.BR.BR35
