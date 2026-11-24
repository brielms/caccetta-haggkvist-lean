import LeanCH.BR.BRSubstitutionWalk
import LeanCH.BR.BRAlternatingSubstitution
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.IntervalCases

/-! A seven-block obstruction to the proposed order-compensated ball bound.
The whole host has 151 vertices, minimum out-degree 46, and no cycle <=3.
Saturation preserves 71 incoming edges at a root, so its two-ball has <=80.
This is above boundary order 139 and does not contradict CH. -/
namespace LeanCH.BR.CompensatedCounter
open BRq2 BRq3 BR45 BRsub

def degree : ℕ → ℕ
  | 0 => 11 | 2 => 15 | 4 => 10 | 6 => 12 | _ => 0

def heads : ℕ → Finset ℕ
  | 0 => {1, 2, 3} | 1 => {2, 3} | 2 => {4} | 3 => {2, 4, 5}
  | 4 => {6} | 5 => {2, 4, 6} | 6 => {0, 1} | _ => ∅

def quotient : CH.Digraph := fun a b => decide (b ∈ heads a)
def size (i : ℕ) := 3 * degree i + 1
def block (i : ℕ) : Finset ℕ := (Finset.range (size i)).image (fun j => i * 46 + j)
def vertices : Finset ℕ := (Finset.range 7).biUnion block
noncomputable def graph : CH.Digraph := by
  classical
  exact fun a b => decide
    (a ∈ vertices ∧ b ∈ vertices ∧
      (b / 46 ∈ heads (a / 46) ∨
        (a / 46 = b / 46 ∧ ∃ k ∈ Finset.Icc 1 (degree (a / 46)),
          (a % 46 + k) % size (a / 46) = b % 46)))

theorem size_bound (i : ℕ) : 0 < size i ∧ size i ≤ 46 := by
  unfold size degree
  split <;> norm_num

theorem heads_bounds {i j : ℕ} (hj : j ∈ heads i) : i < 7 ∧ j < 7 ∧ i ≠ j := by
  unfold heads at hj
  split at hj <;> simp_all <;> omega

theorem heads_relation {a b : ℕ} (h : b ∈ heads a) :
    (a = 0 ∧ (b = 1 ∨ b = 2 ∨ b = 3)) ∨
    (a = 1 ∧ (b = 2 ∨ b = 3)) ∨ (a = 2 ∧ b = 4) ∨
    (a = 3 ∧ (b = 2 ∨ b = 4 ∨ b = 5)) ∨ (a = 4 ∧ b = 6) ∨
    (a = 5 ∧ (b = 2 ∨ b = 4 ∨ b = 6)) ∨ (a = 6 ∧ (b = 0 ∨ b = 1)) := by
  unfold heads at h
  split at h <;> simp_all <;> omega

theorem quotient_free : QFree quotient (Finset.range 7) 3 := by
  have h1 : ∀ a, ¬ quotient a a = true := by
    intro a ha
    exact (heads_bounds (of_decide_eq_true ha)).2.2 rfl
  have h2 : ∀ a b, quotient a b = true → quotient b a = true → False := by
    intro a b hab hba
    have h := heads_relation (of_decide_eq_true hab)
    have h' := heads_relation (of_decide_eq_true hba)
    omega
  have h3 : ∀ a b c, quotient a b = true → quotient b c = true → quotient c a = true → False := by
    intro a b c hab hbc hca
    have h := heads_relation (of_decide_eq_true hab)
    have h' := heads_relation (of_decide_eq_true hbc)
    have h'' := heads_relation (of_decide_eq_true hca)
    omega
  intro a l hl hlq w
  rcases (by omega : l = 1 ∨ l = 2 ∨ l = 3) with rfl | rfl | rfl
  · cases w with
    | step hb hab w => cases w; exact h1 _ hab
  · cases w with
    | step hb hab w => cases w with
      | step hc hbc w => cases w; exact h2 _ _ hab hbc
  · cases w with
    | step hb hab w => cases w with
      | step hc hbc w => cases w with
        | step hd hcd w => cases w; exact h3 _ _ _ hab hbc hcd

theorem block_mem {i a : ℕ} (ha : a ∈ block i) :
    a / 46 = i ∧ a % 46 < size i := by
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ha
  have hj' := Finset.mem_range.mp hj
  obtain ⟨hd, hm⟩ := AlternatingSubstitution.cell_div_mod (i := i) (by decide : 0 < 46)
    (by have := size_bound i; omega : j < 46)
  exact ⟨hd, by simpa only [hm] using hj'⟩

theorem vertex_bounds {a : ℕ} (ha : a ∈ vertices) :
    a / 46 < 7 ∧ a % 46 < size (a / 46) := by
  obtain ⟨i, hi, ha⟩ := Finset.mem_biUnion.mp ha
  obtain ⟨hd, hm⟩ := block_mem ha
  rw [hd]
  exact ⟨Finset.mem_range.mp hi, hm⟩

theorem block_subset {i : ℕ} (hi : i < 7) : block i ⊆ vertices :=
  Finset.subset_biUnion_of_mem block (Finset.mem_range.mpr hi)

theorem block_card (i : ℕ) : (block i).card = size i := by
  rw [block, Finset.card_image_of_injective, Finset.card_range]
  intro a b hab
  dsimp at hab
  omega

theorem blocks_disjoint {i j : ℕ} (hij : i ≠ j) : Disjoint (block i) (block j) := by
  apply Finset.disjoint_left.mpr
  intro a hai haj
  exact hij ((block_mem hai).1.symm.trans (block_mem haj).1)

theorem union_card (T : Finset ℕ) : (T.biUnion block).card = ∑ i ∈ T, size i := by
  rw [Finset.card_biUnion]
  · simp_rw [block_card]
  · intro i hi j hj hij
    exact blocks_disjoint hij

theorem order_card : vertices.card = 151 := by
  rw [vertices, union_card]
  norm_num [Finset.sum_range_succ, size, degree]

theorem free : QFree graph vertices 3 := by
  apply qfree_of_quotient_blocks (E := quotient) (U := Finset.range 7) (fun a => a / 46)
  · intro a ha
    exact Finset.mem_range.mpr (vertex_bounds ha).1
  · intro a b hb hab
    simp only [graph, decide_eq_true_eq] at hab
    obtain ⟨_, _, he⟩ := hab
    rcases he with he | he
    · exact Or.inr (decide_eq_true he)
    · exact Or.inl he.1
  · exact quotient_free
  · intro i
    apply qfree_of_bounded_modular_steps (N := size i) (d := degree i)
      (by simp [size]) (fun a => a % 46)
    intro a ha b hb hab
    have hai : a / 46 = i := (Finset.mem_filter.mp ha).2
    obtain ⟨_, hbi⟩ := Finset.mem_filter.mp hb
    simp only [graph, decide_eq_true_eq] at hab
    obtain ⟨_, _, he⟩ := hab
    rcases he with he | ⟨hei, k, hk, he⟩
    · exact ((heads_bounds he).2.2 (hai.trans hbi.symm)).elim
    · have hai : a / 46 = i := hei.trans hbi
      rw [hai] at hk he
      obtain ⟨hk1, hkd⟩ := Finset.mem_Icc.mp hk
      refine ⟨k, hk1, hkd, ?_⟩
      change (a % 46 + k) % size i = (b % 46) % size i
      have hbsize : b % 46 < size i := by
        simpa only [hbi] using (vertex_bounds (Finset.mem_filter.mp hb).1).2
      exact he.trans (Nat.mod_eq_of_lt hbsize).symm

theorem cell_mem {i j : ℕ} (hi : i < 7) (hj : j < size i) : i * 46 + j ∈ vertices := by
  apply block_subset hi
  exact Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hj, rfl⟩

def internal (a : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (degree (a / 46))).image
    (fun k => a / 46 * 46 + (a % 46 + k) % size (a / 46))

theorem internal_block (a : ℕ) : internal a ⊆ block (a / 46) := by
  intro b hb
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hb
  exact Finset.mem_image.mpr ⟨_, Finset.mem_range.mpr (Nat.mod_lt _ (size_bound _).1), rfl⟩

theorem internal_card (a : ℕ) : (internal a).card = degree (a / 46) := by
  rw [internal, Finset.card_image_iff.mpr]
  · simp
  · intro k hk l hl he
    obtain ⟨hk1, hkd⟩ := Finset.mem_Icc.mp hk
    obtain ⟨hl1, hld⟩ := Finset.mem_Icc.mp hl
    have hm : Nat.ModEq (size (a / 46)) (a % 46 + k) (a % 46 + l) := by
      change (a % 46 + k) % size (a / 46) = (a % 46 + l) % size (a / 46)
      dsimp only at he
      omega
    have hc := hm.add_left_cancel' (a % 46)
    have hklt : k < size (a / 46) := by unfold size; omega
    have hllt : l < size (a / 46) := by unfold size; omega
    simpa only [Nat.ModEq, Nat.mod_eq_of_lt hklt, Nat.mod_eq_of_lt hllt] using hc

theorem internal_out {a : ℕ} (ha : a ∈ vertices) : internal a ⊆ outN graph vertices a := by
  intro b hb
  have hbb := internal_block a hb
  have hbV := block_subset (vertex_bounds ha).1 hbb
  obtain ⟨hd, hbsize⟩ := block_mem hbb
  refine mem_outN.mpr ⟨hbV, ?_⟩
  simp only [graph, decide_eq_true_eq]
  refine ⟨ha, hbV, Or.inr ⟨hd.symm, ?_⟩⟩
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hb
  refine ⟨k, hk, ?_⟩
  exact (AlternatingSubstitution.cell_div_mod (by decide : 0 < 46)
    (lt_of_lt_of_le (Nat.mod_lt _ (size_bound _).1) (size_bound _).2)).2.symm

theorem external_out {a : ℕ} (ha : a ∈ vertices) :
    (heads (a / 46)).biUnion block ⊆ outN graph vertices a := by
  intro b hb
  obtain ⟨j, hj, hb⟩ := Finset.mem_biUnion.mp hb
  have hbV := block_subset (heads_bounds hj).2.1 hb
  refine mem_outN.mpr ⟨hbV, ?_⟩
  simp only [graph, decide_eq_true_eq]
  exact ⟨ha, hbV, Or.inl (by simpa only [(block_mem hb).1] using hj)⟩

theorem degree_lower {a : ℕ} (ha : a ∈ vertices) :
    degree (a / 46) + ∑ j ∈ heads (a / 46), size j ≤ (outN graph vertices a).card := by
  have hd : Disjoint (internal a) ((heads (a / 46)).biUnion block) := by
    apply Finset.disjoint_left.mpr
    intro b hb hb'
    have hbi := (block_mem (internal_block a hb)).1
    obtain ⟨j, hj, hbj⟩ := Finset.mem_biUnion.mp hb'
    exact (heads_bounds hj).2.2 (hbi.symm.trans (block_mem hbj).1)
  have hc := Finset.card_le_card (Finset.union_subset (internal_out ha) (external_out ha))
  rw [Finset.card_union_of_disjoint hd, internal_card, union_card] at hc
  exact hc

theorem minimum_degree : ∀ a ∈ vertices, 46 ≤ (outN graph vertices a).card := by
  intro a ha
  have h := degree_lower ha
  have hi := (vertex_bounds ha).1
  generalize hi' : a / 46 = i at h hi
  interval_cases i <;> norm_num [degree, heads, size] at h <;> omega

theorem root_mem : 46 ∈ vertices := by
  exact cell_mem (i := 1) (j := 0) (by decide) (by norm_num [size, degree])

theorem root_incoming : 71 ≤ (inN graph vertices 46).card := by
  have hsub : block 0 ∪ block 6 ⊆ inN graph vertices 46 := by
    intro a ha
    rcases Finset.mem_union.mp ha with ha | ha
    · have haV := block_subset (by decide : 0 < 7) ha
      refine mem_inN.mpr ⟨haV, ?_⟩
      simp only [graph, decide_eq_true_eq]
      refine ⟨haV, root_mem, Or.inl ?_⟩
      rw [(block_mem ha).1]
      norm_num [heads]
    · have haV := block_subset (by decide : 6 < 7) ha
      refine mem_inN.mpr ⟨haV, ?_⟩
      simp only [graph, decide_eq_true_eq]
      refine ⟨haV, root_mem, Or.inl ?_⟩
      rw [(block_mem ha).1]
      norm_num [heads]
  have hc := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint (blocks_disjoint (by decide : 0 ≠ 6)),
    block_card, block_card] at hc
  simpa only [size, degree] using hc

/-- The saturated witness disproves the compensated bound without a
computational certificate or a premise about saturation of the original graph. -/
theorem saturated_counterexample : ∃ E : CH.Digraph,
    QFree E vertices 3 ∧ Sat 3 E vertices ∧
    (∀ a ∈ vertices, 46 ≤ (outN E vertices a).card) ∧
    (ball E vertices 46 2).card ≤ 80 := by
  obtain ⟨E, hsub, hf, hsat⟩ := exists_satQ free
  have hm : ∀ a ∈ vertices, 46 ≤ (outN E vertices a).card := by
    intro a ha
    apply (minimum_degree a ha).trans
    apply Finset.card_le_card
    intro b hb
    obtain ⟨hbV, hab⟩ := mem_outN.mp hb
    exact mem_outN.mpr ⟨hbV, hsub a ha b hbV hab⟩
  have hin : 71 ≤ (inN E vertices 46).card := by
    apply root_incoming.trans
    apply Finset.card_le_card
    intro a ha
    obtain ⟨haV, har⟩ := mem_inN.mp ha
    exact mem_inN.mpr ⟨haV, hsub a haV 46 root_mem har⟩
  have hb := card_inN_of_satQ (by decide : 1 ≤ 3) hf hsat root_mem
  rw [order_card] at hb
  norm_num only at hb
  exact ⟨E, hf, hsat, hm, by omega⟩

theorem not_compensated_bound : ¬ (∀ (q s : ℕ), 0 < q → 0 < s →
    ∀ (D : CH.Digraph) (V : Finset ℕ), QFree D V q → Sat q D V →
    (∀ v ∈ V, s ≤ (outN D V v).card) →
    ∀ u ∈ V, (2 * q - 1) * s + 2 ≤ V.card + (ball D V u (q - 1)).card) := by
  intro h
  obtain ⟨E, hf, hsat, hm, hb⟩ := saturated_counterexample
  have hh := h 3 46 (by decide) (by decide) E vertices hf hsat hm 46 root_mem
  rw [order_card] at hh
  norm_num only at hh
  omega

end LeanCH.BR.CompensatedCounter
