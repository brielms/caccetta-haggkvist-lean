import LeanCH.BR.BRCyclicBlocks
import LeanCH.BR.BRsubSat

/-! Alternating cyclic and transitive blocks test the order hypothesis in SC. -/

namespace LeanCH.BR.AlternatingSubstitution
open BRq2 BRq3 BR45 BRsub

def vertices (s : ℕ) : Finset ℕ :=
  (Finset.range (s * s)).filter (fun a => a / s % 2 = 0 ∨ a % s < s - 1)

def graph (s : ℕ) : CH.Digraph := fun a b => decide
  (a ∈ vertices s ∧ b ∈ vertices s ∧
    ((a / s + 1) % s = b / s ∨
      (a / s = b / s ∧
        ((a / s % 2 = 0 ∧ (a % s + 1) % s = b % s) ∨
         (a / s % 2 ≠ 0 ∧ a % s < b % s)))))

def block (s i : ℕ) : Finset ℕ :=
  (Finset.range (if i % 2 = 0 then s else s - 1)).image (fun j => i * s + j)

theorem cell_div_mod {s i j : ℕ} (hs : 0 < s) (hj : j < s) :
    (i * s + j) / s = i ∧ (i * s + j) % s = j := by
  constructor
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hs, Nat.div_eq_of_lt hj]
    omega
  · simp [Nat.add_mod, Nat.mod_eq_of_lt hj]

theorem vertex_bounds {s a : ℕ} (ha : a ∈ vertices s) :
    a < s * s ∧ a / s < s := by
  have hn := Finset.mem_range.mp (Finset.mem_filter.mp ha).1
  exact ⟨hn, (Nat.div_lt_iff_lt_mul (by nlinarith : 0 < s)).mpr hn⟩

theorem cell_mem {s i j : ℕ} (hs : 0 < s) (hi : i < s) (hj : j < s)
    (hvalid : i % 2 = 0 ∨ j < s - 1) : i * s + j ∈ vertices s := by
  obtain ⟨hd, hm⟩ := cell_div_mod (i := i) hs hj
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_range.mpr ?_, ?_⟩
  · nlinarith
  · simpa only [hd, hm] using hvalid

theorem block_card {s i : ℕ} (hs : 0 < s) :
    (block s i).card = if i % 2 = 0 then s else s - 1 := by
  rw [block, Finset.card_image_of_injective, Finset.card_range]
  intro x y heq
  dsimp only at heq
  omega

theorem block_mem {s i a : ℕ} (hs : 0 < s) (ha : a ∈ block s i) :
    a / s = i ∧ a % s < s ∧ (i % 2 = 0 ∨ a % s < s - 1) := by
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ha
  have hj' := Finset.mem_range.mp hj
  have hjlt : j < s := by split_ifs at hj' <;> omega
  obtain ⟨hd, hm⟩ := cell_div_mod (i := i) hs hjlt
  refine ⟨hd, by omega, ?_⟩
  by_cases he : i % 2 = 0
  · exact Or.inl he
  · right
    simpa only [if_neg he, hm] using hj'

theorem block_subset {s i : ℕ} (hs : 0 < s) (hi : i < s) : block s i ⊆ vertices s := by
  intro a ha
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ha
  have hj' := Finset.mem_range.mp hj
  apply cell_mem hs hi
  · split_ifs at hj' <;> omega
  · by_cases he : i % 2 = 0
    · exact Or.inl he
    · exact Or.inr (by simpa only [if_neg he] using hj')

theorem free {s : ℕ} (hs : 2 ≤ s) : QFree (graph s) (vertices s) (s - 1) := by
  have hs0 : 0 < s := by omega
  apply qfree_of_cyclic_blocks (N := s) (by omega) (fun a => a / s)
  · intro a b hb hab
    obtain ⟨_, _, he⟩ := of_decide_eq_true hab
    rcases he with he | he
    · right
      change (a / s + 1) % s = (b / s) % s
      rw [← he, Nat.mod_mod]
    · exact Or.inl he.1
  · intro i
    apply qfree_of_rank_phase_on
      (fun a => if i % 2 = 0 then 0 else a % s) (fun a => a % s)
    intro a ha b hb hab
    obtain ⟨haV, hai⟩ := Finset.mem_filter.mp ha
    obtain ⟨hbV, hbi⟩ := Finset.mem_filter.mp hb
    obtain ⟨_, _, he⟩ := of_decide_eq_true hab
    have hai' : a / s = i := hai
    have hbi' : b / s = i := hbi
    rcases he with he | he
    · have hi := (vertex_bounds haV).2
      rw [hai', hbi'] at he
      rw [hai'] at hi
      have heq : Nat.ModEq s (i + 1) i := by
        change (i + 1) % s = i % s
        rwa [Nat.mod_eq_of_lt hi]
      have hd : s ∣ 1 := by simpa using heq.symm.dvd'
      have hh := Nat.le_of_dvd (by decide : 0 < 1) hd
      omega
    · rcases he.2 with he | he
      · have hi : i % 2 = 0 := by simpa only [hai'] using he.1
        simp only [if_pos hi]
        refine ⟨le_rfl, fun _ => ?_⟩
        rw [Nat.sub_add_cancel hs0]
        change (a % s + 1) % s = (b % s) % s
        simpa only [Nat.mod_mod] using he.2
      · have hi : i % 2 ≠ 0 := by simpa only [hai'] using he.1
        simp only [if_neg hi]
        exact ⟨by omega, fun hh => (by omega : False).elim⟩

theorem next_block_ne {s i : ℕ} (hs : 2 ≤ s) (hi : i < s) :
    (i + 1) % s ≠ i := by
  intro he
  have hmod : Nat.ModEq s (i + 1) i := by
    change (i + 1) % s = i % s
    rwa [Nat.mod_eq_of_lt hi]
  have hd : s ∣ 1 := by simpa using hmod.symm.dvd'
  have hh := Nat.le_of_dvd (by decide : 0 < 1) hd
  omega

theorem minimum_degree {s : ℕ} (hs : 2 ≤ s) (heven : 2 ∣ s) :
    ∀ a ∈ vertices s, s ≤ (outN (graph s) (vertices s) a).card := by
  intro a ha
  have hs0 : 0 < s := by omega
  let i := a / s
  let j := (i + 1) % s
  have hi : i < s := (vertex_bounds ha).2
  have hj : j < s := Nat.mod_lt _ hs0
  have hji : j ≠ i := next_block_ne hs hi
  have hsub : block s j ⊆ outN (graph s) (vertices s) a := by
    intro b hb
    have hbV := block_subset hs0 hj hb
    refine mem_outN.mpr ⟨hbV, ?_⟩
    apply decide_eq_true
    exact ⟨ha, hbV, Or.inl (block_mem hs0 hb).1.symm⟩
  have hpar : j % 2 = (i + 1) % 2 := Nat.mod_mod_of_dvd _ heven
  by_cases hie : i % 2 = 0
  · have hje : j % 2 ≠ 0 := by omega
    let b := i * s + (a % s + 1) % s
    have hslot : (a % s + 1) % s < s := Nat.mod_lt _ hs0
    have hbV : b ∈ vertices s := cell_mem hs0 hi hslot (Or.inl hie)
    obtain ⟨hbd, hbm⟩ := cell_div_mod (i := i) hs0 hslot
    have hba : b ∈ outN (graph s) (vertices s) a := by
      refine mem_outN.mpr ⟨hbV, ?_⟩
      apply decide_eq_true
      exact ⟨ha, hbV, Or.inr ⟨hbd.symm, Or.inl ⟨hie, hbm.symm⟩⟩⟩
    have hbnot : b ∉ block s j := by
      intro hh
      have hd := (block_mem hs0 hh).1
      exact hji (hd.symm.trans hbd)
    have hc := Finset.card_le_card (Finset.insert_subset hba hsub)
    rw [Finset.card_insert_of_notMem hbnot, block_card hs0, if_neg hje] at hc
    omega
  · have hje : j % 2 = 0 := by omega
    have hc := Finset.card_le_card hsub
    rwa [block_card hs0, if_pos hje] at hc

/-- One missing final cell in every odd block bounds the order. -/
theorem order_card {m : ℕ} (hm : 1 ≤ m) :
    (vertices (2 * m)).card + m = (2 * m) * (2 * m) := by
  classical
  let holes := (Finset.range m).image (fun i => (2 * i + 1) * (2 * m) + (2 * m - 1))
  have hs0 : 0 < 2 * m := by omega
  have hc : holes.card = m := by
    rw [show holes = _ from rfl, Finset.card_image_of_injOn, Finset.card_range]
    intro i hi j hj he
    dsimp only at he
    nlinarith
  have hholes : ∀ a ∈ holes, a ∈ Finset.range ((2 * m) * (2 * m)) ∧
      a ∉ vertices (2 * m) := by
    intro a ha
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
    have hi' := Finset.mem_range.mp hi
    have hslot : 2 * m - 1 < 2 * m := by omega
    obtain ⟨hd, hr⟩ := cell_div_mod (i := 2 * i + 1) hs0 hslot
    refine ⟨Finset.mem_range.mpr ?_, ?_⟩
    · have he := Nat.sub_add_cancel hs0
      have hh : 2 * i + 1 < 2 * m := by omega
      nlinarith
    · intro hv
      have hv' := (Finset.mem_filter.mp hv).2
      rw [hd, hr] at hv'
      omega
  have hdisj : Disjoint (vertices (2 * m)) holes :=
    Finset.disjoint_left.mpr (fun a ha hh => (hholes a hh).2 ha)
  have hsub : vertices (2 * m) ∪ holes ⊆ Finset.range ((2 * m) * (2 * m)) :=
    Finset.union_subset (Finset.filter_subset _ _) (fun a ha => (hholes a ha).1)
  have heq : vertices (2 * m) ∪ holes = Finset.range ((2 * m) * (2 * m)) := by
    apply Finset.Subset.antisymm hsub
    intro a ha
    by_cases hv : a ∈ vertices (2 * m)
    · exact Finset.mem_union_left _ hv
    · have han := Finset.mem_range.mp ha
      have had : a / (2 * m) < 2 * m := (Nat.div_lt_iff_lt_mul hs0).mpr han
      have hr : a % (2 * m) = 2 * m - 1 := by
        have hlo := Nat.mod_lt a hs0
        have hn : ¬ a % (2 * m) < 2 * m - 1 :=
          fun h => hv (Finset.mem_filter.mpr ⟨ha, Or.inr h⟩)
        omega
      have hodd : a / (2 * m) % 2 = 1 := by
        have hn : a / (2 * m) % 2 ≠ 0 :=
          fun h => hv (Finset.mem_filter.mpr ⟨ha, Or.inl h⟩)
        omega
      have hpart := Nat.mod_add_div (a / (2 * m)) 2
      have hdiv : 2 * (a / (2 * m) / 2) + 1 = a / (2 * m) := by omega
      apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      refine ⟨a / (2 * m) / 2, Finset.mem_range.mpr (by omega), ?_⟩
      rw [hdiv]
      have htotal := Nat.mod_add_div a (2 * m)
      nlinarith
  have hh := congrArg Finset.card heq
  rwa [Finset.card_union_of_disjoint hdisj, hc, Finset.card_range] at hh

theorem order_upper {m : ℕ} (hm : 1 ≤ m) :
    (vertices (2 * m)).card + m ≤ (2 * m) * (2 * m) := (order_card hm).le

def root (s : ℕ) : ℕ := (s - 1) * s + (s - 2)

theorem root_mem {s : ℕ} (hs : 2 ≤ s) : root s ∈ vertices s :=
  cell_mem (by omega) (by omega) (by omega) (Or.inr (by omega))

theorem root_incoming {s : ℕ} (hs : 2 ≤ s) (heven : s % 2 = 0) :
    2 * s - 2 ≤ (inN (graph s) (vertices s) (root s)).card := by
  classical
  have hs0 : 0 < s := by omega
  have hrV := root_mem hs
  have hr := cell_div_mod (i := s - 1) hs0 (by omega : s - 2 < s)
  have hodd : (s - 1) % 2 ≠ 0 := by omega
  have he : (s - 2) % 2 = 0 := by omega
  let P := (Finset.range (s - 2)).image (fun j => (s - 1) * s + j)
  have hPc : P.card = s - 2 := by
    rw [show P = _ from rfl, Finset.card_image_of_injective, Finset.card_range]
    intro x y hxy
    dsimp only at hxy
    omega
  have hsubB : block s (s - 2) ⊆ inN (graph s) (vertices s) (root s) := by
    intro a ha
    have haV := block_subset hs0 (by omega : s - 2 < s) ha
    have hd := (block_mem hs0 ha).1
    refine mem_inN.mpr ⟨haV, ?_⟩
    apply decide_eq_true
    refine ⟨haV, hrV, Or.inl ?_⟩
    change (a / s + 1) % s = ((s - 1) * s + (s - 2)) / s
    rw [hd, hr.1, show s - 2 + 1 = s - 1 by omega, Nat.mod_eq_of_lt (by omega : s - 1 < s)]
  have hsubP : P ⊆ inN (graph s) (vertices s) (root s) := by
    intro a ha
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ha
    have hj' := Finset.mem_range.mp hj
    have haV := cell_mem hs0 (by omega : s - 1 < s) (by omega : j < s) (Or.inr (by omega))
    obtain ⟨hd, ht⟩ := cell_div_mod (i := s - 1) hs0 (by omega : j < s)
    refine mem_inN.mpr ⟨haV, ?_⟩
    apply decide_eq_true
    refine ⟨haV, hrV, Or.inr ⟨hd.trans hr.1.symm, Or.inr ?_⟩⟩
    change ((s - 1) * s + j) / s % 2 ≠ 0 ∧ ((s - 1) * s + j) % s < root s % s
    rw [hd, ht]
    exact ⟨hodd, by change j < ((s - 1) * s + (s - 2)) % s; rwa [hr.2]⟩
  have hdisj : Disjoint (block s (s - 2)) P := by
    apply Finset.disjoint_left.mpr
    intro a ha hP
    have hd := (block_mem hs0 ha).1
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hP
    have hj' := Finset.mem_range.mp hj
    have hd' := (cell_div_mod (i := s - 1) hs0 (by omega : j < s)).1
    omega
  have hc := Finset.card_le_card (Finset.union_subset hsubB hsubP)
  rw [Finset.card_union_of_disjoint hdisj, block_card hs0, if_pos he, hPc] at hc
  omega

/-- For every even degree >=6 there is a saturated host above the boundary
whose (s-2)-ball fails the strict cap. No finite computation is used. -/
theorem saturated_strict_cap_counterexample (m : ℕ) (hm : 3 ≤ m) :
    ∃ E : CH.Digraph,
      QFree E (vertices (2 * m)) (2 * m - 1) ∧
      Sat (2 * m - 1) E (vertices (2 * m)) ∧
      (∀ v ∈ vertices (2 * m), 2 * m ≤ (outN E (vertices (2 * m)) v).card) ∧
      (vertices (2 * m)).card = (2 * m - 1) * (2 * m) + 1 + (m - 1) ∧
      (ball E (vertices (2 * m)) (root (2 * m)) (2 * m - 2)).card + (m - 2) ≤
        (2 * m - 2) * (2 * m) ∧
      (ball E (vertices (2 * m)) (root (2 * m)) (2 * m - 2)).card <
        (2 * m - 2) * (2 * m) := by
  have hs : 2 ≤ 2 * m := by omega
  have hm0 : 1 ≤ m := by omega
  obtain ⟨E, hsub, hf, hsat⟩ := exists_satQ (free hs)
  have hr := root_mem hs
  have hmin : ∀ v ∈ vertices (2 * m), 2 * m ≤ (outN E (vertices (2 * m)) v).card := by
    intro v hv
    apply (minimum_degree hs (by simp) v hv).trans
    apply Finset.card_le_card
    intro w hw
    obtain ⟨hwV, hvw⟩ := mem_outN.mp hw
    exact mem_outN.mpr ⟨hwV, hsub v hv w hwV hvw⟩
  have hin : 4 * m - 2 ≤ (inN E (vertices (2 * m)) (root (2 * m))).card := by
    have hle := root_incoming hs (by omega : (2 * m) % 2 = 0)
    have hmono : inN (graph (2 * m)) (vertices (2 * m)) (root (2 * m)) ⊆
        inN E (vertices (2 * m)) (root (2 * m)) := by
      intro v hv
      obtain ⟨hvV, hvr⟩ := mem_inN.mp hv
      exact mem_inN.mpr ⟨hvV, hsub v hvV _ hr hvr⟩
    have hc := Finset.card_le_card hmono
    omega
  have horder := order_card hm0
  have hbalance := card_inN_of_satQ (by omega : 1 ≤ 2 * m - 1) hf hsat hr
  have hradius : 2 * m - 1 - 1 = 2 * m - 2 := by omega
  rw [hradius] at hbalance
  have hsub1 : 2 * m - 1 + 1 = 2 * m := by omega
  have hsub2 : 2 * m - 2 + 2 = 2 * m := by omega
  have hm1 : m - 1 + 1 = m := by omega
  have hm2 : m - 2 + 2 = m := by omega
  have hsub4 : 4 * m - 2 + 2 = 4 * m := by omega
  refine ⟨E, hf, hsat, hmin, ?_, ?_, ?_⟩ <;> nlinarith

/-- Saturation cannot replace the exact boundary order in a uniform SC claim. -/
theorem not_order_free_strict_cap (m : ℕ) (hm : 3 ≤ m) :
    ¬ (∀ (D : CH.Digraph) (V : Finset ℕ), QFree D V (2 * m - 1) →
      Sat (2 * m - 1) D V → (∀ v ∈ V, 2 * m ≤ (outN D V v).card) →
      ∀ u ∈ V, (2 * m - 2) * (2 * m) ≤ (ball D V u (2 * m - 2)).card) := by
  intro h
  obtain ⟨E, hf, hsat, hmin, _, _, hsmall⟩ := saturated_strict_cap_counterexample m hm
  have hh := h E (vertices (2 * m)) hf hsat hmin _ (root_mem (by omega))
  omega

end LeanCH.BR.AlternatingSubstitution
