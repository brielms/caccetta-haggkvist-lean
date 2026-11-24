import LeanCH.BR.BRWeightedRepair
import LeanCH.BR.BRSubstitutionWalk
import Mathlib.Order.Interval.Finset.Nat

/-! An all-degree, all-cutoff obstruction to closed-neighbourhood deletion
with additions only: the boundary circulant C_(qd+1)(1,...,d). -/
namespace LeanCH.BR.ClosedNeighborhoodRepair
open BRq2 BRq3 BR45 BRsub WeightedSD

def heads (q d a : ℕ) : Finset ℕ :=
  (Finset.Icc 1 d).image (fun k => (a + k) % (q * d + 1))
def graph (q d : ℕ) : CH.Digraph :=
  fun a b => decide (a < q * d + 1 ∧ b ∈ heads q d a)
def retained (q d : ℕ) : Finset ℕ := Finset.Icc (d + 1) (q * d)

theorem heads_subset (q d a : ℕ) : heads q d a ⊆ Finset.range (q * d + 1) := by
  intro b hb
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hb
  exact Finset.mem_range.mpr (Nat.mod_lt _ (by omega))

theorem outN_heads {q d a : ℕ} (ha : a ∈ Finset.range (q * d + 1)) :
    outN (graph q d) (Finset.range (q * d + 1)) a = heads q d a := by
  ext b
  simp only [mem_outN, graph, decide_eq_true_eq]
  constructor
  · exact fun h => h.2.2
  · exact fun h => ⟨heads_subset q d a h, Finset.mem_range.mp ha, h⟩

theorem heads_card {q d : ℕ} (hq : 1 ≤ q) (a : ℕ) : (heads q d a).card = d := by
  have hdlt : d < q * d + 1 := by nlinarith
  rw [heads, Finset.card_image_iff.mpr]
  · simp
  · intro k hk l hl he
    have hkk := (Finset.mem_Icc.mp hk).2
    have hll := (Finset.mem_Icc.mp hl).2
    have hm : Nat.ModEq (q * d + 1) (a + k) (a + l) := he
    have hc := hm.add_left_cancel' a
    simpa only [Nat.ModEq, Nat.mod_eq_of_lt (lt_of_le_of_lt hkk hdlt),
      Nat.mod_eq_of_lt (lt_of_le_of_lt hll hdlt)] using hc

theorem free (q d : ℕ) : QFree (graph q d) (Finset.range (q * d + 1)) q := by
  apply qfree_of_bounded_modular_steps (d := d) (N := q * d + 1) (by omega) id
  intro a ha b hb hab
  obtain ⟨_, hhead⟩ := of_decide_eq_true hab
  obtain ⟨k, hk, heq⟩ := Finset.mem_image.mp hhead
  obtain ⟨hk1, hkd⟩ := Finset.mem_Icc.mp hk
  refine ⟨k, hk1, hkd, ?_⟩
  change (a + k) % (q * d + 1) = b % (q * d + 1)
  rw [heq, Nat.mod_eq_of_lt (Finset.mem_range.mp hb)]

theorem unit_feasible {q d : ℕ} (hq : 1 ≤ q) :
    ∀ v ∈ Finset.range (q * d + 1),
      row q (graph q d) (Finset.range (q * d + 1)) (fun _ => 1) v =
        mass (Finset.range (q * d + 1)) (fun _ => 1) := by
  intro v hv
  rw [row, outW_unit, outN_heads hv, heads_card hq]
  simp only [mass, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  push_cast
  ring

theorem heads_zero {q d : ℕ} (hq : 1 ≤ q) : heads q d 0 = Finset.Icc 1 d := by
  have hdlt : d < q * d + 1 := by nlinarith
  ext b
  constructor
  · intro hb
    obtain ⟨k, hk, heq⟩ := Finset.mem_image.mp hb
    have hklt := lt_of_le_of_lt (Finset.mem_Icc.mp hk).2 hdlt
    simp only [zero_add, Nat.mod_eq_of_lt hklt] at heq
    exact heq ▸ hk
  · intro hb
    exact Finset.mem_image.mpr ⟨b, hb, by
      simp only [zero_add, Nat.mod_eq_of_lt (lt_of_le_of_lt (Finset.mem_Icc.mp hb).2 hdlt)]⟩

theorem retained_eq_delete_closed {q d : ℕ} (hq : 1 ≤ q) :
    retained q d = Finset.range (q * d + 1) \
      insert 0 (outN (graph q d) (Finset.range (q * d + 1)) 0) := by
  rw [outN_heads (by simp), heads_zero hq]
  ext v
  simp only [retained, Finset.mem_Icc, Finset.mem_sdiff, Finset.mem_range,
    Finset.mem_insert, not_or]
  omega

theorem forward_edge {q d a b : ℕ} (hab : a < b) (hstep : b ≤ a + d)
    (hb : b < q * d + 1) : graph q d a b = true := by
  apply decide_eq_true
  refine ⟨by omega, Finset.mem_image.mpr ⟨b - a, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩⟩
  rw [Nat.add_sub_of_le hab.le, Nat.mod_eq_of_lt hb]

theorem interval_walk {q d : ℕ} (hd : 1 ≤ d) (k : ℕ) {b : ℕ}
    (hb : b ∈ retained q d) : ∀ a ∈ retained q d, a ≤ b → b - a ≤ k * d →
      ∃ l, l ≤ k ∧ Walk (graph q d) (retained q d) a b l := by
  induction k with
  | zero =>
    intro a ha hab hbound
    have heq : a = b := by simp only [zero_mul] at hbound; omega
    subst a
    exact ⟨0, le_rfl, .refl _⟩
  | succ k ih =>
    intro a ha hab hbound
    by_cases heq : a = b
    · subst a
      exact ⟨0, by omega, .refl _⟩
    have hbN : b < q * d + 1 := by have hh := (Finset.mem_Icc.mp hb).2; omega
    by_cases hnear : b ≤ a + d
    · exact ⟨1, by omega, .step hb (forward_edge (by omega) hnear hbN) (.refl _)⟩
    · have haR := Finset.mem_Icc.mp ha
      have hbR := Finset.mem_Icc.mp hb
      have hc : a + d ∈ retained q d := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      have hbound' : b - (a + d) ≤ k * d := by rw [Nat.succ_mul] at hbound; omega
      obtain ⟨l, hl, hw⟩ := ih (a + d) hc (by omega) hbound'
      exact ⟨l + 1, by omega, .step hc (forward_edge (by omega) le_rfl (by omega)) hw⟩

theorem terminal_reachable {q d : ℕ} (hq : 2 ≤ q) (hd : 1 ≤ d) :
    ∀ a ∈ retained q d, q * d ∈ ball (graph q d) (retained q d) a (q - 1) := by
  have hprod : (q - 1) * d + d = q * d := by
    have heq : q - 1 + 1 = q := by omega
    calc
      _ = (q - 1 + 1) * d := by ring
      _ = q * d := by rw [heq]
  have ht : q * d ∈ retained q d := Finset.mem_Icc.mpr ⟨by nlinarith, le_rfl⟩
  intro a ha
  have haR := Finset.mem_Icc.mp ha
  obtain ⟨l, hl, hw⟩ := interval_walk hd (q - 1) ht a ha haR.2 (by omega)
  exact mem_ball.mpr ⟨ht, l, hl, hw⟩

/-- All q>=3 and all degrees d>=1. Even arbitrary positive reweighting
cannot repair this deletion if old retained edges must stay. -/
theorem no_addition_repair {q d : ℕ} (hq : 3 ≤ q) (hd : 1 ≤ d) :
    ¬ ∃ E : CH.Digraph,
      (∀ a ∈ retained q d, ∀ b ∈ retained q d, graph q d a b = true → E a b = true) ∧
      QFree E (retained q d) q ∧
      ∃ w : ℕ → ℚ, (∀ u ∈ retained q d, 0 < w u) ∧
        ∀ u ∈ retained q d, mass (retained q d) w ≤ row q E (retained q d) w u := by
  apply no_positive_addition_repair (by omega : 1 ≤ q)
    (t := q * d) (v := d + 1)
  · exact Finset.mem_Icc.mpr ⟨by nlinarith, le_rfl⟩
  · exact Finset.mem_Icc.mpr ⟨le_rfl, by nlinarith⟩
  · nlinarith
  · exact terminal_reachable (by omega) hd

end LeanCH.BR.ClosedNeighborhoodRepair
