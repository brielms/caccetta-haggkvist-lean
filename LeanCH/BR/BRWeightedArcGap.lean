import LeanCH.BR.BRWeightedRichConnection

/-! Exact weighted charges for actual outgoing-neighbour differences.
Equalized rows alone give the charge; no induction or strict value is hidden. -/
namespace LeanCH.BR.WeightedSD
open Finset BRq2 BRq3 BR45 BRsub

def outGap (D : CH.Digraph) (V : Finset ℕ) (x y : ℕ) : Finset ℕ :=
  outN D V x \ outN D V y

theorem outGap_eq_filter (D : CH.Digraph) (V : Finset ℕ) (x y : ℕ) :
    outGap D V x y = V.filter (fun z => D x z = true ∧ ¬ D y z = true) := by
  ext z
  simp only [outGap, Finset.mem_sdiff, mem_outN, Finset.mem_filter]
  tauto

theorem mem_outGap {D : CH.Digraph} {V : Finset ℕ} {x y z : ℕ} :
    z ∈ outGap D V x y ↔ z ∈ V ∧ D x z = true ∧ ¬ D y z = true := by
  rw [outGap_eq_filter, Finset.mem_filter]

theorem equal_rows_gap_balance {q : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (w : ℕ → ℚ) {x y : ℕ} (he : row q D V w x = row q D V w y) :
    (q : ℚ) * mass (outGap D V x y) w + w x =
      (q : ℚ) * mass (outGap D V y x) w + w y := by
  have hs : mass (outGap D V x y) w + outW D V w y =
      mass (outGap D V y x) w + outW D V w x := by
    rw [outGap_eq_filter, outGap_eq_filter]
    simp only [mass, Finset.sum_filter, outW, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro z hz
    by_cases hx : D x z = true <;> by_cases hy : D y z = true <;> simp [hx, hy]
  unfold row at he
  nlinarith

/-- The reverse difference is retained in full, after removing the actual head x. -/
theorem equal_rows_arc_gap_exact {q : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (w : ℕ → ℚ) {x y : ℕ} (hx : x ∈ V) (hyx : D y x = true)
    (hloop : ¬ D x x = true) (he : row q D V w x = row q D V w y) :
    (q : ℚ) * mass (outGap D V x y) w =
      (q - 1 : ℚ) * w x + w y +
        q * mass ((outGap D V y x).erase x) w := by
  have hxG : x ∈ outGap D V y x := mem_outGap.mpr ⟨hx, hyx, hloop⟩
  have hs := Finset.sum_erase_add (outGap D V y x) w hxG
  change mass ((outGap D V y x).erase x) w + w x = mass (outGap D V y x) w at hs
  have hg := equal_rows_gap_balance w he
  rw [← hs] at hg
  nlinarith

theorem equal_rows_arc_gap_lower {q : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (w : ℕ → ℚ) (hw : ∀ z ∈ V, 0 ≤ w z)
    {x y : ℕ} (hx : x ∈ V) (hyx : D y x = true)
    (hloop : ¬ D x x = true) (he : row q D V w x = row q D V w y) :
    (q - 1 : ℚ) * w x + w y ≤ (q : ℚ) * mass (outGap D V x y) w := by
  rw [equal_rows_arc_gap_exact w hx hyx hloop he]
  have hn : 0 ≤ mass ((outGap D V y x).erase x) w :=
    mass_nonneg (fun z hz => hw z (mem_outGap.mp (Finset.mem_erase.mp hz).2).1)
  exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg q) hn)

theorem equal_rows_arc_gap_nonempty {q : ℕ} (hq : 1 ≤ q)
    {D : CH.Digraph} {V : Finset ℕ} (w : ℕ → ℚ) (hw : ∀ z ∈ V, 0 ≤ w z)
    {x y : ℕ} (hx : x ∈ V) (hwy : 0 < w y) (hyx : D y x = true)
    (hloop : ¬ D x x = true) (he : row q D V w x = row q D V w y) :
    (outGap D V x y).Nonempty := by
  have hlow := equal_rows_arc_gap_lower w hw hx hyx hloop he
  have hqR : (1 : ℚ) ≤ q := by exact_mod_cast hq
  have hpos : 0 < (q - 1 : ℚ) * w x + w y :=
    add_pos_of_nonneg_of_pos (mul_nonneg (by linarith) (hw x hx)) hwy
  by_contra hn
  rw [Finset.not_nonempty_iff_eq_empty.mp hn] at hlow
  simp only [mass, Finset.sum_empty, mul_zero] at hlow
  linarith

/-- A two-step actual successor cannot return to the original tail too soon. -/
theorem outGap_no_short_return {q t : ℕ} (ht : t + 2 ≤ q)
    {D : CH.Digraph} {V : Finset ℕ} (hf : QFree D V q)
    {x y z : ℕ} (hx : x ∈ V) (hy : y ∈ V) (hyx : D y x = true)
    (hz : z ∈ outGap D V x y) : y ∉ ball D V z t := by
  intro hb
  obtain ⟨_, k, hk, wk⟩ := mem_ball.mp hb
  obtain ⟨hzV, hxz, _⟩ := mem_outGap.mp hz
  exact hf y (k + 2) (by omega) (by omega) (.step hx hyx (.step hzV hxz wk))

end LeanCH.BR.WeightedSD
