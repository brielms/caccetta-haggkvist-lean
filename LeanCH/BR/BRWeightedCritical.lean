import LeanCH.BR.BRWeightedPrime

/-! Consequences of positive feasibility and smaller-instance self-duality.
No fixed degree or graph order is assumed. -/
namespace LeanCH.BR.WeightedSD
open BRq2 BRq3 BR45 BRsub

def transferWeight (w : ℕ → ℚ) (x y : ℕ) : ℕ → ℚ :=
  fun v => w v + if v = y then w x else 0

theorem mass_transfer {V : Finset ℕ} {x y : ℕ} (hx : x ∈ V) (hy : y ∈ V)
    (hne : x ≠ y) (w : ℕ → ℚ) : mass (V.erase x) (transferWeight w x y) = mass V w := by
  have hyK : y ∈ V.erase x := Finset.mem_erase.mpr ⟨hne.symm, hy⟩
  calc
    _ = mass (V.erase x) w + w x := by simp [mass, transferWeight, Finset.sum_add_distrib, hyK]
    _ = mass V w := Finset.sum_erase_add V w hx

theorem outW_transfer {D : CH.Digraph} {K : Finset ℕ} {x y : ℕ} (hy : y ∈ K)
    (w : ℕ → ℚ) (v : ℕ) :
    outW D K (transferWeight w x y) v =
      outW D K w v + if D v y = true then w x else 0 := by
  calc
    _ = (∑ u ∈ K, if D v u = true then w u else 0) +
        ∑ u ∈ K, if u = y then (if D v y = true then w x else 0) else 0 := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro u hu
      by_cases huy : u = y
      · subst u
        by_cases he : D v y = true <;> simp [transferWeight, he]
      · by_cases he : D v u = true <;> simp [transferWeight, huy, he]
    _ = _ := by simp [hy, outW]

/-- Incoming neighbourhoods cannot dominate one another in a positive
feasible host with smaller-instance SD: transferring the erased weight
makes the recipient row strictly exceed total mass. -/
theorem no_incoming_domination {q : ℕ}
    {D : CH.Digraph} {V : Finset ℕ}
    (hproper : ∀ U ⊆ V, U ≠ V → SelfDual q D U)
    (w : ℕ → ℚ) (hw : ∀ v ∈ V, 0 < w v)
    (hr : ∀ v ∈ V, mass V w ≤ row q D V w v)
    {x y : ℕ} (hx : x ∈ V) (hy : y ∈ V) (hne : x ≠ y)
    (hdom : ∀ v ∈ V.erase x, D v x = true → D v y = true) : False := by
  let K := V.erase x
  let z := transferWeight w x y
  have hKV : K ⊆ V := Finset.erase_subset _ _
  have hyK : y ∈ K := Finset.mem_erase.mpr ⟨hne.symm, hy⟩
  have hneK : K ≠ V := by
    intro heq
    have hh : x ∈ K := by rw [heq]; exact hx
    exact Finset.notMem_erase x V hh
  have hSD := hproper K hKV hneK
  have hwz : ∀ v ∈ K, 0 < z v := by
    intro v hv
    have hpos := hw v (hKV hv)
    dsimp [z, transferWeight]
    split_ifs <;> linarith [hw x hx]
  have hm : mass K z = mass V w := mass_transfer hx hy hne w
  have hout : ∀ v ∈ K, outW D V w v ≤ outW D K z v := by
    intro v hv
    rw [outW_erase hx w v, outW_transfer hyK]
    by_cases hdx : D v x = true
    · simp [K, hdx, hdom v hv hdx]
    · by_cases hdy : D v y = true <;> simp [K, hdx, hdy, (hw x hx).le]
  have hrz : ∀ v ∈ K, mass K z ≤ row q D K z v := by
    intro v hv
    rw [hm]
    apply (hr v (hKV hv)).trans
    apply add_le_add
    · dsimp [z, transferWeight]
      split_ifs <;> linarith [hw x hx]
    · exact mul_le_mul_of_nonneg_left (hout v hv) (Nat.cast_nonneg q)
  have heq := positive_row_eq hSD (fun v hv => (hwz v hv).le) hrz hyK (hwz y hyK)
  have hstrict : row q D V w y < row q D K z y := by
    apply add_lt_add_of_lt_of_le
    · dsimp [z, transferWeight]
      simp only [ite_true]
      linarith [hw x hx]
    · exact mul_le_mul_of_nonneg_left (hout y hyK) (Nat.cast_nonneg q)
  rw [heq, hm] at hstrict
  exact (not_lt_of_ge (hr y hy)) hstrict

/-- Saturation and the incoming antichain force every reversed arc to have
a return walk of exactly q steps. Appending the arc gives length q+1. -/
theorem arc_return_exact {q : ℕ} (hq : 1 ≤ q)
    {D : CH.Digraph} {V : Finset ℕ} (hf : QFree D V q) (hsat : Sat q D V)
    (hproper : ∀ U ⊆ V, U ≠ V → SelfDual q D U)
    (w : ℕ → ℚ) (hw : ∀ v ∈ V, 0 < w v)
    (hr : ∀ v ∈ V, mass V w ≤ row q D V w v)
    {x y : ℕ} (hx : x ∈ V) (hy : y ∈ V) (hxy : D x y = true) :
    Walk D V y x q := by
  have hne : x ≠ y := by
    intro heq
    subst y
    exact loopfree hf hq hx hxy
  have hreach : x ∈ ball D V y q := by
    by_contra hn
    apply no_incoming_domination hproper w hw hr hx hy hne
    intro v hv hvx
    by_contra hvy
    have hball := hsat y hy v (Finset.mem_erase.mp hv).2 hvy
    have hstep := ball_step hball hx hvx
    exact hn (ball_mono_radius (by omega) hstep)
  obtain ⟨_, k, hk, hwalk⟩ := mem_ball.mp hreach
  have hkexact : k = q := by
    by_contra hneq
    exact hf x (k + 1) (by omega) (by omega) (.step hy hxy hwalk)
  simpa only [hkexact] using hwalk

theorem arc_closed_walk {q : ℕ} (hq : 1 ≤ q)
    {D : CH.Digraph} {V : Finset ℕ} (hf : QFree D V q) (hsat : Sat q D V)
    (hproper : ∀ U ⊆ V, U ≠ V → SelfDual q D U)
    (w : ℕ → ℚ) (hw : ∀ v ∈ V, 0 < w v)
    (hr : ∀ v ∈ V, mass V w ≤ row q D V w v)
    {x y : ℕ} (hx : x ∈ V) (hy : y ∈ V) (hxy : D x y = true) :
    Walk D V x x (q + 1) :=
  .step hy hxy (arc_return_exact hq hf hsat hproper w hw hr hx hy hxy)

theorem diameter_le_cutoff {q : ℕ} (hq : 1 ≤ q)
    {D : CH.Digraph} {V : Finset ℕ} (hf : QFree D V q) (hsat : Sat q D V)
    (hproper : ∀ U ⊆ V, U ≠ V → SelfDual q D U)
    (w : ℕ → ℚ) (hw : ∀ v ∈ V, 0 < w v)
    (hr : ∀ v ∈ V, mass V w ≤ row q D V w v)
    {x y : ℕ} (hx : x ∈ V) (hy : y ∈ V) : y ∈ ball D V x q := by
  by_cases hyx : D y x = true
  · exact mem_ball.mpr ⟨hy, q, le_rfl,
      arc_return_exact hq hf hsat hproper w hw hr hy hx hyx⟩
  · exact ball_mono_radius (by omega) (hsat x hx y hy hyx)

end LeanCH.BR.WeightedSD
