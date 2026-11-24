import LeanCH.BR.BRWeightedRealDual

/-! Exact internal-column and external-coverage losses in a weighted cut.
All certificate existence used here follows from rational internal SD. -/
namespace LeanCH.BR.WeightedSD
open Finset BRq2 BRq3 BR45 BRsub

theorem realOutW_split {D : CH.Digraph} {V M : Finset ℕ} (hMV : M ⊆ V)
    (w : ℕ → ℝ) (x : ℕ) :
    realOutW D V w x = realOutW D M w x + realOutW D (V \ M) w x :=
  (Finset.sum_sdiff hMV).symm.trans (add_comm _ _)

theorem real_cross_out (D : CH.Digraph) (M N : Finset ℕ) (w p : ℕ → ℝ) :
    (∑ x ∈ M, p x * realOutW D N w x) = ∑ z ∈ N, w z * realInW D M p z := by
  simp only [realOutW, realInW, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z hz
  apply Finset.sum_congr rfl
  intro x hx
  split_ifs <;> ring

theorem real_cross_rows (q : ℕ) (D : CH.Digraph) (M : Finset ℕ) (w p : ℕ → ℝ) :
    (∑ x ∈ M, p x * realRow q D M w x) = ∑ z ∈ M, w z * realCol q D M p z := by
  simp only [realRow, realCol, mul_add, Finset.sum_add_distrib]
  have he := real_cross_out D M M w p
  have hleft : (∑ x ∈ M, p x * (q * realOutW D M w x)) =
      q * ∑ x ∈ M, p x * realOutW D M w x := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    ring
  have hright : (∑ z ∈ M, w z * (q * realInW D M p z)) =
      q * ∑ z ∈ M, w z * realInW D M p z := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    ring
  rw [hleft, hright, he]
  congr 1
  exact Finset.sum_congr rfl (fun x hx => mul_comm _ _)

theorem weighted_cut_identity {q : ℕ} {D : CH.Digraph} {V M : Finset ℕ}
    (hMV : M ⊆ V) (w p : ℕ → ℝ) :
    (∑ x ∈ M, p x * realRow q D V w x) =
      (∑ z ∈ M, w z * realCol q D M p z) +
        q * ∑ z ∈ V \ M, w z * realInW D M p z := by
  have hr : ∀ x, realRow q D V w x =
      realRow q D M w x + q * realOutW D (V \ M) w x := by
    intro x
    simp only [realRow, realOutW_split hMV w x]
    ring
  simp_rw [hr, mul_add]
  rw [Finset.sum_add_distrib, real_cross_rows]
  congr 1
  calc
    _ = q * ∑ x ∈ M, p x * realOutW D (V \ M) w x := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun x hx => by ring)
    _ = _ := by rw [real_cross_out]

theorem refined_cut_bound {q : ℕ} {D : CH.Digraph} {V M : Finset ℕ}
    (hMV : M ⊆ V) {p w : ℕ → ℝ} {alpha c : ℝ} (hp : RealDual q D M alpha p)
    (hw : ∀ v ∈ V, 0 ≤ w v) (hr : ∀ v ∈ M, c ≤ realRow q D V w v) :
    c ≤ alpha * realMass M w + q * ∑ z ∈ V \ M, w z * realInW D M p z := by
  have hlo : c ≤ ∑ x ∈ M, p x * realRow q D V w x := by
    have h := Finset.sum_le_sum (s := M) (fun x hx =>
      mul_le_mul_of_nonneg_left (hr x hx) (hp.nonneg x hx))
    rw [← Finset.sum_mul] at h
    change realMass M p * c ≤ _ at h
    simpa only [hp.normalized, one_mul] using h
  have hhi : (∑ z ∈ M, w z * realCol q D M p z) ≤ alpha * realMass M w := by
    calc
      _ ≤ ∑ z ∈ M, w z * alpha := Finset.sum_le_sum (fun z hz =>
        mul_le_mul_of_nonneg_left (hp.columns z hz) (hw z (hMV hz)))
      _ = _ := by rw [← Finset.sum_mul]; exact mul_comm _ _
  rw [weighted_cut_identity hMV w p] at hlo
  linarith

theorem coverage_nonneg {D : CH.Digraph} {M : Finset ℕ} {p : ℕ → ℝ}
    (hp : ∀ v ∈ M, 0 ≤ p v) (z : ℕ) : 0 ≤ realInW D M p z := by
  apply Finset.sum_nonneg
  intro v hv
  split_ifs
  · exact hp v hv
  · exact le_rfl

theorem coverage_le_one {D : CH.Digraph} {M : Finset ℕ} {p : ℕ → ℝ}
    (hp : ∀ v ∈ M, 0 ≤ p v) (hm : realMass M p = 1) (z : ℕ) :
    realInW D M p z ≤ 1 := by
  rw [← hm]
  apply Finset.sum_le_sum
  intro v hv
  split_ifs
  · exact le_rfl
  · exact hp v hv

theorem exterior_subset_sdiff (D : CH.Digraph) (V M : Finset ℕ) :
    exterior D V M ⊆ V \ M := by
  intro z hz
  exact Finset.mem_sdiff.mpr ⟨exterior_subset D V M hz, (Finset.mem_sdiff.mp hz).2⟩

theorem coverage_zero_outside {D : CH.Digraph} {V M : Finset ℕ} (p : ℕ → ℝ)
    {z : ℕ} (hz : z ∈ V \ M) (hne : z ∉ exterior D V M) : realInW D M p z = 0 := by
  apply Finset.sum_eq_zero
  intro x hx
  have hn : ¬ D x z = true := by
    intro he
    apply hne
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_biUnion.mpr
      ⟨x, hx, mem_outN.mpr ⟨(Finset.mem_sdiff.mp hz).1, he⟩⟩, (Finset.mem_sdiff.mp hz).2⟩
  simp [hn]

theorem exterior_coverage_sum (D : CH.Digraph) (V M : Finset ℕ) (w p : ℕ → ℝ) :
    (∑ z ∈ exterior D V M, w z * realInW D M p z) =
      ∑ z ∈ V \ M, w z * realInW D M p z := by
  apply Finset.sum_subset (exterior_subset_sdiff D V M)
  intro z hz hn
  rw [coverage_zero_outside p hz hn, mul_zero]

def internalDefect (q : ℕ) (D : CH.Digraph) (M : Finset ℕ) (w p : ℕ → ℝ) : ℝ :=
  ∑ z ∈ M, w z * (1 - realCol q D M p z)
def exteriorDefect (D : CH.Digraph) (V M : Finset ℕ) (w p : ℕ → ℝ) : ℝ :=
  ∑ z ∈ exterior D V M, w z * (1 - realInW D M p z)

theorem internalDefect_eq (q : ℕ) (D : CH.Digraph) (M : Finset ℕ) (w p : ℕ → ℝ) :
    internalDefect q D M w p = realMass M w - ∑ z ∈ M, w z * realCol q D M p z := by
  simp [internalDefect, realMass, mul_sub, Finset.sum_sub_distrib]

theorem exteriorDefect_eq (D : CH.Digraph) (V M : Finset ℕ) (w p : ℕ → ℝ) :
    exteriorDefect D V M w p = realMass (exterior D V M) w -
      ∑ z ∈ V \ M, w z * realInW D M p z := by
  simp only [exteriorDefect, mul_sub, mul_one, Finset.sum_sub_distrib,
    exterior_coverage_sum, realMass]

/-- At equal rows the cut surplus is EXACTLY the sum of internal column
slack and missing exterior coverage, with the latter multiplied by q. -/
theorem cut_slack_identity {q : ℕ} {D : CH.Digraph} {V M : Finset ℕ}
    (hMV : M ⊆ V) (w p : ℕ → ℝ) (hm : realMass M p = 1) {c : ℝ}
    (hr : ∀ x ∈ M, realRow q D V w x = c) :
    realMass M w + q * realMass (exterior D V M) w - c =
      internalDefect q D M w p + q * exteriorDefect D V M w p := by
  have hc : (∑ x ∈ M, p x * realRow q D V w x) = c := by
    calc
      _ = ∑ x ∈ M, p x * c := Finset.sum_congr rfl (fun x hx => by rw [hr x hx])
      _ = c := by rw [← Finset.sum_mul]; change realMass M p * c = c; rw [hm, one_mul]
  have he := weighted_cut_identity (q := q) (D := D) hMV w p
  rw [hc] at he
  rw [internalDefect_eq, exteriorDefect_eq]
  linarith

theorem defects_nonneg {q : ℕ} {D : CH.Digraph} {V M : Finset ℕ}
    (hMV : M ⊆ V) {w p : ℕ → ℝ} (hp : RealDual q D M 1 p)
    (hw : ∀ v ∈ V, 0 ≤ w v) :
    0 ≤ internalDefect q D M w p ∧ 0 ≤ exteriorDefect D V M w p := by
  constructor
  · apply Finset.sum_nonneg
    intro z hz
    exact mul_nonneg (hw z (hMV hz)) (sub_nonneg.mpr (hp.columns z hz))
  · apply Finset.sum_nonneg
    intro z hz
    exact mul_nonneg (hw z (exterior_subset D V M hz))
      (sub_nonneg.mpr (coverage_le_one (D := D) hp.nonneg hp.normalized z))

theorem exists_dual_cut_identity {q : ℕ} {D : CH.Digraph} {V M : Finset ℕ}
    (hMV : M ⊆ V) (hM : M.Nonempty) (hSD : SelfDual q D M)
    (w : ℕ → ℝ) (hw : ∀ v ∈ V, 0 ≤ w v) {c : ℝ}
    (hr : ∀ x ∈ M, realRow q D V w x = c) :
    ∃ p, RealDual q D M 1 p ∧ 0 ≤ internalDefect q D M w p ∧
      0 ≤ exteriorDefect D V M w p ∧
      realMass M w + q * realMass (exterior D V M) w - c =
        internalDefect q D M w p + q * exteriorDefect D V M w p := by
  obtain ⟨p, hp⟩ := realDual_of_selfDual hSD hM
  have hn := defects_nonneg hMV hp hw
  exact ⟨p, hp, hn.1, hn.2, cut_slack_identity hMV w p hp.normalized hr⟩

theorem exists_dual_cut_identity_rat {q : ℕ} {D : CH.Digraph} {V M : Finset ℕ}
    (hMV : M ⊆ V) (hM : M.Nonempty) (hSD : SelfDual q D M)
    (w : ℕ → ℚ) (hw : ∀ v ∈ V, 0 ≤ w v) {c : ℚ}
    (hr : ∀ x ∈ M, row q D V w x = c) :
    ∃ p, RealDual q D M 1 p ∧
      0 ≤ internalDefect q D M (fun v => (w v : ℝ)) p ∧
      0 ≤ exteriorDefect D V M (fun v => (w v : ℝ)) p ∧
      (mass M w : ℝ) + q * (mass (exterior D V M) w : ℝ) - c =
        internalDefect q D M (fun v => (w v : ℝ)) p +
          q * exteriorDefect D V M (fun v => (w v : ℝ)) p := by
  have hwn : ∀ v ∈ V, (0 : ℝ) ≤ (w v : ℝ) := by
    intro v hv
    exact_mod_cast hw v hv
  have hrn : ∀ x ∈ M, realRow q D V (fun v => (w v : ℝ)) x = (c : ℝ) := by
    intro x hx
    rw [realRow_rat, hr x hx]
  obtain ⟨p, hp, hi, he, hid⟩ := exists_dual_cut_identity hMV hM hSD _ hwn hrn
  exact ⟨p, hp, hi, he, by simpa only [realMass_rat] using hid⟩

theorem prime_dual_defect_pos {q : ℕ} (hq : 0 < q) {D : CH.Digraph}
    {V M : Finset ℕ} {w : ℕ → ℚ} (hw : ∀ v ∈ V, 0 < w v) {c : ℚ}
    (hr : ∀ v ∈ V, row q D V w v = c)
    (hproper : ∀ U ⊆ V, U ≠ V → SelfDual q D U)
    (hprime : ∀ U ⊆ V, 2 ≤ U.card → U ≠ V → ¬ OutUniform D V U)
    (hMV : M ⊆ V) (hM : 2 ≤ M.card) (hne : M ≠ V)
    {p : ℕ → ℝ} (hp : RealDual q D M 1 p) :
    0 < internalDefect q D M (fun v => (w v : ℝ)) p +
      q * exteriorDefect D V M (fun v => (w v : ℝ)) p := by
  have hc := strict_cut_at_value hq hw (fun v hv => (hr v hv).ge) hproper hprime hMV hM hne
  have hcR : (c : ℝ) < (mass M w : ℝ) + q * (mass (exterior D V M) w : ℝ) := by
    exact_mod_cast hc
  have hrows : ∀ x ∈ M, realRow q D V (fun v => (w v : ℝ)) x = (c : ℝ) := by
    intro x hx
    rw [realRow_rat, hr x (hMV hx)]
  rw [← cut_slack_identity hMV _ p hp.normalized hrows, realMass_rat, realMass_rat]
  linarith

end LeanCH.BR.WeightedSD
