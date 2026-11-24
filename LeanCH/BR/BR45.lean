import LeanCH.BR.BR45Prof
import LeanCH.BR.BRsGenBBall

/-!
# BR(4,5) and BBall(4,5) (Lean 4.35.0)

Paper: `checkpoints/boundary_20261111/BR45_attempt_subagent.md` (Theorem 11, Corollary 12), audited in
`BR45_audit_subagent.md`.

* `br_four_five : BoundaryRegular 4 5`: every `4`-free digraph on 21 vertices with min out-degree `≥ 5` is
  5-diregular. It is `br45_of_cap_tight` (discharging, `BR45Disc`) applied to `cap45` and `tight45` (profile kills,
  `BR45Prof`).
* `bball45 : BRsGen.BBall 4 5` (**Corollary 12**): in a `4`-free digraph on `range 21` with out-degree exactly 5,
  `|B_3(u)| ≥ 16`. Proof: the saturation `E ⊇ D` is a saturated boundary graph, so it is in-regular
  (`DHyp.regular`), hence out-regular, hence equal to `D` on `range 21`; and `|B_3^E(u)| = 21 − in_E(u) = 16`.
-/

set_option linter.style.longLine false

namespace LeanCH.BR.BR45

open LeanCH.BR.BRq2 LeanCH.BR.BRq3 CH Compose.Boundary

/-- **BR(4,5).** -/
theorem br_four_five : Compose.Boundary.BoundaryRegular 4 5 :=
  br45_of_cap_tight cap45 tight45

/-- Walks of `E` starting in `W` are walks of `D` when `E ⊆ D` inside `W`. -/
theorem walk_back {D E : CH.Digraph} {W : Finset ℕ} (h : ∀ a ∈ W, ∀ b ∈ W, E a b = true → D a b = true)
    {a b m : ℕ} (ha : a ∈ W) (w : Walk E W a b m) : Walk D W a b m := by
  revert ha
  induction w with
  | refl a => exact fun _ => .refl a
  | step hb hab _ ih => exact fun ha => .step hb (h _ ha _ hb hab) (ih hb)

/-- **BBall(4,5)** (Corollary 12). -/
theorem bball45 : LeanCH.BR.BRsGen.BBall 4 5 := by
  classical
  intro D hfree hout u hu
  change QFree D V45 4 at hfree
  change OutEq 5 D V45 at hout
  change u ∈ V45 at hu
  change 16 ≤ (ball D V45 u 3).card
  have hout5 : ∀ v ∈ V45, 5 ≤ (outN D V45 v).card := fun v hv => (hout v hv).ge
  obtain ⟨E, hsub, hEfree, hsat⟩ := exists_sat hfree
  have hsubN : ∀ v ∈ V45, outN D V45 v ⊆ outN E V45 v := fun v hv z hz =>
    mem_outN.mpr ⟨(mem_outN.mp hz).1, hsub v hv z (mem_outN.mp hz).1 (mem_outN.mp hz).2⟩
  have hEout : ∀ v ∈ V45, 5 ≤ (outN E V45 v).card :=
    fun v hv => (hout5 v hv).trans (Finset.card_le_card (hsubN v hv))
  have HE : DHyp E V45 :=
    ⟨Finset.card_range 21, hEfree, hEout, hsat, cap45 E hEfree hEout, tight45 E hEfree hEout⟩
  have hin := HE.regular
  have hsum : ∑ y ∈ V45, (outN E V45 y).card = ∑ z ∈ V45, (inN E V45 z).card :=
    Compose.ThinRigid.sum_out_eq_sum_in E V45
  have heq : ∑ _y ∈ V45, 5 = ∑ y ∈ V45, (outN E V45 y).card := by
    rw [hsum]
    exact (Finset.sum_congr rfl hin).symm
  have hE5 : ∀ v ∈ V45, (outN E V45 v).card = 5 :=
    fun v hv => ((Finset.sum_eq_sum_iff_of_le hEout).mp heq v hv).symm
  have hNeq : ∀ v ∈ V45, outN D V45 v = outN E V45 v := fun v hv =>
    Finset.eq_of_subset_of_card_le (hsubN v hv) (by rw [hE5 v hv, hout v hv])
  have hEarc : ∀ a ∈ V45, ∀ b ∈ V45, E a b = true → D a b = true := by
    intro a ha b hb h
    have : b ∈ outN D V45 a := by
      rw [hNeq a ha]
      exact mem_outN.mpr ⟨hb, h⟩
    exact (mem_outN.mp this).2
  have hball : ball E V45 u 3 ⊆ ball D V45 u 3 := by
    intro v hv
    obtain ⟨hvV, j, hj, w⟩ := mem_ball.mp hv
    exact mem_ball.mpr ⟨hvV, j, hj, walk_back hEarc hu w⟩
  have h1 := HE.in_add hu
  have h2 := hin u hu
  have h3 := Finset.card_le_card hball
  omega

end LeanCH.BR.BR45
