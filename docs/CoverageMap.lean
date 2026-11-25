import checkpoints.shen_extension.CoverageRules
import checkpoints.shen_extension.ShapeClimbMono
import checkpoints.shen_extension.CollarRule
import checkpoints.shen_extension.FlatRule
import checkpoints.shen_extension.TightRule2
import checkpoints.shen_extension.ThinRule

namespace LeanCH.BR.CoverageMapPreview
open CoverageRules ProjectedQuotaTransfer

/-- Both degree-nine results in the README appear in the generated map. -/
example : rule 34 9 (CH.ceilDiv 34 9) ≠ 0 ∧ rule 35 9 (CH.ceilDiv 35 9) ≠ 0 := by decide

/-- The three climb bounds of rules 28, 29 and 32 of one cutoff, computed once per row by the fast evaluation
`ShapeClimbFast` and `ShapeClimbMono` (proved equal to `ShapeClimbMono.guardedBoundM` and
`ShapeClimbAt.guardedBoundAt`). The reach bound is computed once and serves rules 28 and 32.
Where an earlier rule (degree at most eight, cutoff below two, or the top strip and above)
already decides every cell of the row, or neither reach rule applies, it is not computed. -/
def rowBounds (r q : ℕ) : ℕ × ℕ × ℕ :=
  if r ≤ 8 ∨ q < 2 ∨ 2*r-6 ≤ q then (0, 0, 0)
  else
    let b3 := if r ≤ projectionFloor + 1 ∨ q + 8 ≤ 2*r then
      ShapeClimbMono.guardedBoundMF q r projectionFloor 7 else 0
    (if r ≤ projectionFloor + 1 then b3 else 0,
      ShapeClimbFast.guardedBoundAtF q r projectionFloor 2, if q + 8 ≤ 2*r then b3 else 0)

/-- The collar bound of one cutoff, computed once per row; only the row `r = q + 1` uses it. -/
def rowCollar (r q : ℕ) : ℕ := if r = q + 1 then CollarRule.collarBoundF q else 0

/-- The flat bound of one cutoff, computed once per row; only the row `r = q` uses it. -/
def rowFlat (r q : ℕ) : ℕ := if r = q then FlatRule.flatBoundF q else 0

/-- The tight bound of one cutoff, computed once per row; only the row `r = q + 2` uses it, and
only up to the cutoff 9 (`CoverageRules.tightCell`, an evaluation-cost cap). -/
def rowTight (r q : ℕ) : ℕ := if r = q + 2 ∧ q ≤ 9 then TightRule2.tightBound2F q else 0

/-- The thin bound of one cutoff, computed once per row. Outside `9 ≤ r`, `q < 2r - 6` rules
1–32 already decide every printed cell (`base_ne_zero`), and above `q = 12` the thin cell is off
(`CoverageRules.thinCell`, an evaluation-cost cap), so it is not computed there. -/
def rowThin (r q : ℕ) : ℕ :=
  if 9 ≤ r ∧ q + 6 < 2*r ∧ q ≤ 12 then ThinRule.thinBoundF q r else 0

/-- Rules 1–32 of a printed cell are those of the rule (the map has `q = ⌈n/r⌉`, so
`n ≤ q·r`). -/
theorem base_eq (n r q : ℕ) (hn : n ≤ q*r) :
    ruleWith (rowBounds r q).1 (rowBounds r q).2.1 (rowBounds r q).2.2 n r q = ruleBase n r q := by
  unfold rowBounds ruleBase
  split
  next h =>
    by_cases r8 : r ≤ 8
    · simp [ruleWith, r8]
    by_cases q2 : q < 2
    · simp [ruleWith, ShapeClimbAt3.WindowGWith, ShapeClimbAt.WindowGWith, show ¬2 ≤ q by omega]
    have pos : 0 < q*r := Nat.mul_pos (by omega) (by omega)
    have top : (2*r-6 < q ∨ (q = 2*r-6 ∧ (11 < r ∨ n < q*r))) ∨
        (9 ≤ r ∧ q = 2*r-6 ∧ 0 < n ∧ n ≤ q*r) := by
      generalize q*r = m at *
      omega
    rcases top with t | t
    · simp [ruleWith, t]
    · simp only [ruleWith, ite_eq_left t]
  next =>
    have e1 : (if r ≤ projectionFloor + 1 then
        (if r ≤ projectionFloor + 1 ∨ q + 8 ≤ 2*r then
          ShapeClimbMono.guardedBoundMF q r projectionFloor 7 else 0) else 0) =
        ShapeClimbMono.guardedBoundM q r projectionFloor 1 := by
      simp only [ShapeClimbMono.guardedBoundMF_eq, ShapeClimbMono.guardedBoundM]
      split_ifs <;> first | rfl | omega
    have e2 : (if q + 8 ≤ 2*r then
        (if r ≤ projectionFloor + 1 ∨ q + 8 ≤ 2*r then
          ShapeClimbMono.guardedBoundMF q r projectionFloor 7 else 0) else 0) =
        reachBound32 q r := by
      simp only [reachBound32, ShapeClimbMono.guardedBoundMF_eq]
      split_ifs <;> first | rfl | omega
    simp only [e1, e2, ShapeClimbFast.guardedBoundAtF_eq]

private theorem ite_ne {c : Prop} [Decidable c] {k a : ℕ} (hk : k ≠ 0) (h : a ≠ 0) :
    (if c then k else a) ≠ 0 := by
  split
  · exact hk
  · exact h

/-- Outside `9 ≤ r`, `q < 2r - 6`, rules 1–32 decide every printed cell. -/
theorem base_ne_zero (n r q : ℕ) (hn : n ≤ q*r) (h : ¬(9 ≤ r ∧ q + 6 < 2*r)) :
    ruleBase n r q ≠ 0 := by
  unfold ruleBase ruleWith
  by_cases r8 : r ≤ 8
  · rw [ite_eq_left r8]
    decide
  have pos : 0 < q*r := Nat.mul_pos (by omega) (by omega)
  have top : (2*r-6 < q ∨ (q = 2*r-6 ∧ (11 < r ∨ n < q*r))) ∨
      (9 ≤ r ∧ q = 2*r-6 ∧ 0 < n ∧ n ≤ q*r) := by
    generalize q*r = m at *
    omega
  refine ite_ne (by decide) (ite_ne (by decide) (ite_ne (by decide) ?_))
  rcases top with t | t
  · rw [ite_eq_left t]
    decide
  · refine ite_ne (by decide) (ite_ne (by decide) ?_)
    rw [ite_eq_left t]
    decide

/-- Each printed cell is the rule itself. -/
theorem cell_eq (n r q : ℕ) (hn : n ≤ q*r) :
    cellWith (rowBounds r q).1 (rowBounds r q).2.1 (rowBounds r q).2.2 (rowCollar r q)
      (rowFlat r q) (rowTight r q) (rowThin r q) n r q = rule n r q := by
  unfold cellWith cellsWith rule
  rw [base_eq n r q hn]
  have collar : collarCell (rowCollar r q) n r q = collarCell (CollarRule.collarBound q) n r q := by
    unfold rowCollar collarCell
    by_cases row : r = q + 1
    · simp only [row, ↓reduceIte, CollarRule.collarBoundF_eq]
    · simp only [row, false_and, ↓reduceIte]
  have flat : flatCell (rowFlat r q) n r q = flatCell (FlatRule.flatBound q) n r q := by
    unfold rowFlat flatCell
    by_cases row : r = q
    · simp only [row, ↓reduceIte, FlatRule.flatBoundF_eq]
    · simp only [row, false_and, ↓reduceIte]
  have tight : tightCell (rowTight r q) n r q = tightCell (TightRule2.tightBound2 q) n r q := by
    unfold rowTight tightCell
    rw [TightRule2.tightBound2F_eq]
    split_ifs <;> first | rfl | omega
  rw [collar, flat, tight]
  by_cases w : 9 ≤ r ∧ q + 6 < 2*r
  · have thin : thinCell (rowThin r q) n r q = thinCell (ThinRule.thinBound q r) n r q := by
      unfold rowThin thinCell
      rw [ThinRule.thinBoundF_eq]
      split_ifs <;> first | rfl | omega
    rw [thin]
  · exact firstNZ_cons_of_ne (base_ne_zero n r q hn w) _ _

#print axioms zero_on_bad
#print axioms cell_eq
#eval do
  for r in [1:13] do
    let bounds := (List.range (CH.ceilDiv 275 r + 1)).map (fun q =>
      (rowBounds r q, rowCollar r q, rowFlat r q, rowTight r q, rowThin r q))
    let cells := (List.range 275).map fun i =>
      let q := CH.ceilDiv (i+1) r
      let ((b3, b, b3'), bc, bf, bt, bh) := bounds.getD q ((0, 0, 0), 0, 0, 0, 0)
      let id := cellWith b3 b b3' bc bf bt bh (i+1) r q
      Char.ofNat (if id < 10 then 48 + id else if id < 36 then 55 + id else 61 + id)
    IO.println s!"ROW {r} {String.ofList cells}"
end LeanCH.BR.CoverageMapPreview
