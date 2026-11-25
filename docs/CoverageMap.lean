import checkpoints.shen_extension.CoverageRules
import checkpoints.shen_extension.ShapeClimbMono
import checkpoints.shen_extension.CollarRule
import checkpoints.shen_extension.FlatRule

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

/-- A printed cell: rules 1–32 with the row's climb bounds, else the collar rule, else the
flat rule. -/
def cellWith (b3 b b3' b4 b5 n r q : ℕ) : ℕ :=
  if ruleWith b3 b b3' n r q ≠ 0 then ruleWith b3 b b3' n r q
  else if collarCell b4 n r q ≠ 0 then collarCell b4 n r q
  else flatCell b5 n r q

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

/-- Each printed cell is the rule itself. -/
theorem cell_eq (n r q : ℕ) (hn : n ≤ q*r) :
    cellWith (rowBounds r q).1 (rowBounds r q).2.1 (rowBounds r q).2.2 (rowCollar r q)
      (rowFlat r q) n r q = rule n r q := by
  unfold cellWith rule
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
  rw [collar, flat]

#print axioms zero_on_bad
#print axioms cell_eq
#eval do
  for r in [1:13] do
    let bounds := (List.range (CH.ceilDiv 275 r + 1)).map (fun q => (rowBounds r q, rowCollar r q, rowFlat r q))
    let cells := (List.range 275).map fun i =>
      let q := CH.ceilDiv (i+1) r
      let ((b3, b, b3'), b4, b5) := bounds.getD q ((0, 0, 0), 0, 0)
      let id := cellWith b3 b b3' b4 b5 (i+1) r q
      Char.ofNat (if id < 10 then 48 + id else 55 + id)
    IO.println s!"ROW {r} {String.ofList cells}"
end LeanCH.BR.CoverageMapPreview
