import checkpoints.shen_extension.CoverageRules

namespace LeanCH.BR.CoverageMapPreview
open CoverageRules

/-- Both degree-nine results in the README appear in the generated map. -/
example : rule 34 9 (CH.ceilDiv 34 9) ≠ 0 ∧ rule 35 9 (CH.ceilDiv 35 9) ≠ 0 := by decide

#print axioms zero_on_bad
#eval do
  for r in [1:13] do
    let cells := (List.range 275).map fun i =>
      let id := rule (i+1) r (CH.ceilDiv (i+1) r)
      Char.ofNat (if id < 10 then 48 + id else 55 + id)
    IO.println s!"ROW {r} {String.ofList cells}"
end LeanCH.BR.CoverageMapPreview
