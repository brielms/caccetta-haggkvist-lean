import checkpoints.shen_extension.ReceiverOneCoverReplay

namespace LeanCH.BR.CoverageContradictions
open Finset BRq3

/-- Numerically incompatible bounds on the same quantity close a family.
Both terms are retained by the matching index, including vertex labels. -/
@[aesop safe forward (immediate := [upper,overrun]) (rule_sets := [CHGraphFamilies])]
theorem exceeded {a d : ℕ} (upper : a≤d) (overrun : d<a) : False :=
  Nat.not_lt_of_ge upper overrun

/-- Any asserted common cover is impossible if each proposed covering
row misses its own actual column. The missed columns can differ. -/
@[aesop safe forward (immediate := [cover,live,miss]) (rule_sets := [CHGraphFamilies])]
theorem uncovered {D : CH.Digraph} {H F B : Finset ℕ}
    (cover : B.Nonempty → ∃g∈F,B⊆outN D H g)
    (live : B.Nonempty) (miss : ∀g∈F,∃b∈B,D g b≠true) : False := by
  obtain ⟨g,gm,full⟩ := cover live
  obtain ⟨b,bm,off⟩ := miss g gm
  exact off (mem_outN.mp (full bm)).2

ch_family_split_result LabelledCompromiseRecipe.bank_ceiling
#print axioms exceeded
#print axioms uncovered
end LeanCH.BR.CoverageContradictions
