import checkpoints.shen_extension.CHFamilyWorklist
import checkpoints.shen_extension.HeadSlotRules

namespace LeanCH.BR.HeadSlotRules
open Finset BRq2 BRq3

/-- The registered path rule itself produces the alternatives. After
the left alternative closes, the right one retains the original target labels. -/
theorem reached_labels {D : CH.Digraph} {V A T E : Finset ℕ} {x y r d : ℕ}
    (first : y∈ball D V x r) (choice : y∈A∪T) (targets : T⊆V) (off : y∉T)
    (need : ∀a∈A,E.card+d≤(outN D (T∪E) a).card) :
    d≤(T∩ball D V x (r+1)).card := by
  replay_ch_typed_families
  assumption

#print axioms reached_labels
end LeanCH.BR.HeadSlotRules
