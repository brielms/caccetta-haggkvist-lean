import checkpoints.shen_extension.CHFamilyWorklist
import checkpoints.shen_extension.TallBankTransferBudget

namespace LeanCH.BR.TallBankTransfer

open Finset BRq2 BRq3

/-- A missing physical pair is reusable without opening a new family. -/
@[aesop safe forward (immediate := [free,reg,lo,fit,hu,hv,ne,same])
  (rule_sets := [CHGraphFamilies])]
theorem no_reach_between_equal_layers {D V q k r u v}
    (free : QFree D V q) (reg : OutEq r D V) (lo : 2 ≤ k) (fit : k ≤ q)
    (hu : u ∈ V) (hv : v ∈ V) (ne : u ≠ v)
    (same : ball D V u 2 \ ball D V u 1 = ball D V v 2 \ ball D V v 1) :
    v ∉ ball D V u k :=
  (same_second_layer_incomparable free reg lo fit hu hv ne same).1

/-- Keep the path selected at the actual strong sink, with its marks. -/
@[aesop safe forward (immediate := [free,diag,room,reg,hu,ha,sink,unique,two,third,strong])
  (rule_sets := [CHGraphFamilies])]
theorem selected_sink_bank {D V q r u a}
    (free : QFree D V q) (diag : r ≤ q) (room : 4 ≤ r) (reg : OutEq r D V)
    (hu : u ∈ V) (ha : a ∈ outN D V u)
    (sink : ∀ z ∈ outN D V u, D a z ≠ true)
    (unique : ∀ z ∈ outN D V u, (∀ x ∈ outN D V u, D z x ≠ true) → z = a)
    (two : (ball D V u 2).card = 2 * r + 2)
    (third : (ball D V u 3 \ ball D V u 2).card < r)
    (strong : 2 * r + 2 ≤ (ball D V a 2).card) :
    ∃ bank : SinkBank D V u a r, bank.start ∈ outN D V u := by
  obtain ⟨_,x,hx,p,length,last,support,childBall⟩ :=
    unique_sink_geometry free diag room reg hu ha sink unique two third strong
  exact ⟨⟨x,p,length,last,support,childBall⟩,hx⟩

ch_family_split_result selected_sink_bank

attribute [aesop safe forward
  (immediate := [free,lo,fit,reg,order,positive,floor,tall,fibres,gain,tail])
  (rule_sets := [CHGraphFamilies])] no_balanced_child_cover

#print axioms no_reach_between_equal_layers
#print axioms selected_sink_bank
#print axioms no_balanced_child_cover
end LeanCH.BR.TallBankTransfer
