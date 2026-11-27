import checkpoints.shen_extension.CleanSwapTransport
import checkpoints.shen_extension.CleanBankTransition

namespace LeanCH.BR.TripleBank
open Finset BRq2 BRq3 BR45

private theorem local_swap_law : LocalSwapStatement := @clean_swap_kernel

/-- Return one of the original three labels. On precisely this new bank,
at least two rows lose two heads, and all short rows miss a selected target. -/
theorem swap_three_parents_to_unit_rows {D : CH.Digraph} {V B P : Finset ℕ} {s c : ℕ}
    (safe : QFree D V 3) (reg : OutEq s D V) (hs : 7 ≤ s) (order : V.card=3*s)
    (no : BypassRepair.NoHost 3 (s-1)) (bv : B ⊆ V) (three : B.card=3) (pv : P ⊆ V)
    (many : 2 ≤ P.card) (common : ∀ b ∈ B, P ⊆ outN D V b) (cap : TripleCap D V P.card)
    (cu : c∈V\B) (hits : (outN D B c).card=3)
    (lone : ∀ v∈V\B, v≠c → (outN D B v).card ≤ 1)
    (menu : (rowMenu D (V\B) P c).card ≤ 1) (miss : ∃ z∈P, D c z≠true)
    (eq3 : (tightParents D (V\B) c (s-1)).card=3) :
    ∃ k∈B, ∃ u∈V\B, let B' := insert u (B.erase k)
      B'⊆V ∧ B'.card=3 ∧ (∀ b∈B', P⊆outN D V b) ∧
      (∀ v∈V\B', (outN D B' v).card ≤ 2) ∧
      (∀ v∈V\B', 2≤(outN D B' v).card → ∃ z∈P, D v z≠true) ∧
      2 ≤ ((V\B').filter (fun v => 2≤(outN D B' v).card)).card :=
  bank_clean_two_hits local_swap_law safe reg hs order no bv three pv many common cap cu hits lone menu miss (Or.inl eq3)

/-- At top order the maximum common target set has a bank with several
short rows or a lone three-hit row with at least four tight parents.
In the latter case each parent is missed by another parent. -/
theorem selected_clean_bank {D : CH.Digraph} {V : Finset ℕ} {s : ℕ}
    (safe : QFree D V 3) (reg : OutEq s D V) (hs : 8≤s) (order : V.card=3*s)
    (no : BypassRepair.NoHost 3 (s-1)) :
    ∃ P ⊆ V, 2 ≤ P.card ∧ TripleCap D V P.card ∧ ∃ B ⊆ V, B.card=3 ∧
      (∀ b∈B, P⊆outN D V b) ∧
      let U := V\B
      let S := U.filter (fun c => 2≤(outN D B c).card)
      (∀ c∈S, ∃ z∈P, D c z≠true) ∧
      (2≤S.card ∨ ∃ c, S={c} ∧ (outN D B c).card=3 ∧ (rowMenu D U P c).card=1 ∧
        4≤(tightParents D U c (s-1)).card ∧ ∀ d∈tightParents D U c (s-1),
          ∃ h∈tightParents D U c (s-1), h≠d ∧ D h d≠true) :=
  select_several_or_four local_swap_law safe reg hs order no

#print axioms swap_three_parents_to_unit_rows
#print axioms selected_clean_bank
end LeanCH.BR.TripleBank
