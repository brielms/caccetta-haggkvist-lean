import checkpoints.shen_extension.GuardedFamilyRules
import checkpoints.shen_extension.ChildAncestorPairs
import checkpoints.shen_extension.CutoffCapstoneEntry

namespace LeanCH.BR.GuardedDegreeFrontier
open Finset BRq2 BRq3 BR45 CHRuleCatalog GuardedFamilyRules

def Direct (n q : ℕ) : Prop :=
  (q=5 ∧ 39≤n ∧ n≤40) ∨ (q=6 ∧ 45≤n ∧ n≤48) ∨
  (q=7 ∧ 52≤n ∧ n≤56) ∨ (q=8 ∧ n=64) ∨
  (q=9 ∧ 69≤n ∧ n≤72) ∨ (q=10 ∧ n=80)

def Terminal (n q : ℕ) : Prop :=
  (q=5 ∧ 39≤n ∧ n≤40) ∨ (q=6 ∧ 46≤n ∧ n≤48) ∨
  (q=7 ∧ 52≤n ∧ n≤56) ∨ (q=9 ∧ 69≤n ∧ n≤72)

theorem at_input {n D} (bad : Bad ⟨n,8,D⟩) : Direct n (CH.ceilDiv n 8) := by
  have before := DotDegreeEight.narrowed_eight bad
  have four := forbidden bad guarded_four
  have five := forbidden bad guarded_five
  have no44 : n≠44 := by
    rintro rfl
    exact ParentCutFrontier.excluded 44 D (Or.inr rfl) bad
  change ¬Fits n 8 (CH.ceilDiv n 8) 4 8 32 at four
  change ¬Fits n 8 (CH.ceilDiv n 8) 5 8 38 at five
  unfold Fits at four five
  unfold DotDegreeEight.Narrowed at before
  unfold Direct
  omega

theorem at_recursive_input {n D} (bad : Bad ⟨n,8,D⟩) (reduced : ReducedCutoff n 8)
    (loss : ¬OneLossCutoffDescent.Window n 8 (CH.ceilDiv n 8)) : Terminal n (CH.ceilDiv n 8) := by
  have before := at_input bad
  have upper := reduced.upper
  have parity := reduced.parity
  unfold OneLossCutoffDescent.Window at loss
  unfold Direct at before
  unfold Terminal
  rcases before with h|h|h|h|h|h
  · exact .inl h
  · have excluded : ¬(8≤2*6 ∧ n≤(6/2)*(2*8-1)) := by simpa only [h.1] using loss
    exact .inr (.inl ⟨h.1,by omega,h.2.2⟩)
  · exact .inr (.inr (.inl h))
  · rw [h.1] at parity
    omega
  · exact .inr (.inr (.inr h))
  · rw [h.1] at upper
    omega

@[aesop safe forward (immediate := [source]) (rule_sets := [CHGraphFamilies])]
theorem any_input {p} (source : Bad p) : p.s=8 → Direct p.n (cutoff p) := by
  cases p with
  | mk n r D =>
    intro eq
    change r=8 at eq
    subst r
    exact at_input source

@[aesop safe forward (immediate := [source,reduced,loss]) (rule_sets := [CHGraphFamilies])]
theorem any_recursive_input {p} (source : Bad p) (reduced : ReducedCutoff p.n p.s)
    (loss : ¬OneLossCutoffDescent.Window p.n p.s (cutoff p)) : p.s=8 → Terminal p.n (cutoff p) := by
  cases p with
  | mk n r D =>
    intro eq
    change r=8 at eq
    subst r
    exact at_recursive_input source reduced loss

#print axioms at_input
#print axioms at_recursive_input
end LeanCH.BR.GuardedDegreeFrontier
