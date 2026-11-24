import checkpoints.shen_extension.OneLossCutoffDescent

namespace LeanCH.BR.CHRuleCatalog

structure ReducedCutoff (n s : ℕ) : Prop where
  upper : CH.ceilDiv n s≤2*s-7
  parity : CH.ceilDiv n s%2=1 ∨ CH.ceilDiv n s<s

theorem ReducedCutoff.no_boundary {n s : ℕ} (c : ReducedCutoff n s) (six : 6≤s) :
    CH.ceilDiv n s≠2*s-6 := by
  have := c.upper
  omega

/-- Enter the literal capstone after strict induction on the input's own
cutoff. The degree can change in this induction. -/
theorem reduce_even_cutoffs
    (remaining : ∀ (n s : ℕ) (D : CH.Digraph),0<n → 0<s → CH.Loopless D n →
      CH.MinOutdegreeAtLeast D n s → ReducedCutoff n s →
      CH.HasDirectedCycleAtMost D n (CH.ceilDiv n s)) :
    CH.CaccettaHaggkvistConjecture := by
  apply SATBoundaryPilot.ch_of_odd_or_low
  intro p _ low parity bad
  exact bad.missing (remaining p.n p.s p.D bad.order bad.degree_pos bad.loopless bad.degree ⟨low,parity⟩)

theorem reduce_with_one_loss
    (remaining : ∀ (n s : ℕ) (D : CH.Digraph),0<n → 0<s → CH.Loopless D n →
      CH.MinOutdegreeAtLeast D n s → ReducedCutoff n s →
      ¬OneLossCutoffDescent.Window n s (CH.ceilDiv n s) →
      CH.HasDirectedCycleAtMost D n (CH.ceilDiv n s)) :
    CH.CaccettaHaggkvistConjecture := by
  apply OneLossCutoffDescent.reduce
  intro p _ low parity window bad
  exact bad.missing (remaining p.n p.s p.D bad.order bad.degree_pos bad.loopless bad.degree ⟨low,parity⟩ window)

#print axioms reduce_with_one_loss
#print axioms reduce_even_cutoffs
end LeanCH.BR.CHRuleCatalog
