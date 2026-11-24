import checkpoints.shen_extension.ReceiverColumnBudget

/-!
# The shell fork at an arbitrary root

Let `D` have exact outdegree `d = q t + 1` on `V`, with no directed cycle of
length at most `q`, and let boundary regularity hold at `(q, t)`. Fix any
root `v`. Write `H` for its heads and `Y` for its second shell. Each head
`a` satisfies

    |Y \ N⁺(a)| + d = |Y| + |N⁺(a) ∩ H|.

The head bank has `q t + 1` vertices. So either every head keeps exactly `t`
arcs inside `H` and omits exactly `|Y| + t - d` shell columns, or some head
keeps fewer than `t` and omits fewer columns.

No degree, order or count is fixed. A count of omitted incidences that
exceeds `d (|Y| + t - d)` selects the second alternative. When the shell has
`d + 1 - t` vertices the second alternative is a head that covers the whole
shell.
-/

namespace LeanCH.BR.ShellExcessFork
open Finset BRq2 BRq3 BR45 AvoidedHeadQuota

/-- Either the head bank is internally `t`-regular and all heads omit the
same number of shell columns, or an actual head omits fewer. -/
theorem excess_fork {D : CH.Digraph} {V : Finset ℕ} {q d t v : ℕ} (free : QFree D V q)
    (cut : 2≤q) (vm : v∈V) (reg : OutEq d D V) (mult : d=q*t+1)
    (boundary : Compose.Boundary.BoundaryRegular q t) :
    (∀a∈outN D V v,(outN D (outN D V v) a).card=t ∧
        ((ball D V v 2\ball D V v 1)\outN D V a).card+d=(ball D V v 2\ball D V v 1).card+t) ∨
      (∃a∈outN D V v,(outN D (outN D V v) a).card<t ∧
        ((ball D V v 2\ball D V v 1)\outN D V a).card+d<(ball D V v 2\ball D V v 1).card+t) := by
  classical
  let H:=outN D V v
  let Y:=ball D V v 2\ball D V v 1
  have hv : H⊆V := outN_subset
  have rows a (am : a∈H) : (Y\outN D V a).card+d=Y.card+(outN D H a).card :=
    missing_count free cut vm am (reg a (hv am))
  by_cases all : ∀a∈H,t≤(outN D H a).card
  · have eq := WeightedSD.boundary_regular_out_on_set boundary (free.mono_set hv)
      (fun h hm=>loopfree free (by omega) (hv hm)) ((reg v vm).trans mult) all
    exact Or.inl fun a am=>⟨eq a am,by have := rows a am; rw [eq a am] at this; exact this⟩
  · push Not at all
    obtain ⟨a,am,short⟩ := all
    have row := rows a am
    exact Or.inr ⟨a,am,short,(show (Y\outN D V a).card+d<Y.card+t by omega)⟩

/-- More omitted incidences than the regular alternative allows force a
head with fewer than `t` arcs inside the head bank. -/
theorem light_of_omissions {D : CH.Digraph} {V : Finset ℕ} {q d t v : ℕ} (free : QFree D V q)
    (cut : 2≤q) (vm : v∈V) (reg : OutEq d D V) (mult : d=q*t+1)
    (boundary : Compose.Boundary.BoundaryRegular q t)
    (excess : d*((ball D V v 2\ball D V v 1).card+t-d) <
      ∑a∈outN D V v,((ball D V v 2\ball D V v 1)\outN D V a).card) :
    ∃a∈outN D V v,(outN D (outN D V v) a).card<t := by
  obtain flat|⟨a,am,short,_⟩ := excess_fork free cut vm reg mult boundary
  · exfalso
    have each a (am : a∈outN D V v) : ((ball D V v 2\ball D V v 1)\outN D V a).card =
        (ball D V v 2\ball D V v 1).card+t-d := by have := (flat a am).2; omega
    rw [sum_const_nat each,reg v vm] at excess
    exact lt_irrefl _ excess
  · exact ⟨a,am,short⟩

/-- A shell of `d + 1 - t` vertices. Either every head omits exactly one
shell column, or an actual head covers the whole shell. That head keeps
exactly `t - 1` arcs inside the head bank. -/
theorem unit_shell_fork {D : CH.Digraph} {V : Finset ℕ} {q d t v : ℕ} (free : QFree D V q)
    (cut : 2≤q) (vm : v∈V) (reg : OutEq d D V) (mult : d=q*t+1)
    (boundary : Compose.Boundary.BoundaryRegular q t)
    (one : (ball D V v 2\ball D V v 1).card+t=d+1) :
    (∀a∈outN D V v,(outN D (outN D V v) a).card=t ∧
        ((ball D V v 2\ball D V v 1)\outN D V a).card=1) ∨
      (∃g∈outN D V v,(ball D V v 2\ball D V v 1)⊆outN D V g ∧
        (outN D (outN D V v) g).card+1=t) := by
  classical
  obtain flat|⟨g,gm,short,few⟩ := excess_fork free cut vm reg mult boundary
  · exact Or.inl fun a am=>⟨(flat a am).1,by have := (flat a am).2; omega⟩
  · have row := missing_count free cut vm gm (reg g (outN_subset gm))
    have empty : ((ball D V v 2\ball D V v 1)\outN D V g).card=0 := by omega
    exact Or.inr ⟨g,gm,sdiff_eq_empty_iff_subset.mp (card_eq_zero.mp empty),by omega⟩

attribute [aesop safe forward (immediate := [free,cut,vm,reg,mult,boundary,one])
  (rule_sets := [CHGraphFamilies])] unit_shell_fork
ch_family_split_result unit_shell_fork

#print axioms excess_fork
#print axioms light_of_omissions
#print axioms unit_shell_fork
end LeanCH.BR.ShellExcessFork
