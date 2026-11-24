-- leanevolve-block: scratch:sc-finset-enumeration

import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Range
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.GetD

namespace CH.Side

/--
**Any vertex set is the injective image of an initial segment.**

For `S ⊆ range n` there is an `e : Nat → Nat` which is bounded by `n`,
injective on `range S.card`, lands in `S`, and hits every element of `S`.

The witness is the sorted enumeration `fun i => (S.sort (· ≤ ·)).getD i 0`.
Sorting gives a duplicate-free list of length `S.card` whose members are exactly
`S`, so `List.getD_inj` supplies injectivity and `List.mem_iff_getElem`
surjectivity.

This is the last link in the descent chain.  `sc_induced_subgraph_transport`
carries a short cycle from a relabelled induced subgraph back to the ambient
digraph, but supplies no relabelling; this supplies one for an arbitrary vertex
set.  Together with `sc_descent_min_outdegree` — which gives the minimum
out-degree the digraph induced on `N⁺(x)` retains — the out-neighbourhood of a
vertex can now be presented as a Caccetta–Häggkvist instance in its own right,
which is what lets the corpus's proved small-degree cases bear on it.

**Nonclaims.**  Pure combinatorics of finite sets: no digraph, no girth, no
degree, and no case of any conjecture.  The enumeration is the sorted one, so it
is order-preserving, but nothing here states or uses that.  It gives a function
on all of `Nat`; only its restriction below `S.card` is constrained, and its
values elsewhere are junk.
-/
theorem sc_finset_enumeration
    {n : Nat} {S : Finset Nat} (contained : S ⊆ Finset.range n) :
    ∃ e : Nat → Nat,
      (∀ i, i < S.card → e i < n)
        ∧ (∀ i j, i < S.card → j < S.card → e i = e j → i = j)
        ∧ (∀ i, i < S.card → e i ∈ S)
        ∧ (∀ v, v ∈ S → ∃ i, i < S.card ∧ e i = v) := by
  classical
  have lengthEq : (S.sort (· ≤ ·)).length = S.card := Finset.length_sort _
  have nodup : (S.sort (· ≤ ·)).Nodup := Finset.sort_nodup _ _
  have intoS : ∀ i, i < S.card → (S.sort (· ≤ ·)).getD i 0 ∈ S := by
    intro i hi
    have hi' : i < (S.sort (· ≤ ·)).length := by rw [lengthEq]; exact hi
    rw [List.getD_eq_getElem _ _ hi']
    exact (Finset.mem_sort _).mp (List.getElem_mem hi')
  refine ⟨fun i => (S.sort (· ≤ ·)).getD i 0, ?_, ?_, intoS, ?_⟩
  · intro i hi
    exact Finset.mem_range.mp (contained (intoS i hi))
  · intro i j hi hj image
    have hi' : i < (S.sort (· ≤ ·)).length := by rw [lengthEq]; exact hi
    have hj' : j < (S.sort (· ≤ ·)).length := by rw [lengthEq]; exact hj
    exact (List.getD_inj hi' hj' nodup).mp image
  · intro v hv
    have mem : v ∈ S.sort (· ≤ ·) := (Finset.mem_sort _).mpr hv
    obtain ⟨i, hi, image⟩ := List.mem_iff_getElem.mp mem
    refine ⟨i, by rw [← lengthEq]; exact hi, ?_⟩
    show (S.sort (· ≤ ·)).getD i 0 = v
    rw [List.getD_eq_getElem _ _ hi]
    exact image

end CH.Side
