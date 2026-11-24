-- leanevolve-block: scratch:sc-two-hit-free-set-descends

import LeanCH.BR.CH.Conjecture
import LeanCH.BR.CH.Side.ScFinsetEnumeration
import LeanCH.BR.CH.Side.ScInducedSubgraphTransport
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Range
import Mathlib.Data.Finset.SDiff

namespace CH.Side

/--
Every list of members of `C` is the `e`-image of a bounded list, where `e`
enumerates `C` from below `m`. The preimage list inherits `Nodup` from the
original via `List.Nodup.of_map` at the call site.
-/
private theorem sc2h_preimage_list {C : Finset Nat} {e : Nat → Nat} {m : Nat}
    (surj : ∀ v, v ∈ C → ∃ i, i < m ∧ e i = v) :
    ∀ l : List Nat, (∀ w, w ∈ l → w ∈ C) →
      ∃ l' : List Nat, l'.map e = l ∧ ∀ i, i ∈ l' → i < m := by
  intro l
  induction l with
  | nil =>
      intro _
      exact ⟨[], rfl, fun i hi => by simp at hi⟩
  | cons a t ih =>
      intro hmem
      obtain ⟨i, hi, hei⟩ := surj a (hmem a List.mem_cons_self)
      obtain ⟨t', ht', htm⟩ :=
        ih (fun w hw => hmem w (List.mem_cons_of_mem a hw))
      refine ⟨i :: t', by rw [List.map_cons, hei, ht'], ?_⟩
      intro j hj
      rcases List.mem_cons.mp hj with rfl | hjt
      · exact hi
      · exact htm j hjt

/--
**Deleting a two-hit-free vertex set lowers the minimum out-degree by at most
one and reflects short cycles — at every set size.**

Let `S ⊆ range n` be a vertex set such that no vertex outside `S` sends arcs
to two distinct members of `S`. Deleting `S` (realised by pulling the edge
relation back along the sorted enumeration of the surviving labels) leaves a
graph of order `n - S.card` that is loopless, has minimum out-degree `r - 1`
— each survivor's out-neighbours meet `S` in at most one vertex — and whose
directed cycles at any bound are directed cycles of `G` at the same bound.

This is the k-set deletion engine: the generalisation of
`d3_two_hit_free_triple_descends` from `q = 3` to arbitrary `q`, the missing
machinery named by the §C campaign. At `S.card = q` and band order
`n ≤ q * r` it trades `q` vertices for one unit of degree, so the band
inequality descends to `n - q ≤ q * (r - 1)`: the same exact exchange that
carried the ratio-3 window now moves every ratio window `q ≥ 4`.

The construction routes through the shelf named for it:
`sc_finset_enumeration` supplies the sorted enumeration of
`range n \ S`, and the child is built in exactly the guarded induced-subgraph
shape of `sc_induced_subgraph_transport`, so cycle reflection is that theorem
applied verbatim. Vertices inside `S` may point at each other, and at
outsiders, freely; only arcs INTO `S` from outside are constrained, and only
in pairs.
-/
theorem sc_two_hit_free_set_descends
    {G : CH.Digraph} {n r : Nat} {S : Finset Nat}
    (hsub : S ⊆ Finset.range n)
    (loopless : CH.Loopless G n)
    (deg : CH.MinOutdegreeAtLeast G n r)
    (hit : ∀ v, v < n → v ∉ S →
      ∀ s₁, s₁ ∈ S → ∀ s₂, s₂ ∈ S → s₁ ≠ s₂ →
        ¬(G v s₁ = true ∧ G v s₂ = true)) :
    ∃ H : CH.Digraph,
      CH.Loopless H (n - S.card) ∧
      CH.MinOutdegreeAtLeast H (n - S.card) (r - 1) ∧
      (∀ bound, CH.HasDirectedCycleAtMost H (n - S.card) bound →
        CH.HasDirectedCycleAtMost G n bound) := by
  classical
  obtain ⟨e, eBounded, eInj, eMem, eSurj⟩ :=
    sc_finset_enumeration (S := Finset.range n \ S)
      (Finset.sdiff_subset)
  have hcard : (Finset.range n \ S).card = n - S.card := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hsub, Finset.card_range]
  rw [hcard] at eBounded eInj eMem eSurj
  refine ⟨fun a b =>
    if a < n - S.card then
      (if b < n - S.card then G (e a) (e b) else false)
    else false, ?_, ?_, ?_⟩
  · -- looplessness survives deletion
    intro v hv
    show (if v < n - S.card then
      (if v < n - S.card then G (e v) (e v) else false) else false) = false
    rw [if_pos hv, if_pos hv]
    exact loopless (e v) (eBounded v hv)
  · -- each survivor keeps r - 1 out-neighbours
    intro a ha
    have haN : e a < n := eBounded a ha
    have haS : e a ∉ S := (Finset.mem_sdiff.mp (eMem a ha)).2
    obtain ⟨nbrs, hlen, hnodup, hmem⟩ := deg (e a) haN
    -- the survivors of the neighbour list, in the complement of S
    by_cases hcase : ∃ b, b ∈ nbrs ∧ b ∈ S
    · -- one neighbour lies in S; two-hit-freeness makes it unique — erase it
      obtain ⟨b, hb, hbS⟩ := hcase
      have hsurv : ∀ w, w ∈ nbrs.erase b → w ∈ Finset.range n \ S := by
        intro w hw
        obtain ⟨hwb, hwm⟩ := (List.Nodup.mem_erase_iff hnodup).mp hw
        refine Finset.mem_sdiff.mpr
          ⟨Finset.mem_range.mpr (hmem w hwm).1, fun hwS => ?_⟩
        exact hit (e a) haN haS w hwS b hbS hwb
          ⟨(hmem w hwm).2, (hmem b hb).2⟩
      obtain ⟨l', hl'map, hl'lt⟩ :=
        sc2h_preimage_list eSurj (nbrs.erase b) hsurv
      have hl'nodup : l'.Nodup := by
        refine List.Nodup.of_map e ?_
        rw [hl'map]
        exact hnodup.erase b
      refine ⟨l', ?_, hl'nodup, ?_⟩
      · have hlen' := congrArg List.length hl'map
        rw [List.length_map, List.length_erase_of_mem hb, hlen] at hlen'
        exact hlen'
      · intro i hi
        refine ⟨hl'lt i hi, ?_⟩
        show (if a < n - S.card then
          (if i < n - S.card then G (e a) (e i) else false) else false) = true
        rw [if_pos ha, if_pos (hl'lt i hi)]
        have hei : e i ∈ nbrs.erase b := by
          rw [← hl'map]
          exact List.mem_map_of_mem hi
        exact (hmem (e i) (List.mem_of_mem_erase hei)).2
    · -- no neighbour lies in S; drop one to reach length r - 1
      have hnone : ∀ w, w ∈ nbrs → w ∉ S :=
        fun w hw hwS => hcase ⟨w, hw, hwS⟩
      have hsurv : ∀ w, w ∈ nbrs.drop 1 → w ∈ Finset.range n \ S := by
        intro w hw
        have hwm : w ∈ nbrs := (List.drop_sublist 1 nbrs).subset hw
        exact Finset.mem_sdiff.mpr
          ⟨Finset.mem_range.mpr (hmem w hwm).1, hnone w hwm⟩
      obtain ⟨l', hl'map, hl'lt⟩ :=
        sc2h_preimage_list eSurj (nbrs.drop 1) hsurv
      have hl'nodup : l'.Nodup := by
        refine List.Nodup.of_map e ?_
        rw [hl'map]
        exact (List.drop_sublist 1 nbrs).nodup hnodup
      refine ⟨l', ?_, hl'nodup, ?_⟩
      · have hlen' := congrArg List.length hl'map
        rw [List.length_map, List.length_drop, hlen] at hlen'
        exact hlen'
      · intro i hi
        refine ⟨hl'lt i hi, ?_⟩
        show (if a < n - S.card then
          (if i < n - S.card then G (e a) (e i) else false) else false) = true
        rw [if_pos ha, if_pos (hl'lt i hi)]
        have hei : e i ∈ nbrs.drop 1 := by
          rw [← hl'map]
          exact List.mem_map_of_mem hi
        exact (hmem (e i) ((List.drop_sublist 1 nbrs).subset hei)).2
  · -- cycles reflect upstairs: exactly the transport theorem
    intro bound hcyc
    exact sc_induced_subgraph_transport eBounded eInj hcyc

end CH.Side
