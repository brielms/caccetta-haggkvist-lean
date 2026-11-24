-- leanevolve-block: scratch:sc-induced-subgraph-transport

import LeanCH.BR.CH.Conjecture

namespace CH.Side

/-- Relabelling a duplicate-free bounded list along an injection keeps it
duplicate-free. -/
private theorem sct_nodup_map {m : Nat} {e : Nat → Nat}
    (eInjective : ∀ i j, i < m → j < m → e i = e j → i = j) :
    ∀ l : List Nat, (∀ v, v ∈ l → v < m) → l.Nodup → (l.map e).Nodup := by
  intro l
  induction l with
  | nil => intro _ _; simp
  | cons a t ih =>
      intro bounds nodup
      rw [List.nodup_cons] at nodup
      obtain ⟨notMem, tNodup⟩ := nodup
      rw [List.map_cons, List.nodup_cons]
      refine ⟨?_, ih (fun v hv => bounds v (List.mem_cons_of_mem a hv)) tNodup⟩
      intro mem
      obtain ⟨b, bMem, image⟩ := List.mem_map.mp mem
      have bLt : b < m := bounds b (List.mem_cons_of_mem a bMem)
      have aLt : a < m := bounds a (List.mem_cons_self)
      exact notMem (eInjective b a bLt aLt image ▸ bMem)

/-- The edge chain of a relabelled walk is a walk in the ambient digraph. -/
private theorem sct_edges_map {m : Nat} {G : CH.Digraph} {e : Nat → Nat} :
    ∀ (prev : Nat) (l : List Nat), prev < m → (∀ v, v ∈ l → v < m) →
      CH.EdgesFrom
          (fun a b => if a < m then (if b < m then G (e a) (e b) else false)
            else false) prev l →
      CH.EdgesFrom G (e prev) (l.map e) := by
  intro prev l
  induction l generalizing prev with
  | nil => intro _ _ _; trivial
  | cons c t ih =>
      intro prevLt bounds edges
      obtain ⟨step, rest⟩ := edges
      have cLt : c < m := bounds c List.mem_cons_self
      have step' : (if prev < m then (if c < m then G (e prev) (e c) else false)
          else false) = true := step
      rw [if_pos prevLt, if_pos cLt] at step'
      exact ⟨step', ih c cLt
        (fun v hv => bounds v (List.mem_cons_of_mem c hv)) rest⟩

/--
**Induced-subgraph transport: a short cycle in a relabelled induced subgraph is
a short cycle upstairs.**

Let `e` map `range m` injectively into `range n`, and let

`H a b = if a < m then (if b < m then G (e a) (e b) else false) else false`

be the digraph `G` induces on the image of `e`, re-indexed to `range m`.  Then a
directed cycle of length at most `L` in `H` yields one in `G`.

The witness is the relabelled list `vertices.map e`.  Injectivity carries
`Nodup` across, boundedness of `e` carries the vertex bounds, the edge chain
transports one step at a time, and the closing arc transports because
`List.getLastD` commutes with `List.map`.  Length is preserved by `map`, so the
bound `L` is untouched.

**Why this is the gate.**  The corpus proves Caccetta–Häggkvist for small
degrees — `no_exact_counterexample_degree_at_most_four` covers `r ≤ 4`, and at
`(6,2)` its `ceilDiv 6 2 = 3` is exactly a girth-`≥ 4` contradiction.  But those
theorems speak about a digraph on `range n`, whereas the objects the descent
produces — out-neighbourhoods, `sc_descent_min_outdegree` — are arbitrary
subsets.  Before this block the corpus could only relabel around the removal of
a *single* vertex (`liftLabel`/`lowerLabel`); there was no way to treat an
arbitrary `m`-element subset as a digraph in its own right.  With transport in
hand, any proved small-degree case of the conjecture becomes usable against an
induced subgraph, and in particular against `N⁺(x)`.

**Nonclaims.**  This moves cycles in one direction only — downstairs to
upstairs — which is the direction a contradiction argument needs; it does *not*
say `H` inherits `G`'s girth, and indeed the converse transport is false in
general since `H` forgets every vertex outside the image.  It supplies no `e`:
constructing an injection enumerating a given `Finset` is a separate step.  It
says nothing about degrees — that `H` has any particular out-degree is the
caller's obligation (see `sc_descent_min_outdegree`).  No conjecture case is
proved here; this is infrastructure.
-/
theorem sc_induced_subgraph_transport
    {n m L : Nat} {G : CH.Digraph} {e : Nat → Nat}
    (eBounded : ∀ i, i < m → e i < n)
    (eInjective : ∀ i j, i < m → j < m → e i = e j → i = j)
    (short : CH.HasDirectedCycleAtMost
      (fun a b => if a < m then (if b < m then G (e a) (e b) else false)
        else false) m L) :
    CH.HasDirectedCycleAtMost G n L := by
  obtain ⟨vertices, cycle, len⟩ := short
  refine ⟨vertices.map e, ?_, by simpa using len⟩
  cases vertices with
  | nil => exact cycle.elim
  | cons first rest =>
      obtain ⟨restNe, nodup, bounds, edges, closing⟩ := cycle
      have firstLt : first < m := bounds first List.mem_cons_self
      have restLt : ∀ v, v ∈ rest → v < m :=
        fun v hv => bounds v (List.mem_cons_of_mem first hv)
      rw [List.map_cons]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · -- the tail stays nonempty
        intro empty
        exact restNe (List.map_eq_nil_iff.mp empty)
      · exact sct_nodup_map eInjective (first :: rest) bounds nodup
      · intro v hv
        rw [← List.map_cons] at hv
        obtain ⟨w, wMem, image⟩ := List.mem_map.mp hv
        exact image ▸ eBounded w (bounds w wMem)
      · exact sct_edges_map first rest firstLt restLt edges
      · -- the closing arc, using `getLastD_map`
        rw [List.getLastD_map]
        have lastLt : rest.getLastD first < m :=
          bounds _ List.getLastD_mem_cons
        have closing' : (if rest.getLastD first < m then
            (if first < m then G (e (rest.getLastD first)) (e first) else false)
            else false) = true := closing
        rw [if_pos lastLt, if_pos firstLt] at closing'
        exact closing'

end CH.Side
