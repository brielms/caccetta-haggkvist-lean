import LeanCH.BR.Compose.FloorSix

/-!
Boundary regularity (goal set 11 Nov 2026).

`BoundaryRegular q s`: every loopless digraph on `q*s+1` labels with minimum out-degree `s` and no
directed cycle of length at most `q` has every in-degree exactly `s`.

`ch_of_boundaryRegular`: boundary regularity at `(q, s)` gives CH at degree `s` for every order
`n ≤ q*s` (pad a counterexample with sources up to `q*s+1`; a source has in-degree `0 ≠ s`).
-/

namespace Compose.Boundary

open CH Compose.FloorSix

def BoundaryRegular (q s : Nat) : Prop :=
  ∀ G : CH.Digraph, CH.Loopless G (q * s + 1) → CH.MinOutdegreeAtLeast G (q * s + 1) s →
    ¬ CH.HasDirectedCycleAtMost G (q * s + 1) q →
    ∀ v, v < q * s + 1 → (par G (q * s + 1) v).card = s

/-- The padded graph: old labels keep their rows inside `range n`; new labels point to `0, …, s-1`. -/
def pad (G : CH.Digraph) (n s : Nat) : CH.Digraph :=
  fun a b => if a < n then (if b < n then G a b else false) else decide (b < s)

theorem pad_target_lt {G : CH.Digraph} {n s a b : Nat} (hsn : s ≤ n) (h : pad G n s a b = true) : b < n := by
  unfold pad at h
  split at h
  · split at h
    · assumption
    · exact absurd h Bool.false_ne_true
  · have := of_decide_eq_true h; omega

theorem edges_lt {G : CH.Digraph} {n s : Nat} (hsn : s ≤ n) :
    ∀ (prev : Nat) (l : List Nat), CH.EdgesFrom (pad G n s) prev l → ∀ w ∈ l, w < n := by
  intro prev l
  induction l generalizing prev with
  | nil => intro _ w hw; simp at hw
  | cons x rest ih =>
    intro h w hw
    obtain ⟨hx, hrest⟩ := h
    rcases List.mem_cons.mp hw with rfl | hw
    · exact pad_target_lt hsn hx
    · exact ih x hrest w hw

theorem edges_transfer {G : CH.Digraph} {n s : Nat} :
    ∀ (prev : Nat) (l : List Nat), prev < n → (∀ w ∈ l, w < n) →
      CH.EdgesFrom (pad G n s) prev l → CH.EdgesFrom G prev l := by
  intro prev l
  induction l generalizing prev with
  | nil => intros; trivial
  | cons x rest ih =>
    intro hp hall h
    obtain ⟨hx, hrest⟩ := h
    have hxn : x < n := hall x List.mem_cons_self
    refine ⟨?_, ih x hxn (fun w hw => hall w (List.mem_cons_of_mem x hw)) hrest⟩
    simpa [pad, hp, hxn] using hx

theorem ch_of_boundaryRegular {q s n : Nat} (hs : 0 < s) (br : BoundaryRegular q s)
    (hn : 0 < n) (hnq : n ≤ q * s) {G : CH.Digraph}
    (loopless : CH.Loopless G n) (deg : CH.MinOutdegreeAtLeast G n s) :
    CH.HasDirectedCycleAtMost G n q := by
  classical
  by_contra noShort
  -- s < n: vertex 0 has s distinct out-neighbours in range n, none equal to 0
  have hsn : s < n := by
    obtain ⟨nbrs, hlen, hnd, hmem⟩ := deg 0 hn
    have hsub : nbrs.toFinset ⊆ (Finset.range n).erase 0 := by
      intro w hw
      obtain ⟨hwn, hG⟩ := hmem w (List.mem_toFinset.mp hw)
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_range.mpr hwn⟩
      rintro rfl; rw [loopless 0 hn] at hG; exact Bool.false_ne_true hG
    have := Finset.card_le_card hsub
    rw [List.toFinset_card_of_nodup hnd, hlen, Finset.card_erase_of_mem (by simp [hn]),
      Finset.card_range] at this
    omega
  set N := q * s + 1
  have hnN : n < N := by omega
  -- the padded graph is loopless, has minimum out-degree s, and has no short cycle
  have ploop : CH.Loopless (pad G n s) N := by
    intro a ha
    by_cases han : a < n
    · simp [pad, han, loopless a han]
    · simp [pad, han]; omega
  have pdeg : CH.MinOutdegreeAtLeast (pad G n s) N s := by
    intro a ha
    by_cases han : a < n
    · obtain ⟨nbrs, hlen, hnd, hmem⟩ := deg a han
      refine ⟨nbrs, hlen, hnd, fun w hw => ?_⟩
      obtain ⟨hwn, hG⟩ := hmem w hw
      exact ⟨by omega, by simp [pad, han, hwn, hG]⟩
    · refine ⟨List.range s, List.length_range, List.nodup_range, fun w hw => ?_⟩
      have hws : w < s := List.mem_range.mp hw
      exact ⟨by omega, by simp [pad, han, hws]⟩
  have pshort : ¬ CH.HasDirectedCycleAtMost (pad G n s) N q := by
    rintro ⟨l, cyc, len⟩
    apply noShort
    refine ⟨l, ?_, len⟩
    cases l with
    | nil => exact cyc.elim
    | cons first rest =>
      obtain ⟨restNe, nodup, _, edges, closing⟩ := cyc
      have restLt := edges_lt (le_of_lt hsn) first rest edges
      have firstLt : first < n := pad_target_lt (le_of_lt hsn) closing
      have allLt : ∀ w ∈ first :: rest, w < n := by
        intro w hw; rcases List.mem_cons.mp hw with rfl | hw
        · exact firstLt
        · exact restLt w hw
      have lastLt : rest.getLastD first < n := allLt _ List.getLastD_mem_cons
      refine ⟨restNe, nodup, allLt, edges_transfer first rest firstLt restLt edges, ?_⟩
      have c2 : pad G n s (rest.getLastD first) first = true := closing
      unfold pad at c2
      rw [if_pos lastLt, if_pos firstLt] at c2
      exact c2
  -- the new label n has in-degree 0, contradicting regularity
  have hreg := br (pad G n s) ploop pdeg pshort n hnN
  have hzero : par (pad G n s) N n = ∅ := by
    ext u
    simp only [par, Finset.mem_filter, Finset.mem_range, Finset.notMem_empty, iff_false, not_and]
    intro _ h
    exact (lt_irrefl n) (pad_target_lt (le_of_lt hsn) h)
  rw [hzero, Finset.card_empty] at hreg
  omega

end Compose.Boundary
