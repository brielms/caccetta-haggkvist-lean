import LeanCH.BR.ModuleSize
import LeanCH.BR.Compose.ThinRigid

/-!
# Weak degree cap (q = 3), Lean 4.35.0

Let `n = 3s+1`, `G` loopless on `n` labels with minimum out-degree `s ≥ 1` and no directed cycle of length
at most three, and assume `BoundaryRegular 3 t` for every `1 ≤ t < s`. A vertex `v` with in-degree `s+a`
(`a ≥ 0`) and out-degree `s+f` satisfies `3a + 2f + 1 ≤ s`.

Proof. Let `K = range n \ ({v} ∪ I(v))`, so `|K| = 3s - (s+a)` and `O(v) ⊆ K` (no digon). An out-neighbour `x`
of `v` heads neither `v` (digon) nor a member of `I(v)` (triangle), so its heads lie in `K`; at most
`|K \ O(v)| = s - a - f` of them leave `O(v)`, so `x` keeps `r = a + f` heads inside `O(v)`.
* `r = 0`: trivial.
* `1 ≤ r < s`: `module_size` with `M = O(v)`, `c = r` gives `3r + 1 ≤ s + f`.
* `r = s`: `O(v)` is digon-free with every vertex keeping `s` heads, so `2s + 1 ≤ |O(v)| = 3s - (s+a) ≤ 2s`.
-/

namespace LeanCH.BR.WeakCap

open CH Compose.Boundary Compose.FloorSix

/-- **Digon bound.** A set in a loopless digon-free graph where every member keeps `c` out-neighbours
inside the set has at least `2c + 1` members (each member sees at most `|M| - 1` others in either direction). -/
theorem digon_bound {G : CH.Digraph} {n c : Nat} {M : Finset Nat} (hsub : M ⊆ Finset.range n)
    (hne : 0 < M.card) (loopless : CH.Loopless G n) (noShort : ¬ CH.HasDirectedCycleAtMost G n 3)
    (keep : ∀ x ∈ M, c ≤ (M.filter (fun w => G x w = true)).card) :
    2 * c + 1 ≤ M.card := by
  classical
  have hloc : ∀ x ∈ M, (M.filter (fun w => G x w = true)).card + (M.filter (fun u => G u x = true)).card
      ≤ M.card - 1 := by
    intro x hx
    have hxn : x < n := Finset.mem_range.mp (hsub hx)
    have hsub' : M.filter (fun w => G x w = true) ∪ M.filter (fun u => G u x = true) ⊆ M.erase x := by
      intro w hw
      rcases Finset.mem_union.mp hw with hw | hw
      · obtain ⟨hwM, hG⟩ := Finset.mem_filter.mp hw
        refine Finset.mem_erase.mpr ⟨?_, hwM⟩
        intro hwx; rw [hwx, loopless x hxn] at hG; exact Bool.false_ne_true hG
      · obtain ⟨hwM, hG⟩ := Finset.mem_filter.mp hw
        refine Finset.mem_erase.mpr ⟨?_, hwM⟩
        intro hwx; rw [hwx, loopless x hxn] at hG; exact Bool.false_ne_true hG
    have hdisj : M.filter (fun w => G x w = true) ∩ M.filter (fun u => G u x = true) = ∅ := by
      refine Finset.eq_empty_of_forall_notMem (fun w hw => ?_)
      obtain ⟨hw1, hw2⟩ := Finset.mem_inter.mp hw
      obtain ⟨hwM, h1⟩ := Finset.mem_filter.mp hw1
      exact no2 loopless noShort hxn (Finset.mem_range.mp (hsub hwM)) h1 (Finset.mem_filter.mp hw2).2
    have h1 := Finset.card_union_add_card_inter (M.filter (fun w => G x w = true))
      (M.filter (fun u => G u x = true))
    rw [hdisj, Finset.card_empty] at h1
    have h2 := Finset.card_le_card hsub'
    rw [Finset.card_erase_of_mem hx] at h2
    omega
  have hsum := Finset.sum_le_sum hloc
  rw [Finset.sum_add_distrib, ← Compose.ThinRigid.sum_out_eq_sum_in G M] at hsum
  have hlow : ∑ _x ∈ M, c ≤ ∑ x ∈ M, (M.filter (fun w => G x w = true)).card := Finset.sum_le_sum keep
  rw [Finset.sum_const_nat (fun _ _ => rfl)] at hsum hlow
  have hmul : M.card * (2 * c) ≤ M.card * (M.card - 1) := by
    rw [Nat.two_mul, Nat.mul_add]; omega
  have := Nat.le_of_mul_le_mul_left hmul hne
  omega

/-- Out-neighbours of `v` among the labels below `n`. -/
def outs (G : CH.Digraph) (n v : Nat) : Finset Nat := (Finset.range n).filter (fun w => G v w = true)

/-- **Weak degree cap (q = 3), core form** over an order `n = 3s+1` given as a hypothesis. -/
theorem weak_cap_core {G : CH.Digraph} {n s v : Nat} (hN : n = 3 * s + 1) (hs : 0 < s)
    (brs : ∀ t, 1 ≤ t → t < s → BoundaryRegular 3 t)
    (loopless : CH.Loopless G n) (deg : CH.MinOutdegreeAtLeast G n s)
    (noShort : ¬ CH.HasDirectedCycleAtMost G n 3) (hv : v < n)
    (hin : s ≤ (par G n v).card) :
    3 * ((par G n v).card - s) + 2 * ((outs G n v).card - s) + 1 ≤ s := by
  classical
  have ho_ge : s ≤ (outs G n v).card := out_card deg hv
  -- K: labels other than v and its in-neighbours
  have hvI : v ∉ par G n v := by simp [par, loopless v hv]
  have hIsub : insert v (par G n v) ⊆ Finset.range n := by
    intro u hu
    rcases Finset.mem_insert.mp hu with huv | hu
    · rw [huv]; exact Finset.mem_range.mpr hv
    · exact (Finset.mem_filter.mp hu).1
  have hKcard : (Finset.range n \ insert v (par G n v)).card = n - ((par G n v).card + 1) := by
    rw [Finset.card_sdiff_of_subset hIsub, Finset.card_range, Finset.card_insert_of_notMem hvI]
  have hOK : outs G n v ⊆ Finset.range n \ insert v (par G n v) := by
    intro w hw
    obtain ⟨hwn, hG⟩ := Finset.mem_filter.mp hw
    refine Finset.mem_sdiff.mpr ⟨hwn, ?_⟩
    intro hwI
    rcases Finset.mem_insert.mp hwI with hwv | hwI
    · rw [hwv, loopless v hv] at hG; exact Bool.false_ne_true hG
    · exact no2 loopless noShort hv (Finset.mem_range.mp hwn) hG (Finset.mem_filter.mp hwI).2
  have hoK := Finset.card_le_card hOK
  rw [hKcard] at hoK
  have hOsub : outs G n v ⊆ Finset.range n := Finset.filter_subset _ _
  -- every out-neighbour of v keeps i + o - 2s out-neighbours inside O(v)
  have keep : ∀ x ∈ outs G n v,
      (par G n v).card + (outs G n v).card - 2 * s ≤
        ((outs G n v).filter (fun w => G x w = true)).card := by
    intro x hx
    obtain ⟨hxn', hvx⟩ := Finset.mem_filter.mp hx
    have hxn := Finset.mem_range.mp hxn'
    have hsplit : (Finset.range n).filter (fun w => G x w = true) ⊆
        (outs G n v).filter (fun w => G x w = true) ∪
          ((Finset.range n \ insert v (par G n v)) \ outs G n v) := by
      intro w hw
      obtain ⟨hwn', hxw⟩ := Finset.mem_filter.mp hw
      have hwn := Finset.mem_range.mp hwn'
      by_cases hwO : w ∈ outs G n v
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hwO, hxw⟩)
      · refine Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨hwn', ?_⟩, hwO⟩)
        intro hwI
        rcases Finset.mem_insert.mp hwI with hwv | hwI
        · rw [hwv] at hxw; exact no2 loopless noShort hv hxn hvx hxw
        · exact no3 loopless noShort hv hxn hwn hvx hxw (Finset.mem_filter.mp hwI).2
    have hle := (Finset.card_le_card hsplit).trans (Finset.card_union_le _ _)
    rw [Finset.card_sdiff_of_subset hOK, hKcard] at hle
    have hout := out_card deg hxn
    omega
  have hne : 0 < (outs G n v).card := by omega
  by_cases h0 : (par G n v).card + (outs G n v).card - 2 * s = 0
  · omega
  by_cases hlt : (par G n v).card + (outs G n v).card - 2 * s < s
  · -- 1 ≤ r < s: Lemma A on O(v)
    have hc : 0 < (par G n v).card + (outs G n v).card - 2 * s := by
      omega
    have := LeanCH.BR.ModuleSize.module_size (q := 3) hc (brs _ hc hlt) hOsub hne loopless noShort keep
    omega
  · -- r = s: O(v) is digon-free, every member keeps s heads, and |O(v)| ≤ 2s
    have keep' : ∀ x ∈ outs G n v,
        s ≤ ((outs G n v).filter (fun w => G x w = true)).card := by
      intro x hx; have := keep x hx; omega
    have := digon_bound hOsub hne loopless noShort keep'
    omega

/-- **Weak degree cap (q = 3).** On `3s+1` labels, with BR(3,t) for all `1 ≤ t < s`, a vertex of in-degree
`s + a ≥ s` and out-degree `s + f` has `3a + 2f + 1 ≤ s`. -/
theorem weak_cap {G : CH.Digraph} {s v : Nat} (hs : 0 < s)
    (brs : ∀ t, 1 ≤ t → t < s → BoundaryRegular 3 t)
    (loopless : CH.Loopless G (3 * s + 1)) (deg : CH.MinOutdegreeAtLeast G (3 * s + 1) s)
    (noShort : ¬ CH.HasDirectedCycleAtMost G (3 * s + 1) 3) (hv : v < 3 * s + 1)
    (hin : s ≤ (par G (3 * s + 1) v).card) :
    3 * ((par G (3 * s + 1) v).card - s) +
      2 * (((Finset.range (3 * s + 1)).filter (fun w => G v w = true)).card - s) + 1 ≤ s :=
  weak_cap_core rfl hs brs loopless deg noShort hv hin

end LeanCH.BR.WeakCap
