module

public import LeanCH.CompromiseTransport

set_option linter.style.header false

/-! Local induced-graph bounds for the next compromise rank. The
small-set CH hypothesis is explicit; no rank-ten conclusion is assumed. -/

open Finset CH.CompromiseSeven
public section

namespace CH.CompromiseTenLocal

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (adj : V → V → Prop) [DecidableRel adj]

@[expose] def SmallOut : Prop := ∀ S : Finset V, S.Nonempty → S.card ≤ 10 →
  ∃ a ∈ S, (outN adj a ∩ S).card ≤ (S.card - 1) / 3

theorem small_of_induction
    (ih : ∀ (S : Finset V) (r : ℕ), S.Nonempty → 1 ≤ r → r < 10 →
      (∀ a ∈ S, r ≤ (outN adj a ∩ S).card) → 3 * r < S.card) : SmallOut adj := by
  intro S hn hs
  have hp := card_pos.mpr hn
  by_contra missing
  have lower (a : V) (ha : a ∈ S) : (S.card - 1) / 3 + 1 ≤ (outN adj a ∩ S).card := by
    have h : ¬ (outN adj a ∩ S).card ≤ (S.card - 1) / 3 := fun h => missing ⟨a, ha, h⟩
    omega
  have contradiction := ih S ((S.card - 1) / 3 + 1) hn (by omega) (by omega) lower
  omega

/-- Only the local out-neighbourhood needs size at most ten; the
containing induced set S can be larger. -/
theorem local_degree_bound (loopless : ∀ v, ¬ adj v v)
    (noDigon : ∀ u v, adj u v → ¬ adj v u)
    (noTri : ∀ u v w, adj u v → adj v w → ¬ adj w u)
    (small : SmallOut adj) (S : Finset V) (r : ℕ) (hr : 1 ≤ r)
    (hmin : ∀ a ∈ S, r ≤ (outN adj a ∩ S).card)
    (v : V) (hv : v ∈ S) (headSize : (outN adj v ∩ S).card ≤ 10) :
    (inN adj v ∩ S).card + (outN adj v ∩ S).card + r + 1 ≤
      S.card + ((outN adj v ∩ S).card - 1) / 3 := by
  let W := outN adj v ∩ S
  have hW : W ⊆ S := inter_subset_right
  have hpos : 0 < W.card := by have := hmin v hv; change 0 < (outN adj v ∩ S).card; omega
  obtain ⟨a, ha, hsmall⟩ := small W (card_pos.mp hpos) headSize
  have hva : adj v a := (mem_outN adj v a).mp (mem_inter.mp ha).1
  have haS : a ∈ S := (mem_inter.mp ha).2
  let I := inN adj v ∩ S
  let D := (outN adj a ∩ S) \ W
  have hI : I ⊆ S := inter_subset_right
  have hD : D ⊆ S := fun x hx => (mem_inter.mp (mem_sdiff.mp hx).1).2
  have hvI : v ∉ I := by simp [I, loopless]
  have hvW : v ∉ W := by simp [W, loopless]
  have hvD : v ∉ D := by
    simp only [D, mem_sdiff, mem_inter, mem_outN]
    exact fun h => noDigon v a hva h.1.1
  have hIW : Disjoint I W := by
    apply disjoint_left.mpr
    intro x hx hx'
    exact noDigon v x ((mem_outN adj v x).mp (mem_inter.mp hx').1)
      ((mem_inN adj v x).mp (mem_inter.mp hx).1)
  have hID : Disjoint I D := by
    apply disjoint_left.mpr
    intro x hx hx'
    exact noTri v a x hva
      ((mem_outN adj a x).mp (mem_inter.mp (mem_sdiff.mp hx').1).1)
      ((mem_inN adj v x).mp (mem_inter.mp hx).1)
  have hWD : Disjoint W D := disjoint_left.mpr (fun _ hx hx' => (mem_sdiff.mp hx').2 hx)
  have hsub : insert v (I ∪ W ∪ D) ⊆ S := by
    intro x hx
    rcases mem_insert.mp hx with rfl | hx
    · exact hv
    rcases mem_union.mp hx with hx | hx
    · rcases mem_union.mp hx with hx | hx
      · exact hI hx
      · exact hW hx
    · exact hD hx
  have hc := card_le_card hsub
  rw [card_insert_of_notMem (by simp [hvI, hvW, hvD]),
    card_union_of_disjoint (disjoint_union_left.mpr ⟨hID, hWD⟩),
    card_union_of_disjoint hIW] at hc
  have hsplit := card_sdiff_add_card_inter (outN adj a ∩ S) W
  have heq : (outN adj a ∩ S) ∩ W = outN adj a ∩ W := by
    ext x
    simp only [mem_inter]
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, hW h.2⟩, h.2⟩⟩
  rw [heq] at hsplit
  have hamin := hmin a haS
  change D.card + (outN adj a ∩ W).card = _ at hsplit
  change I.card + W.card + r + 1 ≤ S.card + (W.card - 1) / 3
  omega

/-- At the tight orders four, seven and ten, the small-set hypothesis
forces both internal degrees to be exactly r. -/
theorem rigid_small (loopless : ∀ v, ¬ adj v v)
    (noDigon : ∀ u v, adj u v → ¬ adj v u)
    (noTri : ∀ u v w, adj u v → adj v w → ¬ adj w u)
    (small : SmallOut adj) (S : Finset V) (r : ℕ) (hr : 1 ≤ r) (rsmall : r ≤ 3)
    (size : S.card = 3 * r + 1) (minimum : ∀ a ∈ S, r ≤ (outN adj a ∩ S).card) :
    ∀ a ∈ S, (outN adj a ∩ S).card = r ∧ (inN adj a ∩ S).card = r := by
  have upper (a : V) (ha : a ∈ S) : (inN adj a ∩ S).card ≤ r := by
    have outBound := card_le_card (inter_subset_right : outN adj a ∩ S ⊆ S)
    have h := local_degree_bound adj loopless noDigon noTri small S r hr minimum a ha (by omega)
    have hm := minimum a ha
    omega
  have count := double_count adj S S
  have lowerSum := sum_le_sum minimum
  have upperSum := sum_le_sum upper
  have outTotal : (∑ a ∈ S, r) = ∑ a ∈ S, (outN adj a ∩ S).card := by omega
  have inTotal : (∑ a ∈ S, (inN adj a ∩ S).card) = ∑ a ∈ S, r := by omega
  intro a ha
  exact ⟨((sum_eq_sum_iff_of_le minimum).mp outTotal a ha).symm,
    (sum_eq_sum_iff_of_le upper).mp inTotal a ha⟩

end CH.CompromiseTenLocal

#print axioms CH.CompromiseTenLocal.small_of_induction
#print axioms CH.CompromiseTenLocal.local_degree_bound
#print axioms CH.CompromiseTenLocal.rigid_small
