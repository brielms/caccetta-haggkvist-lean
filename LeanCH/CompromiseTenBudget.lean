module

public import LeanCH.CompromiseTenLocal
public import LeanCH.CompromiseNineLocal

set_option linter.style.header false

/-! The internal edge budget for a ten-vertex induced set of minimum
out-degree two. Both small-set CH directions are explicit hypotheses. -/

open Finset CH.CompromiseSeven CH.CompromiseTenLocal
public section

namespace CH.CompromiseTenBudget

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (adj : V → V → Prop) [DecidableRel adj]

/-- Retain the degree of the selected head instead of replacing it by
the minimum degree of the whole induced set. -/
theorem selected_head_bound (loopless : ∀ v, ¬ adj v v)
    (noDigon : ∀ u v, adj u v → ¬ adj v u)
    (noTri : ∀ u v w, adj u v → adj v w → ¬ adj w u)
    (small : SmallOut adj) (S : Finset V) (v : V) (hv : v ∈ S)
    (positive : 0 < (outN adj v ∩ S).card) (size : (outN adj v ∩ S).card ≤ 10) :
    ∃ a ∈ outN adj v ∩ S,
      (inN adj v ∩ S).card + (outN adj v ∩ S).card +
        (outN adj a ∩ S).card + 1 ≤
          S.card + ((outN adj v ∩ S).card - 1) / 3 := by
  let W := outN adj v ∩ S
  obtain ⟨a, ha, low⟩ := small W (card_pos.mp positive) size
  refine ⟨a, ha, ?_⟩
  have edge : adj v a := (mem_outN adj v a).mp (mem_inter.mp ha).1
  let I := inN adj v ∩ S
  let D := (outN adj a ∩ S) \ W
  have vI : v ∉ I := by simp [I, loopless]
  have vW : v ∉ W := by simp [W, loopless]
  have vD : v ∉ D := by
    intro h
    exact noDigon v a edge ((mem_outN adj a v).mp (mem_inter.mp (mem_sdiff.mp h).1).1)
  have iw : Disjoint I W := by
    apply disjoint_left.mpr
    intro x hx hx'
    exact noDigon v x ((mem_outN adj v x).mp (mem_inter.mp hx').1)
      ((mem_inN adj v x).mp (mem_inter.mp hx).1)
  have id : Disjoint I D := by
    apply disjoint_left.mpr
    intro x hx hx'
    exact noTri v a x edge
      ((mem_outN adj a x).mp (mem_inter.mp (mem_sdiff.mp hx').1).1)
      ((mem_inN adj v x).mp (mem_inter.mp hx).1)
  have wd : Disjoint W D := disjoint_left.mpr (fun _ hx hx' => (mem_sdiff.mp hx').2 hx)
  have subset : insert v (I ∪ W ∪ D) ⊆ S :=
    insert_subset hv (union_subset (union_subset inter_subset_right inter_subset_right)
      (sdiff_subset.trans inter_subset_right))
  have count := card_le_card subset
  rw [card_insert_of_notMem (by simp [vI, vW, vD]),
    card_union_of_disjoint (disjoint_union_left.mpr ⟨id, wd⟩),
    card_union_of_disjoint iw] at count
  have split := card_sdiff_add_card_inter (outN adj a ∩ S) W
  have equal : (outN adj a ∩ S) ∩ W = outN adj a ∩ W := by
    ext x
    simp only [mem_inter]
    exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, (mem_inter.mp h.2).2⟩, h.2⟩⟩
  rw [equal] at split
  change D.card + (outN adj a ∩ W).card = _ at split
  change I.card + W.card + (outN adj a ∩ S).card + 1 ≤ S.card + (W.card - 1) / 3
  omega

theorem ten_edge_budget (loopless : ∀ v, ¬ adj v v)
    (noDigon : ∀ u v, adj u v → ¬ adj v u)
    (noTri : ∀ u v w, adj u v → adj v w → ¬ adj w u)
    (small : SmallOut adj) (smallRev : SmallOut (fun u v => adj v u))
    (A : Finset V) (size : A.card = 10)
    (minimum : ∀ a ∈ A, 2 ≤ (outN adj a ∩ A).card) :
    ∑ a ∈ A, (outN adj a ∩ A).card ≤ 38 := by
  let K := ∑ a ∈ A, (outN adj a ∩ A).card
  have outFlip (v : V) : outN (fun u w => adj w u) v = inN adj v := by ext x; simp
  have inFlip (v : V) : inN (fun u w => adj w u) v = outN adj v := by ext x; simp
  have smallNine : CH.CompromiseNineLocal.SmallOut adj :=
    fun S hn hs => small S hn (by omega)
  have smallNineRev : CH.CompromiseNineLocal.SmallIn adj := by
    intro S hn hs
    simpa only [outFlip] using smallRev S hn (by omega)
  by_contra failure
  have large : 39 ≤ K := by change ¬ K ≤ 38 at failure; omega
  have positiveIn (a : V) (ha : a ∈ A) : 1 ≤ (inN adj a ∩ A).card := by
    by_contra hn
    have zero : (inN adj a ∩ A).card = 0 := by omega
    have noInto (b : V) (hb : b ∈ A) : ¬ adj b a := by
      intro edge
      have member : b ∈ inN adj a ∩ A := mem_inter.mpr ⟨(mem_inN adj a b).mpr edge, hb⟩
      rw [card_eq_zero.mp zero] at member
      exact notMem_empty b member
    let S := A.erase a
    have sizeS : S.card = 9 := by dsimp [S]; rw [card_erase_of_mem ha, size]
    have same (b : V) (hb : b ∈ S) : outN adj b ∩ S = outN adj b ∩ A := by
      ext x
      simp only [S, mem_inter, mem_erase]
      constructor
      · exact fun h => ⟨h.1, h.2.2⟩
      · intro h
        refine ⟨h.1, ?_, h.2⟩
        intro equal
        subst x
        exact noInto b (mem_erase.mp hb).2 ((mem_outN adj b a).mp h.1)
    have minS (b : V) (hb : b ∈ S) : 2 ≤ (outN adj b ∩ S).card := by
      rw [same b hb]
      exact minimum b (mem_erase.mp hb).2
    have bound := CH.CompromiseNineLocal.nine_edge_budget adj loopless noDigon noTri
      smallNine smallNineRev S sizeS minS
    have equal := sum_congr rfl (fun b hb => congrArg card (same b hb))
    rw [equal] at bound
    have split := sum_erase_add (s := A) (f := fun b => (outN adj b ∩ A).card) ha
    have outSubset : outN adj a ∩ A ⊆ S := by
      intro b hb
      refine mem_erase.mpr ⟨?_, (mem_inter.mp hb).2⟩
      intro equal
      subst b
      exact loopless a ((mem_outN adj a a).mp (mem_inter.mp hb).1)
    have outBound := card_le_card outSubset
    rw [sizeS] at outBound
    change (∑ b ∈ S, (outN adj b ∩ A).card) + (outN adj a ∩ A).card = K at split
    omega
  have forward (a : V) (ha : a ∈ A) :=
    local_degree_bound adj loopless noDigon noTri small A 2 (by omega) minimum a ha
      ((card_le_card inter_subset_right).trans (by omega))
  have reverse (a : V) (ha : a ∈ A) :
      (outN adj a ∩ A).card + (inN adj a ∩ A).card + 1 + 1 ≤
        A.card + ((inN adj a ∩ A).card - 1) / 3 := by
    simpa only [outFlip, inFlip] using
      (CH.CompromiseTenLocal.local_degree_bound (fun u v => adj v u) loopless
      (fun u v h => noDigon v u h)
      (fun u v w h1 h2 h3 => noTri w v u h2 h1 h3)
      smallRev A 1 (by omega) (fun b hb => by rw [outFlip]; exact positiveIn b hb) a ha
      ((card_le_card inter_subset_right).trans (by omega)))
  let L := A.filter (fun a => (outN adj a ∩ A).card = 2)
  let score := fun a => (inN adj a ∩ A).card + (outN adj a ∩ A).card +
    (if a ∈ L then 1 else 0)
  have scoreCap (a : V) (ha : a ∈ A) : score a ≤ 8 := by
    have hf := forward a ha
    have hr := reverse a ha
    change (outN adj a ∩ A).card + (inN adj a ∩ A).card + 1 + 1 ≤
      A.card + ((inN adj a ∩ A).card - 1) / 3 at hr
    have hm := minimum a ha
    have hp := positiveIn a ha
    rw [size] at hf hr
    by_cases hl : a ∈ L
    · have equal := (mem_filter.mp hl).2
      dsimp [score]
      rw [ite_eq_left hl]
      omega
    · have unequal : (outN adj a ∩ A).card ≠ 2 := fun h => hl (mem_filter.mpr ⟨ha, h⟩)
      dsimp [score]
      rw [ite_eq_right hl]
      omega
  have lowNonempty : L.Nonempty := by
    by_contra hn
    have minimum3 (a : V) (ha : a ∈ A) : 3 ≤ (outN adj a ∩ A).card := by
      have hm := minimum a ha
      have unequal : (outN adj a ∩ A).card ≠ 2 := fun h => hn ⟨a, mem_filter.mpr ⟨ha, h⟩⟩
      omega
    have rigid := rigid_small adj loopless noDigon noTri small A 3 (by omega) (by omega)
      size minimum3
    have equal := sum_congr rfl (fun a ha => (rigid a ha).1)
    simp only [sum_const, smul_eq_mul, size] at equal
    change K = 10 * 3 at equal
    omega
  have lowSubset : L ⊆ A := filter_subset _ _
  have count := double_count adj A A
  have scoreSum : (∑ a ∈ A, score a) = 2 * K + L.card := by
    dsimp [score]
    simp only [sum_add_distrib]
    have indicator : (∑ a ∈ A, if a ∈ L then 1 else 0 : ℕ) = L.card := by
      simp [sum_ite_mem, inter_eq_right.mpr lowSubset]
    rw [indicator]
    dsimp [K]
    omega
  have totalCap := sum_le_sum scoreCap
  simp only [sum_const, smul_eq_mul, size, scoreSum] at totalCap
  have lowSize : L.card ≤ 2 := by omega
  have scoreLower (a : V) (ha : a ∈ A) : 7 ≤ score a := by
    have bound := sum_le_sum (fun b (hb : b ∈ A.erase a) => scoreCap b (mem_erase.mp hb).2)
    simp only [sum_const, smul_eq_mul, card_erase_of_mem ha, size] at bound
    have split := sum_erase_add (s := A) (f := score) ha
    rw [scoreSum] at split
    have lowPos := card_pos.mpr lowNonempty
    omega
  obtain ⟨a, ha, lowHead⟩ := small L lowNonempty (by omega)
  have aA := lowSubset ha
  have aOut := (mem_filter.mp ha).2
  have aScore := scoreLower a aA
  have aIn : 4 ≤ (inN adj a ∩ A).card := by
    dsimp [score] at aScore
    rw [aOut, ite_eq_left ha] at aScore
    omega
  obtain ⟨b, hb, bound⟩ := selected_head_bound adj loopless noDigon noTri small A a aA
    (by rw [aOut]; omega) (by rw [aOut]; omega)
  have bA := (mem_inter.mp hb).2
  have edge := (mem_outN adj a b).mp (mem_inter.mp hb).1
  have bNotLow : b ∉ L := by
    intro h
    have pos := card_pos.mpr (show (outN adj a ∩ L).Nonempty from
      ⟨b, mem_inter.mpr ⟨(mem_inter.mp hb).1, h⟩⟩)
    omega
  have bMinimum := minimum b bA
  have bNotTwo : (outN adj b ∩ A).card ≠ 2 := fun h => bNotLow (mem_filter.mpr ⟨bA, h⟩)
  rw [size, aOut] at bound
  have bOut : (outN adj b ∩ A).card = 3 := by omega
  have aExact : (inN adj a ∩ A).card = 4 := by omega
  have aLowScore : score a = 7 := by dsimp [score]; rw [aExact, aOut, ite_eq_left ha]
  have bLowScore : score b ≤ 7 := by
    have hf := forward b bA
    rw [size, bOut] at hf
    dsimp [score]
    rw [bOut, ite_eq_right bNotLow]
    omega
  have different : b ≠ a := by intro equal; subst b; exact loopless a edge
  have charged (v : V) (hv : v ∈ A) :
      score v + (if v = a then 1 else 0) + (if v = b then 1 else 0) ≤ 8 := by
    by_cases va : v = a
    · subst v
      simp [Ne.symm different, aLowScore]
    · by_cases vb : v = b
      · subst v
        simpa [different] using (show score b + 1 ≤ 8 by omega)
      · simp only [ite_eq_right va, ite_eq_right vb, Nat.add_zero]
        exact scoreCap v hv
  have contradiction := sum_le_sum charged
  simp only [sum_add_distrib, sum_const, smul_eq_mul, size, scoreSum] at contradiction
  have oneA : (∑ v ∈ A, if v = a then 1 else 0 : ℕ) = 1 := by simp [aA]
  have oneB : (∑ v ∈ A, if v = b then 1 else 0 : ℕ) = 1 := by simp [bA]
  rw [oneA, oneB] at contradiction
  have lowPos := card_pos.mpr lowNonempty
  omega

end CH.CompromiseTenBudget

#print axioms CH.CompromiseTenBudget.selected_head_bound
#print axioms CH.CompromiseTenBudget.ten_edge_budget
