module

public import LeanCH.CompromiseTenBudget

set_option linter.style.header false

/-! A six-vertex induced graph with minimum out-degree one and exactly
two vertices of out-degree one has at most eleven edges. Both small-set
CH directions are explicit. -/

open Finset CH.CompromiseSeven CH.CompromiseTenLocal
public section

namespace CH.CompromiseSixBudget

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (adj : V → V → Prop) [DecidableRel adj]

theorem eleven (loopless : ∀ v, ¬ adj v v)
    (noDigon : ∀ u v, adj u v → ¬ adj v u)
    (noTri : ∀ u v w, adj u v → adj v w → ¬ adj w u)
    (small : SmallOut adj) (smallRev : SmallOut (fun u v => adj v u))
    (S : Finset V) (size : S.card = 6)
    (minimum : ∀ a ∈ S, 1 ≤ (outN adj a ∩ S).card)
    (ones : (S.filter (fun a => (outN adj a ∩ S).card = 1)).card = 2) :
    (∑ a ∈ S, (outN adj a ∩ S).card) ≤ 11 := by
  let L := S.filter (fun a => (outN adj a ∩ S).card = 1)
  have lS : L ⊆ S := filter_subset _ _
  have smallNine : CH.CompromiseNineLocal.SmallOut adj := fun A hn hs => small A hn (by omega)
  have positiveIn (a : V) (ha : a ∈ S) : 1 ≤ (inN adj a ∩ S).card := by
    by_contra none
    have zero : (inN adj a ∩ S).card = 0 := by omega
    have noInto (b : V) (hb : b ∈ S) : ¬ adj b a := by
      intro edge
      have positive : 1 ≤ (inN adj a ∩ S).card :=
        card_pos.mpr ⟨b, mem_inter.mpr ⟨(mem_inN adj a b).mpr edge, hb⟩⟩
      omega
    let T := S.erase a
    have sizeT : T.card = 5 := by dsimp [T]; rw [card_erase_of_mem ha, size]
    have same (b : V) (hb : b ∈ T) : outN adj b ∩ T = outN adj b ∩ S := by
      ext x
      simp only [T, mem_inter, mem_erase]
      constructor
      · exact fun h => ⟨h.1, h.2.2⟩
      · intro h
        refine ⟨h.1, ?_, h.2⟩
        intro equal
        subst x
        exact noInto b (mem_erase.mp hb).2 ((mem_outN adj b a).mp h.1)
    have minT (b : V) (hb : b ∈ T) : 1 ≤ (outN adj b ∩ T).card := by
      rw [same b hb]
      exact minimum b (mem_erase.mp hb).2
    have five := CH.CompromiseNineLocal.five_structure adj loopless noDigon noTri
      smallNine T sizeT minT
    have subset : T.filter (fun b => (outN adj b ∩ T).card = 1) ⊆ L := by
      intro b hb
      have bT := (mem_filter.mp hb).1
      refine mem_filter.mpr ⟨(mem_erase.mp bT).2, ?_⟩
      rw [← same b bT]
      exact (mem_filter.mp hb).2
    have count := card_le_card subset
    change L.card = 2 at ones
    omega
  have outFlip (v : V) : outN (fun u w => adj w u) v = inN adj v := by ext x; simp
  have inFlip (v : V) : inN (fun u w => adj w u) v = outN adj v := by ext x; simp
  have scoreCap (a : V) (ha : a ∈ S) :
      (inN adj a ∩ S).card + (outN adj a ∩ S).card ≤ 4 := by
    have outCap := card_le_card (inter_subset_right : outN adj a ∩ S ⊆ S)
    have inCap := card_le_card (inter_subset_right : inN adj a ∩ S ⊆ S)
    have forward := local_degree_bound adj loopless noDigon noTri small S 1
      (by omega) minimum a ha (by omega)
    have reverse := local_degree_bound (fun u v => adj v u) loopless
      (fun u v h => noDigon v u h)
      (fun u v w h1 h2 h3 => noTri w v u h2 h1 h3) smallRev S 1 (by omega)
      (fun b hb => by rw [outFlip]; exact positiveIn b hb) a ha
      (by rw [outFlip]; omega)
    simp only [outFlip, inFlip] at reverse
    rw [size] at forward reverse outCap inCap
    omega
  let K := ∑ a ∈ S, (outN adj a ∩ S).card
  have total := sum_le_sum scoreCap
  have count := double_count adj S S
  simp only [sum_add_distrib, sum_const, smul_eq_mul, size] at total
  have upper : K ≤ 12 := by dsimp [K]; omega
  by_contra failure
  change ¬ K ≤ 11 at failure
  have exactK : K = 12 := by omega
  have scoreEq (a : V) (ha : a ∈ S) :
      (inN adj a ∩ S).card + (outN adj a ∩ S).card = 4 := by
    have equal : (∑ a ∈ S, ((inN adj a ∩ S).card + (outN adj a ∩ S).card)) =
        ∑ _a ∈ S, 4 := by
      simp only [sum_add_distrib, sum_const, smul_eq_mul, size]
      change (∑ a ∈ S, (inN adj a ∩ S).card) + K = 24
      change K = ∑ a ∈ S, (inN adj a ∩ S).card at count
      omega
    exact (sum_eq_sum_iff_of_le scoreCap).mp equal a ha
  have minL (a : V) (ha : a ∈ L) : 1 ≤ (outN adj a ∩ L).card := by
    have aS := lS ha
    have one := (mem_filter.mp ha).2
    have score := scoreEq a aS
    obtain ⟨b, hb, bound⟩ := CH.CompromiseTenBudget.selected_head_bound adj
      loopless noDigon noTri small S a aS (by omega) (by omega)
    have min := minimum b (mem_inter.mp hb).2
    rw [size] at bound
    have bL : b ∈ L := mem_filter.mpr ⟨(mem_inter.mp hb).2, by omega⟩
    exact card_pos.mpr ⟨b, mem_inter.mpr ⟨(mem_inter.mp hb).1, bL⟩⟩
  change L.card = 2 at ones
  obtain ⟨a, ha, low⟩ := small L (card_pos.mp (by omega)) (by omega)
  have min := minL a ha
  rw [ones] at low
  omega

end CH.CompromiseSixBudget

#print axioms CH.CompromiseSixBudget.eleven
