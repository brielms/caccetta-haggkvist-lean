module

public import LeanCH.CompromiseEight

set_option linter.style.header false

/-! Small induced graphs used by the degree-nine compromise candidate.
These results do not assume or prove the final degree-nine conclusion. -/

open Finset CH.CompromiseSeven
public section

namespace CH.CompromiseNineLocal

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (adj : V → V → Prop) [DecidableRel adj]

@[expose] def SmallOut : Prop := ∀ S : Finset V, S.Nonempty → S.card ≤ 9 →
  ∃ a ∈ S, (outN adj a ∩ S).card ≤ (S.card - 1) / 3

@[expose] def SmallIn : Prop := ∀ S : Finset V, S.Nonempty → S.card ≤ 9 →
  ∃ a ∈ S, (inN adj a ∩ S).card ≤ (S.card - 1) / 3

theorem local_degree_bound (loopless : ∀ v, ¬ adj v v)
    (noDigon : ∀ u v, adj u v → ¬ adj v u)
    (noTri : ∀ u v w, adj u v → adj v w → ¬ adj w u)
    (small : SmallOut adj) (S : Finset V) (r : ℕ) (hr : 1 ≤ r)
    (hsize : S.card ≤ 9) (hmin : ∀ a ∈ S, r ≤ (outN adj a ∩ S).card)
    (v : V) (hv : v ∈ S) :
    (inN adj v ∩ S).card + (outN adj v ∩ S).card + r + 1 ≤
      S.card + ((outN adj v ∩ S).card - 1) / 3 := by
  let W := outN adj v ∩ S
  have hW : W ⊆ S := inter_subset_right
  have hpos : 0 < W.card := by
    change 0 < (outN adj v ∩ S).card
    have := hmin v hv
    omega
  obtain ⟨a, ha, hsmall⟩ := small W (card_pos.mp hpos)
    ((card_le_card hW).trans hsize)
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

theorem nine_edge_budget (loopless : ∀ v, ¬ adj v v)
    (noDigon : ∀ u v, adj u v → ¬ adj v u)
    (noTri : ∀ u v w, adj u v → adj v w → ¬ adj w u)
    (small : SmallOut adj) (smallRev : SmallIn adj)
    (A : Finset V) (hA : A.card = 9)
    (hmin : ∀ a ∈ A, 2 ≤ (outN adj a ∩ A).card) :
    ∑ a ∈ A, (outN adj a ∩ A).card ≤ 29 := by
  let K := ∑ a ∈ A, (outN adj a ∩ A).card
  let F := ∑ a ∈ A, ((outN adj a ∩ A).card - 1) / 3
  have hb (a : V) (ha : a ∈ A) :
      (inN adj a ∩ A).card + (outN adj a ∩ A).card + 3 ≤
        9 + ((outN adj a ∩ A).card - 1) / 3 := by
    have := local_degree_bound adj loopless noDigon noTri small A 2 (by omega)
      (by omega) hmin a ha
    omega
  have hf (a : V) (ha : a ∈ A) :
      2 * (((outN adj a ∩ A).card - 1) / 3) + 2 ≤ (outN adj a ∩ A).card := by
    have := hmin a ha
    omega
  have hs := sum_le_sum hb
  have ht := sum_le_sum hf
  have hcount := double_count adj A A
  simp only [sum_add_distrib, sum_const, smul_eq_mul, hA, ← mul_sum] at hs ht
  have h1 : 2 * K + 27 ≤ 81 + F := by dsimp [K, F]; omega
  have h2 : 2 * F + 18 ≤ K := by simpa [K, F] using ht
  have hK : K ≤ 30 := by omega
  by_contra hn
  change ¬ K ≤ 29 at hn
  have hKeq : K = 30 := by omega
  have hFeq : F = 6 := by omega
  have hbEq (a : V) (ha : a ∈ A) :
      (inN adj a ∩ A).card + (outN adj a ∩ A).card + 3 =
        9 + ((outN adj a ∩ A).card - 1) / 3 := by
    have he : ∑ a ∈ A, ((inN adj a ∩ A).card + (outN adj a ∩ A).card + 3) =
        ∑ a ∈ A, (9 + ((outN adj a ∩ A).card - 1) / 3) := by
      simp only [sum_add_distrib, sum_const, smul_eq_mul, hA]
      change (∑ a ∈ A, (inN adj a ∩ A).card) + K + 27 = 81 + F
      change K = ∑ a ∈ A, (inN adj a ∩ A).card at hcount
      omega
    exact (sum_eq_sum_iff_of_le hb).mp he a ha
  have hfEq (a : V) (ha : a ∈ A) :
      2 * (((outN adj a ∩ A).card - 1) / 3) + 2 = (outN adj a ∩ A).card := by
    have he : ∑ a ∈ A, (2 * (((outN adj a ∩ A).card - 1) / 3) + 2) =
        ∑ a ∈ A, (outN adj a ∩ A).card := by
      simp only [sum_add_distrib, sum_const, smul_eq_mul, hA, ← mul_sum]
      change 2 * F + 18 = K
      omega
    exact (sum_eq_sum_iff_of_le hf).mp he a ha
  obtain ⟨a, ha, hin⟩ := smallRev A (card_pos.mp (by omega)) (by omega)
  have := hbEq a ha
  have := hfEq a ha
  have := hmin a ha
  rw [hA] at hin
  omega

theorem five_structure (loopless : ∀ v, ¬ adj v v)
    (noDigon : ∀ u v, adj u v → ¬ adj v u)
    (noTri : ∀ u v w, adj u v → adj v w → ¬ adj w u)
    (small : SmallOut adj) (S : Finset V) (hS : S.card = 5)
    (hmin : ∀ a ∈ S, 1 ≤ (outN adj a ∩ S).card) :
    let L := S.filter (fun a => (outN adj a ∩ S).card = 1)
    3 ≤ L.card ∧ ∀ q ∈ S \ L, ∃ a ∈ L, adj q a := by
  let L := S.filter (fun a => (outN adj a ∩ S).card = 1)
  let Q := S \ L
  have hLS : L ⊆ S := filter_subset _ _
  have hQS : Q ⊆ S := sdiff_subset
  have hpart : L.card + Q.card = 5 := by
    have := card_sdiff_of_subset hLS
    have := card_le_card hLS
    dsimp [Q]
    omega
  have high (a : V) (ha : a ∈ Q) : 2 ≤ (outN adj a ∩ S).card := by
    have hm := hmin a (hQS ha)
    have hn : (outN adj a ∩ S).card ≠ 1 := by
      intro he
      exact (mem_sdiff.mp ha).2 (mem_filter.mpr ⟨hQS ha, he⟩)
    omega
  have inc (a : V) (ha : a ∈ S) :
      (inN adj a ∩ S).card + (if a ∈ Q then 1 else 0) ≤ 2 := by
    have hb := local_degree_bound adj loopless noDigon noTri small S 1 (by omega)
      (by omega) hmin a ha
    have hm := hmin a ha
    by_cases hq : a ∈ Q
    · have hh := high a hq
      simp only [ite_eq_left hq]
      omega
    · have hl : a ∈ L := by
        by_contra hn
        exact hq (mem_sdiff.mpr ⟨ha, hn⟩)
      have hh := (mem_filter.mp hl).2
      simp only [ite_eq_right hq]
      omega
  have outc (a : V) (ha : a ∈ S) :
      1 + (if a ∈ Q then 1 else 0) ≤ (outN adj a ∩ S).card := by
    by_cases hq : a ∈ Q
    · simpa [hq] using high a hq
    · simpa [hq] using hmin a ha
  have hQsum : ∑ a ∈ S, (if a ∈ Q then 1 else 0 : ℕ) = Q.card := by
    simp [sum_ite_mem, inter_eq_right.mpr hQS]
  have hi := sum_le_sum inc
  have ho := sum_le_sum outc
  simp only [sum_add_distrib, sum_const, smul_eq_mul, hS, hQsum] at hi ho
  have hcount := double_count adj S S
  have hQ : Q.card ≤ 2 := by omega
  have hL : 3 ≤ L.card := by omega
  refine ⟨hL, ?_⟩
  intro q hq
  change q ∈ Q at hq
  by_contra hn
  have hsub : outN adj q ∩ S ⊆ Q.erase q := by
    intro a ha
    refine mem_erase.mpr ⟨?_, mem_sdiff.mpr ⟨(mem_inter.mp ha).2, ?_⟩⟩
    · intro heq
      subst a
      exact loopless q (by simpa using (mem_inter.mp ha).1)
    · intro haL
      exact hn ⟨a, haL, by simpa using (mem_inter.mp ha).1⟩
  have hc := card_le_card hsub
  rw [card_erase_of_mem hq] at hc
  have := high q hq
  omega

theorem six_two_degree_one (loopless : ∀ v, ¬ adj v v)
    (noDigon : ∀ u v, adj u v → ¬ adj v u)
    (noTri : ∀ u v w, adj u v → adj v w → ¬ adj w u)
    (small : SmallOut adj) (S : Finset V) (hS : S.card = 6)
    (hmin : ∀ a ∈ S, 1 ≤ (outN adj a ∩ S).card) :
    2 ≤ (S.filter (fun a => (outN adj a ∩ S).card = 1)).card := by
  let L := S.filter (fun a => (outN adj a ∩ S).card = 1)
  by_contra hn
  have hL : L.card ≤ 1 := by change ¬ 2 ≤ L.card at hn; omega
  obtain ⟨a, ha, hsmall⟩ := small S (card_pos.mp (by omega)) (by omega)
  have hamin := hmin a ha
  have haone : (outN adj a ∩ S).card = 1 := by rw [hS] at hsmall; omega
  have haL : a ∈ L := mem_filter.mpr ⟨ha, haone⟩
  have hother (u : V) (hu : u ∈ S) (hne : u ≠ a) :
      2 ≤ (outN adj u ∩ S).card := by
    have hm := hmin u hu
    by_contra hh
    have he : (outN adj u ∩ S).card = 1 := by omega
    have huL : u ∈ L := mem_filter.mpr ⟨hu, he⟩
    exact hne (card_le_one.mp hL u huL a haL)
  let T := S.erase a
  have hTsub : T ⊆ S := erase_subset _ _
  have hT : T.card = 5 := by dsimp [T]; rw [card_erase_of_mem ha, hS]
  have hminT (u : V) (hu : u ∈ T) : 1 ≤ (outN adj u ∩ T).card := by
    have hm := hother u (hTsub hu) (mem_erase.mp hu).1
    have hs : outN adj u ∩ S ⊆ T ∪ {a} := by
      intro x hx
      by_cases he : x = a
      · subst x; simp
      · exact mem_union_left _ (mem_erase.mpr ⟨he, (mem_inter.mp hx).2⟩)
    have hc := degree_bound (outN adj u ∩ S) T {a} hs
    have he : (outN adj u ∩ S) ∩ T = outN adj u ∩ T := by
      ext x; simp only [mem_inter]
      exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, hTsub h.2⟩, h.2⟩⟩
    rw [he, card_singleton] at hc
    omega
  have hfive := five_structure adj loopless noDigon noTri small T hT hminT
  let C := T.filter (fun u => (outN adj u ∩ T).card = 1)
  have hC : 3 ≤ C.card := hfive.1
  have hCT : C ⊆ T := filter_subset _ _
  have parent (u : V) (hu : u ∈ C) : adj u a := by
    have huT := hCT hu
    have hm := hother u (hTsub huT) (mem_erase.mp huT).1
    have hc : (outN adj u ∩ T).card = 1 := (mem_filter.mp hu).2
    by_contra hna
    have hs : outN adj u ∩ S ⊆ outN adj u ∩ T := by
      intro x hx
      refine mem_inter.mpr ⟨(mem_inter.mp hx).1, mem_erase.mpr ⟨?_, (mem_inter.mp hx).2⟩⟩
      intro he
      subst x
      exact hna (by simpa using (mem_inter.mp hx).1)
    have := card_le_card hs
    omega
  obtain ⟨b, hb⟩ := card_pos.mp (show 0 < (outN adj a ∩ S).card by omega)
  have hab : adj a b := (mem_outN adj a b).mp (mem_inter.mp hb).1
  have hbS := (mem_inter.mp hb).2
  have hba : b ≠ a := by intro he; subst b; exact loopless a hab
  have hbmin := hother b hbS hba
  have haC : a ∉ C := fun hh => (mem_erase.mp (hCT hh)).1 rfl
  have hbC : b ∉ C := fun hh => noDigon a b hab (parent b hh)
  let J := insert a (insert b C)
  have hJ : J.card = C.card + 2 := by
    dsimp [J]
    rw [card_insert_of_notMem (by simp [haC, Ne.symm hba]), card_insert_of_notMem hbC]
  have hJS : J ⊆ S := insert_subset ha (insert_subset hbS (hCT.trans hTsub))
  have hdisj : Disjoint (outN adj b ∩ S) J := by
    apply disjoint_left.mpr
    intro x hx hxJ
    have hbx : adj b x := (mem_outN adj b x).mp (mem_inter.mp hx).1
    rcases mem_insert.mp hxJ with hxa | hxJ
    · subst x
      exact noDigon a b hab hbx
    rcases mem_insert.mp hxJ with hxb | hxC
    · subst x
      exact loopless b hbx
    · exact noTri a b x hab hbx (parent x hxC)
  have hc := card_le_card (union_subset (inter_subset_right : outN adj b ∩ S ⊆ S) hJS)
  rw [card_union_of_disjoint hdisj, hJ, hS] at hc
  omega

end CH.CompromiseNineLocal

#print axioms CH.CompromiseNineLocal.nine_edge_budget
#print axioms CH.CompromiseNineLocal.five_structure
#print axioms CH.CompromiseNineLocal.six_two_degree_one
