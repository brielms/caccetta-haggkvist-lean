module

public import LeanCH.CompromiseSeven

set_option linter.style.header false

/-!
Unit compromise at exact out-degree eight, conditional on the prompt's small
induced-subgraph CH bounds and existence of a Seymour vertex. The key new
step is the eight-vertex neighbourhood structure, followed by degree transport.
-/

open Finset CH.CompromiseSeven

public section

namespace CH.CompromiseEight

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (adj : V → V → Prop) [DecidableRel adj]

def LocalSmallEight : Prop := ∀ S : Finset V, S.Nonempty → S.card ≤ 8 →
  ∃ a ∈ S, (outN adj a ∩ S).card ≤ (S.card - 1) / 3

lemma localSmallEight_of_induction
    (ih : ∀ (S : Finset V) (r : ℕ), S.Nonempty → 1 ≤ r → r < 8 →
      (∀ a ∈ S, r ≤ (outN adj a ∩ S).card) → 3 * r < S.card) :
    LocalSmallEight adj := by
  intro S hn hs
  have hp := card_pos.mpr hn
  by_contra h
  have hm : ∀ a ∈ S, (S.card - 1) / 3 + 1 ≤ (outN adj a ∩ S).card := by
    intro a ha
    have hh : ¬ (outN adj a ∩ S).card ≤ (S.card - 1) / 3 := fun hc => h ⟨a, ha, hc⟩
    omega
  have := ih S ((S.card - 1) / 3 + 1) hn (by omega) (by omega) hm
  omega

lemma small_seven (small : LocalSmallEight adj) : LocalSmall adj := by
  intro S hn hc
  exact small S hn (by omega)

/-- The structural step specific to eight vertices. There are at least four
internal degree-two vertices, and every other vertex points to one of them. -/
theorem eight_structure (loopless : ∀ v, ¬ adj v v)
    (noDigon : ∀ u v, adj u v → ¬ adj v u)
    (noTri : ∀ u v w, adj u v → adj v w → ¬ adj w u)
    (small : LocalSmall adj) (A : Finset V) (hA : A.card = 8)
    (hmin : ∀ a ∈ A, 2 ≤ (outN adj a ∩ A).card) :
    let L := A.filter (fun a => (outN adj a ∩ A).card = 2)
    4 ≤ L.card ∧ ∀ q ∈ A \ L, ∃ a ∈ L, adj q a := by
  let L := A.filter (fun a => (outN adj a ∩ A).card = 2)
  let Q := A \ L
  have hLA : L ⊆ A := filter_subset _ _
  have hQA : Q ⊆ A := sdiff_subset
  have hpart : L.card + Q.card = 8 := by
    have := card_sdiff_of_subset hLA
    have := card_le_card hLA
    dsimp [Q]
    omega
  have low (a : V) (ha : a ∈ L) : (outN adj a ∩ A).card = 2 := (mem_filter.mp ha).2
  have high (a : V) (ha : a ∈ Q) : 3 ≤ (outN adj a ∩ A).card := by
    have hm := hmin a (hQA ha)
    have hn : (outN adj a ∩ A).card ≠ 2 := by
      intro he
      exact (mem_sdiff.mp ha).2 (mem_filter.mpr ⟨hQA ha, he⟩)
    omega
  have inc (a : V) (ha : a ∈ A) :
      (inN adj a ∩ A).card + (if a ∈ Q then 1 else 0) ≤ 3 := by
    have hb := local_degree_bound adj loopless noDigon noTri small A (by omega) hmin a ha
    have hm := hmin a ha
    have hs : (outN adj a ∩ A).card ≤ 8 := hA ▸ card_le_card inter_subset_right
    by_cases hq : a ∈ Q
    · have hh := high a hq
      simp only [ite_eq_left hq]
      omega
    · have hl : a ∈ L := by
        by_contra hn
        exact hq (mem_sdiff.mpr ⟨ha, hn⟩)
      have hh := low a hl
      simp only [ite_eq_right hq]
      omega
  have outc (a : V) (ha : a ∈ A) :
      2 + (if a ∈ Q then 1 else 0) ≤ (outN adj a ∩ A).card := by
    by_cases hq : a ∈ Q
    · simpa [hq] using high a hq
    · simpa [hq] using hmin a ha
  have hQsum : ∑ a ∈ A, (if a ∈ Q then 1 else 0 : ℕ) = Q.card := by
    simp [sum_ite_mem, inter_eq_right.mpr hQA]
  have hi := sum_le_sum inc
  have ho := sum_le_sum outc
  simp only [sum_add_distrib, sum_const, smul_eq_mul, hA, hQsum] at hi ho
  have hcount := double_count adj A A
  have hQ : Q.card ≤ 4 := by omega
  have hL : 4 ≤ L.card := by omega
  refine ⟨hL, ?_⟩
  intro q hq
  change q ∈ Q at hq
  by_contra hn
  have avoids : ∀ a ∈ L, ¬ adj q a := by
    intro a ha hqa
    exact hn ⟨a, ha, hqa⟩
  have hqnot : q ∉ outN adj q ∩ A := by simp [loopless]
  have qsub : outN adj q ∩ A ⊆ Q.erase q := by
    intro a ha
    refine mem_erase.mpr ⟨?_, mem_sdiff.mpr ⟨(mem_inter.mp ha).2, ?_⟩⟩
    · intro heq
      subst a
      exact hqnot ha
    · intro hl
      exact avoids a hl ((mem_outN adj q a).mp (mem_inter.mp ha).1)
  have hqc := card_le_card qsub
  rw [card_erase_of_mem hq] at hqc
  have hqhigh := high q hq
  have hQeq : Q.card = 4 := by omega
  have hLeq : L.card = 4 := by omega
  have qeq : outN adj q ∩ A = Q.erase q :=
    eq_of_subset_of_card_le qsub (by rw [card_erase_of_mem hq]; omega)
  have exactIn (a : V) (ha : a ∈ A) :
      (inN adj a ∩ A).card + (if a ∈ Q then 1 else 0) = 3 := by
    have he : ∑ a ∈ A, ((inN adj a ∩ A).card + (if a ∈ Q then 1 else 0)) =
        ∑ _a ∈ A, 3 := by
      simp only [sum_add_distrib, sum_const, smul_eq_mul, hA, hQsum]
      omega
    exact (sum_eq_sum_iff_of_le inc).mp he a ha
  have qind : (inN adj q ∩ A).card = 2 := by
    have := exactIn q (hQA hq)
    simp only [ite_eq_left hq] at this
    omega
  have parentLow (a : V) (ha : a ∈ inN adj q ∩ A) : a ∈ L := by
    have haq : adj a q := (mem_inN adj q a).mp (mem_inter.mp ha).1
    have haA := (mem_inter.mp ha).2
    by_contra hnL
    have haQ : a ∈ Q := mem_sdiff.mpr ⟨haA, hnL⟩
    have hneq : a ≠ q := by intro heq; subst a; exact loopless q haq
    have hqa : adj q a := by
      have he : a ∈ outN adj q ∩ A := qeq.symm ▸ mem_erase.mpr ⟨hneq, haQ⟩
      exact (mem_outN adj q a).mp (mem_inter.mp he).1
    exact noDigon q a hqa haq
  have parentIn (a : V) (ha : a ∈ inN adj q ∩ A) :
      inN adj a ∩ A = L.erase a := by
    have haL := parentLow a ha
    have haq : adj a q := (mem_inN adj q a).mp (mem_inter.mp ha).1
    have hsub : inN adj a ∩ A ⊆ L.erase a := by
      intro x hx
      have hxa : adj x a := (mem_inN adj a x).mp (mem_inter.mp hx).1
      have hxA := (mem_inter.mp hx).2
      have hneq : x ≠ a := by intro heq; subst x; exact loopless a hxa
      refine mem_erase.mpr ⟨hneq, ?_⟩
      by_contra hnL
      have hxQ : x ∈ Q := mem_sdiff.mpr ⟨hxA, hnL⟩
      by_cases hxq : x = q
      · subst x
        exact avoids a haL hxa
      · have hqx : adj q x := by
          have he : x ∈ outN adj q ∩ A := qeq.symm ▸ mem_erase.mpr ⟨hxq, hxQ⟩
          exact (mem_outN adj q x).mp (mem_inter.mp he).1
        exact noTri a q x haq hqx hxa
    have haNotQ : a ∉ Q := fun h => (mem_sdiff.mp h).2 haL
    have hiA := exactIn a (hLA haL)
    simp only [ite_eq_right haNotQ, add_zero] at hiA
    apply eq_of_subset_of_card_le hsub
    rw [card_erase_of_mem haL, hLeq, hiA]
  have hsubsingle : (inN adj q ∩ A).card ≤ 1 := by
    apply card_le_one.mpr
    intro a ha b hb
    by_contra hab
    have hba : adj b a := by
      have hm : b ∈ inN adj a ∩ A :=
        (parentIn a ha).symm ▸ mem_erase.mpr ⟨Ne.symm hab, parentLow b hb⟩
      exact (mem_inN adj a b).mp (mem_inter.mp hm).1
    have hab' : adj a b := by
      have hm : a ∈ inN adj b ∩ A :=
        (parentIn b hb).symm ▸ mem_erase.mpr ⟨hab, parentLow a ha⟩
      exact (mem_inN adj b a).mp (mem_inter.mp hm).1
    exact noDigon a b hab' hba
  omega

lemma second_ge_six (noDigon : ∀ u v, adj u v → ¬ adj v u)
    (small : LocalSmallEight adj) (regular : ∀ v, (outN adj v).card = 8) (v : V) :
    6 ≤ (second adj v).card := by
  obtain ⟨a, ha, hsmall⟩ := small (outN adj v)
    (card_pos.mp (by rw [regular]; omega)) (by rw [regular])
  have hb := degree_bound (outN adj a) (outN adj v) (second adj v)
    (heads_two_steps adj noDigon ha)
  rw [regular] at hb
  rw [regular] at hsmall
  omega

theorem high_has_four_low_heads (loopless : ∀ v, ¬ adj v v)
    (noDigon : ∀ u v, adj u v → ¬ adj v u)
    (noTri : ∀ u v w, adj u v → adj v w → ¬ adj w u)
    (small : LocalSmallEight adj) (regular : ∀ v, (outN adj v).card = 8)
    (bad : ∀ v, (second adj v).card + (inN adj v).card < 16)
    (v : V) (high : (inN adj v).card = 9) :
    4 ≤ (outN adj v ∩ univ.filter (fun a => (inN adj a).card ≤ 6)).card := by
  let A := outN adj v
  let Z := second adj v
  have hA : A.card = 8 := regular v
  have hZ : Z.card = 6 := by
    have := second_ge_six adj noDigon small regular v
    have := bad v
    dsimp [Z]
    omega
  have hheads (a : V) (ha : a ∈ A) : outN adj a ⊆ A ∪ Z :=
    heads_two_steps adj noDigon ha
  have hmin (a : V) (ha : a ∈ A) : 2 ≤ (outN adj a ∩ A).card := by
    have := degree_bound (outN adj a) A Z (hheads a ha)
    rw [regular, hZ] at this
    omega
  let L := A.filter (fun a => (outN adj a ∩ A).card = 2)
  have hLA : L ⊆ A := filter_subset _ _
  have hstructure := eight_structure adj loopless noDigon noTri (small_seven adj small) A hA hmin
  change 4 ≤ L.card ∧ ∀ q ∈ A \ L, ∃ a ∈ L, adj q a at hstructure
  have complete (a : V) (ha : a ∈ L) : Z ⊆ outN adj a := by
    have hsub : outN adj a \ A ⊆ Z := by
      intro z hz
      have hh := hheads a (hLA ha) (mem_sdiff.mp hz).1
      rcases mem_union.mp hh with hh | hh
      · exact False.elim ((mem_sdiff.mp hz).2 hh)
      · exact hh
    have hc := card_sdiff_add_card_inter (outN adj a) A
    rw [regular, (mem_filter.mp ha).2] at hc
    have heq : outN adj a \ A = Z := eq_of_subset_of_card_le hsub (by omega)
    rw [← heq]
    exact sdiff_subset
  have avoids (z : V) (hz : z ∈ Z) (a : V) (ha : a ∈ A) : ¬ adj z a := by
    by_cases haL : a ∈ L
    · exact noDigon a z (by simpa using complete a haL hz)
    · obtain ⟨b, hb, hab⟩ := hstructure.2 a (mem_sdiff.mpr ⟨ha, haL⟩)
      exact noTri a b z hab (by simpa using complete b hb hz)
  let T := (Z.biUnion (outN adj)) \ Z
  have headsZ (z : V) (hz : z ∈ Z) : outN adj z ⊆ Z ∪ T := by
    intro x hx
    by_cases hxZ : x ∈ Z
    · exact mem_union_left _ hxZ
    · exact mem_union_right _ (mem_sdiff.mpr ⟨mem_biUnion.mpr ⟨z, hz, hx⟩, hxZ⟩)
  obtain ⟨z, hz, hsmall⟩ := small Z (card_pos.mp (by omega)) (by omega)
  have hT : 7 ≤ T.card := by
    have hb := degree_bound (outN adj z) Z T (headsZ z hz)
    rw [regular] at hb
    rw [hZ] at hsmall
    omega
  have hTA : Disjoint T A := by
    apply disjoint_left.mpr
    intro x hx hxA
    obtain ⟨z, hz, hzx⟩ := mem_biUnion.mp (mem_sdiff.mp hx).1
    exact avoids z hz x hxA (by simpa using hzx)
  have hlow (a : V) (ha : a ∈ L) : (inN adj a).card ≤ 6 := by
    have hTsecond : T ⊆ second adj a := by
      intro x hx
      obtain ⟨z, hz, hzx⟩ := mem_biUnion.mp (mem_sdiff.mp hx).1
      have hxA : x ∉ A := fun hh => disjoint_left.mp hTA hx hh
      have hxZ : x ∉ Z := (mem_sdiff.mp hx).2
      apply (mem_second adj a x).mpr
      refine ⟨?_, ?_, z, by simpa using complete a ha hz, by simpa using hzx⟩
      · intro heq
        subst x
        exact hxA (hLA ha)
      · intro hax
        have hh := hheads a (hLA ha) (by simpa using hax)
        rcases mem_union.mp hh with hh | hh
        · exact hxA hh
        · exact hxZ hh
    have hins := second_inside_two_of_min adj noDigon (small_seven adj small) A hmin a
      (mem_filter.mp ha).2
    have hdisj : Disjoint T (second adj a ∩ A) := hTA.mono_right inter_subset_right
    have hc := card_le_card (union_subset hTsecond
      (inter_subset_left : second adj a ∩ A ⊆ second adj a))
    rw [card_union_of_disjoint hdisj] at hc
    have hb := bad a
    omega
  have hsub : L ⊆ outN adj v ∩ univ.filter (fun a => (inN adj a).card ≤ 6) := by
    intro a ha
    exact mem_inter.mpr ⟨hLA ha, mem_filter.mpr ⟨mem_univ _, hlow a ha⟩⟩
  exact hstructure.1.trans (card_le_card hsub)

/-- Unit-weight compromise at exact out-degree eight. No order bound or
minimal-counterexample hypothesis occurs. -/
theorem compromise_eight (loopless : ∀ v, ¬ adj v v)
    (noDigon : ∀ u v, adj u v → ¬ adj v u)
    (noTri : ∀ u v w, adj u v → adj v w → ¬ adj w u)
    (small : LocalSmallEight adj) (regular : ∀ v, (outN adj v).card = 8)
    (seymour : ∃ v, 8 ≤ (second adj v).card) :
    ∃ v, 16 ≤ (second adj v).card + (inN adj v).card := by
  by_contra hn
  have bad (v : V) : (second adj v).card + (inN adj v).card < 16 := by
    have : ¬ 16 ≤ (second adj v).card + (inN adj v).card := fun h => hn ⟨v, h⟩
    omega
  have cap (v : V) : (inN adj v).card ≤ 9 := by
    have := second_ge_six adj noDigon small regular v
    have := bad v
    omega
  have balanced := degree_transport_quota adj 8 6 4 (by omega) (by omega) regular cap
    (high_has_four_low_heads adj loopless noDigon noTri small regular bad)
  obtain ⟨v, hv⟩ := seymour
  have := bad v
  have := balanced v
  omega

end CH.CompromiseEight

#print axioms CH.CompromiseSeven.degree_transport_quota
#print axioms CH.CompromiseEight.eight_structure
#print axioms CH.CompromiseEight.high_has_four_low_heads
#print axioms CH.CompromiseEight.compromise_eight
