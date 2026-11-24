module

public import LeanCH.CompromiseSeven

set_option linter.style.header false

/-! Subset accounting for a hypothetical arc-minimal compromise counterexample.
The first batch is chosen at a prescribed vertex; later batches use deletion.
The required good vertices in proper arc deletions remain explicit hypotheses. -/

open Finset CH.CompromiseSeven
public section

namespace CH.CompromiseSubset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (adj : V → V → Prop) [DecidableRel adj]

@[expose] def reach (S : Finset V) : Finset V := S.biUnion (outN adj)
@[simp] theorem mem_reach (S : Finset V) (z : V) :
    z ∈ reach adj S ↔ ∃ a ∈ S, adj a z := by simp [reach]

theorem reach_mono {S T : Finset V} (h : S ⊆ T) : reach adj S ⊆ reach adj T := by
  intro z hz
  obtain ⟨a, ha, haz⟩ := (mem_reach adj S z).mp hz
  exact (mem_reach adj T z).mpr ⟨a, h ha, haz⟩

theorem reach_union (S T : Finset V) : reach adj (S ∪ T) = reach adj S ∪ reach adj T := by
  ext z
  simp only [mem_reach, mem_union]
  aesop

@[expose] def boundary (S : Finset V) : Finset V := reach adj S \ S
@[expose] def inside (S : Finset V) : Finset V := reach adj S ∩ S
@[expose] def growth (I T : Finset V) : ℕ := (reach adj T \ (I ∪ T)).card
@[expose] def localSecond (S : Finset V) (v : V) : Finset V :=
  S.filter (fun z => z ≠ v ∧ ¬ adj v z ∧ ∃ a ∈ S, adj v a ∧ adj a z)
@[expose] def cutEdge (S T : Finset V) (v a : V) : Prop :=
  adj v a ∧ ¬ (v ∈ S ∧ a ∈ boundary adj S \ T)

instance (S T : Finset V) : DecidableRel (cutEdge adj S T) := fun v a => by
  unfold cutEdge
  infer_instance

theorem reach_split (S : Finset V) : reach adj S = inside adj S ∪ boundary adj S := by
  ext z
  simp only [inside, boundary, mem_union, mem_inter, mem_sdiff]
  tauto

theorem terminal_growth (S : Finset V) :
    growth adj (inside adj S) (boundary adj S) =
      (reach adj (reach adj S) \ reach adj S).card := by
  have hi : reach adj (inside adj S) ⊆ reach adj S := reach_mono adj inter_subset_right
  have hs := reach_split adj S
  have he : reach adj (reach adj S) \ reach adj S =
      reach adj (boundary adj S) \ (inside adj S ∪ boundary adj S) := by
    conv_lhs => rw [hs, reach_union]
    ext z
    simp only [mem_sdiff, mem_union]
    have hz : z ∈ reach adj (inside adj S) → z ∈ inside adj S ∪ boundary adj S := by
      intro h
      rw [← hs]
      exact hi h
    simp only [mem_union] at hz
    tauto
  exact congrArg card he.symm

/-- The prescribed first vertex pays its entire induced surplus immediately. -/
theorem first_batch
    (noDigon : ∀ v a, adj v a → ¬ adj a v)
    (bad : ∀ v, (second adj v).card + (inN adj v).card < 2 * (outN adj v).card)
    (S : Finset V) (v : V) (hv : v ∈ S) (gamma : ℕ)
    (hgamma : (localSecond adj S v).card + (inN adj v).card =
      2 * (outN adj v ∩ S).card + gamma) :
    let Q := outN adj v \ S
    Q ⊆ boundary adj S ∧ Q.Nonempty ∧
      growth adj (inside adj S) Q + gamma < 2 * Q.card := by
  let Q := outN adj v \ S
  let C := reach adj Q \ (inside adj S ∪ Q)
  have hQE : Q ⊆ boundary adj S := by
    intro a ha
    obtain ⟨haO, haS⟩ := mem_sdiff.mp ha
    exact mem_sdiff.mpr ⟨(mem_reach adj S a).mpr ⟨v, hv, by simpa using haO⟩, haS⟩
  have hC : C ⊆ second adj v := by
    intro z hz
    obtain ⟨hzF, hznot⟩ := mem_sdiff.mp hz
    obtain ⟨a, haQ, haz⟩ := (mem_reach adj Q z).mp hzF
    have hva : adj v a := by simpa using (mem_sdiff.mp haQ).1
    refine (mem_second adj v z).mpr ⟨?_, ?_, a, hva, haz⟩
    · intro h
      subst z
      exact noDigon v a hva haz
    · intro hvz
      apply hznot
      by_cases hzS : z ∈ S
      · exact mem_union_left _ (mem_inter.mpr
          ⟨(mem_reach adj S z).mpr ⟨v, hv, hvz⟩, hzS⟩)
      · exact mem_union_right _ (mem_sdiff.mpr ⟨by simpa using hvz, hzS⟩)
  have hL : localSecond adj S v ⊆ second adj v := by
    intro z hz
    obtain ⟨_, hne, hnon, a, _, hva, haz⟩ := mem_filter.mp hz
    exact (mem_second adj v z).mpr ⟨hne, hnon, a, hva, haz⟩
  have hLI : localSecond adj S v ⊆ inside adj S := by
    intro z hz
    obtain ⟨hzS, _, _, a, haS, _, haz⟩ := mem_filter.mp hz
    exact mem_inter.mpr ⟨(mem_reach adj S z).mpr ⟨a, haS, haz⟩, hzS⟩
  have hd : Disjoint (localSecond adj S v) C := by
    apply disjoint_left.mpr
    intro z hzL hzC
    exact (mem_sdiff.mp hzC).2 (mem_union_left _ (hLI hzL))
  have hc := card_le_card (union_subset hL hC)
  rw [card_union_of_disjoint hd] at hc
  have ho := card_sdiff_add_card_inter (outN adj v) S
  change Q.card + (outN adj v ∩ S).card = (outN adj v).card at ho
  have hb := bad v
  have bound : growth adj (inside adj S) Q + gamma < 2 * Q.card := by
    change C.card + gamma < 2 * Q.card
    omega
  have hn : Q.Nonempty := card_pos.mp (by omega)
  exact ⟨hQE, hn, bound⟩

/-- Pure set bookkeeping for adjoining a batch disjoint from the old set and I. -/
theorem growth_increment (I T Q : Finset V) (hQI : Disjoint Q I) (hQT : Disjoint Q T) :
    growth adj I (T ∪ Q) + (Q ∩ reach adj T).card =
      growth adj I T + (reach adj Q \ (I ∪ T ∪ Q ∪ reach adj T)).card := by
  let B := reach adj T \ (I ∪ T ∪ Q)
  let C := reach adj Q \ (I ∪ T ∪ Q ∪ reach adj T)
  let G := Q ∩ reach adj T
  have old : reach adj T \ (I ∪ T) = B ∪ G := by
    ext z
    simp only [B, G, mem_sdiff, mem_union, mem_inter]
    have hi : z ∈ Q → z ∉ I := fun hq hi => disjoint_left.mp hQI hq hi
    have ht : z ∈ Q → z ∉ T := fun hq ht => disjoint_left.mp hQT hq ht
    tauto
  have new : reach adj (T ∪ Q) \ (I ∪ (T ∪ Q)) = B ∪ C := by
    rw [reach_union]
    ext z
    simp only [B, C, mem_sdiff, mem_union]
    tauto
  have oldD : Disjoint B G := by
    apply disjoint_left.mpr
    intro z hzB hzG
    exact (mem_sdiff.mp hzB).2 (mem_union_right _ (mem_inter.mp hzG).1)
  have newD : Disjoint B C := by
    apply disjoint_left.mpr
    intro z hzB hzC
    exact (mem_sdiff.mp hzC).2 (mem_union_right _ (mem_sdiff.mp hzB).1)
  unfold growth
  rw [old, new, card_union_of_disjoint oldD, card_union_of_disjoint newD]
  change B.card + C.card + G.card = B.card + G.card + C.card
  omega

theorem cut_subset (S T : Finset V) (v a : V) (h : cutEdge adj S T v a) : adj v a := h.1

theorem cut_in_subset (S T : Finset V) (v : V) : inN (cutEdge adj S T) v ⊆ inN adj v := by
  intro a ha
  have h : cutEdge adj S T a v := by simpa using ha
  simpa using h.1

theorem good_cut_loses_heads
    (bad : ∀ v, (second adj v).card + (inN adj v).card < 2 * (outN adj v).card)
    (S T : Finset V) (v : V)
    (good : 2 * (outN (cutEdge adj S T) v).card ≤
      (second (cutEdge adj S T) v).card + (inN (cutEdge adj S T) v).card) :
    ∃ a, adj v a ∧ ¬ cutEdge adj S T v a := by
  by_contra hn
  have keep (a : V) (ha : adj v a) : cutEdge adj S T v a := by
    by_contra h
    exact hn ⟨a, ha, h⟩
  have ho : outN (cutEdge adj S T) v = outN adj v := by
    ext a
    simp only [mem_outN]
    exact ⟨fun h => h.1, keep a⟩
  have hs : second (cutEdge adj S T) v ⊆ second adj v := by
    intro z hz
    obtain ⟨hne, hnon, a, hva, haz⟩ := (mem_second (cutEdge adj S T) v z).mp hz
    exact (mem_second adj v z).mpr ⟨hne, fun h => hnon (keep z h), a, hva.1, haz.1⟩
  have hsc := card_le_card hs
  have hic := card_le_card (cut_in_subset adj S T v)
  have hb := bad v
  rw [ho] at good
  omega

theorem cut_second_endpoints (S T : Finset V) (v : V) (hv : v ∈ S) :
    second (cutEdge adj S T) v ⊆ inside adj S ∪ T ∪ reach adj T := by
  intro z hz
  obtain ⟨_, _, a, hva, haz⟩ := (mem_second (cutEdge adj S T) v z).mp hz
  by_cases haS : a ∈ S
  · have hzF : z ∈ reach adj S := (mem_reach adj S z).mpr ⟨a, haS, haz.1⟩
    by_cases hzS : z ∈ S
    · exact mem_union_left _ (mem_union_left _ (mem_inter.mpr ⟨hzF, hzS⟩))
    · have hzT : z ∈ T := by
        by_contra hn
        exact haz.2 ⟨haS, mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨hzF, hzS⟩, hn⟩⟩
      exact mem_union_left _ (mem_union_right _ hzT)
  · have haF : a ∈ reach adj S := (mem_reach adj S a).mpr ⟨v, hv, hva.1⟩
    have haT : a ∈ T := by
      by_contra hn
      exact hva.2 ⟨hv, mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨haF, haS⟩, hn⟩⟩
    exact mem_union_right _ ((mem_reach adj T z).mpr ⟨a, haT, haz.1⟩)

/-- One good vertex in a proper deletion supplies a nonempty improving batch. -/
theorem deletion_batch
    (noDigon : ∀ v a, adj v a → ¬ adj a v)
    (bad : ∀ v, (second adj v).card + (inN adj v).card < 2 * (outN adj v).card)
    (S T : Finset V)
    (good : ∃ v, 2 * (outN (cutEdge adj S T) v).card ≤
      (second (cutEdge adj S T) v).card + (inN (cutEdge adj S T) v).card) :
    ∃ Q : Finset V, Q ⊆ boundary adj S \ T ∧ Q.Nonempty ∧
      growth adj (inside adj S) (T ∪ Q) < growth adj (inside adj S) T + 2 * Q.card := by
  obtain ⟨v, hgood⟩ := good
  obtain ⟨a, hva, hcut⟩ := good_cut_loses_heads adj bad S T v hgood
  have hremoved : v ∈ S ∧ a ∈ boundary adj S \ T := by
    by_contra h
    exact hcut ⟨hva, h⟩
  have hv := hremoved.1
  let I := inside adj S
  let Q := outN adj v ∩ (boundary adj S \ T)
  let C := reach adj Q \ (I ∪ T ∪ Q ∪ reach adj T)
  let G := Q ∩ reach adj T
  have hQ : Q ⊆ boundary adj S \ T := inter_subset_right
  have hQn : Q.Nonempty := ⟨a, mem_inter.mpr ⟨by simpa using hva, hremoved.2⟩⟩
  have hQT : Disjoint Q T := by
    apply disjoint_left.mpr
    exact fun z hz ht => (mem_sdiff.mp (hQ hz)).2 ht
  have hQI : Disjoint Q I := by
    apply disjoint_left.mpr
    intro z hz hi
    exact (mem_sdiff.mp (mem_sdiff.mp (hQ hz)).1).2 (mem_inter.mp hi).2
  have heads : outN adj v ⊆ I ∪ T ∪ Q := by
    intro z hz
    have hzadj : adj v z := by simpa using hz
    have hzF : z ∈ reach adj S := (mem_reach adj S z).mpr ⟨v, hv, hzadj⟩
    by_cases hzS : z ∈ S
    · exact mem_union_left _ (mem_union_left _ (mem_inter.mpr ⟨hzF, hzS⟩))
    · by_cases hzT : z ∈ T
      · exact mem_union_left _ (mem_union_right _ hzT)
      · exact mem_union_right _ (mem_inter.mpr
          ⟨hz, mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨hzF, hzS⟩, hzT⟩⟩)
  have hC : C ⊆ second adj v := by
    intro z hz
    obtain ⟨hzF, hznot⟩ := mem_sdiff.mp hz
    obtain ⟨b, hb, hbz⟩ := (mem_reach adj Q z).mp hzF
    have hvb : adj v b := by simpa using (mem_inter.mp hb).1
    refine (mem_second adj v z).mpr ⟨?_, ?_, b, hvb, hbz⟩
    · intro he
      subst z
      exact noDigon v b hvb hbz
    · intro hvz
      exact hznot (mem_union_left _ (heads (by simpa using hvz)))
  have hnew : second (cutEdge adj S T) v ⊆ (second adj v \ C) ∪ G := by
    intro z hz
    obtain ⟨hne, hnon, b, hvb, hbz⟩ := (mem_second (cutEdge adj S T) v z).mp hz
    have hend := cut_second_endpoints adj S T v hv hz
    have hznotC : z ∉ C := by
      intro hc
      have hn := (mem_sdiff.mp hc).2
      simp only [mem_union] at hend hn
      tauto
    by_cases hold : adj v z
    · have hzrem : z ∈ boundary adj S \ T := by
        by_contra h
        exact hnon ⟨hold, fun hh => h hh.2⟩
      have hzQ : z ∈ Q := mem_inter.mpr ⟨by simpa using hold, hzrem⟩
      have hzF : z ∈ reach adj T := by
        have hnI : z ∉ I := fun h => disjoint_left.mp hQI hzQ h
        have hnT : z ∉ T := (mem_sdiff.mp hzrem).2
        simp only [mem_union] at hend
        tauto
      exact mem_union_right _ (mem_inter.mpr ⟨hzQ, hzF⟩)
    · exact mem_union_left _ (mem_sdiff.mpr
        ⟨(mem_second adj v z).mpr ⟨hne, hold, b, hvb.1, hbz.1⟩, hznotC⟩)
  have hnewcard := (card_le_card hnew).trans (card_union_le _ _)
  rw [card_sdiff_of_subset hC] at hnewcard
  have hCcard := card_le_card hC
  have hincard := card_le_card (cut_in_subset adj S T v)
  have hout : outN (cutEdge adj S T) v = outN adj v \ Q := by
    ext z
    simp only [mem_outN, cutEdge, Q, mem_sdiff, mem_inter, hv, true_and]
    tauto
  have hQold : Q ⊆ outN adj v := inter_subset_left
  have hQcard := card_le_card hQold
  rw [hout, card_sdiff_of_subset hQold] at hgood
  have hb := bad v
  have hcost : C.card < 2 * Q.card + G.card := by omega
  have hg := growth_increment adj I T Q hQI hQT
  change growth adj I (T ∪ Q) + G.card = growth adj I T + C.card at hg
  refine ⟨Q, hQ, hQn, ?_⟩
  change growth adj I (T ∪ Q) < growth adj I T + 2 * Q.card
  omega

omit adj [Fintype V] in
theorem grow_to_boundary (E : Finset V) (g : Finset V → ℕ) (gamma : ℕ)
    (seed : ∃ T ⊆ E, g T + gamma < 2 * T.card)
    (step : ∀ T ⊆ E, T ≠ E → ∃ Q : Finset V, Q ⊆ E \ T ∧ Q.Nonempty ∧
      g (T ∪ Q) < g T + 2 * Q.card) : g E + gamma < 2 * E.card := by
  classical
  let candidates := E.powerset.filter (fun T => g T + gamma < 2 * T.card)
  have hn : candidates.Nonempty := by
    obtain ⟨T, hTE, hT⟩ := seed
    exact ⟨T, mem_filter.mpr ⟨mem_powerset.mpr hTE, hT⟩⟩
  obtain ⟨T, hT, hmax⟩ := exists_max_image candidates card hn
  have hTE : T ⊆ E := mem_powerset.mp (mem_filter.mp hT).1
  have hbound := (mem_filter.mp hT).2
  by_cases heq : T = E
  · simpa [heq] using hbound
  obtain ⟨Q, hQ, hQn, hstep⟩ := step T hTE heq
  have hQT : Disjoint T Q := by
    apply disjoint_left.mpr
    exact fun z hzT hzQ => (mem_sdiff.mp (hQ hzQ)).2 hzT
  have hUE : T ∪ Q ⊆ E := union_subset hTE (hQ.trans sdiff_subset)
  have hcard := card_union_of_disjoint hQT
  have hnew : g (T ∪ Q) + gamma < 2 * (T ∪ Q).card := by omega
  have hm := hmax (T ∪ Q) (mem_filter.mpr ⟨mem_powerset.mpr hUE, hnew⟩)
  have hp := card_pos.mpr hQn
  omega

/-- Prescribed induced surplus plus all deletion witnesses gives the full
boundary bound. Neither a CH bound nor an order bound is assumed. -/
theorem boundary_gamma
    (noDigon : ∀ v a, adj v a → ¬ adj a v)
    (bad : ∀ v, (second adj v).card + (inN adj v).card < 2 * (outN adj v).card)
    (S : Finset V) (v : V) (hv : v ∈ S) (gamma : ℕ)
    (hgamma : (localSecond adj S v).card + (inN adj v).card =
      2 * (outN adj v ∩ S).card + gamma)
    (deleted_good : ∀ T ⊆ boundary adj S, T ≠ boundary adj S →
      ∃ a, 2 * (outN (cutEdge adj S T) a).card ≤
        (second (cutEdge adj S T) a).card + (inN (cutEdge adj S T) a).card) :
    (reach adj (reach adj S) \ reach adj S).card + gamma < 2 * (boundary adj S).card := by
  obtain ⟨hQ, _, hb⟩ := first_batch adj noDigon bad S v hv gamma hgamma
  have hg := grow_to_boundary (boundary adj S) (growth adj (inside adj S)) gamma
    ⟨outN adj v \ S, hQ, hb⟩
    (fun T hT hne => deletion_batch adj noDigon bad S T (deleted_good T hT hne))
  rw [terminal_growth] at hg
  exact hg

@[expose] def ArcMinimal : Prop :=
  ∀ (sub : V → V → Prop) [DecidableRel sub],
    (∀ v a, sub v a → adj v a) → (∃ v a, adj v a ∧ ¬ sub v a) →
      ∃ v, 2 * (outN sub v).card ≤ (second sub v).card + (inN sub v).card

theorem deletion_good_of_arcMinimal (minimal : ArcMinimal adj)
    (S T : Finset V) (hT : T ⊆ boundary adj S) (hne : T ≠ boundary adj S) :
    ∃ v, 2 * (outN (cutEdge adj S T) v).card ≤
      (second (cutEdge adj S T) v).card + (inN (cutEdge adj S T) v).card := by
  have hnot : ¬ boundary adj S ⊆ T := fun h => hne (Subset.antisymm hT h)
  obtain ⟨a, haE, haT⟩ := not_subset.mp hnot
  obtain ⟨v, hvS, hva⟩ := (mem_reach adj S a).mp (mem_sdiff.mp haE).1
  apply minimal (cutEdge adj S T) (fun _ _ h => h.1)
  exact ⟨v, a, hva, fun h => h.2 ⟨hvS, mem_sdiff.mpr ⟨haE, haT⟩⟩⟩

@[expose] def gammaValue (S : Finset V) (v : V) : ℤ :=
  (localSecond adj S v).card + (inN adj v).card - 2 * (outN adj v ∩ S).card

/-- The prompt's vertex-maximum Gamma term, derived rather than assumed.
The local good vertex is supplied by order minimality; `ArcMinimal` supplies
the proper arc-deletion witnesses. -/
theorem maximal_boundary_gamma
    (noDigon : ∀ v a, adj v a → ¬ adj a v)
    (bad : ∀ v, (second adj v).card + (inN adj v).card < 2 * (outN adj v).card)
    (minimal : ArcMinimal adj) (S : Finset V)
    (local_good : ∃ v ∈ S, 2 * (outN adj v ∩ S).card ≤
      (localSecond adj S v).card + (inN adj v ∩ S).card) :
    ∃ v ∈ S, (∀ a ∈ S, gammaValue adj S a ≤ gammaValue adj S v) ∧
      0 ≤ gammaValue adj S v ∧
      ((reach adj (reach adj S) \ reach adj S).card : ℤ) + gammaValue adj S v <
        2 * (boundary adj S).card := by
  obtain ⟨u, huS, hu⟩ := local_good
  obtain ⟨v, hvS, hmax⟩ := exists_max_image S (gammaValue adj S) ⟨u, huS⟩
  have huin := card_le_card (inter_subset_left : inN adj u ∩ S ⊆ inN adj u)
  have huG : 0 ≤ gammaValue adj S u := by unfold gammaValue; omega
  have hvG : 0 ≤ gammaValue adj S v := huG.trans (hmax u huS)
  let gamma := (gammaValue adj S v).toNat
  have heq : (gamma : ℤ) = gammaValue adj S v := Int.toNat_of_nonneg hvG
  have hg : (localSecond adj S v).card + (inN adj v).card =
      2 * (outN adj v ∩ S).card + gamma := by
    unfold gammaValue at heq
    omega
  have hb := boundary_gamma adj noDigon bad S v hvS gamma hg
    (fun T hT hne => deletion_good_of_arcMinimal adj minimal S T hT hne)
  refine ⟨v, hvS, hmax, hvG, ?_⟩
  omega

end CH.CompromiseSubset

#print axioms CH.CompromiseSubset.first_batch
#print axioms CH.CompromiseSubset.growth_increment
#print axioms CH.CompromiseSubset.deletion_batch
#print axioms CH.CompromiseSubset.boundary_gamma
#print axioms CH.CompromiseSubset.maximal_boundary_gamma
