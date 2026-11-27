import checkpoints.shen_extension.TwoMarks

/-! Simultaneous repairs across a cut in the retained graph of a marked bank. -/

namespace LeanCH.BR.CutDeficit

open Finset BRq2 BRq3 BR45 OAI.SeymourSecondNeighborhood
open FragmentScoreEquality

/-- Every new arc goes from outside the cut to inside it. A return of length
one or two in the retained carrier prevents adding the arc. -/
def SafeCut (D : CH.Digraph) (U C : Finset ℕ) (A : ℕ → ℕ → Prop) : Prop :=
  ∀ u ∈ U, ∀ z ∈ U, A u z → u ∉ C ∧ z ∈ C ∧ D u z ≠ true ∧
    D z u ≠ true ∧ ∀ w ∈ U, D z w = true → D w u ≠ true

private abbrev augmented (D : CH.Digraph) (U : Finset ℕ) (A : ℕ → ℕ → Prop)
    (u z : ↥U) := D u.val z.val = true ∨ A u.val z.val

private theorem oriented_tri {D U q C A} (free : QFree D U q) (cut : 3 ≤ q)
    (safe : SafeCut D U C A) :
    IsOriented (augmented D U A) ∧
      ∀ u v w, augmented D U A u v → augmented D U A v w → ¬ augmented D U A w u := by
  have info {u z : ↥U} := safe u.val u.property z.val z.property
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rintro u (old | new)
    · exact loopfree free (by omega) u.property old
    · exact (info new).1 (info new).2.1
  · rintro u v (uv | uv) (vu | vu)
    · exact digonfree free (by omega) u.property v.property uv vu
    · exact (info vu).2.2.2.1 uv
    · exact (info uv).2.2.2.1 vu
    · exact (info vu).1 (info uv).2.1
  · rintro u v w (uv | uv) (vw | vw) (wu | wu)
    · exact free u 3 (by decide) cut
        (.step v.property uv (.step w.property vw (.step u.property wu (.refl _))))
    · exact (info wu).2.2.2.2 _ v.property uv vw
    · exact (info vw).2.2.2.2 _ u.property wu uv
    · exact (info wu).1 (info vw).2.1
    · exact (info uv).2.2.2.2 _ w.property vw wu
    · exact (info uv).1 (info wu).2.1
    · exact (info vw).1 (info uv).2.1
    · exact (info vw).1 (info uv).2.1

noncomputable def gains (U : Finset ℕ) (P : ℕ → Prop) : Finset ℕ := by
  classical
  exact U.filter P

private theorem neighbors_card {U : Finset ℕ} (S : Finset ℕ) (P : ℕ → Prop)
    (inside : S ⊆ U) (separate : ∀ z ∈ S, ¬ P z) (R : ↥U → ↥U → Prop) (v : ↥U)
    (edges : ∀ z : ↥U, R v z ↔ z.val ∈ S ∨ P z.val) :
    (firstNeighbors R v).card = S.card + (gains U P).card := by
  classical
  have eq : (firstNeighbors R v).image Subtype.val = S ∪ gains U P := by
    ext z
    constructor
    · rintro hz
      obtain ⟨a, ha, rfl⟩ := mem_image.mp hz
      rcases (edges a).mp (mem_firstNeighbors.mp ha) with h | h
      · exact mem_union_left _ h
      · exact mem_union_right _ (mem_filter.mpr ⟨a.property, h⟩)
    · intro hz
      have hzU : z ∈ U := (union_subset inside (filter_subset _ _)) hz
      refine mem_image.mpr ⟨⟨z, hzU⟩, mem_firstNeighbors.mpr ((edges _).mpr ?_), rfl⟩
      exact (mem_union.mp hz).imp id (fun h => (mem_filter.mp h).2)
  have disj : Disjoint S (gains U P) :=
    disjoint_left.mpr fun z hs hg => separate z hs (mem_filter.mp hg).2
  rw [← card_image_of_injective _ Subtype.val_injective, eq, card_union_of_disjoint disj]

/-- The two-unit deficit persists after all of the designated repairs. Paying the
marked row also forces the four-unit bound for a graph with no short row. -/
theorem cut_bounds {D U q t x C A} (carrier : OneShortCarrier D U q t x)
    (cut : 3 ≤ q) (room : U.card ≤ 3 * t) (ht : 2 ≤ t)
    (marked : t ≤ (outN D U x).card + 1) (safe : SafeCut D U C A) :
    let bill := ∑ v : ↥U, (t - ((inN D U v.val).card + (gains U (fun u => A u v.val)).card))
    2 ≤ bill ∧ (t ≤ (outN D U x).card + (gains U (A x)).card → 4 ≤ bill) := by
  classical
  let R := augmented D U A
  let m : ↥U := ⟨x, carrier.marked⟩
  let : Nonempty ↥U := ⟨m⟩
  obtain ⟨orient, tri⟩ := oriented_tri carrier.free cut safe
  have size : Fintype.card ↥U ≤ 3 * t := by simpa using room
  have out (v : ↥U) :
      (firstNeighbors R v).card = (outN D U v.val).card + (gains U (A v.val)).card := by
    refine neighbors_card _ _ outN_subset ?_ R v ?_
    · intro z hz h
      exact (safe _ v.property _ (mem_outN.mp hz).1 h).2.2.1 (mem_outN.mp hz).2
    · intro z
      simp [R, augmented, mem_outN, z.property]
  have inn (v : ↥U) :
      (firstNeighbors (TwoSeymour.rev R) v).card =
        (inN D U v.val).card + (gains U (fun u => A u v.val)).card := by
    refine neighbors_card _ _ (fun _ h => (mem_inN.mp h).1) ?_ (TwoSeymour.rev R) v ?_
    · intro z hz h
      exact (safe _ (mem_inN.mp hz).1 _ v.property h).2.2.1 (mem_inN.mp hz).2
    · intro z
      simp [R, augmented, TwoSeymour.rev, mem_inN, z.property]
  have other (v : ↥U) (ne : v ≠ m) : t ≤ (firstNeighbors R v).card := by
    rw [out]
    exact (carrier.other _ v.property (fun h => ne (Subtype.ext h))).trans (Nat.le_add_right ..)
  constructor
  · have paid : t ≤ (firstNeighbors R m).card + 1 := by
      rw [out]; change t ≤ (outN D U x).card + _ + 1; omega
    simpa only [inn] using TwoSeymour.overload (r := R) orient tri size ht paid other
  · intro h
    have every (v : ↥U) : t ≤ (firstNeighbors R v).card := by
      by_cases eq : v = m
      · subst v; rw [out]; exact h
      · exact other v eq
    simpa only [inn] using TwoSeymour.parent_deficit (r := R) orient tri size ht every

#print axioms cut_bounds

end LeanCH.BR.CutDeficit

