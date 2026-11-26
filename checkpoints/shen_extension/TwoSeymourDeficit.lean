import OAI.Combinatorics.SecondNeighborhood.Main

/-!
Subset deficits in an arc-minimal graph with one distinguished vertex.

This is the deletion step of the vendored one-vertex proof, run in a graph where every vertex
other than `g` is bad and every sinkless oriented graph with fewer arcs has two good vertices.
The good vertex produced by the deletion is then always different from `g`, so the step and
the resulting strict deficit hold for every source set that avoids `g`.
(Two-vertex strengthening of Seymour's theorem, after M. Kang, October 2026.)
-/

namespace LeanCH.BR.TwoSeymour

open OAI.SeymourSecondNeighborhood

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [Fintype V] in
theorem card_add_loss_le_card_add_gain
    (old new loss gain : Finset V) (hloss : loss ⊆ old)
    (hdisjoint : Disjoint loss new) (hgain : new \ old ⊆ gain) :
    new.card + loss.card ≤ old.card + gain.card := by
  classical
  have hsubset : new ⊆ (old \ loss) ∪ gain := by
    intro x hx
    by_cases hxo : x ∈ old
    · apply Finset.mem_union.mpr
      left
      apply Finset.mem_sdiff.mpr
      refine ⟨hxo, ?_⟩
      intro hxl
      exact Finset.disjoint_left.mp hdisjoint hxl hx
    · exact Finset.mem_union.mpr (Or.inr (hgain (Finset.mem_sdiff.mpr ⟨hx, hxo⟩)))
  have hcard := (Finset.card_le_card hsubset).trans
    (Finset.card_union_le (old \ loss) gain)
  have hpartition := Finset.card_sdiff_add_card_eq_card hloss
  omega

theorem image_sdiff_union_card_balance (r : V → V → Prop)
    (I T Q : Finset V) (hdisjoint : Disjoint Q (I ∪ T)) :
    (image r (T ∪ Q) \ (I ∪ (T ∪ Q))).card + (Q ∩ image r T).card =
      (image r T \ (I ∪ T)).card +
        (image r Q \ (I ∪ T ∪ Q ∪ image r T)).card := by
  classical
  let A := image r T \ (I ∪ T)
  let C := image r Q \ (I ∪ T ∪ Q ∪ image r T)
  have hsplit : image r (T ∪ Q) \ (I ∪ (T ∪ Q)) = (A \ Q) ∪ C := by
    ext x
    simp only [A, C, image_union, Finset.mem_sdiff, Finset.mem_union]
    tauto
  have hpieces : Disjoint (A \ Q) C := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    simp only [A, C, Finset.mem_sdiff, Finset.mem_union] at hx hy
    tauto
  have hinter : A ∩ Q = Q ∩ image r T := by
    ext x
    constructor
    · intro hx
      obtain ⟨hxA, hxQ⟩ := Finset.mem_inter.mp hx
      exact Finset.mem_inter.mpr ⟨hxQ, (Finset.mem_sdiff.mp hxA).1⟩
    · intro hx
      obtain ⟨hxQ, hximage⟩ := Finset.mem_inter.mp hx
      apply Finset.mem_inter.mpr
      refine ⟨Finset.mem_sdiff.mpr ⟨hximage, ?_⟩, hxQ⟩
      exact Finset.disjoint_left.mp hdisjoint hxQ
  have hpartition := Finset.card_sdiff_add_card_inter A Q
  rw [hinter] at hpartition
  rw [hsplit, Finset.card_union_of_disjoint hpieces]
  change (A \ Q).card + C.card + (Q ∩ image r T).card = A.card + C.card
  omega

/-- The deletion step for a source set avoiding the distinguished vertex. -/
theorem deficit_step (r : V → V → Prop) (hr : IsOriented r) (g : V)
    (hsucc : ∃ h, r g h)
    (hbad : ∀ v, v ≠ g → (secondNeighbors r v).card < (firstNeighbors r v).card)
    (hmin : ∀ s : V → V → Prop, IsOriented s → (arcSet s).card < (arcSet r).card →
      (∀ v, ∃ w, s v w) → ∃ u v, u ≠ v ∧ GoodVertex s u ∧ GoodVertex s v)
    (S T : Finset V) (hgS : g ∉ S) (hT : T ⊆ image r S \ S)
    (hproper : T ≠ image r S \ S) :
    ∃ Q : Finset V, Q.Nonempty ∧ Q ⊆ (image r S \ S) \ T ∧
      deficitPotential r S (T ∪ Q) < deficitPotential r S T + Q.card := by
  classical
  let I := image r S ∩ S
  let E := image r S \ S
  let s : V → V → Prop := fun x y => r x y ∧ ¬ (x ∈ S ∧ y ∈ E \ T)
  have hs : IsOriented s := hr.mono (fun _ _ h => h.1)
  have hremain : (E \ T).Nonempty := by
    by_contra hn
    have hET : E ⊆ T := by
      intro y hy
      by_contra hyT
      exact hn ⟨y, Finset.mem_sdiff.mpr ⟨hy, hyT⟩⟩
    exact hproper (Finset.Subset.antisymm hT hET)
  obtain ⟨b, hb⟩ := hremain
  have hbE := (Finset.mem_sdiff.mp hb).1
  have hbimage := (Finset.mem_sdiff.mp hbE).1
  obtain ⟨a, haS, hab⟩ := mem_image.mp hbimage
  have harcSubset : arcSet s ⊆ arcSet r := by
    apply arcSet_mono
    intro x y hxy
    exact hxy.1
  have harcStrict : (arcSet s).card < (arcSet r).card := by
    apply Finset.card_lt_card
    refine ⟨harcSubset, ?_⟩
    intro hreverse
    have habmem : (a, b) ∈ arcSet r := mem_arcSet.mpr hab
    have hsab : s a b := mem_arcSet.mp (hreverse habmem)
    exact hsab.2 ⟨haS, hb⟩
  have hgood : ∃ v, v ≠ g ∧ (firstNeighbors s v).card ≤ (secondNeighbors s v).card := by
    by_cases hsink : ∃ v, ∀ w, ¬ s v w
    · obtain ⟨v, hv⟩ := hsink
      refine ⟨v, ?_, sink_goodVertex hv⟩
      intro hvg
      obtain ⟨h, hgh⟩ := hsucc
      apply hv h
      rw [hvg]
      exact ⟨hgh, fun hc => hgS hc.1⟩
    · have hno : ∀ v, ∃ w, s v w := by
        intro v
        by_contra hn
        exact hsink ⟨v, fun w hw => hn ⟨w, hw⟩⟩
      obtain ⟨u, v, huv, hu, hv⟩ := hmin s hs harcStrict hno
      by_cases hug : u = g
      · exact ⟨v, fun hvg => huv (hug.trans hvg.symm), hv⟩
      · exact ⟨u, hug, hu⟩
  obtain ⟨v, hvg, hvGood⟩ := hgood
  have hlost : ∃ q, r v q ∧ ¬ s v q := by
    by_contra hn
    have hkeep : ∀ q, r v q → s v q := by
      intro q hvq
      by_contra hsfalse
      exact hn ⟨q, hvq, hsfalse⟩
    have hfirst : firstNeighbors r v ⊆ firstNeighbors s v := by
      intro q hq
      exact mem_firstNeighbors.mpr (hkeep q (mem_firstNeighbors.mp hq))
    have hsecond : secondNeighbors s v ⊆ secondNeighbors r v := by
      intro w hw
      obtain ⟨hwv, hnsvw, u, hsvu, hsuw⟩ := mem_secondNeighbors.mp hw
      apply mem_secondNeighbors.mpr
      exact ⟨hwv, (fun hvw => hnsvw (hkeep w hvw)), u, hsvu.1, hsuw.1⟩
    have hfirstCard := Finset.card_le_card hfirst
    have hsecondCard := Finset.card_le_card hsecond
    have hvBad := hbad v hvg
    omega
  obtain ⟨q, hvq, hnsvq⟩ := hlost
  have hcut : v ∈ S ∧ q ∈ E \ T := by
    by_contra hn
    exact hnsvq ⟨hvq, hn⟩
  have hvS := hcut.1
  let Q := firstNeighbors r v ∩ (E \ T)
  have hQnonempty : Q.Nonempty :=
    ⟨q, Finset.mem_inter.mpr ⟨mem_firstNeighbors.mpr hvq, hcut.2⟩⟩
  have hQsubset : Q ⊆ E \ T := by
    intro x hx
    exact (Finset.mem_inter.mp hx).2
  have hQfirst : Q ⊆ firstNeighbors r v := by
    intro x hx
    exact (Finset.mem_inter.mp hx).1
  have hQdisjoint : Disjoint Q (I ∪ T) := by
    apply Finset.disjoint_left.mpr
    intro x hxQ hxIT
    obtain ⟨hxE, hxnotT⟩ := Finset.mem_sdiff.mp (hQsubset hxQ)
    have hxnotS := (Finset.mem_sdiff.mp hxE).2
    rcases Finset.mem_union.mp hxIT with hxI | hxT
    · exact hxnotS (Finset.mem_inter.mp hxI).2
    · exact hxnotT hxT
  have hfirstEq : firstNeighbors s v = firstNeighbors r v \ Q := by
    ext x
    constructor
    · intro hx
      have hsx := mem_firstNeighbors.mp hx
      apply Finset.mem_sdiff.mpr
      refine ⟨mem_firstNeighbors.mpr hsx.1, ?_⟩
      intro hxQ
      exact hsx.2 ⟨hvS, hQsubset hxQ⟩
    · intro hx
      obtain ⟨hxr, hxnotQ⟩ := Finset.mem_sdiff.mp hx
      apply mem_firstNeighbors.mpr
      refine ⟨mem_firstNeighbors.mp hxr, ?_⟩
      rintro ⟨_, hxET⟩
      exact hxnotQ (Finset.mem_inter.mpr ⟨hxr, hxET⟩)
  have hfirstCard : (firstNeighbors s v).card + Q.card = (firstNeighbors r v).card := by
    rw [hfirstEq]
    exact Finset.card_sdiff_add_card_eq_card hQfirst
  have hfirstCover : firstNeighbors r v ⊆ (I ∪ T) ∪ Q := by
    intro x hx
    have hximage := firstNeighbors_subset_image hvS hx
    by_cases hxS : x ∈ S
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr
        (Or.inl (Finset.mem_inter.mpr ⟨hximage, hxS⟩))))
    · by_cases hxT : x ∈ T
      · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr hxT)))
      · exact Finset.mem_union.mpr (Or.inr (Finset.mem_inter.mpr
          ⟨hx, Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨hximage, hxS⟩, hxT⟩⟩))
  have hfirstNewCover : firstNeighbors s v ⊆ I ∪ T := by
    intro x hx
    rw [hfirstEq] at hx
    obtain ⟨hxr, hxnotQ⟩ := Finset.mem_sdiff.mp hx
    rcases Finset.mem_union.mp (hfirstCover hxr) with hxIT | hxQ
    · exact hxIT
    · exact False.elim (hxnotQ hxQ)
  have hsourceCover : ∀ u ∈ S, ∀ x, s u x → x ∈ I ∪ T := by
    intro u huS x hsux
    have hximage : x ∈ image r S := mem_image.mpr ⟨u, huS, hsux.1⟩
    by_cases hxS : x ∈ S
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_inter.mpr ⟨hximage, hxS⟩))
    · by_cases hxT : x ∈ T
      · exact Finset.mem_union.mpr (Or.inr hxT)
      · exact False.elim (hsux.2 ⟨huS,
          Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨hximage, hxS⟩, hxT⟩⟩)
  have hpathCover : ∀ x, (∃ u, s v u ∧ s u x) → x ∈ (I ∪ T) ∪ image r T := by
    intro x hx
    obtain ⟨u, hsvu, hsux⟩ := hx
    rcases Finset.mem_union.mp (hfirstNewCover (mem_firstNeighbors.mpr hsvu)) with huI | huT
    · exact Finset.mem_union.mpr
        (Or.inl (hsourceCover u (Finset.mem_inter.mp huI).2 x hsux))
    · exact Finset.mem_union.mpr (Or.inr (mem_image.mpr ⟨u, huT, hsux.1⟩))
  let B := Q ∩ image r T
  let C := image r Q \ (I ∪ T ∪ Q ∪ image r T)
  have hgain : secondNeighbors s v \ secondNeighbors r v ⊆ B := by
    intro x hx
    obtain ⟨hxnew, hxnotOld⟩ := Finset.mem_sdiff.mp hx
    obtain ⟨hxv, hnsvx, u, hsvu, hsux⟩ := mem_secondNeighbors.mp hxnew
    have hrvx : r v x := by
      by_contra hn
      exact hxnotOld (mem_secondNeighbors.mpr ⟨hxv, hn, u, hsvu.1, hsux.1⟩)
    have hxcut : v ∈ S ∧ x ∈ E \ T := by
      by_contra hn
      exact hnsvx ⟨hrvx, hn⟩
    have hxQ : x ∈ Q := Finset.mem_inter.mpr ⟨mem_firstNeighbors.mpr hrvx, hxcut.2⟩
    apply Finset.mem_inter.mpr
    refine ⟨hxQ, ?_⟩
    rcases Finset.mem_union.mp (hpathCover x ⟨u, hsvu, hsux⟩) with hxIT | hximage
    · exact False.elim (Finset.disjoint_left.mp hQdisjoint hxQ hxIT)
    · exact hximage
  have hloss : C ⊆ secondNeighbors r v := by
    intro x hx
    obtain ⟨hximage, hxnot⟩ := Finset.mem_sdiff.mp hx
    obtain ⟨u, huQ, hrux⟩ := mem_image.mp hximage
    have hrvu := mem_firstNeighbors.mp (hQfirst huQ)
    apply mem_secondNeighbors.mpr
    refine ⟨?_, ?_, u, hrvu, hrux⟩
    · intro hxv
      subst x
      exact hr.asymmetric hrvu hrux
    · intro hrvx
      exact hxnot (Finset.mem_union.mpr
        (Or.inl (hfirstCover (mem_firstNeighbors.mpr hrvx))))
  have hlossDisjoint : Disjoint C (secondNeighbors s v) := by
    apply Finset.disjoint_left.mpr
    intro x hxC hxnew
    have hxnot := (Finset.mem_sdiff.mp hxC).2
    have hxcover := hpathCover x (mem_secondNeighbors.mp hxnew).2.2
    apply hxnot
    rcases Finset.mem_union.mp hxcover with hxIT | hximage
    · exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl hxIT)))
    · exact Finset.mem_union.mpr (Or.inr hximage)
  have hsecondCard := card_add_loss_le_card_add_gain
    (secondNeighbors r v) (secondNeighbors s v) C B hloss hlossDisjoint hgain
  have hbalance : deficitPotential r S (T ∪ Q) + B.card =
      deficitPotential r S T + C.card := by
    exact image_sdiff_union_card_balance r I T Q hQdisjoint
  have hvBad := hbad v hvg
  refine ⟨Q, hQnonempty, hQsubset, ?_⟩
  omega

/-- Strict subset deficit for every source set avoiding the distinguished vertex. -/
theorem deficit_avoiding (r : V → V → Prop) (hr : IsOriented r) (g : V)
    (hsucc : ∃ h, r g h)
    (hbad : ∀ v, v ≠ g → (secondNeighbors r v).card < (firstNeighbors r v).card)
    (hmin : ∀ s : V → V → Prop, IsOriented s → (arcSet s).card < (arcSet r).card →
      (∀ v, ∃ w, s v w) → ∃ u v, u ≠ v ∧ GoodVertex s u ∧ GoodVertex s v)
    (S : Finset V) (hgS : g ∉ S) (hE : (image r S \ S).Nonempty) :
    (image r (image r S) \ image r S).card < (image r S \ S).card := by
  classical
  have hg : deficitPotential r S (image r S \ S) < (image r S \ S).card := by
    apply strict_deficit_of_augmentation (image r S \ S) hE (deficitPotential r S)
    · simp [deficitPotential]
    · intro T hT hTproper
      exact deficit_step r hr g hsucc hbad hmin S T hgS hT hTproper
  rw [deficitPotential_terminal] at hg
  exact hg

/-- Passing to the graph with `g` deleted, written inside the original vertex set:
the deficit stays weak, and it is strict when the unique successor `h` of `g`
is not reached in one or two steps. -/
theorem erase_deficit (r : V → V → Prop) (hr : IsOriented r) (g h : V) (hgh : r g h)
    (S : Finset V)
    (hD : (image r (image r S) \ image r S).card < (image r S \ S).card) (hgS : g ∉ S) :
    ((image r ((image r S).erase g)).erase g \ (image r S).erase g).card ≤
        ((image r S).erase g \ S).card ∧
      (h ∉ (image r S).erase g → h ∉ (image r ((image r S).erase g)).erase g →
        ((image r ((image r S).erase g)).erase g \ (image r S).erase g).card <
          ((image r S).erase g \ S).card) := by
  classical
  have hhg : h ≠ g := by
    intro heq
    rw [heq] at hgh
    exact hr.loopless g hgh
  have hsub : (image r ((image r S).erase g)).erase g \ (image r S).erase g ⊆
      image r (image r S) \ image r S := by
    intro x hx
    obtain ⟨hxM, hxN⟩ := Finset.mem_sdiff.mp hx
    obtain ⟨hxg, hxim⟩ := Finset.mem_erase.mp hxM
    refine Finset.mem_sdiff.mpr ⟨image_mono r (Finset.erase_subset g _) hxim, ?_⟩
    intro hxS
    exact hxN (Finset.mem_erase.mpr ⟨hxg, hxS⟩)
  have hle := Finset.card_le_card hsub
  by_cases hgN : g ∈ image r S
  · have hgE : g ∈ image r S \ S := Finset.mem_sdiff.mpr ⟨hgN, hgS⟩
    have hEq : (image r S).erase g \ S = (image r S \ S).erase g := by
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_erase]
      tauto
    have hcard := Finset.card_erase_add_one hgE
    rw [← hEq] at hcard
    refine ⟨by omega, ?_⟩
    intro h1 h2
    have hhN : h ∉ image r S := fun hc => h1 (Finset.mem_erase.mpr ⟨hhg, hc⟩)
    have hhD : h ∈ image r (image r S) \ image r S :=
      Finset.mem_sdiff.mpr ⟨mem_image.mpr ⟨g, hgN, hgh⟩, hhN⟩
    have hsub' : (image r ((image r S).erase g)).erase g \ (image r S).erase g ⊆
        (image r (image r S) \ image r S).erase h := by
      intro x hx
      refine Finset.mem_erase.mpr ⟨?_, hsub hx⟩
      intro hxh
      rw [hxh] at hx
      exact h2 (Finset.mem_sdiff.mp hx).1
    have hle' := Finset.card_le_card hsub'
    have hcard' := Finset.card_erase_add_one hhD
    omega
  · have hEq : (image r S).erase g = image r S := Finset.erase_eq_of_notMem hgN
    rw [hEq]
    rw [hEq] at hle
    exact ⟨by omega, fun _ _ => by omega⟩

end LeanCH.BR.TwoSeymour

#print axioms LeanCH.BR.TwoSeymour.deficit_avoiding
#print axioms LeanCH.BR.TwoSeymour.erase_deficit
