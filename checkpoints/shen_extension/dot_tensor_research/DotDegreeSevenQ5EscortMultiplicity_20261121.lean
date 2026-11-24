import checkpoints.shen_extension.dot_tensor_research.DotDegreeSevenQ5SameBank_20261121

namespace LeanCH.BR.DotDegreeSevenLow
open Finset BRq2 BRq3 BR45 BRsGen

/-- Source-label relations left when one full cycle row is used by
several different short banks. The marks are its first and second
cycle successors; they are not free scalar variables. -/
structure SharedEscortMarks (D : CH.Digraph) (V X J : Finset ℕ)
    (s a : ℕ→ℕ) (T : ℕ→Finset ℕ) : Prop where
  xV : X⊆V
  x7 : X.card=7
  sMem : ∀ i∈J, s i∈X
  sInj : (↑J : Set ℕ).InjOn s
  avoidS : ∀ i∈J, ∀ x∈X, D x (s i)≠true
  aV : ∀ i∈J, a i∈V
  aOut : ∀ i∈J, a i∉X
  aArc : ∀ i∈J, D (s i) (a i)=true
  aNot : ∀ i∈J, a i∉T i
  aOther : ∀ i∈J, ∀ j∈J, i≠j → a i∈T j
  support : ∀ i∈J, ∀ x∈X, x≠s i → outN D V x⊆X∪T i

private theorem escort_a_inj {D : CH.Digraph} {V X J : Finset ℕ}
    {s a : ℕ→ℕ} {T : ℕ→Finset ℕ} (P : SharedEscortMarks D V X J s a T) :
    (↑J : Set ℕ).InjOn a := by
  intro i hi j hj e
  by_contra ne
  have v := P.aOther i hi j hj ne
  rw [e] at v
  exact P.aNot j hj v

/-- With a nonempty common core, its actual sink row contributes seven
heads besides all the distinct second successors from the other banks. -/
theorem sharedEscort_thick_spill {D : CH.Digraph} {V X J : Finset ℕ}
    {s a : ℕ→ℕ} {T : ℕ→Finset ℕ}
    (hf : QFree D V 5) (ho : OutEq 7 D V)
    (P : SharedEscortMarks D V X J s a T) (lo : 2≤J.card) (hi : J.card≤6) :
    ∀ i∈J, J.card+6≤(T i).card := by
  classical
  let Y := J.image s
  let K := X\Y
  have yX : Y⊆X := by
    intro x hx
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hx
    exact P.sMem i hi
  have yJ : Y.card=J.card := card_image_of_injOn P.sInj
  have size : K.card+J.card=7 := by
    have e := card_sdiff_add_card_eq_card yX
    simpa only [K,yJ,P.x7] using e
  have kv : K⊆V := sdiff_subset.trans P.xV
  obtain ⟨y,hy,sink⟩ := exists_sink (hf.mono_set kv) (card_pos.mp (by omega)) (by omega)
  have my (i) (hi : i∈J) : outN D V y⊆T i := by
    have yX := (mem_sdiff.mp hy).1
    have nes : y≠s i := by
      intro e
      exact (mem_sdiff.mp hy).2 (mem_image.mpr ⟨i,hi,e.symm⟩)
    intro x hx
    rcases mem_union.mp (P.support i hi y yX nes hx) with inX|inT
    · have arc := (mem_outN.mp hx).2
      by_cases xy : x∈Y
      · obtain ⟨j,jJ,rfl⟩ := mem_image.mp xy
        exact (P.avoidS j jJ y yX arc).elim
      · exact (sink x (mem_sdiff.mpr ⟨inX,xy⟩) arc).elim
    · exact inT
  intro i ii
  let A := (J.erase i).image a
  have aT : A⊆T i := by
    intro x hx
    obtain ⟨j,jm,rfl⟩ := mem_image.mp hx
    exact P.aOther j (mem_erase.mp jm).2 i ii (mem_erase.mp jm).1
  have aJ : A.card=J.card-1 := by
    rw [show A=(J.erase i).image a from rfl,card_image_of_injOn,card_erase_of_mem ii]
    exact (escort_a_inj P).mono (fun _ hx => mem_of_mem_erase hx)
  have sep : Disjoint A (outN D V y) := disjoint_left.mpr (by
    intro x xa xy
    obtain ⟨j,hj,rfl⟩ := mem_image.mp xa
    exact (P.aNot j (mem_erase.mp hj).2) (my j (mem_erase.mp hj).2 xy))
  have cnt := card_le_card (union_subset aT (my i ii))
  rw [card_union_of_disjoint sep,aJ,ho y (kv hy)] at cnt
  omega

#print axioms sharedEscort_thick_spill
end LeanCH.BR.DotDegreeSevenLow

