import checkpoints.shen_extension.CycleExteriorPacking
import checkpoints.shen_extension.SecondShellClasses
import LeanCH.BR.BRShortestCycle

namespace LeanCH.BR.CycleRowMultiplicity
open Finset BRq2 BRq3 BR45 BRsGen ExteriorPacking

/-- If every row of a set misses at most c other labels, a shortest
internal cycle would have at most c+2 vertices. -/
theorem dense_choices {D S q c} (free : QFree D S q) (cut : c+2≤q)
    (dense : ∀x∈S,S.card≤(outN D S x).card+c+1) : S.card≤c+1 := by
  by_contra! many
  have degree x (xs : x∈S) : 1≤(outN D S x).card := by have := dense x xs; omega
  obtain ⟨p,C,qp,_,sub,size,one⟩ := exists_minimal_cycle_support (by omega) free degree
    (card_pos.mp (by omega))
  obtain ⟨x,xc⟩ := card_pos.mp (show 0<C.card by omega)
  have head : outN D S x⊆outN D C x ∪ (S \ C) := by
    intro y ym
    by_cases yc : y∈C
    · exact mem_union_left _ (mem_outN.mpr ⟨yc,(mem_outN.mp ym).2⟩)
    · exact mem_union_right _ (mem_sdiff.mpr ⟨outN_subset ym,yc⟩)
  have room := (card_le_card head).trans (card_union_le _ _)
  rw [one x xc,card_sdiff_of_subset sub] at room
  have := dense x (sub xc)
  have := card_le_card sub
  omega

/-- At the marked row x, the real successors used by these physical
cycles form a small set. The allowance c counts missed exterior labels
at the successor itself; it may be measured separately on each support. -/
theorem successors {D V q c x} {F : Finset (Finset ℕ)}
    (free : QFree D V q) (cut : c+2≤q) (rooted : ∀C∈F,Rooted D V x C)
    (omissions : ∀C∈F,(exterior D V C \ outN D V (internalHead D C x)).card≤c) :
    (F.image (fun C=>internalHead D C x)).card≤c+1 := by
  classical
  let f := fun C=>internalHead D C x
  let S := F.image f
  have turn C (cm : C∈F) : f C∈outN D C x := by
    have pos := (rooted C cm).one x (rooted C cm).root
    have ne : (outN D C x).Nonempty := card_pos.mp (by omega)
    simpa only [f,internalHead,dite_eq_left ne] using min'_mem (outN D C x) ne
  have sv : S⊆V := by
    intro y ym
    obtain ⟨C,cm,rfl⟩ := mem_image.mp ym
    exact (rooted C cm).sub (outN_subset (turn C cm))
  apply dense_choices (free.mono_set sv) cut
  intro y ym
  obtain ⟨C,cm,rfl⟩ := mem_image.mp ym
  have rest : (S \ outN D S (f C)).erase (f C)⊆ exterior D V C \ outN D V (f C) := by
    intro a am
    obtain ⟨ne,another⟩ := mem_erase.mp am
    obtain ⟨as,miss⟩ := mem_sdiff.mp another
    obtain ⟨K,km,ak⟩ := mem_image.mp as
    have edge : D x a=true := ak ▸ (mem_outN.mp (turn K km)).2
    have ac : a∉C := by
      intro hit
      exact ne (card_le_one.mp ((rooted C cm).one x (rooted C cm).root).le a
        (mem_outN.mpr ⟨hit,edge⟩) (f C) (turn C cm))
    exact mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨mem_biUnion.mpr ⟨x,(rooted C cm).root,
      mem_outN.mpr ⟨sv as,edge⟩⟩,ac⟩,fun old=>miss (mem_outN.mpr ⟨as,(mem_outN.mp old).2⟩)⟩
  have size := (card_le_card rest).trans (omissions C cm)
  have union := card_sdiff_add_card_eq_card (outN_subset : outN D S (f C)⊆S)
  by_cases self : f C∈S \ outN D S (f C)
  · have := card_erase_add_one self
    omega
  · rw [erase_eq_of_notMem self] at size
    omega

/-- A cycle containing the marked row is counted once, even if several
source roots selected it. The omission bound and quota stay variable. -/
theorem physical_multiplicity {D V q c d x} {F : Finset (Finset ℕ)}
    (free : QFree D V q) (cut : c+2≤q) (rooted : ∀C∈F,Rooted D V x C)
    (deg : (outN D V x).card=d) (regular : ∀C∈F, ∀y∈C,(outN D V y).card=d)
    (outer : ∀C∈F,(exterior D V C).card≤d-1+c) :
    F.card≤(c+1)*2^c := by
  classical
  let f := fun C=>internalHead D C x
  let S := F.image f
  have chosen C (cm : C∈F) z (zc : z∈C) : internalHead D C z∈outN D C z := by
    have one := (rooted C cm).one z zc
    have ne : (outN D C z).Nonempty := card_pos.mp (by omega)
    simpa only [internalHead,dite_eq_left ne] using min'_mem (outN D C z) ne
  have om C (cm : C∈F) : (exterior D V C \ outN D V (f C)).card≤c := by
    let y := f C
    have yc : y∈C := outN_subset (chosen C cm x (rooted C cm).root)
    let r := internalHead D C y
    have rm : r∈outN D C y := chosen C cm y yc
    let P := (outN D V y).erase r
    have pv : P⊆exterior D V C := by
      intro a am
      obtain ⟨ne,ym⟩ := mem_erase.mp am
      exact mem_sdiff.mpr ⟨mem_biUnion.mpr ⟨y,yc,ym⟩,fun ac=>ne
        (card_le_one.mp ((rooted C cm).one y yc).le _ (mem_outN.mpr ⟨ac,(mem_outN.mp ym).2⟩) _ rm)⟩
    have small : exterior D V C \ outN D V y ⊆ exterior D V C \ P :=
      sdiff_subset_sdiff Subset.rfl (erase_subset _ _)
    have lim := card_le_card small
    rw [card_sdiff_of_subset pv] at lim
    have size : P.card=d-1 := by
      dsimp [P]
      rw [card_erase_of_mem (outN_mono (rooted C cm).sub y rm),regular C cm y yc]
    have ex := outer C cm
    dsimp only [y] at *
    omega
  have mult := successors free cut rooted om
  have on (u) (_ : u∈S) : (F.filter (fun C=>f C=u)).card≤2^c := by
    apply degree_turn_limit (V:=V) (r:=x) (u:=u) (d:=d)
    · exact fun C cm=>rooted C (mem_filter.mp cm).1
    · intro C cm
      rw [←(mem_filter.mp cm).2]
      exact chosen C (mem_filter.mp cm).1 x (rooted C (mem_filter.mp cm).1).root
    · exact deg
    · exact fun C cm=>outer C (mem_filter.mp cm).1
  have count := sum_le_sum on
  rw [sum_const_nat (fun _ _=>rfl),sum_card_fiberwise_eq_card_filter] at count
  have all : F.filter (fun a=>f a∈S)=F := filter_eq_self.mpr (fun a am=>mem_image_of_mem f am)
  rw [all] at count
  exact count.trans (Nat.mul_le_mul_right _ mult)

attribute [aesop safe forward (immediate := [free,cut,dense]) (rule_sets := [CHGraphFamilies])] dense_choices
attribute [aesop safe forward (immediate := [free,cut,rooted,omissions]) (rule_sets := [CHGraphFamilies])] successors
attribute [aesop safe forward (immediate := [free,cut,rooted,deg,regular,outer])
  (rule_sets := [CHGraphFamilies])] physical_multiplicity

#print axioms dense_choices
#print axioms successors
#print axioms physical_multiplicity
end LeanCH.BR.CycleRowMultiplicity
