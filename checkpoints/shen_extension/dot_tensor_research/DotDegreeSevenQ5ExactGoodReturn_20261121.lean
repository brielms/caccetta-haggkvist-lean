import checkpoints.shen_extension.dot_tensor_research.DotDegreeSevenQ5ExactGoodSpill_20261121

namespace LeanCH.BR.DotDegreeSevenLow
open Finset BRq2 BRq3 BR45 BRsGen

theorem exact_good_bank_no_direct_return {D : CH.Digraph} {V A G B T : Finset ℕ}
    (hf : QFree D V 5) (ho : OutEq 7 D V) (n : V.card≤35)
    (cap : ∀ v∈V, (ball D V v 2).card≤15)
    (aV : A⊆V) (bV : B⊆V) (tV : T⊆V) (disj : Disjoint B T)
    (g6 : G.card≤6) (b7 : B.card=7) (t6 : T.card≤6)
    (hmiss : ∀ x∈G, (B \ outN D V x).card≤1)
    (reach : ∀ a∈A, ∃ g∈G, ∃ j≤2, Walk D V a g j)
    (keep : ∀ b∈B, outN D V b⊆A∪(B∪T)) :
    ∀ b∈B, ∀ a∈A, D b a≠true := by
  classical
  let R := B.filter (fun b => ∃ a∈A, D b a=true)
  have rb : R⊆B := filter_subset _ _
  have pack (b : ℕ) (hb : b∈R) : ∃ g∈G, B \ outN D V g = {b} ∧
      (∀ y∈B, D y b≠true) := by
    obtain ⟨bb,a,aa,e⟩ := mem_filter.mp hb
    obtain ⟨g,hg,j,hj,w⟩ := reach a aa
    have wbg : Walk D V b g (j+1) := .step (aV aa) e w
    have hnot : b∉outN D V g := by
      intro h
      exact hf b ((j+1)+1) (by omega) (by omega)
        (wbg.append (.step (bV bb) (mem_outN.mp h).2 (.refl b)))
    have e' : B \ outN D V g = {b} := by
      apply (eq_of_subset_of_card_le ?_ ?_).symm
      · simpa using mem_sdiff.mpr ⟨bb,hnot⟩
      · simpa using hmiss g hg
    refine ⟨g,hg,e',?_⟩
    intro y yb ey
    have yn : y≠b := by
      rintro rfl
      exact loopfree hf (by decide) (bV yb) ey
    have eg : D g y=true := by
      by_contra h
      have k : y∈B \ outN D V g := mem_sdiff.mpr ⟨yb,fun hy => h (mem_outN.mp hy).2⟩
      rw [e'] at k
      exact yn (mem_singleton.mp k)
    exact hf b ((j+1)+2) (by omega) (by omega)
      (wbg.append (.step (bV yb) eg (.step (bV bb) ey (.refl b))))
  choose g gG ge gn using pack
  let f (b : ℕ) := if h : b∈R then g b h else 0
  have fw (b : ℕ) (hb : b∈R) : f b = g b hb := by
    unfold f
    split
    · rfl
    · contradiction
  have rc : R.card≤G.card := card_le_card_of_injOn f
    (fun b hb => by
      change b∈R at hb
      change f b∈G
      rw [fw b hb]
      exact gG b hb) (by
      intro b hb c hc he
      change b∈R at hb
      change c∈R at hc
      rw [fw b hb,fw c hc] at he
      have eqg := he
      have eb := ge b hb
      have ec := ge c hc
      rw [eqg,ec] at eb
      exact Finset.singleton_inj.mp eb.symm)
  intro b bb a aa e
  have pos : 0<R.card := card_pos.mpr ⟨b,mem_filter.mpr ⟨bb,a,aa,e⟩⟩
  have cc := card_sdiff_of_subset rb
  apply exact_endpoint_no_supported_bank (B:=B \ R) (T:=T) hf ho n cap (sdiff_subset.trans bV) tV
    (disj.mono_left sdiff_subset) (card_pos.mp (by omega)) (by omega) t6
  intro x hx y hy
  rcases mem_union.mp (keep x (mem_sdiff.mp hx).1 hy) with ha|ht
  · exact ((mem_sdiff.mp hx).2 (mem_filter.mpr
      ⟨(mem_sdiff.mp hx).1,y,ha,(mem_outN.mp hy).2⟩)).elim
  · rcases mem_union.mp ht with hB|hT
    · exact mem_union_left _ (mem_sdiff.mpr ⟨hB,fun hR =>
        gn y hR x (mem_sdiff.mp hx).1 (mem_outN.mp hy).2⟩)
    · exact mem_union_right _ hT

#print axioms exact_good_bank_no_direct_return

end LeanCH.BR.DotDegreeSevenLow


