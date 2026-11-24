import checkpoints.shen_extension.dot_tensor_research.DotDegreeSevenQ5EscortMultiplicity_20261121

namespace LeanCH.BR.DotDegreeSevenLow
open Finset BRq2 BRq3 BR45 BRsGen

/-- With seven omitted labels there is no common core, but seven
original successors and one full row of spill still pay all uses. -/
theorem q4_sharedEscort_all_seven
    {D : CH.Digraph} {V J : Finset ℕ} {c : ℕ}
    {s a : ℕ→ℕ} {T : ℕ→Finset ℕ}
    (hf : QFree D V 4) (ho : OutEq 7 D V) (hc : c∈V)
    (P : SharedEscortMarks D V (outN D V c) J s a T) (j7 : J.card=7) :
    21≤(ball D V c 2).card := by
  classical
  let X := outN D V c
  let Y := J.image s
  let W := J.image a
  have yX : Y⊆X := by
    intro x hx
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hx
    exact P.sMem i hi
  have yJ : Y.card=J.card := card_image_of_injOn P.sInj
  have yEq : Y=X := eq_of_subset_of_card_le yX (by rw [yJ,j7,ho c hc])
  have indep (x) (hx : x∈X) (y) (hy : y∈X) : D x y≠true := by
    have h : y∈Y := yEq.symm ▸ hy
    obtain ⟨i,hi,rfl⟩ := mem_image.mp h
    exact P.avoidS i hi x hx
  have wJ : W.card=J.card := by
    apply card_image_of_injOn
    intro i hi j hj e
    by_contra ne
    have mem := P.aOther i hi j hj ne
    rw [e] at mem
    exact P.aNot j hj mem
  have hsupport (i j : ℕ) (hi : i∈J) (hj : j∈J) (neq : i≠j) :
      outN D V (s j)⊆T i := by
    intro x hx
    have jX : s j∈X := P.sMem j hj
    have ne : s j≠s i := fun e => neq (P.sInj hj hi e).symm
    rcases mem_union.mp (P.support i hi (s j) jX ne hx) with xX|xT
    · exact (indep (s j) jX x xX (mem_outN.mp hx).2).elim
    · exact xT
  obtain ⟨h,hh⟩ := card_pos.mp (by omega : 0<J.card)
  let Z := (outN D V (s h)).erase (a h)
  have z6 : Z.card=6 := by
    have mem : a h∈outN D V (s h) := mem_outN.mpr ⟨P.aV h hh,P.aArc h hh⟩
    have hV := (mem_outN.mp (P.sMem h hh)).1
    rw [show Z=(outN D V (s h)).erase (a h) from rfl,card_erase_of_mem mem,ho _ hV]
  have nz (i) (hi : i∈J) : a i∉Z := by
    intro ia
    have ne : i≠h := by
      intro e
      subst i
      exact (mem_erase.mp ia).1 rfl
    exact P.aNot i hi (hsupport i h hi hh ne (mem_of_mem_erase ia))
  have nW : Disjoint (insert c X) W := disjoint_left.mpr (by
    intro x hx xW
    obtain ⟨i,hi,rfl⟩ := mem_image.mp xW
    rcases mem_insert.mp hx with ce|inX
    · have sc : D (s i) c=true := ce ▸ P.aArc i hi
      have ⟨iv,cs⟩ := mem_outN.mp (P.sMem i hi)
      exact hf c 2 (by decide) (by decide) (.step iv cs (.step hc sc (.refl c)))
    · exact P.aOut i hi inX)
  have nZ : Disjoint (insert c X ∪ W) Z := disjoint_left.mpr (by
    intro x mx xz
    have e := (mem_outN.mp (mem_of_mem_erase xz)).2
    rcases mem_union.mp mx with ix|wx
    · rcases mem_insert.mp ix with xc|xx
      · have ⟨sv,cs⟩ := mem_outN.mp (P.sMem h hh)
        exact hf c 2 (by decide) (by decide) (.step sv cs (.step hc (xc ▸ e) (.refl c)))
      · exact indep _ (P.sMem h hh) _ xx e
    · obtain ⟨i,hi,rfl⟩ := mem_image.mp wx
      exact nz i hi xz)
  have xin : insert c X⊆ball D V c 2 := by
    intro x hx
    rcases mem_insert.mp hx with rfl|xX
    · exact self_mem_ball hc
    · obtain ⟨xv,e⟩ := mem_outN.mp xX
      exact mem_ball.mpr ⟨xv,1,by decide,.step xv e (.refl x)⟩
  have win : W⊆ball D V c 2 := by
    intro x hx
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hx
    obtain ⟨sv,cs⟩ := mem_outN.mp (P.sMem i hi)
    exact mem_ball.mpr ⟨P.aV i hi,2,by decide,
      .step sv cs (.step (P.aV i hi) (P.aArc i hi) (.refl _))⟩
  have zin : Z⊆ball D V c 2 := by
    intro x hx
    obtain ⟨xv,e⟩ := mem_outN.mp (mem_of_mem_erase hx)
    obtain ⟨sv,cs⟩ := mem_outN.mp (P.sMem h hh)
    exact mem_ball.mpr ⟨xv,2,by decide,.step sv cs (.step xv e (.refl x))⟩
  have notCX : c∉X := by
    intro cx
    exact hf c 1 (by decide) (by decide) (.step hc (mem_outN.mp cx).2 (.refl c))
  have lower := card_le_card (union_subset (union_subset xin win) zin)
  rw [card_union_of_disjoint nZ,card_union_of_disjoint nW,card_insert_of_notMem notCX,
    wJ,j7,z6,ho c hc] at lower
  omega

/-- At cutoff four the common core may have five labels. A row
of internal degree at most one suffices for the exact payment. -/
theorem q4_sharedEscort_thick_spill {D : CH.Digraph} {V X J : Finset ℕ}
    {s a : ℕ→ℕ} {T : ℕ→Finset ℕ}
    (hf : QFree D V 4) (ho : OutEq 7 D V)
    (P : SharedEscortMarks D V X J s a T) (lo : 2≤J.card) (hi : J.card≤6) :
    ∀ i∈J, J.card+5≤(T i).card := by
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
  have small : ∃ y∈K, (outN D K y).card≤1 := by
    by_contra! h
    have low : ∀ y∈K,2≤(outN D K y).card := fun y hy => h y hy
    have bound := corB (D:=D) (U:=K) (q:=4) (by decide) (hf.mono_set kv) low
      (card_pos.mp (by omega))
    change 9≤K.card at bound
    omega
  obtain ⟨y,hy,yd⟩ := small
  let W := outN D V y \ K
  have il : outN D V y∩K=outN D K y := by
    ext x
    simp only [mem_inter,mem_outN]
    exact ⟨fun h => ⟨h.2,h.1.2⟩,fun h => ⟨⟨kv h.1,h.2⟩,h.1⟩⟩
  have w6 : 6≤W.card := by
    have k := card_sdiff_add_card_inter (outN D V y) K
    change W.card+(outN D V y∩K).card=(outN D V y).card at k
    rw [il,ho y (kv hy)] at k
    omega
  have my (i) (hi : i∈J) : W⊆T i := by
    have yX := (mem_sdiff.mp hy).1
    have nes : y≠s i := by
      intro e
      exact (mem_sdiff.mp hy).2 (mem_image.mpr ⟨i,hi,e.symm⟩)
    intro x hx
    obtain ⟨hd,hk⟩ := mem_sdiff.mp hx
    rcases mem_union.mp (P.support i hi y yX nes hd) with inX|inT
    · have arc := (mem_outN.mp hd).2
      by_cases xy : x∈Y
      · obtain ⟨j,jJ,rfl⟩ := mem_image.mp xy
        exact (P.avoidS j jJ y yX arc).elim
      · exact (hk (mem_sdiff.mpr ⟨inX,xy⟩)).elim
    · exact inT
  intro i ii
  let A := (J.erase i).image a
  have aT : A⊆T i := by
    intro x hx
    obtain ⟨j,jm,rfl⟩ := mem_image.mp hx
    exact P.aOther j (mem_erase.mp jm).2 i ii (mem_erase.mp jm).1
  have ai : (↑J : Set ℕ).InjOn a := by
    intro u hu v hv eq
    by_contra n
    have h := P.aOther u hu v hv n
    rw [eq] at h
    exact P.aNot v hv h
  have aJ : A.card=J.card-1 := by
    rw [show A=(J.erase i).image a from rfl,card_image_of_injOn,card_erase_of_mem ii]
    exact ai.mono (fun _ hx => mem_of_mem_erase hx)
  have sep : Disjoint A W := disjoint_left.mpr (by
    intro x xa xy
    obtain ⟨j,hj,rfl⟩ := mem_image.mp xa
    exact (P.aNot j (mem_erase.mp hj).2) (my j (mem_erase.mp hj).2 xy))
  have cnt := card_le_card (union_subset aT (my i ii))
  rw [card_union_of_disjoint sep,aJ] at cnt
  omega

#print axioms q4_sharedEscort_thick_spill
#print axioms q4_sharedEscort_all_seven
end LeanCH.BR.DotDegreeSevenLow
