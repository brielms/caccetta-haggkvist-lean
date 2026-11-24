import checkpoints.shen_extension.RemainingPayerEntry

namespace LeanCH.BR.LowShellCycleSelection
open Finset BRq2 BRq3 BR45 BRsGen ExteriorPacking PhysicalCycleStock
open scoped Classical

/-- If a column points to a row with few omissions, all its parents in the
tested bank are among those omitted labels. The count uses physical arcs. -/
theorem returning_column {D V K Y q b c} (free : QFree D V q) (hq : 3≤q)
    (ky : K⊆Y) (yv : Y⊆V) (bv : b∈V) (cv : c∈V) (bc : D b c=true) :
    inN D K b ⊆ Y\outN D V c := by
  intro a am
  obtain ⟨ak,ab⟩ := mem_inN.mp am
  exact mem_sdiff.mpr ⟨ky ak,fun ca=>free c 3 (by decide) hq
    (.step (yv (ky ak)) (mem_outN.mp ca).2 (.step bv ab (.step cv bc (.refl c))))⟩

/-- Every cycle row missing two slots beyond Y must use an exceptional
column in X or Y. Their capacities compete, even if their parents overlap. -/
theorem two_layer_columns {D V X Y Z C K q r d} (free : QFree D V q) (hq : 3≤q)
    (xv : X⊆V) (yv : Y⊆V) (cx : C⊆X) (ky : K⊆Y)
    (roots : ∀a∈K,Rooted D V a K) (ks : q<K.card)
    (degree : ∀x∈X∪Y,r≤(outN D V x).card)
    (firstRows : ∀x∈X,outN D V x⊆X∪Y) (secondRows : ∀y∈Y,outN D V y⊆(X∪Y)∪Z)
    (miss : ∀c∈C,(Y\outN D V c).card≤d) (depth : d<q-1)
    (xroom : (X\C).card≤1) (yroom : (Y\K).card≤1) (quota : Y.card≤r)
    (scarce : Z.card+1<r) :
    K.card ≤ (X\C).card*d + (Y\K).card*max d (K.card-(q-1)) := by
  classical
  let good := fun a (ak : a∈K) c (cm : c∈C) (edge : D a c=true)=> 
    crossed_omissions free (by omega) yv ky ks roots ak (xv (cx cm)) edge
  have noBack a (ak : a∈K) c (cm : c∈C) : D a c≠true := by
    intro arc; have := good a ak c cm arc; have := miss c cm; omega
  have hits a (ak : a∈K) : ∃b∈(X\C)∪(Y\K),D a b=true := by
    by_contra! none
    have sub : outN D V a⊆outN D K a∪Z := by
      intro b bm
      have arc := (mem_outN.mp bm).2
      rcases mem_union.mp (secondRows a (ky ak) bm) with old|zm
      · have inside : b∈K := by
          by_contra off
          rcases mem_union.mp old with bx|by'
          · by_cases bc : b∈C
            · exact noBack a ak b bc arc
            · exact none b (mem_union_left _ (mem_sdiff.mpr ⟨bx,bc⟩)) arc
          · exact none b (mem_union_right _ (mem_sdiff.mpr ⟨by',off⟩)) arc
        exact mem_union_left _ (mem_outN.mpr ⟨inside,arc⟩)
      · exact mem_union_right _ zm
    have h := (degree a (mem_union_right _ (ky ak))).trans ((card_le_card sub).trans (card_union_le _ _))
    rw [(roots a ak).one a ak] at h; omega
  have direct b (bv : b∈V) c (cm : c∈C) (bc : D b c=true) :
      (inN D K b).card≤d := (card_le_card (returning_column free hq ky yv bv (xv (cx cm)) bc)).trans (miss c cm)
  have first b (bm : b∈X\C) : (inN D K b).card≤d := by
    have bx := (mem_sdiff.mp bm).1
    by_cases e : ∃c∈C,D b c=true
    · obtain ⟨c,cm,bc⟩ := e; exact direct b (xv bx) c cm bc
    have sub : outN D V b⊆Y := by
      intro a am
      apply (mem_union.mp (firstRows b bx am)).resolve_left
      intro ax
      have off : a∉C := fun ac=>e ⟨a,ac,(mem_outN.mp am).2⟩
      have eq := card_le_one.mp xroom a (mem_sdiff.mpr ⟨ax,off⟩) b bm
      exact loopfree free (by omega) (xv bx) (eq ▸ (mem_outN.mp am).2)
    have all := eq_of_subset_of_card_le sub (quota.trans (degree b (mem_union_left _ bx)))
    have empty : inN D K b=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro a am
      have ⟨ak,arc⟩ := mem_inN.mp am
      exact digonfree free (by omega) (xv bx) (yv (ky ak)) (mem_outN.mp (all.symm ▸ ky ak)).2 arc
    simp [empty]
  have second b (bm : b∈Y\K) : (inN D K b).card≤max d (K.card-(q-1)) := by
    have by' := (mem_sdiff.mp bm).1
    by_cases e : ∃c∈C,D b c=true
    · obtain ⟨c,cm,bc⟩ := e; exact (direct b (yv by') c cm bc).trans (le_max_left _ _)
    by_cases f : ∃a∈K,D b a=true
    · obtain ⟨a,ak,ba⟩ := f
      have lim := exception_parents free (ky.trans yv) (fun z zm=>((roots z zm).one z zm).ge) (yv by') ak
        (Walk.step (yv (ky ak)) ba (.refl a)) (by omega)
      omega
    have sub : outN D V b⊆(X\C)∪Z := by
      intro a am
      rcases mem_union.mp (secondRows b by' am) with old|zm
      · rcases mem_union.mp old with ax|ay
        · exact mem_union_left _ (mem_sdiff.mpr ⟨ax,fun ac=>e ⟨a,ac,(mem_outN.mp am).2⟩⟩)
        · have off : a∉K := fun ak=>f ⟨a,ak,(mem_outN.mp am).2⟩
          have eq := card_le_one.mp yroom a (mem_sdiff.mpr ⟨ay,off⟩) b bm
          exact (loopfree free (by omega) (yv by') (eq ▸ (mem_outN.mp am).2)).elim
      · exact mem_union_right _ zm
    have := (degree b (mem_union_right _ by')).trans ((card_le_card sub).trans (card_union_le _ _))
    omega
  have covered : K⊆(X\C).biUnion (fun b=>inN D K b) ∪ (Y\K).biUnion (fun b=>inN D K b) := by
    intro a ak
    obtain ⟨b,bm,arc⟩ := hits a ak
    rcases mem_union.mp bm with bx|by'
    · exact mem_union_left _ (mem_biUnion.mpr ⟨b,bx,mem_inN.mpr ⟨ak,arc⟩⟩)
    · exact mem_union_right _ (mem_biUnion.mpr ⟨b,by',mem_inN.mpr ⟨ak,arc⟩⟩)
  have a := card_biUnion_le.trans (sum_le_sum first)
  have b := card_biUnion_le.trans (sum_le_sum second)
  simp only [sum_const_nat (fun _ _=>rfl)] at a b
  exact (card_le_card covered).trans ((card_union_le _ _).trans (Nat.add_le_add a b))

#print axioms two_layer_columns
end LeanCH.BR.LowShellCycleSelection
