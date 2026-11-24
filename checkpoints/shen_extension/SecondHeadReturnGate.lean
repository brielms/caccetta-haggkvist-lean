import checkpoints.shen_extension.SharedCycleContacts

namespace LeanCH.BR.LowShellCycleSelection
open Finset BRq2 BRq3 BR45 BRsGen ExteriorPacking PhysicalCycleStock

/-- A competitor outside the first row must use a named exceptional second
head. Its remaining walk and the reverse-distance obstruction refer to that
very head, in the original graph. -/
theorem exceptional_second_contact {D V q k u v w C} (free : QFree D V q)
    (hq : 4≤q) (uv : u∈V) (distinct : u≠v)
    (first : outN D V u=insert w C) (common : C⊆outN D V v)
    (time : k+1≤q) (hit : v∈ball D V u k) :
    v=w ∨ ∃b∈N2 D V u\exterior D V C, D w b=true ∧ ∃l,l+2≤k ∧
      Walk D V b v l ∧ ∀j,0<j → Walk D V v b j → q<j+l := by
  obtain ⟨_,_,bound,road⟩ := mem_ball.mp hit
  cases road with
  | refl => exact (distinct rfl).elim
  | @step x a z m av ua tail =>
    have ax : a∈outN D V u := mem_outN.mpr ⟨av,ua⟩
    have avoid := avoids_columns free common tail (by omega)
    have aw : a=w := (mem_insert.mp (first ▸ ax)).resolve_right (fun h=>avoid (mem_union_left _ h))
    subst a
    cases tail with
    | refl => exact Or.inl rfl
    | @step _ b _ l bv wb rest =>
      have off := avoids_columns free common rest (by omega)
      have loop := loopfree free (by omega : 1≤q) av
      have outside : b∉outN D V u := by
        intro bx
        rcases mem_insert.mp (first ▸ bx) with eq|bank
        · subst b; exact loop wb
        · exact off (mem_union_left _ bank)
      have by' := (mem_union.mp (headX (free.mono_bound hq) uv ax bv wb)).resolve_left outside
      refine Or.inr ⟨b,mem_sdiff.mpr ⟨by',fun e=>off (mem_union_right _ e)⟩,wb,l,by omega,rest,?_⟩
      intro j pos back
      by_contra! short
      exact free _ _ (by omega) short (back.append rest)

/-- Positive return paths to the exceptional heads screen all of them
simultaneously. Only heads actually reached from the private first label
need to be screened. -/
theorem screened_second_contact {D V q k u v w C} (free : QFree D V q)
    (hq : 4≤q) (uv : u∈V) (distinct : u≠v)
    (first : outN D V u=insert w C) (common : C⊆outN D V v)
    (time : k+1≤q) (hit : v∈ball D V u k)
    (screen : ∀b∈N2 D V u\exterior D V C,D w b=true →
      ∃j,0<j ∧ Walk D V v b j ∧ j+(k-2)≤q) : v=w := by
  rcases exceptional_second_contact free hq uv distinct first common time hit with same|⟨b,bm,wb,l,lim,_,far⟩
  · exact same
  · obtain ⟨j,pos,back,short⟩ := screen b bm wb
    have := far j pos back
    omega

/-- If all common columns feed an exterior label that hits the sole
exception in the second shell, even the private first head cannot be a
competing representative. The only degree comparison is on that exception. -/
theorem exterior_screens_single_exception {D V q k u v w C b e}
    (free : QFree D V q) (hq : 4≤q) (uv : u∈V) (vv : v∈V) (distinct : u≠v)
    (first : outN D V u=insert w C) (common : C⊆outN D V v)
    (slots : (outN D V v\C).card≤1) (live : C.Nonempty)
    (second : N2 D V u\exterior D V C={b}) (ee : e∈exterior D V C)
    (paid : ∀c∈C,D c e=true) (eb : D e b=true)
    (capacity : (N2 D V v).card≤(outN D V b).card) (time : k+1≤q) :
    v∉ball D V u k := by
  classical
  intro hit
  have bm : b∈N2 D V u\exterior D V C := second.symm ▸ mem_singleton_self b
  have bv := N2_subV (mem_sdiff.mp bm).1
  have be := (mem_sdiff.mp bm).2
  obtain ⟨a,ac,ae⟩ := mem_biUnion.mp (mem_sdiff.mp ee).1
  have ev := outN_subset ae
  obtain ⟨c,cm⟩ := live
  have vc := common cm
  have back : Walk D V v b 3 := .step (outN_subset vc) (mem_outN.mp vc).2
    (.step ev (paid c cm) (.step bv eb (.refl b)))
  have same := screened_second_contact free hq uv distinct first common time hit (by
    intro d dm _
    have eq : d=b := mem_singleton.mp (second ▸ dm)
    exact eq ▸ ⟨3,by decide,back,by omega⟩)
  subst w
  have outside : b∉C := fun bc=>(mem_N2.mp (mem_sdiff.mp bm).1).2 (X_B1 (first.symm ▸ mem_insert_of_mem bc))
  obtain ⟨x,xm,xb⟩ := parY uv (mem_sdiff.mp bm).1
  have xb' : x=v := (mem_insert.mp (first ▸ xm)).resolve_right (fun xc=>be
    (mem_sdiff.mpr ⟨mem_biUnion.mpr ⟨x,xc,mem_outN.mpr ⟨bv,xb⟩⟩,outside⟩))
  subst x
  have vb : b∈outN D V v := mem_outN.mpr ⟨bv,xb⟩
  have unique : outN D V v\C={b} := eq_of_subset_of_card_le
    (s:={b}) (t:=outN D V v\C) (singleton_subset_iff.mpr (mem_sdiff.mpr ⟨vb,outside⟩))
    (by simpa using slots) |>.symm
  have backMenu {j} (jm : j∈outN D V v) : j∈C ∨ j=b := by
    by_cases jc : j∈C
    · exact Or.inl jc
    · exact Or.inr (mem_singleton.mp (unique ▸ (mem_sdiff.mpr ⟨jm,jc⟩ : j∈outN D V v\C)))
  have en : e∉outN D V v := fun h=>(backMenu h).elim (mem_sdiff.mp ee).2 (fun eq=>be (eq ▸ ee))
  have ey := (mem_union.mp (headX (free.mono_bound hq) vv vc ev (paid c cm))).resolve_left en
  have into : outN D V b⊆N2 D V v := by
    intro j jm
    have bj := (mem_outN.mp jm).2
    apply (mem_union.mp (headX (free.mono_bound hq) vv vb (outN_subset jm) bj)).resolve_left
    intro jx
    rcases backMenu jx with jc|eq
    · exact free b 3 (by decide) (by omega) (.step (outN_subset jm) bj
        (.step ev (paid j jc) (.step bv eb (.refl b))))
    · subst j; exact loopfree free (by omega) bv bj
  have exhausted := eq_of_subset_of_card_le into capacity
  exact digonfree free (by omega) ev bv eb (mem_outN.mp (exhausted.symm ▸ ey)).2

/-- A sink on the complete exterior handles every larger second shell with
one spare label. Degrees are measured at the two physical rows that need them. -/
theorem sink_excludes_larger_contact {D V q k u v w C e} (free : QFree D V q)
    (hq : 4≤q) (uv : u∈V) (vv : v∈V) (distinct : u≠v)
    (first : outN D V u=insert w C) (common : C⊆outN D V v)
    (slots : (outN D V v\C).card≤1) (ee : e∈exterior D V C)
    (paid : ∀a∈C,D a e=true) (sink : ∀a∈exterior D V C,D e a≠true)
    (large : N2 D V u≠exterior D V C)
    (width : (N2 D V u).card≤(exterior D V C).card+1)
    (crowd : (N3 D V u).card<(outN D V e).card)
    (capacity : ∀b∈N2 D V u\exterior D V C,(N2 D V v).card≤(outN D V b).card)
    (time : k+2≤q) : v∉ball D V u k := by
  classical
  obtain ⟨c,cm,ce⟩ := mem_biUnion.mp (mem_sdiff.mp ee).1
  have ev := outN_subset ce
  have vc := common cm
  have firstC : C⊆outN D V u := first.symm ▸ subset_insert w C
  by_cases we : w∈exterior D V C
  · obtain ⟨a,am,aw⟩ := mem_biUnion.mp (mem_sdiff.mp we).1
    exact fast_first_side free (by omega) (by omega) vv distinct first common ⟨a,am,(mem_outN.mp aw).2⟩
  have inc : exterior D V C⊆N2 D V u := by
    intro j jm
    apply (mem_union.mp (exterior_subset_menu free hq uv firstC jm)).resolve_left
    intro bad
    have eq := (mem_insert.mp (first ▸ (mem_sdiff.mp bad).1)).resolve_right (mem_sdiff.mp bad).2
    exact we (eq ▸ jm)
  have sizes := card_sdiff_add_card_eq_card inc
  have cardlt := card_lt_card (ssubset_of_subset_of_ne inc (Ne.symm large))
  obtain ⟨b,one⟩ := card_eq_one.mp (show (N2 D V u\exterior D V C).card=1 by omega)
  have bm : b∈N2 D V u\exterior D V C := one.symm ▸ mem_singleton_self b
  by_cases ew : D e w=true
  · intro hit
    have wv : w∈V := outN_subset (first.symm ▸ mem_insert_self w C)
    have returnPath : Walk D V v w 3 := .step (outN_subset vc) (mem_outN.mp vc).2
      (.step ev (paid c cm) (.step wv ew (.refl w)))
    have same := first_side_contact free (k:=k) (t:=3) (by omega) (by decide) vv distinct first common
      (mem_ball.mpr ⟨wv,3,le_rfl,returnPath⟩) hit
    subst w
    exact free v 3 (by decide) (by omega) returnPath
  have eb : D e b=true := by
    by_contra missing
    have spill : outN D V e⊆N3 D V u := by
      intro j jm
      have ej := (mem_outN.mp jm).2
      apply (headY (free.mono_bound hq) uv (inc ee) (outN_subset jm) ej).resolve_left
      intro earlier
      rcases mem_union.mp earlier with jx|jy
      · rcases mem_insert.mp (first ▸ jx) with eq|jc
        · exact ew (eq ▸ ej)
        · exact digonfree free (by omega) ev (outN_subset jm) ej (paid j jc)
      · by_cases je : j∈exterior D V C
        · exact sink j je ej
        · have jb : j=b := mem_singleton.mp (one ▸ (mem_sdiff.mpr ⟨jy,je⟩ : j∈N2 D V u\exterior D V C))
          exact missing (jb ▸ ej)
    exact crowd.not_ge (card_le_card spill)
  exact exterior_screens_single_exception free hq uv vv distinct first common slots ⟨c,cm⟩ one ee paid eb
    (capacity b bm) (by omega)

attribute [aesop safe forward (immediate := [free,hq,uv,vv,distinct,first,common,slots,ee,paid,sink,large,width,crowd,capacity,time]) (rule_sets := [CHGraphFamilies])] sink_excludes_larger_contact
#print axioms sink_excludes_larger_contact
#print axioms exterior_screens_single_exception
#print axioms exceptional_second_contact
#print axioms screened_second_contact
end LeanCH.BR.LowShellCycleSelection
