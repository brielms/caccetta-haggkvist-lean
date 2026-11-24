import checkpoints.shen_extension.PrimaryContactBudget

namespace LeanCH.BR.LowShellCycleSelection
open Finset BRq2 BRq3 BR45 BRsGen ExteriorPacking PhysicalCycleStock
open scoped Classical

theorem exhaust_successor {D V E S r} (reg : OutEq r D V) (live : E.Nonempty)
    (roots : ∀e∈E,Rooted D V e E) (inside : exterior D V E⊆S) (bound : S.card≤r-1) :
    exterior D V E=S ∧ ∀e∈E,S⊆outN D V e := by
  obtain ⟨e,em⟩ := live
  have root := roots e em
  have hv := outN_mono root.sub e (successor_mem root)
  have floor := card_le_card ((row_exterior root).symm ▸ inter_subset_left :
    (outN D V e).erase (internalHead D E e)⊆exterior D V E)
  rw [card_erase_of_mem hv,reg e (root.sub em)] at floor
  have width := (eq_of_subset_of_card_le inside (bound.trans floor))
  refine ⟨width,?_⟩
  intro a am
  have ra := roots a am
  have exactSize := Nat.le_antisymm ((card_le_card inside).trans bound) floor
  rw [← width,← complete_row ra (reg a (ra.sub am)) exactSize]
  exact erase_subset _ _

private theorem private_arc {D V u C w b} (uv : u∈V) (first : outN D V u=insert w C)
    (bm : b∈N2 D V u) (off : b∉exterior D V C) : D w b=true := by
  obtain ⟨p,pm,pb⟩ := parY uv bm
  rcases mem_insert.mp (first ▸ pm) with rfl|pc
  · exact pb
  exfalso
  apply off
  exact mem_sdiff.mpr ⟨mem_biUnion.mpr ⟨p,pc,mem_outN.mpr ⟨N2_subV bm,pb⟩⟩,
    fun bc=>(mem_N2.mp bm).2 (X_B1 (first.symm ▸ mem_insert_of_mem bc))⟩

/-- A second marked origin with one exceptional head and one exceptional
second-layer vertex cannot lie in the first origin's three-ball when the
two successive common banks are full. All degrees are local bounds. -/
theorem full_bank_separates {D V q u v C E W w b d f} (free : QFree D V q) (hq : 4≤q)
    (uv : u∈V) (vv : v∈V) (ne : u≠v) (liveC : C.Nonempty) (liveE : E.Nonempty)
    (first : outN D V u=insert w C) (second : N2 D V u=insert b E) (third : N3 D V u=W)
    (first' : outN D V v=insert d C) (second' : N2 D V v=insert f E)
    (ce : ∀c∈C,E⊆outN D V c) (ew : ∀e∈E,W⊆outN D V e)
    (dC : d∉C) (fE : f∉E) (wb : D w b=true) (df : D d f=true)
    (degreeD : 1<(outN D V d).card) (degreeF : (N3 D V v).card<(outN D V f).card) :
    v∉ball D V u 3 := by
  classical
  obtain ⟨c,cm⟩ := liveC
  obtain ⟨e,em⟩ := liveE
  have cedge := ce c cm em
  have ev := outN_subset cedge
  have vC {i} (im : i∈C) : i∈outN D V v := first'.symm ▸ mem_insert_of_mem im
  have dv := outN_subset (first'.symm ▸ mem_insert_self d C)
  have dvHead : d∈outN D V v := first'.symm ▸ mem_insert_self d C
  have fm : f∈N2 D V v := second'.symm ▸ mem_insert_self f E
  have bm : b∈N2 D V u := second.symm ▸ mem_insert_self b E
  have fv := N2_subV fm
  have bv := N2_subV bm
  have blocked {i} (im : i∈W) : ∀j,j∈C ∨ j∈E → D i j≠true := by
    intro j jm ij
    have ei := ew e em im
    rcases jm with jc|je
    · exact free i 3 (by decide) (by omega) (.step (outN_subset (vC jc)) ij
        (.step ev (mem_outN.mp (ce j jc em)).2 (.step (outN_subset ei) (mem_outN.mp ei).2 (.refl i))))
    · have ji := ew j je im
      exact digonfree free (by omega) (outN_subset ji) (outN_subset (ce c cm je)) ij (mem_outN.mp ji).2
  have targetW : v∉W := fun vm=>blocked vm c (.inl cm) (mem_outN.mp (vC cm)).2
  have targetE : v∉E := fun vm=>digonfree free (by omega) vv (outN_subset (vC cm))
    (mem_outN.mp (vC cm)).2 (mem_outN.mp (ce c cm vm)).2
  have targetC : v∉C := fun vm=>loopfree free (by omega) vv (mem_outN.mp (vC vm)).2
  have dOff : d∉W := by
    intro dm
    have only : outN D V d⊆{f} := by
      intro j jm
      have arc := (mem_outN.mp jm).2
      have cases := headX (free.mono_bound hq) vv dvHead (outN_subset jm) arc
      rw [first',second'] at cases
      rcases mem_union.mp cases with jx|jy
      · rcases mem_insert.mp jx with rfl|jc
        · exact (loopfree free (by omega) dv arc).elim
        · exact (blocked dm j (.inl jc) arc).elim
      · rcases mem_insert.mp jy with rfl|je
        · exact mem_singleton_self _
        · exact (blocked dm j (.inr je) arc).elim
    have := card_le_card only
    simp only [card_singleton] at this
    omega
  have fOff : f∉W := by
    intro fmW
    apply (Nat.not_le_of_lt degreeF)
    apply card_le_card
    intro j jm
    have arc := (mem_outN.mp jm).2
    apply (headY (free.mono_bound hq) vv fm (outN_subset jm) arc).resolve_left
    rw [first',second']
    intro early
    rcases mem_union.mp early with x|y
    · rcases mem_insert.mp x with rfl|jc
      · exact digonfree free (by omega) fv dv arc df
      · exact blocked fmW j (.inl jc) arc
    · rcases mem_insert.mp y with rfl|je
      · exact loopfree free (by omega) fv arc
      · exact blocked fmW j (.inr je) arc
  intro hit
  have either : v=w ∨ v=b := by
    rcases split4 uv v with eq|x|y|z|off
    · exact (ne eq.symm).elim
    · exact .inl ((mem_insert.mp (first ▸ x)).resolve_right targetC)
    · exact .inr ((mem_insert.mp (second ▸ y)).resolve_right targetE)
    · exact (targetW (third ▸ z)).elim
    · exact (off hit).elim
  rcases either with h|h
  · have bh : b∈outN D V v := mem_outN.mpr ⟨bv,h.symm ▸ wb⟩
    have bc : b∉C := fun bc=>(mem_N2.mp bm).2 (X_B1 (first.symm ▸ mem_insert_of_mem bc))
    have bd := (mem_insert.mp (first' ▸ bh)).resolve_right bc
    have early := (headY (free.mono_bound hq) uv bm fv (bd.symm ▸ df)).resolve_right (fun hz=>fOff (third ▸ hz))
    rw [first,second] at early
    rcases mem_union.mp early with x|y
    · rcases mem_insert.mp x with fw|fc
      · exact (mem_N2.mp fm).2 (by rw [fw,←h,ball1_eq vv]; exact mem_insert_self _ _)
      · exact (mem_N2.mp fm).2 (X_B1 (vC fc))
    · rcases mem_insert.mp y with fb|fe
      · exact (mem_N2.mp fm).2 (fb.symm ▸ X_B1 bh)
      · exact fE fe
  · have early := (headY (free.mono_bound hq) uv bm dv (h ▸ (mem_outN.mp dvHead).2)).resolve_right
      (fun hz=>dOff (third ▸ hz))
    rw [first,second] at early
    rcases mem_union.mp early with x|y
    · rcases mem_insert.mp x with dw|dc'
      · exact digonfree free (by omega) dv bv (dw.symm ▸ wb) (h ▸ (mem_outN.mp dvHead).2)
      · exact dC dc'
    · rcases mem_insert.mp y with db|de
      · exact loopfree free (by omega) vv ((db.trans h.symm) ▸ (mem_outN.mp dvHead).2)
      · exact (mem_N2.mp (second'.symm ▸ mem_insert_of_mem de)).2 (X_B1 dvHead)

/-- Saturation of the second bank and separation follow from the measured
shell widths on the two marked origins, before choosing any further cycle. -/
theorem priced_origins_separate {D V q r u v C b f} (free : QFree D V q) (hq : 5≤q)
    (reg : OutEq r D V) (hr : 2≤r) (uv : u∈V) (vv : v∈V) (ne : u≠v)
    (live : C.Nonempty) (width : C.card=r-1)
    (common : C⊆outN D V u) (common' : C⊆outN D V v)
    (ce : ∀c∈C,exterior D V C⊆outN D V c)
    (eWidth : (exterior D V C).card=r-1)
    (roots : ∀e∈exterior D V C,Rooted D V e (exterior D V C))
    (bE : b∉exterior D V C) (fE : f∉exterior D V C)
    (second : N2 D V u=insert b (exterior D V C))
    (second' : N2 D V v=insert f (exterior D V C))
    (small : (N3 D V u).card≤r-1) (small' : (N3 D V v).card<r) : v∉ball D V u 3 := by
  classical
  let E := exterior D V C
  have splitRow a (av : a∈V) (sub : C⊆outN D V a) :
      ∃j∉C,outN D V a=insert j C := by
    have size := card_sdiff_of_subset sub
    rw [reg a av,width] at size
    obtain ⟨j,single⟩ := card_eq_one.mp (show (outN D V a\C).card=1 by omega)
    have ins : j∈outN D V a\C := single.symm ▸ mem_singleton_self _
    exact ⟨j,(mem_sdiff.mp ins).2,by rw [← singleton_union,← single,sdiff_union_of_subset sub]⟩
  obtain ⟨w,_,first⟩ := splitRow u uv common
  obtain ⟨d,dC,first'⟩ := splitRow v vv common'
  have bm : b∈N2 D V u := second.symm ▸ mem_insert_self _ _
  have fm : f∈N2 D V v := second'.symm ▸ mem_insert_self _ _
  have dV := outN_subset (first'.symm ▸ mem_insert_self d C)
  have budget : (N2 D V v).card≤(outN D V b).card := by
    rw [second',card_insert_of_notMem fE,eWidth,reg b (N2_subV bm)]; omega
  intro hit
  have inside := successor_inside_third free (by omega) (by omega : 3+2≤q) uv vv ne first common'
    (by rw [card_sdiff_of_subset common',reg v vv,width]; omega) live ce
    (show E⊆N2 D V u from second.symm ▸ subset_insert _ _)
    (show N2 D V u\E={b} by rw [second]; ext a; simp [E,Finset.mem_sdiff]; grind)
    budget hit
  have eLive : E.Nonempty := card_pos.mp (by change 0<(exterior D V C).card; omega)
  obtain ⟨third,ew⟩ := exhaust_successor reg eLive roots inside small
  exact full_bank_separates free (by omega) uv vv ne live eLive first second rfl first' second' ce ew
    dC fE (private_arc uv first bm bE) (private_arc vv first' fm fE)
    (by rw [reg d dV]; omega) (by rw [reg f (N2_subV fm)]; exact small') hit

#print axioms priced_origins_separate
#print axioms full_bank_separates
end LeanCH.BR.LowShellCycleSelection
