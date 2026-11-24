import checkpoints.shen_extension.SingleOmissionOrigin
namespace LeanCH.BR.OneOmissionSinkBank
open Finset BRq2 BRq3 BR45 BRsGen SinkReturnAncestors

/-- Remove the returning labels and their possible second origin, preserving
access from every first-shell sink and the identities of the return arcs. -/
theorem partition {D V X Y q r} (free : QFree D V q) (xv : X⊆V) (yv : Y⊆V)
    (apart : Disjoint X Y) (dx : X.card=r) (dy : Y.card=r+1) (time : r+1≤q) (hr : 7≤r)
    (budget : ∀s∈X,Sink D X s → (Y\outN D V s).card≤1)
    (rank : ∀x∈X,r≤(outN D (X∪Y) x).card) :
    ∃E⊆Y, returning D X Y⊆E ∧ E.card≤max 2 (sinks D X).card ∧
      (∀a∈Y\E,∀e∈E,D a e≠true) ∧
      (∀s∈X,Sink D X s → (outN D (Y\E) s).Nonempty) ∧
      ∀e∈E,(∃x∈X,D e x=true) ∨
        ∃y∈Y,∃x∈X,D e y=true ∧ D y x=true ∧ Y\E⊆outN D V x := by
  classical
  obtain ⟨size,a,am,head⟩ := shared_entry free xv yv (by omega) (by omega) budget
  by_cases earlier : ∃b∈Y,∃y∈returning D X Y,D b y=true
  · obtain ⟨b,bm,y,ym,byArc⟩ := earlier
    obtain ⟨yy,x,xh⟩ := mem_filter.mp ym
    have xm := outN_subset xh
    have yx := (mem_outN.mp xh).2
    have ⟨only,missing,avoid⟩ := parentful free xv yv apart dx dy time (by omega) budget (rank x xm) xm yy bm yx byArc
    have ne : b≠y := fun eq=>loopfree free (by omega) (yv yy) (eq ▸ byArc)
    have two : ({b,y} : Finset ℕ).card=2 := by simp [ne]
    have sub : ({b,y} : Finset ℕ)⊆Y := by intro v vm; rcases mem_insert.mp vm with eq | one; exacts [eq ▸ bm, (mem_singleton.mp one) ▸ yy]
    refine ⟨{b,y},sub,by simp [only],by omega,?_,?_,?_⟩
    · intro v vm e em
      rcases mem_insert.mp em with eq|eq
      · exact eq ▸ (avoid v vm).1
      · exact (mem_singleton.mp eq) ▸ (avoid v vm).2
    · intro s sm stop
      by_contra none
      have bad : Y\{b,y}⊆Y\outN D V s := by
        intro v vm
        exact mem_sdiff.mpr ⟨(mem_sdiff.mp vm).1,fun hit=>none ⟨v,mem_outN.mpr ⟨vm,(mem_outN.mp hit).2⟩⟩⟩
      have le := (card_le_card bad).trans (budget s sm stop)
      rw [card_sdiff_of_subset sub] at le
      omega
    · intro e em
      rcases mem_insert.mp em with eq|eq
      · subst e
        refine Or.inr ⟨y,yy,x,xm,byArc,yx,?_⟩
        intro v vm
        apply outN_mono yv x
        by_contra off
        exact (mem_sdiff.mp vm).2 (missing ▸ mem_sdiff.mpr ⟨(mem_sdiff.mp vm).1,off⟩)
      · obtain rfl := mem_singleton.mp eq
        exact Or.inl ⟨x,xm,yx⟩
  · refine ⟨returning D X Y,filter_subset _ _,Subset.rfl,by omega,?_,?_,?_⟩
    · exact fun v vm e em arc=>earlier ⟨v,(mem_sdiff.mp vm).1,e,em,arc⟩
    · exact fun s sm stop=>⟨a,mem_outN.mpr ⟨am,head s (mem_filter.mpr ⟨sm,stop⟩)⟩⟩
    · intro e em
      obtain ⟨_,x,xh⟩ := mem_filter.mp em
      exact Or.inl ⟨x,outN_subset xh,(mem_outN.mp xh).2⟩

attribute [aesop safe forward (immediate := [free,xv,yv,apart,dx,dy,time,hr,budget,rank]) (rule_sets := [CHGraphFamilies])] partition
#print axioms partition
end LeanCH.BR.OneOmissionSinkBank
