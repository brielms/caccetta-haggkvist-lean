import checkpoints.shen_extension.OneOmissionTransit
namespace LeanCH.BR.OneOmissionSinkBank
open Finset BRq2 BRq3 BR45 BRsGen SinkReturnAncestors

/-- With a single omission at every sink, the ancestors of a parentful
return have just two possible labels. The actual return target heads
every remaining label of Y. -/
theorem parentful {D V X Y q r x y b} (free : QFree D V q) (xv : X⊆V) (yv : Y⊆V)
    (apart : Disjoint X Y) (dx : X.card=r) (dy : Y.card=r+1) (time : r+1≤q) (hr : 4≤r)
    (budget : ∀s∈X,Sink D X s → (Y\outN D V s).card≤1)
    (rank : r≤(outN D (X∪Y) x).card)
    (xm : x∈X) (ym : y∈Y) (bm : b∈Y) (yx : D y x=true) (byArc : D b y=true) :
    returning D X Y={y} ∧ Y\outN D Y x={b,y} ∧
    ∀a∈Y\{b,y},D a b≠true ∧ D a y≠true := by
  classical
  obtain ⟨p⟩ := exists_shortest_sink_path (free.mono_set xv) (by omega) xm
  let s := p.vertex p.len
  have sx : s∈X := p.mem _ le_rfl
  have path : Walk D V x s p.len := by
    simpa only [p.start,Nat.sub_zero] using (p.walk (Nat.zero_le _) le_rfl).mono xv
  have ne : b≠y := fun eq=>loopfree free (by omega) (yv ym) (eq ▸ byArc)
  have diff : ({b,y} : Finset ℕ).card=2 := by simp [ne]
  have deep : q<p.len+3 := by
    by_contra! le
    have missed : ({b,y} : Finset ℕ)⊆Y\outN D V s := by
      intro a am
      rcases mem_insert.mp am with eq|eq
      · subst a
        exact mem_sdiff.mpr ⟨bm,fun head=> free x _ (by omega) (by omega)
          (((path.snoc (yv bm) (mem_outN.mp head).2).snoc (yv ym) byArc).snoc (xv xm) yx)⟩
      · obtain rfl := mem_singleton.mp eq
        exact mem_sdiff.mpr ⟨ym,fun head=>free x _ (by omega) (by omega)
          ((path.snoc (yv ym) (mem_outN.mp head).2).snoc (xv xm) yx)⟩
    have := (card_le_card missed).trans (budget s sx p.sink)
    omega
  have depth := depth_count (free.mono_set xv) (by omega) p
  have internal := SinkTransit.internal_depth (free.mono_set xv) (by omega) p
  have tally := (shared_entry free xv yv (by omega) (by omega) budget).1
  have only : returning D X Y={y} := eq_of_subset_of_card_le
    (s:={y}) (t:=returning D X Y) (singleton_subset_iff.mpr
      (mem_filter.mpr ⟨ym,x,mem_outN.mpr ⟨xm,yx⟩⟩)) (by rw [card_singleton]; omega) |>.symm
  have missing : ({b,y} : Finset ℕ)⊆Y\outN D Y x := by
    intro a am
    rcases mem_insert.mp am with eq|eq
    · subst a
      exact mem_sdiff.mpr ⟨bm,fun head=>free x 3 (by decide) (by omega)
        (.step (yv bm) (mem_outN.mp head).2 (.step (yv ym) byArc (.step (xv xm) yx (.refl x))))⟩
    · obtain rfl := mem_singleton.mp eq
      exact mem_sdiff.mpr ⟨ym,fun head=>free x 2 (by decide) (by omega)
        (.step (yv ym) (mem_outN.mp head).2 (.step (xv xm) yx (.refl x)))⟩
  rw [card_outN_union apart] at rank
  have card := card_sdiff_add_card_eq_card (outN_subset : outN D Y x⊆Y)
  have eq := eq_of_subset_of_card_le missing (by omega)
  refine ⟨only,eq.symm,?_⟩
  intro a am
  obtain ⟨ay,off⟩ := mem_sdiff.mp am
  have head : a∈outN D Y x := by
    by_contra none
    exact off (eq.symm ▸ mem_sdiff.mpr ⟨ay,none⟩)
  have xa := (mem_outN.mp head).2
  exact ⟨fun ab=>free x 4 (by decide) (by omega)
    (.step (yv ay) xa (.step (yv bm) ab (.step (yv ym) byArc (.step (xv xm) yx (.refl x))))),
    fun az=>free x 3 (by decide) (by omega) (.step (yv ay) xa (.step (yv ym) az (.step (xv xm) yx (.refl x))))⟩

/-- To a sink in a marked subset of Y, either use a short X path or use
the many Y heads forced by a long X path. Up to three removed labels
are affordable on the long-path branch. -/
theorem quick_sink {D V X Y E q r x} (free : QFree D V q) (xv : X⊆V) (yv : Y⊆V)
    (apart : Disjoint X Y) (dx : X.card=r) (dy : Y.card=r+1) (time : r+1≤q) (hr : 7≤r)
    (xm : x∈X) (rank : r≤(outN D (X∪Y) x).card)
    (budget : ∀s∈X,Sink D X s → (Y\outN D V s).card≤1)
    (size : E.card≤max 2 (sinks D X).card)
    (access : ∀s∈X,Sink D X s → (outN D (Y\E) s).Nonempty) :
    ∃t∈Y\E,Sink D (Y\E) t ∧ ∃k,k+2≤r ∧ Walk D V x t k := by
  let A := Y\E
  have ay : A⊆Y := sdiff_subset
  have av := ay.trans yv
  have small := (card_le_card ay).trans (show Y.card≤q by omega)
  obtain ⟨p⟩ := exists_shortest_sink_path (free.mono_set xv) (by omega) xm
  let s := p.vertex p.len
  have sx : s∈X := p.mem _ le_rfl
  have path : Walk D V x s p.len := by
    simpa only [p.start,Nat.sub_zero] using (p.walk (Nat.zero_le _) le_rfl).mono xv
  have diff v : A\outN D A v⊆Y\outN D V v := fun a am=>mem_sdiff.mpr ⟨ay (mem_sdiff.mp am).1,
    fun head=>(mem_sdiff.mp am).2 (mem_outN.mpr ⟨(mem_sdiff.mp am).1,(mem_outN.mp head).2⟩)⟩
  by_cases short : p.len+4≤r
  · obtain ⟨t,tm,stop,k,le,walk⟩ := SinkTransit.from_heads free av small (access s sx p.sink)
    have cap := (card_le_card (diff s)).trans (budget s sx p.sink)
    exact ⟨t,tm,stop,p.len+k,by omega,path.append walk⟩
  have depth := depth_count (free.mono_set xv) (by omega) p
  have internal := SinkTransit.internal_depth (free.mono_set xv) (by omega) p
  rw [card_outN_union apart] at rank
  have room : E.card≤3 := by omega
  have start : (outN D A x).Nonempty := by
    by_contra none
    have cut : outN D Y x⊆E := by
      intro v vm
      by_contra off
      exact none ⟨v,mem_outN.mpr ⟨mem_sdiff.mpr ⟨outN_subset vm,off⟩,(mem_outN.mp vm).2⟩⟩
    have := card_le_card cut
    omega
  obtain ⟨t,tm,stop,k,le,walk⟩ := SinkTransit.from_heads free av small start
  have cap : A\outN D A x⊆Y\outN D Y x := fun a am=>mem_sdiff.mpr ⟨ay (mem_sdiff.mp am).1,
    fun head=>(mem_sdiff.mp am).2 (mem_outN.mpr ⟨(mem_sdiff.mp am).1,(mem_outN.mp head).2⟩)⟩
  have cc := card_le_card cap
  have all := card_sdiff_add_card_eq_card (outN_subset : outN D Y x⊆Y)
  exact ⟨t,tm,stop,k,by omega,walk⟩

attribute [aesop safe forward (immediate := [free,xv,yv,apart,dx,dy,time,hr,budget,rank,xm,ym,bm,yx,byArc]) (rule_sets := [CHGraphFamilies])] parentful
attribute [aesop safe forward (immediate := [free,xv,yv,apart,dx,dy,time,hr,xm,rank,budget,size,access]) (rule_sets := [CHGraphFamilies])] quick_sink
#print axioms parentful
#print axioms quick_sink
end LeanCH.BR.OneOmissionSinkBank
