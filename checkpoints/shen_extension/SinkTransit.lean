import checkpoints.shen_extension.SinkLayerWindow
namespace LeanCH.BR.SinkTransit
open Finset BRq2 BRq3 BR45 BRsGen SinkReturnAncestors

/-- A shortest sink path and the actual outgoing row share at most the
first successor. Each further step occupies a different missed label. -/
theorem internal_depth {D X q x} (free : QFree D X q) (size : X.card≤q)
    (path : ShortestSinkPath D X x) : path.len+(outN D X x).card≤X.card := by
  classical
  let f := fun i=>path.vertex (i+1)
  let S := (range path.len).image f
  have inside : S⊆X := by
    intro a am
    obtain ⟨i,im,rfl⟩ := mem_image.mp am
    exact path.mem _ (mem_range.mp im)
  have inj : Set.InjOn f (range path.len) := by
    intro i im j jm eq
    have eq' := path.injective free size (x₁:=i+1) (x₂:=j+1)
      (mem_range.mpr (Nat.succ_lt_succ (mem_range.mp im)))
      (mem_range.mpr (Nat.succ_lt_succ (mem_range.mp jm))) eq
    omega
  have count : S.card=path.len := by dsimp [S]; rw [card_image_of_injOn inj,card_range]
  let A := insert x S
  have xm : x∈X := path.start ▸ path.mem 0 (Nat.zero_le _)
  have xs : x∉S := by
    intro hit
    obtain ⟨i,im,hit⟩ := mem_image.mp hit
    have eq := path.injective free size (x₁:=i+1) (x₂:=0)
      (mem_range.mpr (Nat.succ_lt_succ (mem_range.mp im)))
      (mem_range.mpr (Nat.zero_lt_succ _)) (hit.trans path.start.symm)
    omega
  have av : A⊆X := insert_subset xm inside
  have lim : (A∩outN D X x)⊆{path.vertex 1} := by
    intro a am
    obtain ⟨aa,head⟩ := mem_inter.mp am
    rcases mem_insert.mp aa with eq|on
    · subst a
      exact (loopfree free (by have := path.bounded; omega) xm (mem_outN.mp head).2).elim
    obtain ⟨i,im,rfl⟩ := mem_image.mp on
    have e : D (path.vertex 0) (path.vertex (i+1))=true := by rw [path.start]; exact (mem_outN.mp head).2
    have step := path.no_chord free size (Nat.zero_le _) (mem_range.mp im) e
    exact mem_singleton.mpr (congrArg path.vertex step)
  have ca : A.card=path.len+1 := by dsimp [A]; rw [card_insert_of_notMem xs,count]
  have cap := card_le_card (union_subset av (outN_subset : outN D X x⊆X))
  have eq := card_union_add_card_inter A (outN D X x)
  have h := card_le_card lim
  rw [card_singleton] at h
  omega

/-- Starting with the whole set of available entries into Y, a shortest
route to any Y-sink spends one *omitted* entry per internal step. -/
theorem from_heads {D V Y q x} (free : QFree D V q) (yv : Y⊆V) (size : Y.card≤q)
    (live : (outN D Y x).Nonempty) :
    ∃s∈Y,Sink D Y s ∧ ∃k,k≤(Y \ outN D Y x).card+1 ∧ Walk D V x s k := by
  classical
  let P := fun k=>∃h∈outN D Y x,∃s∈Y,Sink D Y s ∧ Walk D Y h s k
  have existsP : ∃k,P k := by
    obtain ⟨h,hm⟩ := live
    obtain ⟨s,sm,stop,k,_,walk⟩ := reach_sink_of_card (free.mono_set yv) size (outN_subset hm)
    exact ⟨k,h,hm,s,sm,stop,walk⟩
  obtain ⟨h,hh,s,sm,stop,kroad⟩ := Nat.find_spec existsP
  obtain ⟨path⟩ := exists_shortest_sink_path (free.mono_set yv) size (outN_subset hh)
  have p0 := path.start
  have last := path.mem path.len le_rfl
  let f := fun i=>path.vertex (i+1)
  have sub : (range path.len).image f⊆Y \ outN D Y x := by
    intro a am
    obtain ⟨i,im,rfl⟩ := mem_image.mp am
    have le := mem_range.mp im
    refine mem_sdiff.mpr ⟨path.mem _ le,?_⟩
    intro entry
    have shorter := Nat.find_min' existsP (show P (path.len-(i+1)) from
      ⟨_,entry,_,last,path.sink,path.walk le le_rfl⟩)
    have bound := path.minimal s sm stop _ kroad
    omega
  have inj : Set.InjOn f (range path.len) := by
    intro i hi j hj eq
    have eq' := path.injective (free.mono_set yv) size (x₁:=i+1) (x₂:=j+1)
      (mem_range.mpr (Nat.succ_lt_succ (mem_range.mp hi)))
      (mem_range.mpr (Nat.succ_lt_succ (mem_range.mp hj))) eq
    omega
  have cap := card_le_card sub
  rw [card_image_of_injOn inj,card_range] at cap
  have way : Walk D Y h (path.vertex path.len) path.len := by
    simpa only [path.start,Nat.sub_zero] using path.walk (Nat.zero_le _) le_rfl
  exact ⟨_,last,path.sink,path.len+1,by omega,Walk.step (yv (outN_subset hh)) (mem_outN.mp hh).2 (way.mono yv)⟩

/-- Two routes from x to an actual sink in the next layer. Going first to
an internal sink costs one plus internal depth. Direct entries into Y
cost one plus the number of omitted entries. -/
theorem two_routes {D V X Y q x r} (free : QFree D V q) (xv : X⊆V) (yv : Y⊆V)
    (sizeX : X.card≤q) (sizeY : Y.card≤q) (xm : x∈X) (apart : Disjoint X Y)
    (rank : r≤(outN D (X∪Y) x).card) (entries : (outN D Y x).Nonempty)
    (full : ∀s∈X,Sink D X s → Y⊆outN D V s) :
    ∃s∈Y,Sink D Y s ∧ ∃k,k≤min (X.card-(outN D X x).card+1)
      (Y.card+(outN D X x).card-r+1) ∧ Walk D V x s k := by
  obtain ⟨p⟩ := exists_shortest_sink_path (free.mono_set xv) sizeX xm
  have depth := internal_depth (free.mono_set xv) sizeX p
  obtain ⟨s,sy,stop,k,le,path⟩ := from_heads free yv sizeY entries
  have count := card_sdiff_add_card_eq_card (outN_subset : outN D Y x⊆Y)
  rw [card_outN_union apart] at rank
  obtain ⟨r0,r0m⟩ := entries
  have via : Walk D V x s (p.len+1) := by
    have walk := (p.walk (Nat.zero_le _) le_rfl).mono xv
    simp only [p.start,Nat.sub_zero] at walk
    exact walk.snoc (yv sy) (mem_outN.mp (full _ (p.mem _ le_rfl) p.sink sy)).2
  by_cases shorter : k≤p.len+1
  · exact ⟨s,sy,stop,k,by omega,path⟩
  · exact ⟨s,sy,stop,p.len+1,by omega,via⟩

attribute [aesop safe forward (immediate := [free,size,path]) (rule_sets := [CHGraphFamilies])] internal_depth
attribute [aesop safe forward (immediate := [free,yv,size,live]) (rule_sets := [CHGraphFamilies])] from_heads
attribute [aesop safe forward (immediate := [free,xv,yv,sizeX,sizeY,xm,apart,rank,entries,full])
  (rule_sets := [CHGraphFamilies])] two_routes
#print axioms internal_depth
#print axioms from_heads
#print axioms two_routes
end LeanCH.BR.SinkTransit
