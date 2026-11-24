import checkpoints.shen_extension.CHFamilyWorklist
import checkpoints.shen_extension.ExtremalSinkReturn

namespace LeanCH.BR.TerminalLayerReturns
open Finset BRq2 BRq3 BR45 BRsGen SinkReturnAncestors

/-- A physical target with more returning parents than a sink can omits
cannot drain to any sink before the final allowable step. -/
theorem return_depth {D V X Y q c x t k} (free : QFree D V q) (xv : X⊆V) (yv : Y⊆V)
    (xm : x∈X) (tm : t∈X) (stop : Sink D X t) (route : Walk D X x t k)
    (omissions : ∀s∈X,Sink D X s → (Y \ outN D V s).card≤c)
    (many : c < (inN D Y x).card) : q≤k+1 := by
  by_contra! early
  have sub : inN D Y x⊆Y \ outN D V t := by
    intro y ym
    obtain ⟨yy,back⟩ := mem_inN.mp ym
    refine mem_sdiff.mpr ⟨yy,fun head => ?_⟩
    exact free x _ (by omega) (by omega)
      (((route.mono xv).snoc (yv yy) (mem_outN.mp head).2).snoc (xv xm) back)
  exact (not_lt_of_ge ((card_le_card sub).trans (omissions t tm stop))) many

/-- Across the two banks there is at most one target above the common
omission allowance. If it exists, its shortest sink path uses every
vertex, and it has exactly the depth forced by the cutoff. -/
theorem exceptional_target {D V X Y q c x} (free : QFree D V q) (xv : X⊆V) (yv : Y⊆V)
    (room : X.card≤q) (xm : x∈X)
    (omits : ∀s∈X,Sink D X s → (Y \ outN D V s).card≤c) (many : c<(inN D Y x).card) :
    ∃p : ShortestSinkPath D X x, p.len+1=q ∧ (range (p.len+1)).image p.vertex=X ∧
      (outN D X x).card≤1 ∧ ∀v∈X,c<(inN D Y v).card → v=x := by
  classical
  obtain ⟨p⟩ := exists_shortest_sink_path (free.mono_set xv) room xm
  have walk := p.walk (Nat.zero_le _) le_rfl
  rw [p.start,Nat.sub_zero] at walk
  have lo := return_depth free xv yv xm (p.mem _ le_rfl) p.sink walk omits many
  have hi := p.bounded
  have eq : p.len+1=q := by omega
  have full : (range (p.len+1)).image p.vertex=X := by
    apply eq_of_subset_of_card_le
    · intro a am
      obtain ⟨i,im,rfl⟩ := mem_image.mp am
      exact p.mem i (Nat.le_of_lt_succ (mem_range.mp im))
    · rw [card_image_of_injOn (p.injective (free.mono_set xv) room),card_range]; omega
  have degree := SinkTransit.internal_depth (free.mono_set xv) room p
  refine ⟨p,eq,full,by omega,?_⟩
  intro v vm manyV
  obtain ⟨i,im,rfl⟩ := mem_image.mp (full.symm ▸ vm)
  have limit : i≤p.len := Nat.le_of_lt_succ (mem_range.mp im)
  have length := return_depth free xv yv vm (p.mem _ le_rfl) p.sink (p.walk limit le_rfl) omits manyV
  have start : i=0 := by omega
  rw [start,p.start]

/-- Even the exceptional target pays for its incoming arcs with its own
missing opposite-bank heads, leaving one internal successor at most. -/
theorem parent_capacity {D V X Y q c r x} (free : QFree D V q) (xv : X⊆V) (yv : Y⊆V)
    (time : 2≤q) (room : X.card≤q) (apart : Disjoint X Y) (xm : x∈X)
    (degree : r≤(outN D (X∪Y) x).card) (omits : ∀s∈X,Sink D X s → (Y \ outN D V s).card≤c)
    (many : c<(inN D Y x).card) : (inN D Y x).card+r≤Y.card+1 := by
  obtain ⟨_,_,_,one,_⟩ := exceptional_target free xv yv room xm omits many
  have disjoint : Disjoint (outN D Y x) (inN D Y x) := by
    apply disjoint_left.mpr
    intro y outY inY
    exact digonfree free time (xv xm) (yv (outN_subset outY)) (mem_outN.mp outY).2 (mem_inN.mp inY).2
  have total := card_le_card (union_subset (outN_subset : outN D Y x ⊆ Y)
    (fun _ a=>(mem_inN.mp a).1 : inN D Y x ⊆ Y))
  rw [card_union_of_disjoint disjoint] at total
  rw [card_outN_union apart] at degree
  omega
#print axioms return_depth
#print axioms exceptional_target
#print axioms parent_capacity
end LeanCH.BR.TerminalLayerReturns

namespace LeanCH.BR.TerminalLayerReturns
open Finset BRq2 BRq3 BR45 BRsGen SinkReturnAncestors

/-- The same physical rows hit every proposed recipient. Once their
number exceeds the omissions they can hit at most one. A larger bank
cannot hit even that recipient. -/
theorem common_recipients {D V X Y H W q c r} (free : QFree D V q) (xv : X⊆V) (yv : Y⊆V)
    (time : 2≤q) (room : X.card≤q) (apart : Disjoint X Y)
    (degree : ∀x∈X,r≤(outN D (X∪Y) x).card)
    (omits : ∀s∈X,Sink D X s → (Y \ outN D V s).card≤c)
    (parents : H⊆Y) (targets : W⊆X) (paid : ∀y∈H,∀x∈W,D y x=true) :
    (c<H.card → W.card≤1) ∧ (c<H.card → Y.card+1<H.card+r → W=∅) := by
  classical
  have covers (x) (wx : x∈W) : H⊆inN D Y x := fun y hy=>mem_inN.mpr ⟨parents hy,paid y hy x wx⟩
  constructor
  · intro large
    apply card_le_one.mpr
    intro x wx v wv
    have many := large.trans_le (card_le_card (covers x wx))
    obtain ⟨_,_,_,_,only⟩ := exceptional_target free xv yv room (targets wx) omits many
    exact (only v (targets wv) (large.trans_le (card_le_card (covers v wv)))).symm
  · intro large excess
    apply eq_empty_iff_forall_notMem.mpr
    intro x wx
    have bill := card_le_card (covers x wx)
    have cap := parent_capacity free xv yv time room apart (targets wx) (degree x (targets wx)) omits (large.trans_le bill)
    omega

attribute [aesop safe forward (immediate := [free,xv,yv,xm,tm,stop,route,omissions,many]) (rule_sets := [CHGraphFamilies])] return_depth
attribute [aesop safe forward (immediate := [free,xv,yv,room,xm,omits,many]) (rule_sets := [CHGraphFamilies])] exceptional_target
attribute [aesop safe forward (immediate := [free,xv,yv,time,room,apart,xm,degree,omits,many]) (rule_sets := [CHGraphFamilies])] parent_capacity
attribute [aesop safe forward (immediate := [free,xv,yv,time,room,apart,degree,omits,parents,targets,paid]) (rule_sets := [CHGraphFamilies])] common_recipients
#print axioms common_recipients
end LeanCH.BR.TerminalLayerReturns