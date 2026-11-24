import checkpoints.shen_extension.SinkTransit
namespace LeanCH.BR.OneOmissionSinkBank
open Finset BRq2 BRq3 BR45 BRsGen SinkReturnAncestors

def sinks (D : CH.Digraph) (X : Finset ℕ) := X.filter (fun s=>∀a∈X,D s a≠true)
def returning (D : CH.Digraph) (X Y : Finset ℕ) := Y.filter (fun y=>(outN D X y).Nonempty)

/-- The interior of a shortest path to a sink misses every sink,
including sinks the path was not chosen to visit. -/
theorem depth_count {D X q x} (free : QFree D X q) (size : X.card≤q)
    (p : ShortestSinkPath D X x) : p.len+(sinks D X).card≤X.card := by
  have sub : (range p.len).image p.vertex⊆X\sinks D X := by
    intro a am
    obtain ⟨i,im,rfl⟩ := mem_image.mp am
    have le := mem_range.mp im
    exact mem_sdiff.mpr ⟨p.mem i le.le,fun h=>(mem_filter.mp h).2 _ (p.mem _ le) (p.edge i le)⟩
  have cap := card_le_card sub
  have incl : (range p.len : Set ℕ) ⊆ range (p.len+1) := by
    intro i im
    exact mem_range.mpr (Nat.lt_succ_of_lt (mem_range.mp im))
  rw [card_image_of_injOn ((p.injective free size).mono incl),card_range,
    card_sdiff_of_subset (show sinks D X⊆X from filter_subset _ _)] at cap
  have := card_le_card (show sinks D X⊆X from filter_subset _ _)
  omega

/-- The omitted labels over *all* sinks cover every row returning
from Y. At least one Y label is headed by all sinks if Y is larger. -/
theorem shared_entry {D V X Y q} (free : QFree D V q) (xv : X⊆V) (yv : Y⊆V)
    (time : X.card+1≤q) (wide : X.card<Y.card)
    (budget : ∀s∈X,Sink D X s → (Y\outN D V s).card≤1) :
    (returning D X Y).card≤(sinks D X).card ∧
      ∃a∈Y\returning D X Y,∀s∈sinks D X,D s a=true := by
  classical
  let S := sinks D X
  let O := returning D X Y
  let M := S.biUnion (fun s=>Y\outN D V s)
  have om : O⊆M := by
    intro y ym
    obtain ⟨yy,x,xa⟩ := mem_filter.mp ym
    obtain ⟨s,sm,last,k,le,way⟩ := reach_sink_of_card (free.mono_set xv) (by omega) (outN_subset xa)
    refine mem_biUnion.mpr ⟨s,mem_filter.mpr ⟨sm,last⟩,mem_sdiff.mpr ⟨yy,?_⟩⟩
    intro head
    exact free x _ (by omega) (by omega)
      (((way.mono xv).snoc (yv yy) (mem_outN.mp head).2).snoc (xv (outN_subset xa)) (mem_outN.mp xa).2)
  have cost := card_biUnion_le_card_mul S (fun s=>Y\outN D V s) 1
    (fun s sm=> budget s (mem_filter.mp sm).1 (mem_filter.mp sm).2)
  have tally : M.card≤S.card := by simpa only [Nat.mul_one] using cost
  have bound := card_le_card (show S⊆X from filter_subset _ _)
  have off : ¬Y⊆M := fun inc=>by have := card_le_card inc; omega
  obtain ⟨a,ay,no⟩ := not_subset.mp off
  refine ⟨(card_le_card om).trans tally,a,mem_sdiff.mpr ⟨ay,fun ao=>no (om ao)⟩,?_⟩
  intro s sm
  by_contra none
  exact no (mem_biUnion.mpr ⟨s,sm,mem_sdiff.mpr ⟨ay,fun head=>none (mem_outN.mp head).2⟩⟩)

/-- A row returning into X has no parent in Y when sinks of X omit one
and the return still has time for one preceding Y-arc. -/
theorem no_parent {D V X Y q} (free : QFree D V q) (xv : X⊆V) (yv : Y⊆V)
    (time : X.card+2≤q) (budget : ∀s∈X,Sink D X s → (Y\outN D V s).card≤1)
    {b y} (by' : b∈Y) (yo : y∈returning D X Y) : D b y≠true := by
  obtain ⟨yy,x,xh⟩ := mem_filter.mp yo
  have yx := mem_inN.mpr ⟨yy,(mem_outN.mp xh).2⟩
  have bound := sink_budget (l:=1) free xv yv (outN_subset xh) (by omega) budget
  intro arc
  have eq := card_le_one.mp bound b (mem_filter.mpr ⟨by',y,yx,ball_of_adj yy arc⟩) y
    (mem_filter.mpr ⟨yy,y,yx,self_mem_ball yy⟩)
  exact loopfree free (by omega) (yv yy) (eq ▸ arc)

attribute [aesop safe forward (immediate := [free,size,p]) (rule_sets := [CHGraphFamilies])] depth_count
attribute [aesop safe forward (immediate := [free,xv,yv,time,wide,budget]) (rule_sets := [CHGraphFamilies])] shared_entry
attribute [aesop safe forward (immediate := [free,xv,yv,time,budget,by',yo]) (rule_sets := [CHGraphFamilies])] no_parent
#print axioms depth_count
#print axioms shared_entry
#print axioms no_parent
end LeanCH.BR.OneOmissionSinkBank
