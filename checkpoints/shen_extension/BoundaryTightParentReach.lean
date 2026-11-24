import checkpoints.shen_extension.ReceiverProtectedMenu

namespace LeanCH.BR.BoundaryTightParentReach
open Finset BRq2 BRq3 BR45 BRsub BypassTwoStepRow

def tight (D : CH.Digraph) (H : Finset ℕ) (t g : ℕ) :=
  H.filter fun a=>D a g=true ∧ (outN D H a).card=t

/-- The complement of the backward (q−2)-balls of the tight parents,
restricted to the physical labels other than the row itself. -/
noncomputable def remote (D : CH.Digraph) (H : Finset ℕ) (q t g : ℕ) :=
  (H.erase g).filter fun b=>Disjoint (ball D H b (q-2)) (tight D H t g)

private def spareRows (D : CH.Digraph) (H : Finset ℕ) (t : ℕ) :=
  H.filter fun a=>t<(outN D H a).card

private def trim (D : CH.Digraph) (H : Finset ℕ) (t g : ℕ) :=
  DotFullReturnCut.cut D (spareRows D H t) g

private noncomputable def fill (D : CH.Digraph) (H : Finset ℕ) (q t g : ℕ) :=
  DeleteRepair.repair (trim D H t g) {g} (fun _=>remote D H q t g)

theorem old_heads_remote {D H q t g} (free : QFree D H q) (cut : 2≤q) (gm : g∈H) :
    outN D H g⊆remote D H q t g := by
  intro b bm
  obtain ⟨bh,gb⟩ := mem_outN.mp bm
  have ne : b≠g := fun eq=>loopfree free (by omega) gm (eq ▸ gb)
  refine mem_filter.mpr ⟨mem_erase.mpr ⟨ne,bh⟩,disjoint_left.mpr ?_⟩
  intro a reach parent
  obtain ⟨_,k,le,w⟩ := mem_ball.mp reach
  obtain ⟨_,ag,_⟩ := mem_filter.mp parent
  exact free a (k+1+1) (by omega) (by omega) (.step gm ag (.step bh gb w))

private theorem fill_free {D H q t g} (free : QFree D H q) (cut : 2≤q)
    (gm : g∈H) (other : ∀a∈H,a≠g → t≤(outN D H a).card) : QFree (fill D H q t g) H q := by
  have sub a b (h : trim D H t g a b=true) := DotFullReturnCut.cut_sub h
  apply DeleteRepair.repair_qfree (qfree_sub sub free)
  intro _ _ b bm v vm k cap ret
  have vg := mem_singleton.mp vm
  subst v
  obtain ⟨bh,far⟩ := mem_filter.mp bm
  obtain ⟨ne,bh⟩ := mem_erase.mp bh
  cases k with
  | zero => cases ret; exact ne rfl
  | succ k =>
    obtain ⟨a,path,_,last⟩ := ret.unsnoc
    have ah : a∈H := path.end_mem_or.elim (fun e=>e ▸ bh) id
    obtain ⟨ag,keep⟩ := DotFullReturnCut.cut_edge.mp last
    have ao : a≠g := fun e=>loopfree free (by omega) gm (e ▸ ag)
    have lo : (outN D H a).card≤t := by
      by_contra! hi
      exact keep.elim (fun out=>out (mem_filter.mpr ⟨ah,hi⟩)) (fun n=>n rfl)
    exact disjoint_left.mp far (mem_ball.mpr ⟨ah,k,by omega,walk_sub sub path⟩)
      (mem_filter.mpr ⟨ah,ag,Nat.le_antisymm lo (other a ah ao)⟩)

private theorem fill_row {D H q t g} (free : QFree D H q) (cut : 2≤q) (gm : g∈H)
    (low : (outN D H g).card≤t) : outN (fill D H q t g) H g=remote D H q t g := by
  have off : g∉spareRows D H t := fun m=>(Nat.not_lt_of_ge low) (mem_filter.mp m).2
  ext b
  simp only [fill,trim,mem_outN,DeleteRepair.repair,Bool.or_eq_true,Bool.and_eq_true,
    decide_eq_true_eq,mem_singleton_self,true_and,DotFullReturnCut.cut_edge,off,not_false_eq_true,true_or,and_true]
  constructor
  · rintro ⟨bh,old|hit⟩
    · exact old_heads_remote free cut gm (mem_outN.mpr ⟨bh,old⟩)
    · exact hit
  · exact fun m=>⟨(mem_erase.mp (mem_filter.mp m).1).2,Or.inr m⟩

private theorem fill_others {D H q t g} (other : ∀a∈H,a≠g → t≤(outN D H a).card)
    {a} (ah : a∈H) (ag : a≠g) : t≤(outN (fill D H q t g) H a).card := by
  have incl : outN (trim D H t g) H a ⊆ outN (fill D H q t g) H a :=
    fun _ m=>mem_outN.mpr ⟨outN_subset m,DeleteRepair.repair_old (mem_outN.mp m).2⟩
  apply le_trans _ (card_le_card incl)
  by_cases has : a∈spareRows D H t
  · rw [trim,DotFullReturnCut.cut_donor_row has]
    have slack := (mem_filter.mp has).2
    by_cases edge : g∈outN D H a
    · have := card_erase_add_one edge; omega
    · rw [erase_eq_of_notMem edge]; exact slack.le
  · rw [trim,DotFullReturnCut.cut_outside_row has]; exact other a ah ag

/-- At the boundary order all remote columns fit in the quota. If the
quota is attained, the trim-and-fill graph is regular in both directions. -/
theorem boundary_table {D H q t g} (free : QFree D H q) (cut : 2≤q) (gm : g∈H)
    (size : H.card=q*t+1) (br : Compose.Boundary.BoundaryRegular q t)
    (low : (outN D H g).card≤t) (other : ∀a∈H,a≠g → t≤(outN D H a).card) :
    (remote D H q t g).card≤t ∧
    (t≤(remote D H q t g).card →
      (tight D H t g).card=t ∧
      ∀b∈H,b≠g → (inN D H b ∪ (if b∈remote D H q t g then {g} else ∅)).card=t) := by
  classical
  have safe := fill_free (t:=t) free cut gm other
  have row := fill_row free cut gm low
  have paid (hit : t≤(remote D H q t g).card) a (ah : a∈H) : t≤(outN (fill D H q t g) H a).card := by
    by_cases eq : a=g
    · simpa [eq,row] using hit
    · exact fill_others other ah eq
  constructor
  · by_contra! high
    exact WeightedSD.boundary_regular_no_excess (by omega) br safe size (paid high.le) gm (row ▸ high)
  · intro hit
    have indeg := RootRegularBridge.inRegular_of_boundaryRegular (by omega) br _ _ safe size (paid hit)
    have core : inN (fill D H q t g) H g=tight D H t g := by
      ext a
      have off : g∉remote D H q t g := fun m=>notMem_erase _ _ (mem_filter.mp m).1
      simp only [fill,trim,mem_inN,DeleteRepair.repair,Bool.or_eq_true,Bool.and_eq_true,
        decide_eq_true_eq,off,and_false,or_false,DotFullReturnCut.cut_edge,ne_eq,not_true_eq_false,or_false,
        tight,mem_filter,spareRows]
      constructor
      · rintro ⟨ah,ag,no⟩
        have ao : a≠g := fun e=>loopfree free (by omega) gm (e ▸ ag)
        exact ⟨ah,ag,le_antisymm (Nat.le_of_not_gt (fun hi=>no ⟨ah,hi⟩)) (other a ah ao)⟩
      · exact fun ⟨ah,ag,eq⟩=>⟨ah,ag,fun ⟨_,hi⟩=>by omega⟩
    refine ⟨core ▸ indeg g gm,?_⟩
    intro b bh bg
    have col : inN (fill D H q t g) H b=inN D H b ∪ (if b∈remote D H q t g then {g} else ∅) := by
      ext a
      by_cases mem : b∈remote D H q t g <;>
        simp [fill,trim,mem_inN,DeleteRepair.repair,DotFullReturnCut.cut_edge,bg,mem]
      grind
    exact col ▸ indeg b bh

/-- A viable fresh column in a one-slot row is unique. All other column
degrees away from g are exactly t, and this particular one has t−1. -/
theorem fresh_profile {D H q t g b} (free : QFree D H q) (cut : 2≤q) (gm : g∈H)
    (size : H.card=q*t+1) (br : Compose.Boundary.BoundaryRegular q t)
    (short : (outN D H g).card+1=t) (other : ∀a∈H,a≠g → t≤(outN D H a).card)
    (fresh : b∈remote D H q t g) (miss : D g b≠true) :
    remote D H q t g=insert b (outN D H g) ∧ (tight D H t g).card=t ∧
    ∀a∈H,a≠g → (inN D H a).card+(if a=b then 1 else 0)=t := by
  classical
  have off : b∉outN D H g := fun m=>miss (mem_outN.mp m).2
  have sub := insert_subset fresh (old_heads_remote free cut gm (t:=t))
  have eq := card_insert_of_notMem off
  obtain ⟨cap,cost⟩ := boundary_table free cut gm size br (by omega) other
  have enough := card_le_card sub
  have same : insert b (outN D H g)=remote D H q t g := eq_of_subset_of_card_le sub (by omega)
  obtain ⟨parents,cols⟩ := cost (by omega)
  refine ⟨same.symm,parents,?_⟩
  intro a am ag
  have col := cols a am ag
  rw [←same] at col
  by_cases ab : a=b
  · subst a
    have absent : g∉inN D H b := fun m=>miss (mem_inN.mp m).2
    simpa [absent] using col
  · by_cases ga : a∈outN D H g
    · have inc : g∈inN D H a := mem_inN.mpr ⟨gm,(mem_outN.mp ga).2⟩
      simpa [ab,ga,inc] using col
    · simpa [ab,ga] using col

#print axioms fresh_profile
attribute [aesop safe forward (immediate := [free,cut,gm,size,br,low,other]) (rule_sets := [CHGraphFamilies])]
  boundary_table
ch_family_split_result boundary_table
#print axioms old_heads_remote
#print axioms boundary_table
end LeanCH.BR.BoundaryTightParentReach
