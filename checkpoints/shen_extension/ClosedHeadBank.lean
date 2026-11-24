import checkpoints.shen_extension.SinkTransit
namespace LeanCH.BR.ClosedHeadBank
open Finset BRq2 BRq3 BR45 BRsGen

/-- Start at all heads in Y at once. Once a round fails to add a vertex,
every later round has the same labels. At most the initially missing
labels can be added, so closure is reached by that radius. -/
theorem closure {D : CH.Digraph} {Y F : Finset ℕ} (fy : F⊆Y) :
    ∃C⊆Y,F⊆C ∧ (∀x∈C,outN D Y x⊆C) ∧
      ∀x∈C,∃a∈F,x∈ball D Y a (Y.card-F.card) := by
  classical
  let B := fun k=>F.biUnion (fun a=>ball D Y a k)
  have inside k : B k⊆Y := by
    intro x xm
    obtain ⟨a,_,hit⟩ := mem_biUnion.mp xm
    exact ball_subset hit
  have start k : F⊆B k := fun a am=>mem_biUnion.mpr ⟨a,am,self_mem_ball (fy am)⟩
  have mono {i j : ℕ} (ij : i≤j) : B i⊆B j := by
    intro x xm
    obtain ⟨a,am,hit⟩ := mem_biUnion.mp xm
    exact mem_biUnion.mpr ⟨a,am,ball_mono_radius ij hit⟩
  let k := Y.card-F.card
  have room := card_le_card fy
  have stop : ∃j,j≤k ∧ B j=B (j+1) := by
    by_contra! none
    have grows (j) (le : j≤k+1) : F.card+j≤(B j).card := by
      induction j with
      | zero => simpa using card_le_card (start 0)
      | succ j ih =>
        have h := ih (by omega)
        have strict := card_lt_card (ssubset_of_subset_of_ne (mono (show j≤j+1 by omega)) (none j (by omega)))
        omega
    have high := grows (k+1) le_rfl
    have low := card_le_card (inside (k+1))
    dsimp only [k] at high low
    omega
  obtain ⟨j,le,fixed⟩ := stop
  refine ⟨B j,inside j,start j,?_,fun _ h=>mem_biUnion.mp (mono le h)⟩
  intro x xm y ym
  obtain ⟨a,am,hit⟩ := mem_biUnion.mp xm
  rw [fixed]
  exact mem_biUnion.mpr ⟨a,am,ball_step hit (outN_subset ym) (mem_outN.mp ym).2⟩

/-- An anchor with few omitted heads supplies an internally closed set,
including all its heads and excluding *all* its parents. The allowance
counts labels in Y and the cutoff measures the actual return. -/
theorem at_anchor {D V Y q b} (free : QFree D V q) (yv : Y⊆V) (bv : b∈V)
    (time : (Y.card-(outN D Y b).card)+2≤q) :
    ∃C⊆Y,outN D Y b⊆C ∧ (∀x∈C,outN D Y x⊆C) ∧ ∀x∈C,D x b≠true := by
  obtain ⟨C,cy,heads,closed,near⟩ := closure (D:=D) (outN_subset : outN D Y b⊆Y)
  refine ⟨C,cy,heads,closed,?_⟩
  intro x xc arc
  obtain ⟨a,ah,path⟩ := near x xc
  obtain ⟨_,l,le,walk⟩ := mem_ball.mp path
  exact free a _ (by omega) (by omega)
    (((walk.mono yv).snoc bv arc).snoc (yv (outN_subset ah)) (mem_outN.mp ah).2)

/-- A fixed row and each of its actual heads have d heads in the same
carrier. A sink of d chosen heads supplies d disjoint labels; it also
misses the starting label by the digon constraint. -/
theorem two_row_size {D V X q d x} (free : QFree D V q) (xv : X⊆V) (xm : x∈X)
    (low : 0<d) (small : d≤q) (hq : 2≤q) (one : d≤(outN D X x).card)
    (two : ∀y∈outN D X x,d≤(outN D X y).card) : 2*d+1≤X.card := by
  classical
  obtain ⟨H,hh,ds⟩ := exists_subset_card_eq one
  have hx : H⊆X := hh.trans outN_subset
  obtain ⟨a,am,last⟩ := exists_sink (free.mono_set (hx.trans xv)) (card_pos.mp (by omega)) (by omega)
  have dis : Disjoint H (outN D X a) := disjoint_left.mpr (fun y ym head=>last y ym (mem_outN.mp head).2)
  have rest : H∪outN D X a⊆X.erase x := by
    intro z zm
    rcases mem_union.mp zm with zH|za
    · exact mem_erase.mpr ⟨fun eq=> loopfree free (by omega) (xv xm) (eq ▸ (mem_outN.mp (hh zH)).2),hx zH⟩
    · refine mem_erase.mpr ⟨?_,outN_subset za⟩
      rintro rfl
      exact free z 2 (by decide) hq (.step (xv (hx am)) (mem_outN.mp (hh am)).2 (.step (xv xm) (mem_outN.mp za).2 (.refl z)))
  have cap := card_le_card rest
  rw [card_union_of_disjoint dis,card_erase_of_mem xm] at cap
  have high := two a (hh am)
  omega

attribute [aesop safe forward (immediate := [free,yv,bv,time]) (rule_sets := [CHGraphFamilies])] at_anchor
attribute [aesop safe forward (immediate := [free,xv,xm,low,small,hq,one,two]) (rule_sets := [CHGraphFamilies])] two_row_size
#print axioms closure
#print axioms at_anchor
#print axioms two_row_size
end LeanCH.BR.ClosedHeadBank
