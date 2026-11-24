import checkpoints.shen_extension.CycleDeficitReplay

namespace LeanCH.BR.LowShellCycleSelection
open Finset BRq2 BRq3 BR45 BRsGen ExteriorPacking PhysicalCycleStock

/-- Each proposed smaller order is ruled out by retaining the named quota. -/
def GrowthRoom (q r lo target : ℕ) : Prop :=
  ∀h∈Ico lo target,∃d∈Icc 2 5,h≤q*d ∧ target+d≤r+h+1
instance {q r lo target} : Decidable (GrowthRoom q r lo target) := by unfold GrowthRoom; infer_instance

theorem advance_bank {D V Z q r j lo target} (free : QFree D V q) (hq : 5≤q)
    (degree : ∀v∈V,r≤(outN D V v).card) (zv : Z⊆V) (live : Z.Nonempty)
    (initial : lo≤(neighborhood D V Z j).card) (room : GrowthRoom q r lo target) :
    target≤(neighborhood D V Z (j+1)).card := by
  classical
  let H := neighborhood D V Z j
  let T := neighborhood D V Z (j+1)
  have ht : H⊆T := by
    intro x xm
    obtain ⟨a,am,hit⟩ := mem_biUnion.mp xm
    exact mem_biUnion.mpr ⟨a,am,ball_mono_radius (Nat.le_succ j) hit⟩
  have hv : H⊆V := by intro x xm; obtain ⟨a,am,hit⟩ := mem_biUnion.mp xm; exact ball_subset hit
  have zh : Z⊆H := fun a am=>mem_biUnion.mpr ⟨a,am,self_mem_ball (zv am)⟩
  by_contra! fail
  change T.card<target at fail
  have card := card_le_card ht
  obtain ⟨d,dm,cap,limit⟩ := room H.card (mem_Ico.mpr ⟨initial,by omega⟩)
  have rank x (xm : x∈H) : d≤(outN D H x).card := by
    have menu : outN D V x⊆outN D H x ∪ (T\H) := by
      intro y ym
      by_cases inH : y∈H
      · exact mem_union_left _ (mem_outN.mpr ⟨inH,(mem_outN.mp ym).2⟩)
      obtain ⟨a,am,hit⟩ := mem_biUnion.mp xm
      exact mem_union_right _ (mem_sdiff.mpr ⟨mem_biUnion.mpr ⟨a,am,ball_step hit (outN_subset ym) (mem_outN.mp ym).2⟩,inH⟩)
    have bill := (degree x (hv xm)).trans ((card_le_card menu).trans (card_union_le _ _))
    rw [card_sdiff_of_subset ht] at bill
    omega
  obtain ⟨low,high⟩ := mem_Icc.mp dm
  have := BRq6.lower_order hq low (by omega : d<6) (free.mono_set hv) rank (live.mono zh)
  omega

/-- Physical rows complete to A. No indegree hypothesis on individual labels. -/
def allParents (D : CH.Digraph) (V A : Finset ℕ) := V.filter (fun u=>A⊆outN D V u)

theorem parent_avoids_bank {D V A q j} (free : QFree D V q) (time : j+1≤q) :
    Disjoint (allParents D V A) (neighborhood D V A j) := by
  apply disjoint_left.mpr
  intro u pm hit
  obtain ⟨a,am,atU⟩ := mem_biUnion.mp hit
  obtain ⟨_,k,lk,walk⟩ := mem_ball.mp atU
  have arc := (mem_filter.mp pm).2 am
  exact free u _ (by omega) (by omega) (.step (outN_subset arc) (mem_outN.mp arc).2 walk)

/-- A complete next bank supplies its whole j-ball. The old bank and every
row feeding it are both disjoint from that ball, and from each other. -/
theorem common_parent_capacity {D V A B q j} (free : QFree D V q) (time : j+2≤q)
    (av : A⊆V) (edges : ∀a∈A,B⊆outN D V a) (live : A.Nonempty) :
    (allParents D V A).card+A.card+(neighborhood D V B j).card≤V.card := by
  classical
  let P := allParents D V A
  let T := neighborhood D V B j
  have ap : A⊆allParents D V B := fun a am=>mem_filter.mpr ⟨av am,edges _ am⟩
  have disAT : Disjoint A T := (parent_avoids_bank free (by omega : j+1≤q)).mono_left ap
  have around : A∪T⊆neighborhood D V A (j+1) := by
    intro x xm
    rcases mem_union.mp xm with a|t
    · exact mem_biUnion.mpr ⟨x,a,self_mem_ball (av a)⟩
    obtain ⟨a,am⟩ := live
    obtain ⟨b,bm,hit⟩ := mem_biUnion.mp t
    obtain ⟨xv,l,lim,walk⟩ := mem_ball.mp hit
    have arc := edges a am bm
    exact mem_biUnion.mpr ⟨a,am,mem_ball.mpr ⟨xv,l+1,by omega,.step (outN_subset arc) (mem_outN.mp arc).2 walk⟩⟩
  have disP : Disjoint P (A∪T) := (parent_avoids_bank free (by omega : (j+1)+1≤q)).mono_right around
  have tv : T⊆V := by intro x xm; obtain ⟨a,am,h⟩ := mem_biUnion.mp xm; exact ball_subset h
  have bound := card_le_card (union_subset (filter_subset _ _ : P⊆V) (union_subset av tv))
  change (P∪(A∪T)).card≤V.card at bound
  change P.card+A.card+T.card≤V.card
  rw [card_union_of_disjoint disP,card_union_of_disjoint disAT] at bound
  omega

/-- Numeric floors are used solely for the actual next bank. Its complete
predecessor therefore limits the priceable incoming rows to V−A−top. -/
theorem parent_room {D V A B q r g mid top} (free : QFree D V q) (hq : 6≤q)
    (reg : OutEq r D V) (room : r+2≤2*q) (av : A⊆V) (bv : B⊆V)
    (al : A.Nonempty) (bl : B.Nonempty) (small : B.card≤2*q) (edges : ∀a∈A,B⊆outN D V a)
    (score : ScoreRoom q r B.card g) (step : GrowthRoom q r g mid) (again : GrowthRoom q r mid top) :
    (allParents D V A).card+A.card+top≤V.card := by
  have start := bank_growth free hq reg bv bl small room score
  have first := advance_bank free (by omega) (fun v vm=>(reg v vm).ge) bv bl start step
  have last := advance_bank free (by omega) (fun v vm=>(reg v vm).ge) bv bl first again
  have bound := common_parent_capacity (j:=4) free (by omega) av edges al
  change top≤(neighborhood D V B 4).card at last
  omega


/-- Complete predecessors sharing a nonempty sparse next bank are either
the same labelled cycle, or require both their sets of rows at that bank. -/
theorem competing_predecessors {D V q r A A' Z} (free : QFree D V q) (hq : 2≤q)
    (reg : OutEq r D V) (hr : 3≤r) (ra : ∀a∈A,Rooted D V a A)
    (rb : ∀a∈A',Rooted D V a A') (rz : ∀z∈Z,Rooted D V z Z)
    (intoA : exterior D V A=Z) (intoB : exterior D V A'=Z) (zs : Z.card=r-1) :
    A=A' ∨ A.card+A'.card≤(allParents D V Z).card := by
  classical
  by_cases same : A=A'
  · exact Or.inl same
  right
  have covered {P} (root : ∀x∈P,Rooted D V x P) (eq : exterior D V P=Z) : P⊆allParents D V Z := by
    intro a am
    have av := (root a am).sub am
    refine mem_filter.mpr ⟨av,?_⟩
    intro z zm
    have full := complete_row (root a am) (reg a av) ((congrArg card eq).trans zs)
    rw [eq] at full
    exact mem_of_mem_erase (full.symm ▸ zm)
  have dis : Disjoint A A' := by
    apply disjoint_left.mpr
    intro v va vb
    apply same
    apply complete_exclusive (c:=0) (d:=1) free hq ra rb reg ((congrArg card intoA).trans zs) _ _ (by omega) va vb
    · rw [intoA]
      exact fun z zm=>((rz z zm).one z zm).le
    · simp [omissions,intoB,zs]
  have bound := card_le_card (union_subset (covered ra intoA) (covered rb intoB))
  rwa [card_union_of_disjoint dis] at bound

/-- Capacity for a weak cycle's first landing. An arriving complete bank
and a genuinely noncomplete claiming cycle spend disjoint physical rows. -/
theorem predecessor_and_claim {D V q r A Z C} (free : QFree D V q) (hq : 2≤q)
    (reg : OutEq r D V) (ra : ∀a∈A,Rooted D V a A) (rc : ∀a∈C,Rooted D V a C)
    (rz : ∀z∈Z,Rooted D V z Z) (into : exterior D V A=Z) (zs : Z.card=r-1)
    (nonzero : 0<omissions D V C r) (room : omissions D V C r+1<r-1) :
    A.card+(C.filter (fun v=>Z⊆outN D V v)).card≤(allParents D V Z).card := by
  classical
  let G := C.filter (fun v=>Z⊆outN D V v)
  have aSub : A⊆allParents D V Z := by
    intro a am
    have av := (ra a am).sub am
    have row := complete_row (ra a am) (reg a av) ((congrArg card into).trans zs)
    rw [into] at row
    exact mem_filter.mpr ⟨av,fun z zm=>mem_of_mem_erase (row.symm ▸ zm)⟩
  have gSub : G⊆allParents D V Z := fun v vm=>mem_filter.mpr ⟨(rc v (mem_filter.mp vm).1).sub (mem_filter.mp vm).1,
    (mem_filter.mp vm).2⟩
  have dis : Disjoint A G := by
    apply disjoint_left.mpr
    intro v va vg
    have equal := complete_exclusive (c:=omissions D V C r) (d:=1) free hq ra rc reg
      ((congrArg card into).trans zs) (by rw [into]; exact fun z zm=>((rz z zm).one z zm).le)
      le_rfl room va (mem_filter.mp vg).1
    rw [←equal] at nonzero
    simp [omissions,into,zs] at nonzero
  have bound := card_le_card (union_subset aSub gSub)
  rwa [card_union_of_disjoint dis] at bound

/-- Every actual receiving bank in a routed chain satisfies the capacity
bill, up to and including the strong terminal itself. -/
theorem along_chain {D V q r Z k g mid top} (free : QFree D V q) (hq : 6≤q)
    (reg : OutEq r D V) (hr : 2≤r) (fit : r≤q+2)
    (score : ScoreRoom q r (r-1) g) (step : GrowthRoom q r g mid) (again : GrowthRoom q r mid top)
    (valid : ∀j≤k+1,(bankIteration D V Z j).card=r-1 ∧
      ∀x∈bankIteration D V Z j,Rooted D V x (bankIteration D V Z j)) :
    ∀j≤k,(allParents D V (bankIteration D V Z j)).card+(r-1)+top≤V.card := by
  intro j jm
  let A := bankIteration D V Z j
  let B := bankIteration D V Z (j+1)
  have ⟨asize,roots⟩ := valid j (by omega)
  have ⟨bsize,next⟩ := valid (j+1) (by omega)
  change A.card=r-1 at asize
  change B.card=r-1 at bsize
  have av : A⊆V := fun a am=>(roots a am).sub am
  have bv : B⊆V := fun b bm=>(next b bm).sub bm
  have covered a (am : a∈A) : B⊆outN D V a := by
    have row := complete_row (roots a am) (reg a (av am)) bsize
    exact fun v vm=>mem_of_mem_erase (row.symm ▸ (show v∈exterior D V A from vm))
  have count := parent_room free hq reg (by omega) av bv (card_pos.mp (by omega)) (card_pos.mp (by omega))
    (by omega) covered (bsize ▸ score) step again
  change (allParents D V A).card+(r-1)+top≤V.card
  omega

#print axioms along_chain
#print axioms competing_predecessors
#print axioms predecessor_and_claim

#print axioms parent_room
end LeanCH.BR.LowShellCycleSelection
