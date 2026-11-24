import checkpoints.shen_extension.SparseCycleReturns
import LeanCH.BR.BRq3FSE4
namespace LeanCH.BR.SparseCycleReturns
open Finset BRq2 BRq3 BR45 BRsGen

/-- Each returning exterior label is missed by all but at most two of the
marked cycle rows. The misses are charged to the actual row-column cells. -/
theorem omission_budget {D V C P A q m} (free : QFree D V q) (cv : C⊆V) (av : A⊆V) (pc : P⊆C)
    (size : C.card=q+1) (positive : ∀v∈C,1≤(outN D C v).card) (hq : 2≤q)
    (returns : ∀v∈A,(outN D C v).Nonempty) (misses : ∀v∈P,(A\outN D A v).card≤m) :
    A.card*(P.card-2)≤P.card*m := by
  classical
  have byColumn a (am : a∈A) : P.card-2≤(P.filter (fun v=>D v a≠true)).card := by
    obtain ⟨c,cm⟩ := returns a am
    have step : Walk D V a c 1 := .step (cv (outN_subset cm)) (mem_outN.mp cm).2 (.refl c)
    have cap := parent_cap free cv pc size positive (av am) (outN_subset cm) step hq
    have eq : P.filter (fun v=>D v a≠true)=P\inN D P a := by
      ext v; simp [inN]; tauto
    rw [eq,card_sdiff_of_subset (show inN D P a⊆P from fun _ h=>(mem_inN.mp h).1)]
    omega
  have byRow v (vm : v∈P) : (A.filter (fun a=>D v a≠true)).card≤m := by
    have eq : A.filter (fun a=>D v a≠true)=A\outN D A v := by ext a; simp [outN]; tauto
    rw [eq]; exact misses v vm
  have col := sum_le_sum byColumn
  have row := sum_le_sum byRow
  rw [sum_const_nat (fun _ _=>rfl)] at col row
  rw [BRq3.double_count (fun v a=>D v a≠true)] at row
  omega

/-- Three recipients each missing at most two of the labels in their own
carrier induce a positive-degree triple, which is forbidden. -/
theorem heavy_cluster {D V A S q} (free : QFree D V q) (hq : 3≤q) (av : A⊆V)
    (sa : S⊆A) (heavy : ∀a∈S,A.card≤(outN D A a).card+2) : S.card≤2 := by
  by_contra! many
  obtain ⟨T,ts,dt⟩ := exists_subset_card_eq (show 3≤S.card by omega)
  have ta := ts.trans sa
  obtain ⟨x,xm,stop⟩ := exists_sink (free.mono_set (ta.trans av)) (card_pos.mp (by omega)) (by omega)
  have off : outN D A x⊆A\T := fun a am=>mem_sdiff.mpr ⟨outN_subset am,fun at'=>stop a at' (mem_outN.mp am).2⟩
  have total := card_sdiff_add_card_eq_card ta
  have h := card_le_card off
  have := heavy x (ts xm)
  omega

/-- One spare label beyond the tight shortest-cycle room allows at most
six full rows if the cycle meets some full row. All counts concern the
actual exterior labels and their return arcs. -/
theorem marked_cycle_cap {D V C H q d} (free : QFree D V q) (hq : 3≤q) (cv : C⊆V)
    (hv : H⊆V) (size : C.card=q+1) (one : OutEq 1 D C)
    (positive : ∀v∈V,1≤(outN D V v).card) (quota : ∀v∈H,d≤(outN D V v).card)
    (room : (V\C).card≤d) (range : (V\C).card≤q) (lo : 3≤d) (met : (C∩H).Nonempty) :
    H.card≤6 := by
  classical
  let A := V\C
  let P := C∩H
  let F := H\C
  have av : A⊆V := sdiff_subset
  have pc : P⊆C := inter_subset_left
  have ph : P⊆H := inter_subset_right
  have fa : F⊆A := fun x xm=>mem_sdiff.mpr ⟨hv (mem_sdiff.mp xm).1,(mem_sdiff.mp xm).2⟩
  have split x : (outN D C x).card+(outN D A x).card=(outN D V x).card := by
    rw [←card_outN_union (disjoint_sdiff : Disjoint C A),union_sdiff_of_subset cv]
  obtain ⟨p,pm⟩ := met
  have misses v (vm : v∈P) : (A\outN D A v).card≤1 := by
    have h := split v
    rw [one v (pc vm)] at h
    have := quota v (ph vm)
    rw [card_sdiff_of_subset outN_subset]
    change A.card≤d at room
    omega
  have minC v (vm : v∈C) := (one v vm).ge
  have heads v (vm : v∈F) : (outN D C v).Nonempty := by
    have sub : outN D A v⊆A.erase v := fun a am=>mem_erase.mpr
      ⟨fun eq=>loopfree free (by omega) (av (fa vm)) (eq ▸ (mem_outN.mp am).2),outN_subset am⟩
    have h := card_le_card sub
    rw [card_erase_of_mem (fa vm)] at h
    have := split v
    have := quota v (mem_sdiff.mp vm).1
    change A.card≤d at room
    exact card_pos.mp (by omega)
  have small := two_port_cap free cv av pc size minC range (by
    have h := split p
    rw [one p (pc pm)] at h
    have := quota p (ph pm)
    have := card_le_card (outN_subset : outN D A p⊆A)
    omega) hq (fun v vm=>by rw [union_sdiff_of_subset cv]; exact card_pos.mp (positive v (av vm))) misses
  have total := omission_budget free cv (fa.trans av) pc size minC (by omega) heads (fun v vm=>by
    have sub : F\outN D F v⊆A\outN D A v := by
      intro a am
      obtain ⟨af,no⟩ := mem_sdiff.mp am
      exact mem_sdiff.mpr ⟨fa af,fun h=>no (mem_outN.mpr ⟨af,(mem_outN.mp h).2⟩)⟩
    exact (card_le_card sub).trans (misses v vm))
  have base := card_sdiff_add_card_inter H C
  rw [inter_comm H C] at base
  change F.card+P.card=H.card at base
  by_cases many : 3≤P.card
  · interval_cases m : P.card <;> simp only [Nat.reduceSub,Nat.mul_one] at total <;> omega
  have sub : F∩outN D A p⊆A := inter_subset_right.trans outN_subset
  have heavy a (am : a∈F∩outN D A p) : A.card≤(outN D A a).card+2 := by
    obtain ⟨v,vm⟩ := card_pos.mp (show 0<(outN D C p).card by rw [one p (pc pm)]; decide)
    obtain ⟨w,wm⟩ := card_pos.mp (show 0<(outN D C v).card by rw [one v (outN_subset vm)]; decide)
    have ao := WeightedSD.cycle_two_step_detour_heads (by omega) free cv size one (pc pm)
      (outN_subset vm) (outN_subset wm) (av (sub am)) (mem_outN.mp vm).2 (mem_outN.mp wm).2 (mem_outN.mp (mem_inter.mp am).2).2
    have cap := (card_le_card ao).trans (card_insert_le v {w})
    rw [card_singleton] at cap
    have := quota a (mem_sdiff.mp (mem_inter.mp am).1).1
    have := split a
    change A.card≤d at room
    omega
  have most := heavy_cluster free hq av sub heavy
  have diff := card_sdiff_add_card_inter F (outN D A p)
  have missing := card_le_card (show F\outN D A p⊆A\outN D A p from fun _ h=>mem_sdiff.mpr ⟨fa (mem_sdiff.mp h).1,(mem_sdiff.mp h).2⟩)
  have := misses p pm
  omega
/-- When every cycle of the carrier meets the full set, one spare slot
above q+d still permits at most six full rows. Equivalently, a larger
full set forces a physical directed cycle in its complement. -/
theorem one_spare {D V H q d} (free : QFree D V q) (hq : 3≤q) (hv : H⊆V)
    (positive : ∀v∈V,1≤(outN D V v).card) (quota : ∀v∈H,d≤(outN D V v).card)
    (lo : 3≤d) (fits : d≤q) (size : V.card≤q+d+1)
    (acyclic : QFree D (V\H) (V\H).card) : H.card≤6 := by
  classical
  by_contra! many
  have live : V.Nonempty := (card_pos.mp (by omega : 0<H.card)).mono hv
  obtain ⟨p,C,pq,pfree,cv,sz,one⟩ := exists_minimal_cycle_support (by omega) free positive live
  have met : (C∩H).Nonempty := by
    by_contra empty
    have sub : C⊆V\H := fun x xm=>mem_sdiff.mpr ⟨cv xm,fun xh=>empty ⟨x,mem_inter.mpr ⟨xm,xh⟩⟩⟩
    obtain ⟨s,sm,stopped⟩ := exists_sink (acyclic.mono_set sub) (card_pos.mp (by omega)) (card_le_card sub)
    obtain ⟨a,am⟩ := card_pos.mp (show 0<(outN D C s).card by rw [one s sm]; decide)
    exact stopped a (outN_subset am) (mem_outN.mp am).2
  have delta := card_sdiff_add_card_eq_card cv
  exact many.not_ge (marked_cycle_cap pfree (by omega) cv hv sz one positive quota (by omega) (by omega) lo met)

attribute [aesop safe forward (immediate := [free,cv,av,pc,size,positive,hq,returns,misses]) (rule_sets := [CHGraphFamilies])] omission_budget
attribute [aesop safe forward (immediate := [free,hq,av,sa,heavy]) (rule_sets := [CHGraphFamilies])] heavy_cluster
attribute [aesop safe forward (immediate := [free,hq,cv,hv,size,one,positive,quota,room,range,lo,met]) (rule_sets := [CHGraphFamilies])] marked_cycle_cap
attribute [aesop safe forward (immediate := [free,hq,hv,positive,quota,lo,fits,size,acyclic]) (rule_sets := [CHGraphFamilies])] one_spare
#print axioms one_spare
#print axioms omission_budget
#print axioms heavy_cluster
#print axioms marked_cycle_cap
end LeanCH.BR.SparseCycleReturns
