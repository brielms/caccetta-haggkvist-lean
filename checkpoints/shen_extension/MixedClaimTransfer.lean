import checkpoints.shen_extension.OmissionFamilyEntry

namespace LeanCH.BR.LowShellCycleSelection
open Finset BRq2 BRq3 BR45 BRsGen ExteriorPacking PhysicalCycleStock
open scoped Classical

/-- An individual acyclic claimant may use the weak-bank route even if a
primary claimant is also assigned to its source cycle. The actual tier
budget controls the compression, without a singleton account hypothesis. -/
theorem itemized_route {D V q r target g mid top C Y budget} (free : QFree D V q)
    (reg : OutEq r D V) (sel : Selection D V q r 3 (3*r)) (ready : RoutingRoom q r V.card target)
    (ym : Y∈claims sel C) (dag : QFree D (outN D V (sel.rep Y)) (outN D V (sel.rep Y)).card)
    (om : omissions D V C r=1)
    (tier : (C.filter (fun a=>3*r<(ball D V a 3).card)).card+
      2*(C.filter (fun a=>3*r+1<(ball D V a 3).card)).card≤budget)
    (afford : budget<3*fullRowFloor q r)
    (score : ScoreRoom q r (r-1) g) (grow : GrowthRoom q r g mid) (again : GrowthRoom q r mid top) :
    ∃T,StrongTerminal D V r T ∧
      WeakArrival D V r (V.card-((r-1)+top)) (fullRowFloor q r) 1 C T := by
  classical
  have yc := (mem_filter.mp ym).2
  have chain := weak_row_chain free reg (by have := ready.growth.2.1; omega) sel (mem_filter.mp ym).1 dag ready.cycle
    ready.close ready.space ready.distance ready.score ready.high ready.squeeze ready.finite budget (yc.symm ▸ tier) afford
  rw [yc] at chain
  obtain ⟨v,vc,sends,high,k,kt,valid,strong⟩ := chain
  let Z := N3 D V (sel.rep Y)
  let B := bankIteration D V Z
  let δ := V.card-((r-1)+top)
  have hq := ready.cycle.1
  have hr := ready.growth.2.1
  have yk := (mem_filter.mp ym).1
  have supply := selected_stock free reg (by omega) sel yk ready.cycle dag
    (by have := ready.close; have := ready.space; omega) ready.distance ready.score
  dsimp only at supply
  rw [yc] at supply
  obtain ⟨cy,sz,nfull,paid⟩ := supply
  let G := C.filter (fun a=>Z⊆outN D V a)
  change C.card≤G.card+(r-C.card)*(r-q) at nfull
  have cc := sel.length _ (sel.assigned Y yk)
  rw [yc] at cc
  have delta := Nat.mul_le_mul_right (r-q) (show r-C.card≤r-(q+1) by omega)
  have count : fullRowFloor q r≤G.card := by dsimp [fullRowFloor]; omega
  have cv := sel.rooted _ (sel.assigned Y yk)
  rw [yc] at cv
  have sep : Disjoint C Z := disjoint_left.mpr (fun a am az=>(mem_N3.mp az).2
    (mem_N2.mp ((rep_key sel yk).symm ▸ cy am)).1)
  have capacity := along_chain (Z:=Z) free hq reg (by omega) ready.close score grow again valid
  have node j (jm : j≤k) : RouteBank D V r δ (B j) := by
    have p := capacity j jm
    change (allParents D V (B j)).card+(r-1)+top≤V.card at p
    exact ⟨(valid j (by omega)).1,(valid j (by omega)).2,by dsimp [δ]; omega⟩
  have path j (jm : j≤k) : Relation.ReflTransGen (RouteEdge D V r δ) Z (B j) := by
    induction j with
    | zero => exact .refl
    | succ j ih => exact .tail (ih (by omega)) ⟨node j (by omega),node _ jm,rfl⟩
  refine ⟨B k,⟨(valid k (by omega)).1,(valid k (by omega)).2,(valid (k+1) le_rfl).1,
    (valid (k+1) le_rfl).2,strong⟩,cv,⟨by omega,by omega⟩,Z,node 0 (by omega),sep,count,path k le_rfl⟩


/-- Find the actual weak route at the lower score available in the native
graph. The selected marks and original stock agree with the primary account. -/
theorem medium_route {D V q r target g mid top cap δ C A Z} (free : QFree D V q)
    (reg : OutEq r D V) (t : Selection D V q r 3 (3*r)) (policy : ShellBooking t)
    (room : PrimaryRoom q r V.card target g mid top cap) (mark : MixedPayer t C δ cap A)
    (width : (exterior D V C).card=r) (zm : Z∈claims t C)
    (dag : QFree D (outN D V (t.rep Z)) (outN D V (t.rep Z)).card)
    (medium : ∀Y∈claims t C,C⊆outN D V (t.rep Y) → 3*r≤(ball D V (t.rep Y) 3).card)
    (afford : 4*(r-q+1)<3*fullRowFloor q r) :
    ∃T,StrongTerminal D V r T ∧
      WeakArrival D V r (V.card-((r-1)+top)) (fullRowFloor q r) 1 C T := by
  classical
  have hq := room.route.cycle.1
  have hr := room.route.growth.2.1
  have fit := room.route.close
  have off : C∉shortSwitches t := by
    intro sw
    have := (switched_shell_paid free reg t (by omega) hr fit sw).1.width
    omega
  have size : C.card+1=r := by rw [mark.length,mark.degree]
  have small := one_omission_total free reg t room.route policy off width size medium
  have empty : A=∅ := eq_empty_iff_forall_notMem.mpr (fun T tm=>by
    have := (mark.charges.routed T tm).2.2.2.2.1.nextSize; omega)
  have due := mark.charges.due
  rw [empty,sum_empty,add_zero] at due
  have original := le_sub_iff_add_le.mp due
  have scale K (km : K∈booked t) : omissions D V K r≤r-q := by
    obtain ⟨Y,ym,rfl⟩ := mem_image.mp km; exact t.loss _ (t.assigned _ ym)
  have bill := shortfall_of_bill free reg (by omega : r-q+2≤q) t scale mark.charges.bookedHere
    (by rw [add_comm]; exact original)
  have loss : omissions D V C r=1 := by unfold omissions; rw [width]; omega
  have charges : ∑Y∈claims t C,shellDebt D V 3 (3*r) Y≤(receipts t C).card+2 := by
    have rat := sub_le_iff_le_add.mp small
    rw [add_comm] at rat
    exact_mod_cast rat
  have mult := Nat.mul_le_mul_right ((r-q+1)*2^1) charges
  rw [Nat.add_mul (receipts t C).card 2] at mult
  rw [loss] at bill
  simp only [pow_one] at mult bill
  have tier := tier_stock D V C 3 (3*r)
  exact itemized_route free reg t room.route zm dag loss (budget:=4*(r-q+1)) (by omega) afford
    room.transfer.2.1 room.transfer.2.2.1 room.transfer.2.2.2.1

#print axioms itemized_route
#print axioms medium_route
end LeanCH.BR.LowShellCycleSelection
