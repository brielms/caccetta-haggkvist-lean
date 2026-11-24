import checkpoints.shen_extension.FullSuccessorContact

namespace LeanCH.BR.LowShellCycleSelection
open Finset BRq2 BRq3 BR45 BRsGen ExteriorPacking PhysicalCycleStock CHRuleCatalog
open scoped Classical

/-- The unpaid account forces two distinct representatives within three
steps. The full successor bank forbids that very contact at those labels. -/
theorem priced_primary_false {p : Input} {target δ cap} (bad : Bad p)
    (priced : PricedPrimaryInput p δ cap) (ready : RoutingRoom (cutoff p) p.s p.n target) : False := by
  obtain ⟨F,sub,reg,t,policy,C,mark,length,degree,account,next,_,profile⟩ := priced
  have free := qfree_sub sub (qfree_of_noShort bad.loopless bad.missing)
  have room : RoutingRoom (cutoff p) p.s (range p.n).card target := by simpa using ready
  have hq := ready.cycle.1
  have lookup Y (ym : Y∈primaryKeys t C) := profile Y (mem_filter.mp ym).1 (mem_filter.mp ym).2
  have residual : shellDebt F (range p.n) 3 (3*p.s) C≤4 := by
    apply (class_residual (m:=3) _).trans (by decide)
    intro v _
    unfold debit
    split_ifs <;> omega
  obtain ⟨Y,ym,Z,zm,ne,hit⟩ := actual_primary_contact free reg t policy room mark account next
    (fun Y ym=>(lookup Y ym).1.ge) (by omega) (by omega)
  have y := (mem_filter.mp (mem_filter.mp ym).1).1
  have z := (mem_filter.mp (mem_filter.mp zm).1).1
  obtain ⟨_,size,b,bm,heads⟩ := lookup Y ym
  obtain ⟨_,size',f,fm,heads'⟩ := lookup Z zm
  exact priced_origins_separate free (by omega) reg (by omega) (rep_native t y) (rep_native t z) ne
    (card_pos.mp (by omega)) (by omega) (mem_filter.mp ym).2 (mem_filter.mp zm).2
    account.allHeads account.width next (mem_sdiff.mp bm).2 (mem_sdiff.mp fm).2
    ((rep_key t y).trans heads) ((rep_key t z).trans heads') size.le (by omega) hit

/-- Numerical suppliers for the local contradiction, with each floor and
allowance left as a witness. -/
def PrimaryContactWindow (n r q : ℕ) : Prop :=
  ∃ target g mid top cap, PrimaryRoom q r n target g mid top cap ∧
    cap+5<3*(r-1) ∧ 4*(r-q+1)<3*fullRowFloor q r ∧ CompletePriceRoom q r ∧
    ArrivalRoom q r (n-((r-1)+top)) cap ∧ n+8<(r-1)+top+3*(r-1) ∧
    (2*r-1)*(2*r)<(r-1)*(2*(r+4))+r*14

theorem outside_primary_contact_window {p : Input} (bad : Bad p) :
    ¬PrimaryContactWindow p.n p.s (cutoff p) := by
  rintro ⟨target,g,mid,top,cap,room,reserve,afford,prices,route,cost,capacity⟩
  have cyclic := (cyclic_exterior_on_bad bad).on_room _ _ _ _ _ room reserve afford prices route
  obtain ⟨_,score,step,again,_⟩ := room.transfer
  exact priced_primary_false bad (price_cyclic_primaries bad cyclic room.route score step again cost capacity) room.route

attribute [aesop safe forward (immediate := [bad,priced,ready]) (rule_sets := [CHGraphFamilies])] priced_primary_false
attribute [aesop safe forward (immediate := [bad]) (rule_sets := [CHGraphFamilies])] outside_primary_contact_window
#print axioms priced_primary_false
#print axioms outside_primary_contact_window
end LeanCH.BR.LowShellCycleSelection
