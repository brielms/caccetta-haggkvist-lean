import checkpoints.shen_extension.FourCycleMarkedReturns
import checkpoints.shen_extension.FourCycleReturnSlack
import checkpoints.shen_extension.OneArcReturnBudget

namespace LeanCH.BR.WalkReturn
open Finset BRq2 BRq3 BR45 TripleBank

/-- The residual graph H determines which middles need payment from y.
Only its two relevant neighbourhoods have to be inherited by the source D.
The same tight middle gives an overlap bound at every successor of w in D. -/
theorem tight_return_obstruction {D H : CH.Digraph} {V U : Finset ℕ} {s t p w y : ℕ}
    (safe : QFree D V 3) (reg : OutEq s D V)
    (lower : ∀ j, j<s → BypassRepair.NoHost 3 j) (order : V.card≤3*s)
    (sub : U⊆V) (wu : w∈U) (yu : y∈U) (pv : p∈V) (pw : D p w=true) (py : D p y=true)
    (no : BypassRepair.NoHost 3 t) (size : U.card≤3*t) (ok : QFree H U 3)
    (wy : w≠y) (off : H w y≠true) (back : H y w≠true)
    (need : t≤(outN H U w).card+1) (floor : ∀ v∈U, v≠w → t≤(outN H U v).card)
    (oldY : outN H U y⊆outN D V y) (oldW : inN H U w⊆inN D V w) :
    let K := (outN H U y ∩ inN H U w).filter (fun z => (outN H U z).card≤t)
    ∃ z∈K, 3*(outN D K z).card<K.card ∧ ∀ d∈V, D w d=true →
      2*K.card+4+3*(3*s-V.card)≤3*returnOverlap D V z w d ∧
      2*((outN H U y).card-t)+6+3*(3*s-V.card)≤3*returnOverlap D V z w d := by
  classical
  intro K
  have unpaid : (outN H U y).card<t+K.card := by
    by_contra! paid
    obtain ⟨E,good,_,rows⟩ := one_arc_return_budget ok wu yu wy off back need floor paid
    exact no E U ⟨w,wu⟩ size good rows
  have fy := floor y yu wy.symm
  have live : K.Nonempty := card_pos.mp (by omega)
  have copy : K⊆outN D V y ∩ inN D V w := by
    intro z zk
    obtain ⟨zy,zw⟩ := mem_inter.mp (mem_filter.mp zk).1
    exact mem_inter.mpr ⟨oldY zy,oldW zw⟩
  have common : p∈inN D V y ∩ inN D V w :=
    mem_inter.mpr ⟨mem_inN.mpr ⟨pv,py⟩,mem_inN.mpr ⟨pv,pw⟩⟩
  have pcount := card_pos.mpr (show (inN D V y ∩ inN D V w).Nonempty from ⟨p,common⟩)
  obtain ⟨z,zk,light,all⟩ := light_return_middle safe reg (sub yu) (sub wu) copy live lower
  refine ⟨z,zk,light,?_⟩
  intro d dv wd
  have h := all d dv wd
  constructor <;> omega

/-- A sufficiently small four-cycle score in the original two-label
source pays the residual one-arc repair. Extra reverse middles w→i→y
improve the threshold one for one. -/
theorem witness_walk_pays {D H : CH.Digraph} {V U : Finset ℕ} {s t y z w x : ℕ}
    (safe : QFree D V 3) (reg : OutEq s D V) (hs : 2≤s)
    (order : V.card=3*(s-1)+2) (no : BypassRepair.NoHost 3 (s-1))
    (yv : y∈V) (zv : z∈V) (wv : w∈V) (xv : x∈V)
    (yz : D y z=true) (zw : D z w=true) (wx : D w x=true) (xy : D x y=true)
    (ok : QFree H U 3) (wu : w∈U) (yu : y∈U) (wy : w≠y)
    (off : H w y≠true) (back : H y w≠true)
    (need : t≤(outN H U w).card+1) (floor : ∀ v∈U, v≠w → t≤(outN H U v).card)
    (oldY : outN H U y⊆outN D V y) (oldW : inN H U w⊆inN D V w)
    (budget : 3*(overlap D V y z+overlap D V z w+overlap D V w x+overlap D V x y) +
      (witnesses D V y z w+witnesses D V z w x+witnesses D V w x y+witnesses D V x y z) ≤
      18+middles D V w y+((outN H U y).card-t)) :
    ∃ E : CH.Digraph, QFree E U 3 ∧ E w y=true ∧ ∀ i∈U, t≤(outN E U i).card := by
  classical
  have walk := two_label_diagonal_budget safe reg hs order no yv zv wv xv yz zw wx xy
  have retained : (outN H U y ∩ inN H U w).filter (fun i => (outN H U i).card≤t)
      ⊆ outN D V y ∩ inN D V w := by
    intro i hi
    obtain ⟨yi,iw⟩ := mem_inter.mp (mem_filter.mp hi).1
    exact mem_inter.mpr ⟨oldY yi,oldW iw⟩
  have count := card_le_card retained
  rw [←middles_eq_card] at count
  have fy := floor y yu wy.symm
  exact one_arc_return_budget ok wu yu wy off back need floor (by omega)

#print axioms witness_walk_pays
#print axioms tight_return_obstruction
end LeanCH.BR.WalkReturn
