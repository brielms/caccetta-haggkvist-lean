import checkpoints.shen_extension.LastArcHeadDeposit

namespace LeanCH.BR.Closure.LastArcMenuPayment
open Finset BRq2 BRq3 BR45 WeightedSD ShortestCycleWeights FirstPacketBarrier

/-- Choose the small menu after the old price is fixed. If its two
distinguishing rows reach the real parents and all dangerous columns are
covered, one actual dry row gives a simultaneous payment certificate. -/
theorem pay {q n F L v t r y z} (X : Model q n) (hq : 3≤q)
    (S : Finset ℕ) (ss : S⊆X.V) (size : S.card≤q) (vm : v∈S) (ym : y∈S) (zm : z∈S)
    (yz : y≠z) (tv : t∈X.V) (rv : r∈X.V)
    (pt : X.D t v=true) (pr : X.D r v=true) (yt : X.D y t=true) (zr : X.D z r=true)
    (p : ℕ→ℝ) (old : RealDual q (graph X.D F) X.V 1 p) {C : ℝ} (high : 1≤C)
    (cap : ∀j∈X.V,realCol q (graph X.D (insert L F)) X.V p j≤C)
    (att : ∃j∈X.V,realCol q (graph X.D (insert L F)) X.V p j=C)
    (diagonal : ∀i∈S,i≠y → i≠z → realCol q (graph X.D (insert L F)) X.V p i≤1)
    (cover : ∀j∈X.V,1<realCol q (graph X.D (insert L F)) X.V p j+((q:ℝ)-1)*(C-1) →
      j∈S∪{t,r}) :
    ∃ i∈S, i≠y ∧ i≠z ∧ ∃ u:ℝ, 0≤u ∧
      RealDual q (graph X.D (insert L F)) X.V 1 (LastArcHeadDeposit.price p i u) := by
  classical
  have ts : ({t,r} : Finset ℕ)⊆X.V := insert_subset tv (singleton_subset_iff.mpr rv)
  have parents (j) (jm : j∈({t,r} : Finset ℕ)) : X.D j v=true := by
    simp only [mem_insert, mem_singleton] at jm
    exact jm.elim (fun h=>h ▸ pt) (fun h=>h ▸ pr)
  obtain ⟨i,im,dry⟩ := LastArcReturnMenu.dry_row hq X.free ss ts size vm parents ym zm yz
    ⟨t,by simp,yt⟩ ⟨r,by simp,zr⟩
  have avoids {j} (jm : j∈S∪{t,r}) : X.D i j≠true := by
    intro arc
    have hit := mem_outN.mpr ⟨jm,arc⟩
    rw [dry] at hit
    exact notMem_empty _ hit
  have iy : i≠y := fun h=>avoids (j:=t) (by simp) (h ▸ yt)
  have iz : i≠z := fun h=>avoids (j:=r) (by simp) (h ▸ zr)
  have loop : graph X.D (insert L F) i i=false := Bool.eq_false_iff.mpr
    (fun e=>loopfree X.free (by omega) (ss im) (CrossValueOmissions.selected_sub e))
  refine ⟨i,im,iy,iz,(LastArcHeadDeposit.deposit_iff (by omega : 1≤q) (ss im) loop p
    old.nonneg old.normalized (diagonal i im iy iz) high cap att).mpr ?_⟩
  intro j jm arc
  exact le_of_not_gt (fun expensive=>avoids (cover j jm expensive) (CrossValueOmissions.selected_sub arc))

/-- The supplier sought in the attachment problem. Every price test and
incidence in the package is on the specified old family and alternative. -/
def Cover {q n} (X : Model q n) (F : MarkedCyclePeeling.Family) (L : Finset ℕ) : Prop :=
  let val := fun p => realCol q (graph X.D (insert L F)) X.V p
  ∃ (S : Finset ℕ) (v t r y z : ℕ) (p : ℕ→ℝ) (C : ℝ),
    S⊆X.V ∧ S.card≤q ∧ v∈S ∧ y∈S ∧ z∈S ∧ y≠z ∧ t∈X.V ∧ r∈X.V ∧
    X.D t v=true ∧ X.D r v=true ∧ X.D y t=true ∧ X.D z r=true ∧
    RealDual q (graph X.D F) X.V 1 p ∧ 1≤C ∧ (∀j∈X.V,val p j≤C) ∧ (∃j∈X.V,val p j=C) ∧
    (∀i∈S,i≠y → i≠z → val p i≤1) ∧ (∀j∈X.V,1<val p j+((q:ℝ)-1)*(C-1) → j∈S∪{t,r})

def OnFamily {q n} (X : Model q n) (F : MarkedCyclePeeling.Family) : Prop :=
  ∀ L, Cover X F L → SmallRow q (graph X.D (insert L F)) X.V

theorem on_model {q n} (X : Model q n) (hq : 3≤q) (F) : OnFamily X F := by
  intro L supply
  obtain ⟨S,v,t,r,y,z,p,C,ss,size,vm,ym,zm,yz,tv,rv,pt,pr,yt,zr,old,high,cap,att,diag,con⟩ := supply
  obtain ⟨_,_,_,_,_,_,paid⟩ := pay X hq S ss size vm ym zm yz tv rv pt pr yt zr p old high cap att diag con
  exact smallRow_of_realDual paid

#print axioms pay
#print axioms on_model
end LeanCH.BR.Closure.LastArcMenuPayment
