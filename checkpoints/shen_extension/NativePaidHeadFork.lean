import checkpoints.shen_extension.ProtectedHeadPayment
import checkpoints.shen_extension.CycleWithdrawal

namespace LeanCH.BR.Closure.NativePaidHeadFork
open Finset BRq2 BRq3 BR45 ShenPrimeTransition ShenCycleSuccessor ShortestCycleWeights MarkedCyclePeeling FirstPacketBarrier
open JointCycleFamilyBarrier TwoCycleTransfer CycleWithdrawal

/-- From the protected witness for one head, pay the transfer using the
same exterior row, then move to a witness for a different head on A. -/
def Fork {q n} (X : Model q n) (F : Family) (w : ℕ→ℕ) : Prop :=
  let E := graph X.D F
  ∃A∈F,∃p∈X.V\A,∃y∈outN E A p,∃z∈(outN E A p).erase y,∃M∈F,∃L∈F,
    p∈M ∧ y∈M ∧ p∈L ∧ z∈L ∧ Disjoint (A∩M) (A∩L) ∧ ExitTo X F w A M L ∧
    score q E (X.V\(A\M)) (fun v => w v+deposit E A M w v) p ≤
      (∑v∈X.V\(A\M),(w v+deposit E A M w v))

/-- The numerical sufficient test uses the actual margin and two consecutive
weights on A. It is independent of which witness is chosen to protect y. -/
theorem of_credit {q n} (X : Model q n) (hq : 2≤q) {F A p y w} (sub : F⊆family X)
    (af : A∈F) (row : BarrierRow q (graph X.D F) X.V A w p) (yh : y∈outN (graph X.D F) A p)
    (credit : (score q (graph X.D F) X.V w p-(∑v∈X.V,w v))+(∑v∈A,w v)≤
      q*(∑v∈(outN (graph X.D F) A p).erase y,w v)+w y+w (succHead (graph X.D F) A y)) :
    Fork X F w := by
  classical
  let E := graph X.D F
  let H := outN E A p
  obtain ⟨pv,two,_,_,_⟩ := row
  have other := card_erase_add_one yh
  obtain ⟨z,zh⟩ := card_pos.mp (show 0<(H.erase y).card by change 2≤H.card at two; change (H.erase y).card+1=H.card at other; omega)
  obtain ⟨ya,py⟩ := mem_outN.mp yh
  obtain ⟨diff,zc⟩ := mem_erase.mp zh
  obtain ⟨za,pz⟩ := mem_outN.mp zc
  obtain ⟨M,muse⟩ := active.mp py
  obtain ⟨L,luse⟩ := active.mp pz
  obtain ⟨mf,pm,ym,_⟩ := mem_col.mp muse
  obtain ⟨lf,pl,zl,_⟩ := mem_col.mp luse
  have act (B) (bf : B∈F) : Cycle E X.V q B := retain_cycle
    (show Cycle X.D X.V q B from (mem_filter.mp (sub bf)).2) bf
  have free := PrivateArcEndpoints.graph_free X F
  have cost := ProtectedHeadPayment.two_head_credit hq free (act A af) (act M mf) pm ym ya py w
  change unused E A M w+deposit E A M w p+w y+w (succHead E A y)≤(∑v∈A,w v) at cost
  have bill : score q E X.V w p+unused E A M w+deposit E A M w p ≤
      (∑v∈X.V,w v)+q*(∑v∈H.erase y,w v) := by
    change (score q E X.V w p-(∑v∈X.V,w v))+(∑v∈A,w v)≤
      q*(∑v∈H.erase y,w v)+w y+w (succHead E A y) at credit
    omega
  have go := ProtectedHeadPayment.paid X sub af mf (mem_sdiff.mp pv).2 pm ya ym py w bill z zh L lf pl zl
  have separated := CyclePhaseFork.disjoint_overlaps hq free (act A af) (act M mf) (act L lf)
    ya za py pz (Ne.symm diff) pm ym pl zl
  exact ⟨A,af,p,pv,y,yh,z,zh,M,mf,L,lf,pm,ym,pl,zl,separated,go,
    (ProtectedHeadPayment.test (act A af) (act M mf) pm ym ya py w).2.2.mpr bill⟩

/-- With one least feasible allocation, a paid phase conflict exists, or
the displayed strict deficit is required at every head of a low-margin
exterior row on every member of the family. -/
theorem alternatives {q n} (X : Model q n) (hq : 2≤q) {F w} (sub : F⊆family X)
    (rows : ∀A∈F,∃p,BarrierRow q (graph X.D F) X.V A w p) :
    let E := graph X.D F
    Fork X F w ∨ ∀A∈F,∃p,BarrierRow q E X.V A w p ∧
      ∀y∈outN E A p, q*(∑v∈(outN E A p).erase y,w v)+w y+w (succHead E A y) <
        (score q E X.V w p-(∑v∈X.V,w v))+(∑v∈A,w v) := by
  classical
  intro E
  by_cases fork : Fork X F w
  · exact Or.inl fork
  refine Or.inr ?_
  intro A af
  obtain ⟨p,row⟩ := rows A af
  exact ⟨p,row,fun y yh => lt_of_not_ge (fun paid => fork (of_credit X hq sub af row yh paid))⟩

/-- A uniform unit cycle already supplies a paid conflict whenever the
exterior row margin is 0 or 1 modulo q. Only the cycle weights are fixed. -/
theorem unit_cycle {q n} (X : Model q n) (hq : 2≤q) {F A p w} (sub : F⊆family X)
    (af : A∈F) (row : BarrierRow q (graph X.D F) X.V A w p)
    (units : ∀v∈A,w v=1)
    (residue : ∃j e,e≤1 ∧ score q (graph X.D F) X.V w p-(∑v∈X.V,w v)=q*j+e) : Fork X F w := by
  classical
  let E := graph X.D F
  let H := outN E A p
  obtain ⟨j,e,es,margin⟩ := residue
  have c : Cycle E X.V q A := retain_cycle (show Cycle X.D X.V q A from (mem_filter.mp (sub af)).2) af
  have barrier := row
  obtain ⟨_,two,_,cap,_⟩ := barrier
  change 2≤H.card at two
  rw [margin] at cap
  change q*j+e+(q+1)≤q*H.card at cap
  obtain ⟨y,yh⟩ := card_pos.mp (by omega : 0<H.card)
  have ya := (mem_outN.mp yh).1
  have sy : succHead E A y∈A := by
    have pos : (outN E A y).Nonempty := card_pos.mp (by rw [c.heads y ya]; decide)
    exact (mem_outN.mp (show succHead E A y∈outN E A y by
      simpa only [succHead,dite_eq_left pos] using (outN E A y).min'_mem pos)).1
  have sumA : (∑v∈A,w v)=q+1 := by
    rw [sum_congr rfl (fun v vv => units v vv)]; simp [c.size]
  have sumH : (∑v∈H.erase y,w v)=(H.erase y).card := by
    rw [sum_congr rfl (fun v vv => units v (mem_outN.mp (mem_of_mem_erase vv)).1)]; simp [H]
  have count := card_erase_add_one yh
  have jlt : j<(H.erase y).card := by
    by_contra! large
    have b := Nat.mul_le_mul_left q large
    have id : q*H.card=q*(H.erase y).card+q := by rw [←count,Nat.mul_succ]
    omega
  have mul := Nat.mul_le_mul_left q (show j+1≤(H.erase y).card by omega)
  rw [Nat.mul_succ] at mul
  apply of_credit X hq sub af row yh
  change (score q (graph X.D F) X.V w p-(∑v∈X.V,w v))+(∑v∈A,w v)≤
    q*(∑v∈H.erase y,w v)+w y+w (succHead E A y)
  rw [margin,sumA,sumH,units y ya,units _ sy]
  omega

#print axioms unit_cycle
#print axioms of_credit
#print axioms alternatives
end LeanCH.BR.Closure.NativePaidHeadFork
