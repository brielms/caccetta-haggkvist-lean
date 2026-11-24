import checkpoints.shen_extension.BypassRepair
import checkpoints.shen_extension.RootFamilyEntry
import LeanCH.BR.CH.Side.ScFinsetEnumeration

namespace LeanCH.BR.BypassDegreeDescent
open Finset BRq2 BRq3 BR45 CHRuleCatalog BypassRepair

/-- A paid host carries its physical enumeration to a literal counterexample
    child. Its own cutoff can decrease after the change in quota. -/
theorem host_child (p : Input) {t : ℕ} {E : CH.Digraph} {U : Finset ℕ}
    (pos : 0<t) (hq : 1≤cutoff p) (live : U.Nonempty) (size : U.card≤cutoff p*t)
    (free : QFree E U (cutoff p)) (deg : ∀v∈U,t≤(outN E U v).card) :
    ∃ c : Input, ∃ e : ℕ→ℕ, Child p c ∧ c.s=t ∧ c.n=U.card ∧ cutoff c≤cutoff p ∧
      (∀i<c.n,e i∈U) ∧ (∀v∈U,∃i<c.n,e i=v) ∧ (∀i<c.n,∀j<c.n,e i=e j → i=j) ∧
      ∀i<c.n,∀j<c.n,c.D i j=E (e i) (e j) := by
  classical
  have sub : U⊆range (U.sup id + 1) := fun v hv => mem_range.mpr
    (Nat.lt_succ_of_le (le_sup (f:=id) hv))
  obtain ⟨e,_,inj,into,onto⟩ := CH.Side.sc_finset_enumeration sub
  let c : Input := ⟨U.card,t,fun i j=>E (e i) (e j)⟩
  have cap : cutoff c≤cutoff p := by
    have lim : U.card+t-1<(cutoff p+1)*t := by rw [Nat.add_mul,Nat.one_mul]; omega
    exact Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul pos).mpr lim)
  have lift {i j k} (w : Walk c.D (range c.n) i j k) : Walk E U (e i) (e j) k := by
    induction w with
    | refl => exact .refl _
    | step inside hit _ ih => exact .step (into _ (mem_range.mp inside)) hit ih
  have safe : QFree c.D (range c.n) (cutoff c) :=
    fun _ _ hp hlen w => free _ _ hp (hlen.trans cap) (lift w)
  have missing := ShenReachTransition.no_cycle_of_free safe
  have loopless : CH.Loopless c.D c.n := by
    intro i hi
    change E (e i) (e i)=false
    exact Bool.eq_false_iff.mpr (loopfree free hq (into i hi))
  have minimum : CH.MinOutdegreeAtLeast c.D c.n c.s := by
    intro i hi
    let H := outN c.D (range c.n) i
    have covers : outN E U (e i)⊆H.image e := by
      intro z hz
      obtain ⟨j,hj,rfl⟩ := onto z (outN_subset hz)
      exact mem_image.mpr ⟨j,mem_outN.mpr ⟨mem_range.mpr hj,(mem_outN.mp hz).2⟩,rfl⟩
    obtain ⟨T,ts,count⟩ := exists_subset_card_eq
      ((deg _ (into i hi)).trans ((card_le_card covers).trans card_image_le))
    refine ⟨T.toList,by simpa using count,T.nodup_toList,?_⟩
    intro j hj
    obtain ⟨jv,hit⟩ := mem_outN.mp (ts (mem_toList.mp hj))
    exact ⟨mem_range.mp jv,hit⟩
  exact ⟨c,e,⟨card_pos.mpr live,pos,loopless,minimum,fun hit=>(missing hit).elim⟩,
    rfl,rfl,cap,into,onto,fun i hi j hj=>inj i j hi hj,fun _ _ _ _=>rfl⟩

/-- First minimize the cutoff among reachable bad descendants, then minimize
    the degree at that cutoff. A reduction of the cutoff may raise degree. -/
private theorem terminal (p : Input) (bp : Bad p) :
    ∃c : Input, Relation.ReflTransGen Child p c ∧ Bad c ∧
      ∀d : Input, Child c d → cutoff c≤cutoff d ∧ (cutoff c=cutoff d → c.s≤d.s) := by
  classical
  let Q := fun k => ∃c : Input, Relation.ReflTransGen Child p c ∧ Bad c ∧ cutoff c=k
  have nonempty : ∃k,Q k := ⟨_,p,.refl,bp,rfl⟩
  let k := Nat.find nonempty
  obtain ⟨first,via,bad,atK⟩ : Q k := Nat.find_spec nonempty
  let R := fun r => ∃c : Input, Relation.ReflTransGen Child p c ∧ Bad c ∧ cutoff c=k ∧ c.s=r
  have degrees : ∃r,R r := ⟨_,first,via,bad,atK,rfl⟩
  obtain ⟨c,path,bc,ck,cr⟩ := Nat.find_spec degrees
  refine ⟨c,path,bc,fun d edge => ⟨?_,?_⟩⟩
  · rw [ck]
    exact Nat.find_min' nonempty ⟨d,path.tail edge,bad_child bc edge,rfl⟩
  · intro same
    rw [cr]
    exact Nat.find_min' degrees ⟨d,path.tail edge,bad_child bc edge,same.symm.trans ck,rfl⟩

/-- The cutoff and degree comparison holds for every legal child of this
particular selected input. -/
structure MinimalChild (c : Input) : Prop where
  compare : ∀ d : Input, Child c d → cutoff c≤cutoff d ∧ (cutoff c=cutoff d → c.s≤d.s)

/-- Keep the comparison that selected the terminal input, together with
the original root and its certified repair chain. -/
theorem from_root_minimal (remaining : ∀root : Input,Bad root → ∀c : Input,
    Relation.ReflTransGen Child root c → Bad c → ReducedCutoff c.n c.s →
    ¬OneLossCutoffDescent.Window c.n c.s (cutoff c) → NoHost (cutoff c) (c.s-1) →
    MinimalChild c → CH.HasDirectedCycleAtMost c.D c.n (cutoff c)) : CH.CaccettaHaggkvistConjecture := by
  apply RootFamilyEntry.from_root
  intro root original p parentPath bp _ _
  exfalso
  obtain ⟨c,path,bc,least⟩ := terminal p bp
  obtain ⟨three,six,reg⟩ := remaining_from_run c bc
  have window : ¬OneLossCutoffDescent.Window c.n c.s (cutoff c) := by
    intro w
    obtain ⟨d,edge,_,_,_,less⟩ := OneLossCutoffDescent.descends bc (by omega) w
    have := (least d edge).1
    omega
  have parity : cutoff c%2=1 ∨ cutoff c<c.s := by
    by_contra h
    push Not at h
    obtain ⟨d,edge,_,_,_,_,less⟩ := SATBoundaryPilot.even_bad_descends bc
      (k:=cutoff c/2) (by omega) h.2 (by omega)
    exact (Nat.not_lt_of_ge (least d edge).1) less
  have upper : cutoff c≤2*c.s-7 := by
    obtain ⟨_,_,_,_⟩|⟨_,_⟩ := reg <;> omega
  have none : NoHost (cutoff c) (c.s-1) := by
    intro E U live room free deg
    obtain ⟨d,_,edge,dr,_,limit,_⟩ := host_child c (by omega : 0<c.s-1) (by omega) live room free deg
    obtain ⟨low,atSame⟩ := least d edge
    have := atSame (Nat.le_antisymm low limit)
    omega
  exact bc.missing (remaining root original c (parentPath.trans path) bc ⟨upper,parity⟩ window none ⟨least⟩)

/-- Original entry for consumers that use only the one-degree host exclusion. -/
theorem from_root (remaining : ∀root : Input,Bad root → ∀c : Input,
    Relation.ReflTransGen Child root c → Bad c → ReducedCutoff c.n c.s →
    ¬OneLossCutoffDescent.Window c.n c.s (cutoff c) → NoHost (cutoff c) (c.s-1) →
    CH.HasDirectedCycleAtMost c.D c.n (cutoff c)) : CH.CaccettaHaggkvistConjecture :=
  from_root_minimal fun root original c path bc reduced loss none _ =>
    remaining root original c path bc reduced loss none

#print axioms host_child
#print axioms from_root_minimal
#print axioms from_root
end LeanCH.BR.BypassDegreeDescent
