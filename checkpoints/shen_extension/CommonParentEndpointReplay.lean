import checkpoints.shen_extension.CommonParentEndpointPath

namespace LeanCH.BR.Closure.CommonParentEndpointReplay
open Finset BRq2 BRq3 BR45 WeightedSD CommonParentReplay CommonParentHeadRepair

/-- Keep the original inner ball, every selected head and a specified fresh head.
The reflexive case occurs precisely when there is nothing outside this union. -/
theorem retain_fresh {q n D H R U} (hq : 2≤q) (free : QFree D U q)
    (small : SmallerSmallRow q n) (room : U.card+1<n) (hl : H.Nonempty)
    {s : CommonParentReplay.State} (valid : CommonParentReplay.Valid q D H R U s) {k} (ku : k∈s.carrier) :
    let W := R ∪ insert k s.heads
    let t : CommonParentReplay.State := ⟨W,s.heads,s.weights⟩
    Relation.ReflTransGen (CommonParentReplay.Edge q D H) s t ∧ CommonParentReplay.Checks q D H R U t ∧
      (W=s.carrier ∨ (W⊂s.carrier ∧ CommonParentReplay.Edge q D H s t)) := by
  classical
  intro W t
  have rs : R⊆s.carrier := by
    rw [←valid.same]
    exact BRsub.ballSet_subset
  have sub : W⊆s.carrier := union_subset rs (insert_subset ku valid.selected)
  have keep : s.heads⊆W := fun x hx=>mem_union_right _ (mem_insert_of_mem hx)
  have alternative : W=s.carrier ∨ (W⊂s.carrier ∧ CommonParentReplay.Edge q D H s t) := by
    by_cases same : W=s.carrier
    · exact Or.inl same
    · have strict := Finset.ssubset_iff_subset_ne.mpr ⟨sub,same⟩
      let X := s.carrier\W
      have live : X.Nonempty := sdiff_nonempty.mpr (fun back=>same (Subset.antisymm sub back))
      have cut : s.carrier\X=W := by
        ext x
        simp only [X,mem_sdiff]
        exact ⟨fun ⟨xu,off⟩=>by_contra fun xw=>off ⟨xu,xw⟩,
          fun xw=>⟨sub xw,fun off=>off.2 xw⟩⟩
      have outer : X⊆s.carrier\CommonParentReplay.ball q D H s.carrier := by
        rw [valid.same]
        exact fun x hx=>mem_sdiff.mpr ⟨(mem_sdiff.mp hx).1, fun xr=>(mem_sdiff.mp hx).2 (mem_union_left _ xr)⟩
      have e := @CommonParentReplay.Edge.cut q D H s.carrier s.heads s.weights X live outer (cut.symm ▸ keep)
      rw [cut] at e
      exact Or.inr ⟨strict,e⟩
  have path : Relation.ReflTransGen (CommonParentReplay.Edge q D H) s t := by
    rcases alternative with same|⟨_,e⟩
    · have eq : t=s := by
        change CommonParentReplay.State.mk W s.heads s.weights = s
        rw [same]
      exact eq ▸ Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.single e
  exact ⟨path,CommonParentReplay.replay hq free small room hl valid path,alternative⟩

/-- On a sink after deletion, its original heads either left the original
carrier before the trace, or were actually removed by this cut. Only the
latter may be charged at the repaired prices. -/
theorem discarded_mass {q D V U W z} {original repaired : ℕ→ℚ}
    (pos : ∀i∈V,0<original i) (us : U⊆V)
    (inc : ∀i∈U,original i≤repaired i) (dead : outN D W z=∅) :
    WeightedSD.row q D V original z-original z ≤
      (q:ℚ)*(mass (U\W) repaired + mass (outN D V z\U) original) := by
  classical
  let A := outN D V z
  have sub : A∩U⊆U\W := by
    intro x hx
    have ⟨xa,xu⟩ := mem_inter.mp hx
    refine mem_sdiff.mpr ⟨xu,fun xw=>?_⟩
    have h : x∈outN D W z := mem_outN.mpr ⟨xw,(mem_outN.mp xa).2⟩
    simp [dead] at h
  have parts : mass (A∩U) original+mass (A\U) original=mass A original := by
    classical
    unfold mass
    exact sum_inter_add_sum_sdiff _ _ _
  have charge : mass (A∩U) original≤mass (U\W) repaired :=
    (sum_le_sum (fun x hx=>inc x (mem_inter.mp hx).2)).trans
      (sum_le_sum_of_subset_of_nonneg sub (fun x hx _=>
        (pos x (us (mem_sdiff.mp hx).1)).le.trans (inc x (mem_sdiff.mp hx).1)))
  rw [WeightedSD.row,outW_eq_mass,add_sub_cancel_left]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg q)
  change mass A original ≤ _
  rw [←parts]
  linarith only [charge]

theorem weights_grow {q D U H} {p t : Finset ℕ × (ℕ→ℚ)}
    (trace : Relation.ReflTransGen (CommonParentHeadRepair.Step q D U H) p t) :
    ∀i∈U,p.2 i≤t.2 i := by
  induction trace with
  | refl => exact fun _ _=>le_rfl
  | tail _ edge ih => exact fun i hi=>(ih i hi).trans (edge.1 i hi)

/-- Both outcomes retain the actual terminal head set and repaired prices.
In the missed case the fresh head is retained as a vertex without declaring it paid. -/
def Fork (q : ℕ) (D : CH.Digraph) (V U H R T : Finset ℕ) (w v : ℕ→ℚ) : Prop :=
  (∃r∈R,(∀a∈T,D r a=false) ∧ ∃k∈outN D U r,k∉T ∧
    (insert k T).card=q ∧ IndependentHeads D R (insert k T) ∧
    let W := R ∪ insert k T
    let s : CommonParentReplay.State := ⟨U,T,v⟩
    let t : CommonParentReplay.State := ⟨W,T,v⟩
    Relation.ReflTransGen (CommonParentReplay.Edge q D H) s t ∧
      CommonParentReplay.Checks q D H R U t ∧
      (W=U ∨ (W⊂U ∧ CommonParentReplay.Edge q D H s t))) ∨
  ((∀r∈R,∃k∈T,D r k=true) ∧ ∃z∈T,z∉R ∧ ∃t : CommonParentReplay.State,
    Relation.ReflTransGen (CommonParentReplay.Edge q D H) ⟨U,T,v⟩ t ∧
    t.heads=T ∧ t.weights=v ∧ t.carrier\R={z} ∧ outN D t.carrier z=∅ ∧
    (∃i∈R,((q:ℚ)-1)*(WeightedSD.row q D t.carrier t.weights i-mass t.carrier t.weights)
      < mass t.carrier t.weights-t.weights z) ∧
    WeightedSD.row q D V w z-w z ≤ (q:ℚ)*(mass (U\t.carrier) v + mass (outN D V z\U) w) ∧
    (∃a∈T,∃p : ShortestSinkPath D T a,p.len+2=q ∧ p.vertex p.len=z ∧
      (range (p.len+1)).image p.vertex=T ∧
      (∀i≤p.len,∀j≤p.len,D (p.vertex i) (p.vertex j)=true ↔ j=i+1) ∧
      ∀h∈H,∀k∈T,D h k=true ↔ k=a) ∧
    let B := V.filter (fun x=>∀k∈T,D x k=false)
    insert z (outN D V z)⊆B ∧ Disjoint B R ∧
      WeightedSD.row q D V w z+((q:ℚ)-1)*w z≤q*mass B w)

private theorem fresh_independent {D R T r k} (old : IndependentHeads D R T) (rr : r∈R)
    (miss : ∀a∈T,D r a=false) (hit : D r k=true) (fresh : k∉T) :
    IndependentHeads D R (insert k T) := by
  classical
  intro f zero x xt
  have fk : f k=0 := by
    have e := zero r rr
    rw [sum_insert fresh,ite_eq_left hit] at e
    have rest : (∑a∈T,if D r a=true then f a else 0)=0 :=
      sum_eq_zero fun a ha=>by simp [miss a ha]
    linarith
  have onOld := old f (by
    intro y yr
    have e := zero y yr
    rw [sum_insert fresh,fk] at e
    simpa using e)
  rcases mem_insert.mp xt with eq|inside
  · exact eq ▸ fk
  · exact onOld x inside

/-- Evaluate the endpoint on a supplied repair trace. No existential source is selected again. -/
theorem on_trace {q n D V U H i k l w z T v} (hq : 2≤q) (free : QFree D V q)
    (us : U⊆V) (small : SmallerSmallRow q n) (room : U.card+1<n)
    (hs : H⊆U) (hl : H.Nonempty) (pos : ∀x∈V,0<w x) (heavy : mass U w<q*mass H w)
    (ir : i∈BRsub.ballSet D U H (q-2)) (kk : k∈outN D U i)
    (first : CommonParentHeadRepair.Step q D U H ({k},w) (insert l {k},z))
    (path : Relation.ReflTransGen (CommonParentHeadRepair.Step q D U H) (insert l {k},z) (T,v))
    (count : T.card+1=q) (live : ∀r∈BRsub.ballSet D U H (q-2),(outN D U r).Nonempty) :
    Fork q D V U H (BRsub.ballSet D U H (q-2)) T w v := by
  classical
  let R := BRsub.ballSet D U H (q-2)
  let st := fun p : Finset ℕ × (ℕ→ℚ) => CommonParentReplay.State.mk U p.1 p.2
  have start : CommonParentReplay.Valid q D H R U (st ({k},w)) :=
    ⟨Subset.rfl,hs,singleton_subset_iff.mpr (mem_outN.mp kk).1,fun x xu=>pos x (us xu),heavy,rfl⟩
  have steps := path.head first
  have edges := steps.lift st (fun _ _ e=>CommonParentReplay.Edge.repair e)
  have valid := (CommonParentReplay.replay hq (free.mono_set us) small room hl start edges).1
  have rank := trace_minor ir (mem_outN.mp kk).2 first path
  by_cases cover : ∀r∈R,∃a∈T,D r a=true
  · right
    have outcome := CommonParentEndpointPath.endpoint_fork hq (free.mono_set us) small room hl valid count rank live
    rcases outcome with ⟨r,rr,miss,_⟩|⟨last,lt,far,t,walk,heads,prices,one,dead,bill⟩
    · obtain ⟨a,at',hit⟩ := cover r rr
      exact False.elim (Bool.noConfusion ((miss a at').symm.trans hit))
    · refine ⟨cover,last,lt,far,t,walk,heads,prices,one,dead,bill,?_,?_,?_⟩
      · exact discarded_mass pos us (weights_grow steps) dead
      · obtain ⟨_,_,a,at',p,len,onto,induced,entrance,single,_,_⟩ :=
          CommonParentEndpointPath.full_cover hq (free.mono_set us) hs hl (show T⊆U from valid.selected)
            (by omega : T.card<q) cover
        have lastEq : last=p.vertex p.len := mem_singleton.mp (single ▸ mem_sdiff.mpr ⟨lt,far⟩)
        exact ⟨a,at',p,len,lastEq.symm,onto,induced,entrance⟩
      · exact CommonParentEndpointPath.exterior_bank hq free us hs hl (show T⊆U from valid.selected) (by omega : T.card<q) cover
          (mem_sdiff.mpr ⟨lt,far⟩) w pos rfl
  · left
    push Not at cover
    obtain ⟨r,rr,off⟩ := cover
    obtain ⟨fresh,arc⟩ := live r rr
    have hit := (mem_outN.mp arc).2
    have misses : ∀a∈T,D r a=false := fun a ha=>by simpa using off a ha
    have newHead : fresh∉T := fun e=>Bool.noConfusion ((misses fresh e).symm.trans hit)
    refine ⟨r,rr,misses,fresh,arc,newHead,?_,fresh_independent rank rr misses hit newHead,?_⟩
    · rw [card_insert_of_notMem newHead,count]
    · exact retain_fresh hq (free.mono_set us) small room hl valid (mem_outN.mp arc).1

/-- Adapter for the very inner row, first head and common parent of live_run. -/
theorem selected {q D V} (hq : 3≤q) (free : QFree D V q) (small : SmallerSmallRow q V.card)
    (w : ℕ→ℚ) (pos : ∀x∈V,0<w x) {c : ℚ} (high : mass V w<c)
    (flat : ∀x∈V,WeightedSD.row q D V w x=c) {a b : V} (ba : D b a=true)
    {j i k l : ℕ} {z : ℕ→ℚ} {T : Finset ℕ} {v : ℕ→ℚ} :
    let U := (V.erase a.val).erase b.val
    let H := outN D U a
    let R := BRsub.ballSet D U H (q-2)
    j∈U → i∈R → k∈outN D U i →
    (∀r∈R,c-mass V w+w j<(q:ℚ)*mass (outN D U r) w) →
    CommonParentHeadRepair.Step q D U H ({k},w) (insert l {k},z) →
    Relation.ReflTransGen (CommonParentHeadRepair.Step q D U H) (insert l {k},z) (T,v) →
    T.card+1=q → Fork q D V U H R T w v := by
  intro U H R ju ir kk budget first path count
  have h2 : 2≤q := by omega
  have us : U⊆V := (erase_subset _ _).trans (erase_subset _ _)
  have distinct : b.val≠a.val := fun eq=>loopfree free (by omega) a.property (eq ▸ ba)
  have room : U.card+1<V.card := by
    have ra := card_erase_add_one a.property
    have rb := card_erase_add_one (mem_erase.mpr ⟨distinct,b.property⟩ : b.val∈V.erase a.val)
    dsimp [U]; omega
  obtain ⟨h,hh,_⟩ := BRsub.mem_ballSet.mp ir
  apply on_trace h2 free us small room outN_subset ⟨h,hh⟩ pos
    (PairedArcAudit.rows_iff h2 free small w pos high flat ba).1 ir kk first path count
  intro r rr
  apply nonempty_iff_ne_empty.mpr
  intro empty
  have bound := budget r rr
  rw [empty,show mass ∅ w=0 by simp [mass],mul_zero] at bound
  linarith [pos j (us ju)]

#print axioms selected

#print axioms retain_fresh
#print axioms discarded_mass
#print axioms on_trace

end LeanCH.BR.Closure.CommonParentEndpointReplay
