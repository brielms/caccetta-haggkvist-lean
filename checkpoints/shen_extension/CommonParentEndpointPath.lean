import checkpoints.shen_extension.CommonParentReplay
import LeanCH.BR.BRFiniteWalk

/-! At q−1 selected heads, covering the inner ball forces a spanning induced path.
The last head is the unique exterior survivor of a legal deletion in the existing
repair graph. A missed inner row instead extends the actual incidence minor.

Entry point: `on_common_parent` takes the hypotheses of `CommonParentHeadRepair.live_run`
and a common parent of the deleted arc endpoints. Its conclusion follows the very
same first head through a legal repair trace. The incidence extension does not
claim payment on the new head. The single-exterior alternative identifies the
remaining unpaid row on the cut carrier. -/
namespace LeanCH.BR.Closure.CommonParentEndpointPath
open Finset BRq2 BRq3 BR45 WeightedSD

/-- Starting in the intersection gives an inner sink of the selected heads. -/
theorem missed {q : ℕ} (hq : 2≤q) {E : CH.Digraph} {U H T : Finset ℕ}
    (free : QFree E U q) (ts : T⊆U) (small : T.card<q) {h} (hh : h∈H) (ht : h∈T) :
    ∃z∈T, z∈BRsub.ballSet E U H (q-2) ∧ ∀v∈T, ¬E z v=true := by
  obtain ⟨z,zt,sink,m,ms,w⟩ := reach_sink_of_card (free.mono_set ts) small.le ht
  exact ⟨z,zt,BRsub.mem_ballSet.mpr ⟨h,hh,mem_ball.mpr ⟨ts zt,m,by omega,w.mono ts⟩⟩,sink⟩

/-- Equality in the size bound forces an induced path with common entrance and dead exit. -/
theorem full_cover {q : ℕ} (hq : 2≤q) {E : CH.Digraph} {U H T : Finset ℕ}
    (free : QFree E U q) (hs : H⊆U) (live : H.Nonempty) (ts : T⊆U) (small : T.card<q)
    (cover : ∀r∈BRsub.ballSet E U H (q-2),∃k∈T,E r k=true) :
    T.card+1=q ∧ Disjoint H T ∧ ∃a∈T,∃p : ShortestSinkPath E T a,
      p.len+2=q ∧ (range (p.len+1)).image p.vertex=T ∧
      (∀i≤p.len,∀j≤p.len, E (p.vertex i) (p.vertex j)=true ↔ j=i+1) ∧
      (∀h∈H,∀k∈T,E h k=true ↔ k=a) ∧
      T\BRsub.ballSet E U H (q-2)={p.vertex p.len} ∧
      p.vertex p.len∉BRsub.ballSet E U H (q-2) ∧
      (∀h∈H,¬E (p.vertex p.len) h=true) ∧
      ∀r∈BRsub.ballSet E U H (q-2),¬E (p.vertex p.len) r=true := by
  classical
  have Hmem {h} (hh : h∈H) : h∈BRsub.ballSet E U H (q-2) :=
    BRsub.mem_ballSet.mpr ⟨h,hh,self_mem_ball (hs hh)⟩
  have dis : Disjoint H T := by
    apply Finset.disjoint_left.mpr
    intro h hh ht
    obtain ⟨z,_,zr,sk⟩ := missed hq free ts small hh ht
    obtain ⟨k,kt,hk⟩ := cover z zr
    exact sk k kt hk
  obtain ⟨r,hr⟩ := live
  obtain ⟨a,at',ra⟩ := cover r (Hmem hr)
  obtain ⟨p⟩ := exists_shortest_sink_path (free.mono_set ts) small.le at'
  have endT := p.mem p.len le_rfl
  have far : p.vertex p.len∉BRsub.ballSet E U H (q-2) := by
    intro near
    obtain ⟨k,kt,e⟩ := cover _ near
    exact p.sink k kt e
  have long {h i} (hh : h∈H) (hi : i≤p.len) (ei : E h (p.vertex i)=true) :
      q-2 < p.len-i+1 := by
    by_contra! le
    exact far (BRsub.mem_ballSet.mpr ⟨h,hh,mem_ball.mpr ⟨ts endT,_,le,
      .step (ts (p.mem i hi)) ei ((p.walk hi le_rfl).mono ts)⟩⟩)
  have zero : E r (p.vertex 0)=true := p.start.symm ▸ ra
  have low := long hr (Nat.zero_le _) zero
  have bound := p.bounded
  have eq : p.len+2=q := by omega
  have cnt : T.card+1=q := by omega
  have onto : (range (p.len+1)).image p.vertex=T := by
    apply eq_of_subset_of_card_le
    · intro x hx
      obtain ⟨i,hi,rfl⟩ := mem_image.mp hx
      exact p.mem i (by have := mem_range.mp hi; omega)
    · rw [card_image_of_injOn (p.injective (free.mono_set ts) small.le),card_range]
      omega
  have first {h k} (hh : h∈H) (kt : k∈T) (hk : E h k=true) : k=a := by
    obtain ⟨i,hi,rfl⟩ := mem_image.mp (onto.symm ▸ kt)
    have ib := mem_range.mp hi
    have := long hh (by omega : i≤p.len) hk
    obtain rfl : i=0 := by omega
    exact p.start
  refine ⟨cnt,dis,a,at',p,eq,onto,?_,?_,?_,far,?_,?_⟩
  · intro i hi j hj
    exact ⟨p.no_chord (free.mono_set ts) small.le hi hj,fun e=> e ▸ p.edge i (by omega)⟩
  · intro h hh k kt
    obtain ⟨b,bt,eb⟩ := cover h (Hmem hh)
    exact ⟨first hh kt,fun ka => (ka.trans (first hh bt eb).symm) ▸ eb⟩
  · ext v
    constructor
    · intro hv
      obtain ⟨vt,miss⟩ := mem_sdiff.mp hv
      obtain ⟨k,hk,rfl⟩ := mem_image.mp (onto.symm ▸ vt)
      have kb := mem_range.mp hk
      apply mem_singleton.mpr
      suffices k=p.len by rw [this]
      by_contra! diff
      apply miss
      apply BRsub.mem_ballSet.mpr
      refine ⟨r,hr,mem_ball.mpr ⟨ts (p.mem _ (by omega)),k-0+1,by omega,?_⟩⟩
      exact .step (ts (p.mem 0 (Nat.zero_le _))) zero ((p.walk (Nat.zero_le _) (by omega)).mono ts)
    · intro hv
      obtain rfl := mem_singleton.mp hv
      exact mem_sdiff.mpr ⟨endT,far⟩
  · intro h hh e
    obtain ⟨b,bt,eb⟩ := cover h (Hmem hh)
    have ha : E h (p.vertex 0)=true := by rw [p.start,←first hh bt eb]; exact eb
    have walk : Walk E U h (p.vertex p.len) (p.len-0+1) :=
      .step (ts (p.mem 0 (Nat.zero_le _))) ha ((p.walk (Nat.zero_le _) le_rfl).mono ts)
    exact free h _ (by omega) (by omega) (walk.snoc (hs hh) e)
  · intro x xr sx
    obtain ⟨k,kt,xk⟩ := cover x xr
    obtain ⟨i,idx,rfl⟩ := mem_image.mp (onto.symm ▸ kt)
    have ib := mem_range.mp idx
    have wu : x∈U := by obtain ⟨_,_,e⟩ := BRsub.mem_ballSet.mp xr; exact (mem_ball.mp e).1
    have trail := (p.walk (show i≤p.len by omega) le_rfl).mono ts
    exact free _ _ (by omega) (show p.len-i+1+1≤q by omega)
      (.step wu sx (.step (ts (p.mem i (by omega))) xk trail))
open Closure.CommonParentReplay in
/-- Realize the exterior deletion in the existing replay and retest the paired rows. -/
theorem replay_one_exterior {q n : ℕ} (hq : 2≤q) {D : CH.Digraph} {U H R : Finset ℕ}
    (free : QFree D U q) (smallRow : SmallerSmallRow q n) (room : U.card+1<n) (hl : H.Nonempty)
    {s : CommonParentReplay.State} (v : CommonParentReplay.Valid q D H R U s) (cap : s.heads.card<q)
    (cover : ∀i∈R,∃k∈s.heads,D i k=true) :
    ∃z∈s.heads, z∉R ∧ ∃t : CommonParentReplay.State, Relation.ReflTransGen (CommonParentReplay.Edge q D H) s t ∧
      t.heads=s.heads ∧ t.weights=s.weights ∧ t.carrier\R={z} ∧ outN D t.carrier z=∅ ∧ CommonParentReplay.Checks q D H R U t ∧
      ∃i∈R, WeightedSD.row q D t.carrier t.weights i≤WeightedSD.mass t.carrier t.weights ∨
        Closure.CommonParentHeadRepair.margin q D t.carrier t.weights i z<0 := by
  classical
  have br : BRsub.ballSet D s.carrier H (q-2)=R := v.same
  obtain ⟨_,_,a,_,p,_,_,_,_,one,_,_,dead⟩ := full_cover hq (free.mono_set v.inside)
    v.keeps hl v.selected cap (br ▸ cover)
  rw [br] at one dead
  let z := p.vertex p.len
  have zt : z∈s.heads\R := by rw [one]; exact mem_singleton_self _
  let X := (s.carrier\R)\s.heads
  have cut : (s.carrier\X)\R={z} := by
    ext i
    rw [← one]
    simp only [X,mem_sdiff]
    constructor
    · tauto
    · exact fun h=>⟨⟨v.selected h.1,by tauto⟩,h.2⟩
  let t : CommonParentReplay.State := ⟨s.carrier\X,s.heads,s.weights⟩
  have path : Relation.ReflTransGen (CommonParentReplay.Edge q D H) s t := by
    by_cases live : X.Nonempty
    · apply Relation.ReflTransGen.single
      apply CommonParentReplay.Edge.cut live
      · rw [v.same]
        exact sdiff_subset
      · exact fun k hk=>mem_sdiff.mpr ⟨v.selected hk,fun e=>(mem_sdiff.mp e).2 hk⟩
    · have empty := not_nonempty_iff_eq_empty.mp live
      have st : t=s := by simp [t,empty]
      exact st ▸ Relation.ReflTransGen.refl
  have out : t.carrier\R={z} := cut
  have facts := replay hq free smallRow room hl v path
  have sink : outN D t.carrier z=∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    have ⟨xu,zx⟩ := mem_outN.mp hx
    by_cases xr : x∈R
    · exact dead x xr zx
    · have e : x=z := mem_singleton.mp (out ▸ mem_sdiff.mpr ⟨xu,xr⟩)
      exact loopfree free (by omega) (v.inside (v.selected (mem_sdiff.mp zt).1)) (e ▸ zx)
  refine ⟨z,(mem_sdiff.mp zt).1,(mem_sdiff.mp zt).2,t,path,rfl,rfl,out,sink,facts,?_⟩
  obtain ⟨i,ir,bill⟩ := facts.2.1
  refine ⟨i,ir,bill.imp_right ?_⟩
  rintro ⟨j,jr,low⟩
  rw [out,mem_singleton] at jr
  exact jr ▸ low
open CommonParentHeadRepair CommonParentReplay

/-- The missed-row alternative records independence. The covered alternative records
the cut and the exact shortfall on its new carrier. -/
def Outcome (q : ℕ) (D : CH.Digraph) (H R : Finset ℕ) (s : CommonParentReplay.State) : Prop :=
    (∃r∈R, (∀k∈s.heads,D r k=false) ∧ ∃k∈outN D s.carrier r, k∉s.heads ∧
      (insert k s.heads).card=q ∧ IndependentHeads D R (insert k s.heads)) ∨
    ∃z∈s.heads, z∉R ∧ ∃t : CommonParentReplay.State, Relation.ReflTransGen (CommonParentReplay.Edge q D H) s t ∧
      t.heads=s.heads ∧ t.weights=s.weights ∧ t.carrier\R={z} ∧ outN D t.carrier z=∅ ∧
      ∃i∈R, ((q:ℚ)-1)*(WeightedSD.row q D t.carrier t.weights i-mass t.carrier t.weights)
        < mass t.carrier t.weights-t.weights z

/-- Test a terminal repair on its actual weights and selected heads. -/
theorem endpoint_fork {q n : ℕ} (hq : 2≤q) {D : CH.Digraph} {U H R : Finset ℕ}
    (free : QFree D U q) (small : SmallerSmallRow q n) (room : U.card+1<n)
    (hl : H.Nonempty) {s : CommonParentReplay.State} (valid : CommonParentReplay.Valid q D H R U s)
    (count : s.heads.card+1=q) (rank : IndependentHeads D R s.heads)
    (live : ∀r∈R,(outN D s.carrier r).Nonempty) :
    Outcome q D H R s := by
  classical
  by_cases cover : ∀r∈R,∃k∈s.heads,D r k=true
  · right
    obtain ⟨z,zt,zr,t,path,heads,weights,out,dead,facts,i,ir,fail⟩ :=
      replay_one_exterior hq free small room hl valid (by omega) cover
    refine ⟨z,zt,zr,t,path,heads,weights,out,dead,i,ir,?_⟩
    have zu := facts.1.selected (heads.symm ▸ zt)
    have iu : i∈t.carrier := by
      have ball := facts.1.same
      rw [←ball] at ir
      obtain ⟨_,_,near⟩ := BRsub.mem_ballSet.mp ir
      exact (mem_ball.mp near).1
    have iz : i≠z := fun e=>zr (e ▸ ir)
    have sum := sum_erase_add _ t.weights zu
    have rest : 0<mass (t.carrier.erase z) t.weights :=
      (single_le_sum (fun j hj=>(facts.1.positive j (mem_of_mem_erase hj)).le)
        (mem_erase.mpr ⟨iz,iu⟩)).trans_lt' (facts.1.positive i iu)
    change mass (t.carrier.erase z) t.weights+t.weights z=mass t.carrier t.weights at sum
    rcases fail with low|bill
    · have sign := mul_nonpos_of_nonneg_of_nonpos
          (sub_nonneg.mpr (show (1:ℚ)≤q by exact_mod_cast (by omega : 1≤q)))
          (sub_nonpos.mpr low)
      linarith
    · unfold margin at bill
      have rz : WeightedSD.row q D t.carrier t.weights z=t.weights z := by
        simp [WeightedSD.row,outW_eq_mass,dead,mass]
      rw [rz] at bill
      linarith
  · left
    push Not at cover
    obtain ⟨r,rr,miss⟩ := cover
    obtain ⟨k,kk⟩ := live r rr
    have hit := (mem_outN.mp kk).2
    have fresh : k∉s.heads := fun tk=>by simpa [hit] using miss k tk
    refine ⟨r,rr,fun k hk=>by simpa using miss k hk,k,kk,fresh,?_,?_⟩
    · rw [card_insert_of_notMem fresh,count]
    · intro f zero x xt
      have fk : f k=0 := by
        have e := zero r rr
        rw [sum_insert fresh,ite_eq_left hit] at e
        have rest : (∑a∈s.heads,if D r a=true then f a else 0)=0 :=
          sum_eq_zero fun a ha=>by simp [miss a ha]
        linarith
      have old := rank f (by
        intro y yr
        have e := zero y yr
        rw [sum_insert fresh,fk] at e
        simpa using e)
      rcases mem_insert.mp xt with eq|inT
      · exact eq ▸ fk
      · exact old x inT
/-- Apply the fork to the terminal weights and labels returned by live_run.
The common parent j is an explicit hypothesis on the selected arc b → a. -/
theorem on_common_parent {q D V} (hq : 3≤q) (free : QFree D V q)
    (small : SmallerSmallRow q V.card) (w : ℕ→ℚ) (pos : ∀x∈V,0<w x)
    {c : ℚ} (high : mass V w<c) (flat : ∀x∈V,WeightedSD.row q D V w x=c)
    {a b : V} (ba : D b a=true)
    (two : ∀r∈V,∀j∈V,r≠j → D r b=true → D j b=true → w r+w j+q*w b<mass V w)
    {j : ℕ} (ju : j∈(V.erase a.val).erase b.val) (ja : D j a=true) (jb : D j b=true) :
    let U := (V.erase a.val).erase b.val
    let H := outN D U a
    let R := BRsub.ballSet D U H (q-2)
    ∃i∈R, (outN D U i).Nonempty ∧ ∀k∈outN D U i,
      ∃T v, k∈T ∧ T.card+1=q ∧
        Relation.ReflTransGen (CommonParentHeadRepair.Step q D U H) ({k},w) (T,v) ∧
        Outcome q D H R ⟨U,T,v⟩ := by
  intro U H R
  have h2 : 2≤q := by omega
  obtain ⟨i,ir,_,_,_,repair⟩ := live_run hq free small w pos high flat ba two
  obtain ⟨_,_,budget,live,go⟩ := repair j ju ja jb
  refine ⟨i,ir,live,?_⟩
  intro k kk
  obtain ⟨l,z,T,v,_,_,_,first,path,_,cnt⟩ := go k kk
  have rank := trace_minor ir (mem_outN.mp kk).2 first path
  have kept := (avoiding_minor first path).1
  have steps := path.head first
  refine ⟨T,v,kept,cnt,steps,?_⟩
  have us : U⊆V := (erase_subset _ _).trans (erase_subset _ _)
  have distinct : b.val≠a.val := fun eq=>loopfree free (by omega) a.property (eq ▸ ba)
  have room : U.card+1<V.card := by
    have x := card_erase_add_one a.property
    have y := card_erase_add_one (mem_erase.mpr ⟨distinct,b.property⟩ : b.val∈V.erase a.val)
    dsimp [U]; omega
  have heavy := (PairedArcAudit.rows_iff h2 free small w pos high flat ba).1
  obtain ⟨h,hh,_⟩ := BRsub.mem_ballSet.mp ir
  let st := fun p : Finset ℕ × (ℕ→ℚ) => CommonParentReplay.State.mk U p.1 p.2
  have start : CommonParentReplay.Valid q D H R U (st ({k},w)) :=
    ⟨Subset.rfl,outN_subset,singleton_subset_iff.mpr (mem_outN.mp kk).1,
      fun x hx=>pos _ (us hx),heavy,rfl⟩
  have edges : Relation.ReflTransGen (CommonParentReplay.Edge q D H) (st ({k},w)) (st (T,v)) :=
    steps.lift st (fun _ _ e=> CommonParentReplay.Edge.repair e)
  have valid := (CommonParentReplay.replay h2 (free.mono_set us) small room ⟨h,hh⟩ start edges).1
  apply endpoint_fork h2 (free.mono_set us) small room ⟨h,hh⟩ valid cnt rank
  intro r rr
  apply nonempty_iff_ne_empty.mpr
  intro em
  have bound := budget r rr
  change c-mass V w+w j<(q:ℚ)*mass (outN D U r) w at bound
  rw [em,show mass ∅ w=0 by simp [mass],mul_zero] at bound
  linarith [pos j (us ju)]

/-- On the original carrier with its flat row law, the same exterior label
carries a heavy bank of vertices missing every selected head. -/
theorem exterior_bank {q : ℕ} (hq : 2≤q) {D : CH.Digraph} {V U H T : Finset ℕ}
    (free : QFree D V q) (us : U⊆V) (hs : H⊆U) (hl : H.Nonempty)
    (ts : T⊆U) (small : T.card<q)
    (cover : ∀i∈BRsub.ballSet D U H (q-2),∃k∈T,D i k=true)
    {z : ℕ} (zt : z∈T\BRsub.ballSet D U H (q-2))
    (w : ℕ→ℚ) (pos : ∀x∈V,0<w x) {c : ℚ} (row : WeightedSD.row q D V w z=c) :
    let B := V.filter (fun x=>∀k∈T,D x k=false)
    insert z (outN D V z)⊆B ∧ Disjoint B (BRsub.ballSet D U H (q-2)) ∧
      c+((q:ℚ)-1)*w z ≤ q*mass B w := by
  classical
  intro B
  obtain ⟨_,_,a,_,p,eq,onto,_,_,one,_,_,_⟩ :=
    full_cover hq (free.mono_set us) hs hl ts small cover
  obtain rfl := mem_singleton.mp (one ▸ zt)
  have zv := us (ts (p.mem p.len le_rfl))
  have inBank : insert (p.vertex p.len) (outN D V (p.vertex p.len))⊆B := by
    intro x hx
    rcases mem_insert.mp hx with rfl | arc
    · exact mem_filter.mpr ⟨zv,fun k kt=>Bool.eq_false_iff.mpr (p.sink k kt)⟩
    · have ⟨xv,zx⟩ := mem_outN.mp arc
      refine mem_filter.mpr ⟨xv,?_⟩
      intro k kt
      apply Bool.eq_false_iff.mpr
      intro xk
      obtain ⟨i,idx,rfl⟩ := mem_image.mp (onto.symm ▸ kt)
      have ib := mem_range.mp idx
      have trail := (p.walk (show i≤p.len by omega) le_rfl).mono (ts.trans us)
      exact free _ _ (by omega) (show p.len-i+1+1≤q by omega)
        (.step xv zx (.step ((ts.trans us) (p.mem i (by omega))) xk trail))
  refine ⟨inBank,?_,?_⟩
  · apply Finset.disjoint_left.mpr
    intro r rb rr
    obtain ⟨k,kt,rk⟩ := cover r rr
    exact Bool.noConfusion (((mem_filter.mp rb).2 k kt).symm.trans rk)
  · have diff : p.vertex p.len∉outN D V (p.vertex p.len) :=
      fun e=>loopfree free (by omega) zv (mem_outN.mp e).2
    have bound : mass (insert (p.vertex p.len) (outN D V (p.vertex p.len))) w ≤ mass B w :=
      sum_le_sum_of_subset_of_nonneg inBank (fun i bi _=>(pos i (mem_filter.mp bi).1).le)
    rw [WeightedSD.row,outW_eq_mass] at row
    unfold mass at bound
    rw [sum_insert diff] at bound
    change w (p.vertex p.len)+mass (outN D V (p.vertex p.len)) w ≤ mass B w at bound
    linarith only [row,mul_le_mul_of_nonneg_left bound (Nat.cast_nonneg q : (0:ℚ)≤q)]

#print axioms exterior_bank
#print axioms on_common_parent
#print axioms endpoint_fork
#print axioms replay_one_exterior
#print axioms missed
#print axioms full_cover
end LeanCH.BR.Closure.CommonParentEndpointPath
