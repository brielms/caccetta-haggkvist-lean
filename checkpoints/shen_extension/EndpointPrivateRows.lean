import checkpoints.shen_extension.CommonParentEndpointReplay

namespace LeanCH.BR.Closure.EndpointPrivateRows
open Finset BRq2 BRq3 BR45 WeightedSD CommonParentHeadRepair

def Covers (E : CH.Digraph) (R S : Finset ℕ) : Prop :=
  ∀r∈R,∃k∈S,E r k=true

/-- The layer is measured on the original carrier, independently of which column is removed. -/
private noncomputable def depth (E : CH.Digraph) (U H : Finset ℕ) (x : ℕ) : ℕ := by
  classical
  exact if h : ∃d,x∈BRsub.ballSet E U H d then Nat.find h else 0

private theorem cover_layers {q E U H T} (hq : 2≤q) (free : QFree E U q)
    (hs : H⊆U) (hl : H.Nonempty) (ts : T⊆U) (size : T.card<q)
    (cov : Covers E (BRsub.ballSet E U H (q-2)) T) :
    Set.InjOn (depth E U H) (↑T : Set ℕ) ∧
    (∀x∈T,1≤depth E U H x ∧ depth E U H x<q) ∧
    ∀d,1≤d → d<q → ∃x∈T,depth E U H x=d := by
  classical
  obtain ⟨_,_,a,ha,p,len,onto,_,entry,_,far,_,_⟩ :=
    CommonParentEndpointPath.full_cover hq free hs hl ts size cov
  obtain ⟨h,hh⟩ := hl
  have first : E h (p.vertex 0)=true := p.start.symm ▸ (entry h hh a ha).2 rfl
  have atIndex (i) (hi : i≤p.len) : depth E U H (p.vertex i)=i+1 := by
    have near : p.vertex i∈BRsub.ballSet E U H (i+1) := by
      refine BRsub.mem_ballSet.mpr ⟨h,hh,mem_ball.mpr ⟨ts (p.mem i hi),i-0+1,by omega,?_⟩⟩
      exact .step (ts (p.mem 0 (Nat.zero_le _))) first ((p.walk (Nat.zero_le i) hi).mono ts)
    have ex : ∃d,p.vertex i∈BRsub.ballSet E U H d := ⟨_,near⟩
    rw [depth,dite_eq_left ex]
    apply Nat.le_antisymm (Nat.find_min' ex near)
    by_contra! low
    obtain ⟨u,uh,reach⟩ := BRsub.mem_ballSet.mp (Nat.find_spec ex)
    obtain ⟨_,k,bound,w⟩ := mem_ball.mp reach
    exact far (BRsub.mem_ballSet.mpr ⟨u,uh,mem_ball.mpr ⟨ts (p.mem _ le_rfl),_,by omega,
      w.append ((p.walk hi le_rfl).mono ts)⟩⟩)
  have idx (x) (xt : x∈T) : ∃i,i≤p.len ∧ p.vertex i=x := by
    obtain ⟨i,hi,e⟩ := mem_image.mp (onto.symm ▸ xt)
    exact ⟨i,by have := mem_range.mp hi; omega,e⟩
  refine ⟨?_,?_,?_⟩
  · intro x hx y hy eq
    obtain ⟨i,hi,rfl⟩ := idx x hx
    obtain ⟨j,hj,rfl⟩ := idx y hy
    rw [atIndex i hi,atIndex j hj] at eq
    exact congrArg p.vertex (by omega)
  · intro x hx
    obtain ⟨i,hi,rfl⟩ := idx x hx
    rw [atIndex i hi]; omega
  · intro d dp dq
    have di : d-1≤p.len := by omega
    exact ⟨_,p.mem _ di,(atIndex _ di).trans (by omega)⟩

/-- At most two of q columns can individually be removed while still covering the inner rows. -/
theorem removable_bound {q E U H S} (hq : 2≤q) (free : QFree E U q)
    (hs : H⊆U) (hl : H.Nonempty) (ss : S⊆U) (size : S.card=q) :
    ∃B⊆S,B.card≤2 ∧ ∀a∈S,Covers E (BRsub.ballSet E U H (q-2)) (S.erase a) → a∈B := by
  classical
  let R := BRsub.ballSet E U H (q-2)
  have layers (a) (ha : a∈S) (c : Covers E R (S.erase a)) :=
    cover_layers hq free hs hl ((erase_subset a S).trans ss)
      (show (S.erase a).card<q by rw [card_erase_of_mem ha,size]; omega) c
  by_cases one : ∃a∈S,Covers E R (S.erase a)
  · obtain ⟨a,as,ca⟩ := one
    by_cases two : ∃b∈S,b≠a ∧ Covers E R (S.erase b)
    · obtain ⟨b,bs,ba,cb⟩ := two
      obtain ⟨lo,hi⟩ := (layers b bs cb).2.1 a (mem_erase.mpr ⟨ba.symm,as⟩)
      obtain ⟨y,ya,eq⟩ := (layers a as ca).2.2 _ lo hi
      refine ⟨{a,y},insert_subset as (singleton_subset_iff.mpr (mem_of_mem_erase ya)),
        (card_insert_le _ _).trans (by simp),?_⟩
      intro c cs good
      by_contra off
      have ac : a≠c := fun h=>off (h ▸ mem_insert_self _ _)
      have yc : y≠c := fun h=>off (h ▸ mem_insert_of_mem (mem_singleton_self _))
      have same : y=a := (layers c cs good).1
        (mem_erase.mpr ⟨yc,mem_of_mem_erase ya⟩) (mem_erase.mpr ⟨ac,as⟩) eq
      exact (mem_erase.mp ya).1 same
    · refine ⟨{a},singleton_subset_iff.mpr as,by simp,?_⟩
      intro b bs good
      exact mem_singleton.mpr (by_contra fun ne=>two ⟨b,bs,ne,good⟩)
  · exact ⟨∅,empty_subset _,by simp,fun a ha good=>False.elim (one ⟨a,ha,good⟩)⟩

theorem private_rows {q E U H S} (hq : 2≤q) (free : QFree E U q)
    (hs : H⊆U) (hl : H.Nonempty) (ss : S⊆U) (size : S.card=q)
    (cov : Covers E (BRsub.ballSet E U H (q-2)) S) :
    ∃P⊆S,q-2≤P.card ∧ ∀a∈P,∃r∈BRsub.ballSet E U H (q-2),outN E S r={a} := by
  classical
  obtain ⟨B,bs,cap,all⟩ := removable_bound hq free hs hl ss size
  refine ⟨S\B,sdiff_subset,by rw [card_sdiff_of_subset bs,size]; omega,?_⟩
  intro a ha
  have no : ¬Covers E (BRsub.ballSet E U H (q-2)) (S.erase a) :=
    fun cov'=> (mem_sdiff.mp ha).2 (all a (mem_sdiff.mp ha).1 cov')
  unfold Covers at no
  push Not at no
  obtain ⟨r,rr,off⟩ := no
  obtain ⟨k,ks,hit⟩ := cov r rr
  have unique (y) (ys : y∈S) (arc : E r y=true) : y=a := by
    by_contra ne
    have miss := off y (mem_erase.mpr ⟨ne,ys⟩)
    simp [arc] at miss
  refine ⟨r,rr,?_⟩
  ext y
  constructor
  · intro h
    exact mem_singleton.mpr (unique y (mem_outN.mp h).1 (mem_outN.mp h).2)
  · intro h
    have eq := (unique k ks hit).trans (mem_singleton.mp h).symm
    exact eq ▸ mem_outN.mpr ⟨ks,hit⟩

/-- If this unselected exterior head can be avoided by a different fresh
choice, retain that choice and delete the first head. Otherwise the original
rows have private columns, or a covering erasure pins the exterior sink. -/
def ExteriorResult (q : ℕ) (E : CH.Digraph) (U H R T : Finset ℕ) (v : ℕ→ℚ) (x : ℕ) : Prop :=
  (∃r∈R,(∀k∈T,E r k=false) ∧ ∃k∈outN E U r,
    let W := R ∪ insert k T
    x∉W ∧ W⊂U ∧ CommonParentReplay.Edge q E H ⟨U,T,v⟩ ⟨W,T,v⟩ ∧
      CommonParentReplay.Checks q E H R U ⟨W,T,v⟩) ∨
  let S := insert x T
  (∃P⊆S,q-2≤P.card ∧ ∀a∈P,∃r∈R,outN E S r={a}) ∧
    ((∀a∈S,∃r∈R,outN E S r={a}) ∨
      ∃t∈T,Covers E R (S.erase t) ∧ S.erase t\R={x} ∧ ∀r∈R,E x r=false)

theorem at_exterior {q n E U H T v} (hq : 2≤q) (free : QFree E U q)
    (small : SmallerSmallRow q n) (room : U.card+1<n) (hs : H⊆U) (hl : H.Nonempty)
    (ts : T⊆U) (count : T.card+1=q) (positive : ∀u∈U,0<v u)
    (heavy : WeightedSD.mass U v < q*WeightedSD.mass H v)
    (live : ∀r∈BRsub.ballSet E U H (q-2),(outN E U r).Nonempty)
    {r₀ x} (rr₀ : r₀∈BRsub.ballSet E U H (q-2)) (miss₀ : ∀k∈T,E r₀ k=false)
    (hit : x∈outN E U r₀) (outside : x∉BRsub.ballSet E U H (q-2)) :
    ExteriorResult q E U H (BRsub.ballSet E U H (q-2)) T v x := by
  classical
  let R := BRsub.ballSet E U H (q-2)
  let S := insert x T
  have xu := (mem_outN.mp hit).1
  have fresh : x∉T := fun e=>Bool.noConfusion ((miss₀ x e).symm.trans (mem_outN.mp hit).2)
  have ss : S⊆U := insert_subset xu ts
  have size : S.card=q := by rw [show S=insert x T from rfl,card_insert_of_notMem fresh,count]
  by_cases cov : Covers E R S
  · right
    refine ⟨private_rows hq free hs hl ss size cov,?_⟩
    by_cases all : ∀a∈S,∃r∈R,outN E S r={a}
    · exact Or.inl all
    · right
      push Not at all
      obtain ⟨t,st,no⟩ := all
      have cover : Covers E R (S.erase t) := by
        intro r rr
        by_contra! off
        obtain ⟨k,ks,arc⟩ := cov r rr
        have only (y) (ys : y∈S) (ry : E r y=true) : y=t := by
          by_contra ne
          have fail := off y (mem_erase.mpr ⟨ne,ys⟩)
          simp [ry] at fail
        apply no r rr
        ext y
        exact ⟨fun h=>mem_singleton.mpr (only y (mem_outN.mp h).1 (mem_outN.mp h).2),
          fun h=>((only k ks arc).trans (mem_singleton.mp h).symm) ▸ mem_outN.mpr ⟨ks,arc⟩⟩
      have tx : t≠x := by
        rintro rfl
        obtain ⟨b,hb,arc⟩ := cover r₀ rr₀
        have bt : b∈T := (mem_insert.mp (mem_erase.mp hb).2).resolve_left (mem_erase.mp hb).1
        exact Bool.noConfusion ((miss₀ b bt).symm.trans arc)
      obtain ⟨_,_,a,_,p,_,_,_,_,endSet,_,_,sink⟩ := CommonParentEndpointPath.full_cover hq free hs hl
        ((erase_subset t S).trans ss) (by rw [card_erase_of_mem st,size]; omega) cover
      have member : x∈S.erase t\R := mem_sdiff.mpr ⟨mem_erase.mpr ⟨tx.symm,mem_insert_self _ _⟩,outside⟩
      have eq : x=p.vertex p.len := mem_singleton.mp (endSet ▸ member)
      exact ⟨t,(mem_insert.mp st).resolve_left tx,cover,endSet.trans (by rw [eq]),
        fun r rr=>Bool.eq_false_iff.mpr (eq.symm ▸ sink r rr)⟩
  · left
    unfold Covers at cov
    push Not at cov
    obtain ⟨r,rr,miss⟩ := cov
    obtain ⟨k,kk⟩ := live r rr
    have kx : x≠k := by
      intro eq
      have no := miss x (mem_insert_self _ _)
      have arc : E r x=true := eq ▸ (mem_outN.mp kk).2
      simp [arc] at no
    have absent : x∉R ∪ insert k T := by simp [outside,kx,fresh,R]
    have valid : CommonParentReplay.Valid q E H R U ⟨U,T,v⟩ := ⟨Subset.rfl,hs,ts,positive,heavy,rfl⟩
    obtain ⟨_,checks,equal|⟨strict,edge⟩⟩ :=
      CommonParentEndpointReplay.retain_fresh hq free small room hl valid (mem_outN.mp kk).1
    · exact False.elim (absent (equal ▸ xu))
    · exact ⟨r,rr,fun a ha=>by simpa using miss a (mem_insert_of_mem ha),k,kk,absent,strict,edge,checks⟩

def Tests (q : ℕ) (E : CH.Digraph) (U H R T : Finset ℕ) (v : ℕ→ℚ) : Prop :=
  ∀r∈R,(∀k∈T,E r k=false) → ∀x∈outN E U r,x∉R → ExteriorResult q E U H R T v x

/-- Apply the column test to the actual terminal state of the priced trace. -/
theorem on_trace {q n E V U H i k l w z T v} (hq : 2≤q) (free : QFree E V q)
    (us : U⊆V) (small : SmallerSmallRow q n) (room : U.card+1<n)
    (hs : H⊆U) (hl : H.Nonempty) (pos : ∀a∈V,0<w a) (heavy : mass U w<q*mass H w)
    (ir : i∈BRsub.ballSet E U H (q-2)) (kk : k∈outN E U i)
    (first : CommonParentHeadRepair.Step q E U H ({k},w) (insert l {k},z))
    (path : Relation.ReflTransGen (CommonParentHeadRepair.Step q E U H) (insert l {k},z) (T,v))
    (count : T.card+1=q) (live : ∀r∈BRsub.ballSet E U H (q-2),(outN E U r).Nonempty) :
    CommonParentEndpointReplay.Fork q E V U H (BRsub.ballSet E U H (q-2)) T w v ∧
    Tests q E U H (BRsub.ballSet E U H (q-2)) T v := by
  refine ⟨CommonParentEndpointReplay.on_trace hq free us small room hs hl pos heavy ir kk first path count live,?_⟩
  let st := fun p : Finset ℕ × (ℕ→ℚ) => CommonParentReplay.State.mk U p.1 p.2
  have start : CommonParentReplay.Valid q E H (BRsub.ballSet E U H (q-2)) U (st ({k},w)) :=
    ⟨Subset.rfl,hs,singleton_subset_iff.mpr (mem_outN.mp kk).1,fun a ha=>pos a (us ha),heavy,rfl⟩
  have edges := (path.head first).lift st (fun _ _ e=>CommonParentReplay.Edge.repair e)
  have valid := (CommonParentReplay.replay hq (free.mono_set us) small room hl start edges).1
  intro r rr miss x hit outside
  exact at_exterior hq (free.mono_set us) small room hs hl valid.selected count valid.positive valid.heavy
    live rr miss hit outside

/-- The surplus bound at the port provides the live row used by the new cut. -/
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
    T.card+1=q → CommonParentEndpointReplay.Fork q D V U H R T w v ∧ Tests q D U H R T v := by
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

#print axioms at_exterior

#print axioms private_rows
end LeanCH.BR.Closure.EndpointPrivateRows

