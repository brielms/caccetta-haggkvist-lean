import checkpoints.shen_extension.TwoHeadForcedMiss
import checkpoints.shen_extension.TwoParentWithdrawalDual

namespace LeanCH.BR.Closure.MissedFreshCut
open Finset BRq2 BRq3 BR45 WeightedSD CommonParentReplay LabelledLeakageCapacity TwoHeadRepairReplay

theorem native_degree {q E V w c} (hq : 2≤q) (high : 1<c)
    (rows : ∀i∈V,WeightedSD.row q E V w i=c) (cap : ∀j∈V,(q:ℚ)^2*w j≤1)
    {r} (rv : r∈V) : q≤(outN E V r).card := by
  by_contra! low
  let N := outN E V r
  change N.card<q at low
  have bounds := sum_le_sum (s:=N) (fun j jn=>cap j (outN_subset jn))
  have sumcap : (q:ℚ)^2*mass N w≤N.card := by
    simpa [mass,mul_sum] using bounds
  have size : (N.card:ℚ)+1≤q := by exact_mod_cast (show N.card+1≤q by omega)
  have row := rows r rv
  rw [WeightedSD.row,outW_eq_mass] at row
  change w r+(q:ℚ)*mass N w=c at row
  have qt : (2:ℚ)≤q := by exact_mod_cast hq
  nlinarith only [cap r rv,mul_le_mul_of_nonneg_left sumcap (Nat.cast_nonneg q),
    mul_le_mul_of_nonneg_left size (Nat.cast_nonneg q),congrArg (fun t : ℚ=>(q:ℚ)^2*t) row,
    mul_lt_mul_of_pos_left high (sq_pos_of_pos (show 0<(q:ℚ) by linarith)),qt]

theorem first_drop {q n w c} (X : ShortestCycleWeights.Model q n) (hq : 2≤q)
    (s : Seeds q X.D X.V w c) {x y} (orientation : (x=s.x ∧ y=s.y) ∨ (x=s.y ∧ y=s.x)) :
    y∈inN X.D X.V s.a := by
  have hit : y∈outN X.D (X.V\region q X.D X.V s.a) s.i := by
    rcases orientation with ⟨_,rfl⟩|⟨_,rfl⟩
    · exact s.yhit
    · exact s.xhit
  obtain ⟨yv,yr⟩ := mem_sdiff.mp (outN_subset hit)
  have cross : s.a∈X.V.filter (fun a=>s.i∈region q X.D X.V a ∧ y∉region q X.D X.V a) :=
    mem_filter.mpr ⟨s.av,s.ir,yr⟩
  rw [crossing hq X.free X.sat (BRsub.ballSet_subset s.ir) yv (mem_outN.mp hit).2] at cross
  exact mem_inN.mpr ⟨yv,(mem_outN.mp (mem_sdiff.mp cross).1).2⟩

/-- Every head of a missed row is fresh. Any individually specified
unselected exterior vertex can be deleted while keeping one such head. -/
def AtRow (q : ℕ) (E : CH.Digraph) (V : Finset ℕ) (a y : ℕ) (T : Finset ℕ)
    (v w : ℕ→ℚ) (c : ℚ) (r : ℕ) : Prop :=
  let U := V\{a,y}
  let R := region q E V a
  let H := outN E V a
  q≤(outN E U r).card+1 ∧ Disjoint (outN E U r) T ∧
    (∀e∈U\(R∪T),∃k∈outN E U r,k∉T ∧
      let W := R∪insert k T
      e∉W ∧ W⊂U ∧ Edge q E H ⟨U,T,v⟩ ⟨W,T,v⟩ ∧ Checks q E H R U ⟨W,T,v⟩) ∧
    (U=R∪T → inN E V a=insert y (T\R) ∧ (inN E V a).card≤q ∧
      outN E U r=outN E R r ∧
      WeightedSD.row q E R w r=c-(if E r y then (q:ℚ)*w y else 0))

theorem on_terminal {q n w c} (X : ShortestCycleWeights.Model q n) (hq : 3≤q)
    (small : SmallerSmallRow q X.V.card) (high : 1<c) (flat : ∀i∈X.V,WeightedSD.row q X.D X.V w i=c)
    (cap : ∀i∈X.V,(q:ℚ)^2*w i≤1) {a y T v r}
    (av : a∈X.V) (par : y∈inN X.D X.V a) (sz : T.card+1=q)
    (check : Checks q X.D (outN X.D X.V a) (region q X.D X.V a) (X.V\{a,y}) ⟨X.V\{a,y},T,v⟩)
    (rr : r∈region q X.D X.V a) (miss : ∀k∈T,X.D r k=false) : AtRow q X.D X.V a y T v w c r := by
  classical
  let E := X.D
  let V := X.V
  let R := region q E V a
  let H := outN E V a
  let U := V\{a,y}
  have two : 2≤q := by omega
  have rv : r∈V := BRsub.ballSet_subset rr
  have ra := ((saturated_region two X.free X.sat av rv).mp rr).2
  obtain ⟨yv,ya⟩ := mem_inN.mp par
  have ay : a≠y := fun eq=>loopfree X.free (by omega) av (eq.symm ▸ ya)
  have us : U⊆V := sdiff_subset
  have ts : T⊆U := check.1.selected
  have same : CommonParentReplay.ball q E H U=R := check.1.same
  have rs : R⊆U := by rw [←same]; exact BRsub.ballSet_subset
  have hn : H.Nonempty := by obtain ⟨h,hh,_⟩ := BRsub.mem_ballSet.mp rr; exact ⟨h,hh⟩
  have yn : y∉U := fun h=>(mem_sdiff.mp h).2 (by simp)
  have yV : y∈V := yv
  have split : outN E V r=if E r y then insert y (outN E U r) else outN E U r := by
    ext k
    by_cases ky : k=y
    · subst k; cases hy : E r y <;> simp [hy,mem_outN,yn,yV]
    · have extend : k∈V ∧ E r k=true ↔ k∈U ∧ E r k=true := by
        refine ⟨fun ⟨kv,rk⟩=>⟨mem_sdiff.mpr ⟨kv,?_⟩,rk⟩,fun ⟨ku,rk⟩=>⟨us ku,rk⟩⟩
        simpa [ky] using (show k≠a from fun eq=>ra (eq ▸ rk))
      cases hy : E r y <;> simpa [mem_outN,ky] using extend
  have degree := native_degree two high flat cap rv
  change q≤(outN E V r).card at degree
  have yo : y∉outN E U r := fun hit=>(mem_sdiff.mp (outN_subset hit)).2 (by simp)
  have enough : q≤(outN E U r).card+1 := by
    rw [split] at degree
    split at degree
    · simpa [card_insert_of_notMem yo] using degree
    · omega
  have dis : Disjoint (outN E U r) T :=
    disjoint_left.mpr (fun k hit kt=>Bool.noConfusion ((miss k kt).symm.trans (mem_outN.mp hit).2))
  have cutSize := card_sdiff_of_subset (insert_subset av (singleton_subset_iff.mpr yv) : ({a,y}:Finset ℕ)⊆V)
  have room : U.card+1<V.card := by
    have lb := card_le_card (insert_subset av (singleton_subset_iff.mpr yv) : ({a,y}:Finset ℕ)⊆V)
    rw [card_pair ay] at cutSize lb
    dsimp only [U]; omega
  refine ⟨enough,dis,?_,?_⟩
  · intro e he
    obtain ⟨eu,off⟩ := mem_sdiff.mp he
    obtain ⟨j,jh,k,kh,ne⟩ := one_lt_card.mp (show 1<(outN E U r).card by omega)
    obtain ⟨f,fh,diff⟩ : ∃f∈outN E U r,e≠f := by
      by_cases ej : e=j
      · exact ⟨k,kh,ej ▸ ne⟩
      · exact ⟨j,jh,ej⟩
    have absent : e∉R∪insert f T := by simpa [mem_union,mem_insert,diff] using off
    have replay := CommonParentEndpointReplay.retain_fresh two (X.free.mono_set us) small room hn check.1 (outN_subset fh)
    refine ⟨f,fh,fun ft=>disjoint_left.mp dis fh ft,absent,?_⟩
    obtain eq|strict := replay.2.2
    · exact False.elim (absent (eq ▸ eu))
    · exact ⟨strict.1,strict.2,replay.2.1⟩
  · intro full
    have parents : inN E V a=insert y (T\R) := by
      ext k
      constructor
      · intro kp
        by_cases ky : k=y
        · exact mem_insert.mpr (Or.inl ky)
        obtain ⟨kv,ka⟩ := mem_inN.mp kp
        have nr : k∉R := fun kr=>((saturated_region two X.free X.sat av kv).mp kr).2 ka
        have ak : k≠a := fun eq=>loopfree X.free (by omega) av (eq ▸ ka)
        have ku : k∈U := mem_sdiff.mpr ⟨kv,by simp [ak,ky]⟩
        exact mem_insert_of_mem (mem_sdiff.mpr ⟨(mem_union.mp (full ▸ ku)).resolve_left nr,nr⟩)
      · intro kT
        rcases mem_insert.mp kT with eq|ht
        · exact eq ▸ par
        obtain ⟨kt,kr⟩ := mem_sdiff.mp ht
        have ku := ts kt
        have kv := us ku
        have ne : k≠a := fun eq=>(mem_sdiff.mp ku).2 (mem_insert.mpr (Or.inl eq))
        exact mem_inN.mpr ⟨kv,by by_contra no; exact kr ((saturated_region two X.free X.sat av kv).mpr ⟨ne,no⟩)⟩
    have bound := card_le_card (sdiff_subset : T\R⊆T)
    have capN := card_insert_le y (T\R)
    have only : outN E U r=outN E R r := by
      ext k
      constructor
      · intro h
        have kt := fun kt=>disjoint_left.mp dis h kt
        exact mem_outN.mpr ⟨(mem_union.mp (full ▸ outN_subset h)).resolve_right kt,(mem_outN.mp h).2⟩
      · intro h; exact mem_outN.mpr ⟨rs (outN_subset h),(mem_outN.mp h).2⟩
    refine ⟨parents,by rw [parents]; omega,only,?_⟩
    have row := flat r rv
    rw [WeightedSD.row,outW_eq_mass,show outN X.D X.V r=_ from split] at row
    rw [WeightedSD.row,outW_eq_mass,←only]
    cases h : E r y <;> simp [E,h,mass,yo,Finset.sum_insert] at row ⊢ <;> linarith

/-- All continuations keeping these exact heads and prices have a common
descendant. On the minimal carrier another such continuation stays there. -/
theorem common_cut {q n E H R U T v p} (two : 2≤q) (free : QFree E U q)
    (small : SmallerSmallRow q n) (room : U.card+1<n) (hl : H.Nonempty)
    (pt : p∈T) (check : Checks q E H R U ⟨U,T,v⟩) :
    let K := R∪T
    let edge := Edge q E H
    Checks q E H R U ⟨K,T,v⟩ ∧
    (∀W,Relation.ReflTransGen edge ⟨U,T,v⟩ ⟨W,T,v⟩ →
      Relation.ReflTransGen edge ⟨W,T,v⟩ ⟨K,T,v⟩) ∧
    (∀W,Relation.ReflTransGen edge ⟨K,T,v⟩ ⟨W,T,v⟩ → W=K) := by
  intro K edge
  have reduce (W) (good : CommonParentReplay.Valid q E H R U ⟨W,T,v⟩) :=
    CommonParentEndpointReplay.retain_fresh two free small room hl good (good.selected pt)
  have root := reduce U check.1
  simp only [insert_eq_of_mem pt] at root
  refine ⟨root.2.1,?_,?_⟩
  · intro W path
    have next := reduce W (replay two free small room hl check.1 path).1
    simpa only [insert_eq_of_mem pt] using next.1
  · intro W path
    have valid := (replay two free small room hl root.2.1.1 path).1
    have eq : CommonParentReplay.ball q E H W=R := valid.same
    have rw' : R⊆W := by rw [←eq]; exact BRsub.ballSet_subset
    exact Subset.antisymm (TwoHeadRepairLanes.nested path).2 (union_subset rw' valid.selected)

/-- Count and weigh the same labelled set: the native heads of a missed
row together with the selected exterior parents which the row misses. -/
theorem inner_heads {q n w c} (X : ShortestCycleWeights.Model q n) (hq : 3≤q)
    (high : 1<c) (flat : ∀i∈X.V,WeightedSD.row q X.D X.V w i=c)
    (pos : ∀i∈X.V,0<w i) (cap : ∀i∈X.V,(q:ℚ)^2*w i≤1) {a y r T}
    (av : a∈X.V) (ts : T⊆X.V\{a,y}) (rr : r∈region q X.D X.V a)
    (miss : ∀j∈T,X.D r j=false) :
    let R := region q X.D X.V a
    let P := inN X.D X.V a
    q+(T\R).card≤(outN X.D R r).card+P.card ∧
    c+(q:ℚ)*mass (T\R) w≤WeightedSD.row q X.D R w r+(q:ℚ)*mass P w := by
  classical
  intro R P
  let A := outN X.D R r
  let N := outN X.D X.V r
  let S := T\R
  have rv : r∈X.V := BRsub.ballSet_subset rr
  have two : 2≤q := by omega
  have absent := ((saturated_region two X.free X.sat av rv).mp rr).2
  have par {j} (jv : j∈X.V) (ne : j≠a) (jr : j∉R) : j∈P := by
    apply mem_inN.mpr
    exact ⟨jv,by by_contra no; exact jr ((saturated_region two X.free X.sat av jv).mpr ⟨ne,no⟩)⟩
  have sub : N∪S⊆A∪P := by
    intro j hj
    obtain jn|js := mem_union.mp hj
    · obtain ⟨jv,arc⟩ := mem_outN.mp jn
      by_cases jr : j∈R
      · exact mem_union_left _ (mem_outN.mpr ⟨jr,arc⟩)
      · exact mem_union_right _ (par jv (fun eq=>absent (eq ▸ arc)) jr)
    · obtain ⟨jt,jr⟩ := mem_sdiff.mp js
      have ju := mem_sdiff.mp (ts jt)
      exact mem_union_right _ (par ju.1 (fun eq=>ju.2 (mem_insert.mpr (Or.inl eq))) jr)
  have dn : Disjoint N S := disjoint_left.mpr (fun j jn js=>
    Bool.noConfusion ((miss j (mem_sdiff.mp js).1).symm.trans (mem_outN.mp jn).2))
  have da : Disjoint A P := disjoint_left.mpr (fun j ja jp=>
    ((saturated_region two X.free X.sat av (mem_inN.mp jp).1).mp (outN_subset ja)).2 (mem_inN.mp jp).2)
  have ct := card_le_card sub
  rw [card_union_of_disjoint dn,card_union_of_disjoint da] at ct
  have sum := sum_le_sum_of_subset_of_nonneg (f:=w) sub (fun j hv _=>by
    obtain ja|jp := mem_union.mp hv
    · exact (pos j (BRsub.ballSet_subset (outN_subset ja))).le
    · exact (pos j (mem_inN.mp jp).1).le)
  rw [sum_union dn,sum_union da] at sum
  change mass N w+mass S w≤mass A w+mass P w at sum
  have eq := flat r rv
  rw [WeightedSD.row,outW_eq_mass] at eq ⊢
  refine ⟨(Nat.add_le_add_right (native_degree two high flat cap rv) S.card).trans ct,?_⟩
  change w r+(q:ℚ)*mass N w=c at eq
  change c+(q:ℚ)*mass S w≤w r+(q:ℚ)*mass A w+(q:ℚ)*mass P w
  linarith only [eq,mul_le_mul_of_nonneg_left sum (Nat.cast_nonneg q)]

/-- A row that dies on the minimal carrier is a paying row for the
original native prices. Its surviving native seeds avoid the old selection. -/
def Restart (q : ℕ) (E : CH.Digraph) (V : Finset ℕ) (w : ℕ→ℚ) (c : ℚ)
    (a y r : ℕ) (T : Finset ℕ) : Prop :=
  let R := region q E V a
  let O := outN E (V\R) r
  let G := outN E (V\{a,y}) r
  O=outN E V r ∧ c-mass R w≤q*mass O w ∧ q≤O.card ∧
    G⊆O\T ∧ (∃j∈G,∃k∈G,j≠k) ∧ TwoHeadRepairLanes.OpposedFrom q E V w a r

theorem restart {q n w c} (X : ShortestCycleWeights.Model q n) (hq : 3≤q)
    (small : SmallerSmallRow q X.V.card) (pos : ∀i∈X.V,0<w i) (high : 1<c)
    (flat : ∀i∈X.V,WeightedSD.row q X.D X.V w i=c) (cap : ∀i∈X.V,(q:ℚ)^2*w i≤1)
    {a y T v r} (av : a∈X.V) (rr : r∈region q X.D X.V a)
    (facts : AtRow q X.D X.V a y T v w c r) (dead : outN X.D (region q X.D X.V a) r=∅) :
    Restart q X.D X.V w c a y r T := by
  let R := region q X.D X.V a
  have rv : r∈X.V := BRsub.ballSet_subset rr
  have outside : outN X.D (X.V\R) r=outN X.D X.V r := by
    ext j
    constructor
    · intro h; exact mem_outN.mpr ⟨(mem_sdiff.mp (outN_subset h)).1,(mem_outN.mp h).2⟩
    · intro h
      have off : j∉R := fun jr=>Finset.notMem_empty j (dead ▸ mem_outN.mpr ⟨jr,(mem_outN.mp h).2⟩)
      exact mem_outN.mpr ⟨mem_sdiff.mpr ⟨outN_subset h,off⟩,(mem_outN.mp h).2⟩
  have size := native_degree (by omega : 2≤q) high flat cap rv
  have charge := flat r rv
  rw [WeightedSD.row,outW_eq_mass] at charge
  have atom : w r≤mass R w := single_le_sum (fun j jr=>(pos j (BRsub.ballSet_subset jr)).le) rr
  obtain ⟨count,dis,_,_⟩ := facts
  have large : 2≤(outN X.D (X.V\R) r).card := by rw [outside]; omega
  refine ⟨outside,by rw [outside]; linarith, outside ▸ size,?_,one_lt_card.mp (by omega),
    TwoHeadRepairLanes.at_row hq X.free X.sat small pos high flat cap av rr large⟩
  intro j h
  exact mem_sdiff.mpr ⟨outside ▸ mem_outN.mpr ⟨(mem_sdiff.mp (outN_subset h)).1,(mem_outN.mp h).2⟩,
    fun jt=>disjoint_left.mp dis h jt⟩

/-- At a root without a dead parent, both restarted traces miss again. -/
theorem repeat_misses {q n w c a y r T} (X : ShortestCycleWeights.Model q n) (hq : 3≤q)
    (av : a∈X.V) (rr : r∈region q X.D X.V a)
    (returns : ∀x∈inN X.D X.V a,∃j∈region q X.D X.V a,X.D x j=true)
    (data : Restart q X.D X.V w c a y r T) :
    let H := outN X.D X.V a
    let R := region q X.D X.V a
    ∃z,∃j∈outN X.D (X.V\{a,y}) r,∃k∈outN X.D (X.V\{a,y}) r,j≠k ∧ j∉T ∧ k∉T ∧
      CommonParentHeadRepair.Step q X.D X.V H (∅,w) ({j},z) ∧
      CommonParentHeadRepair.Step q X.D X.V H (∅,w) ({k},z) ∧
      Missed q X.D X.V H R a j k z ∧ Missed q X.D X.V H R a k j z := by
  intro H R
  obtain ⟨_,_,_,sub,⟨j,jh,k,kh,ne⟩,z,_,start,fork⟩ := data
  obtain ⟨jo,jt⟩ := mem_sdiff.mp (sub jh)
  obtain ⟨ko,kt⟩ := mem_sdiff.mp (sub kh)
  obtain ⟨left,right,_⟩ := fork j jo k ko ne
  have force {u d} (uo : u∈outN X.D (X.V\R) r) (l : TwoHeadRepairLanes.Lane q X.D X.V H R a u d z) :
      Missed q X.D X.V H R a u d z := by
    obtain m|exit := replay_lane l
    · exact m
    obtain ⟨uv,ur⟩ := mem_sdiff.mp (outN_subset uo)
    have cross : a∈X.V.filter (fun v=>r∈region q X.D X.V v ∧ u∉region q X.D X.V v) :=
      mem_filter.mpr ⟨av,rr,ur⟩
    rw [crossing (by omega : 2≤q) X.free X.sat (BRsub.ballSet_subset rr) uv (mem_outN.mp uo).2] at cross
    obtain ⟨t,tr,hit⟩ := returns u (mem_inN.mpr ⟨uv,(mem_outN.mp (mem_sdiff.mp cross).1).2⟩)
    obtain ⟨_,_,_,_,_,_,_,_,_,dead⟩ := exit
    exact False.elim (Bool.noConfusion ((dead t (mem_insert_of_mem tr)).symm.trans hit))
  exact ⟨z,j,jh,k,kh,ne,jt,kt,start j jo,start k ko,force jo left,force ko right⟩

def Terminal {q n} (X : ShortestCycleWeights.Model q n) (w : ℕ→ℚ) (c : ℚ)
    (a y : ℕ) (T : Finset ℕ) (v : ℕ→ℚ) : Prop :=
  let U := X.V\{a,y}
  let R := region q X.D X.V a
  let H := outN X.D X.V a
  let K := R∪T
  let edge := Edge q X.D H
  Checks q X.D H R U ⟨K,T,v⟩ ∧
  (∀W,Relation.ReflTransGen edge ⟨U,T,v⟩ ⟨W,T,v⟩ → Relation.ReflTransGen edge ⟨W,T,v⟩ ⟨K,T,v⟩) ∧
  (∀W,Relation.ReflTransGen edge ⟨K,T,v⟩ ⟨W,T,v⟩ → W=K) ∧
  ∀r∈R,(∀j∈T,X.D r j=false) →
    AtRow q X.D X.V a y T v w c r ∧
    let P := inN X.D X.V a
    q+(T\R).card≤(outN X.D R r).card+P.card ∧
    c+(q:ℚ)*mass (T\R) w≤WeightedSD.row q X.D R w r+(q:ℚ)*mass P w ∧
    (P.card≤q → (outN X.D R r).Nonempty) ∧ (P.card≤2 → q≤(outN X.D R r).card+1) ∧
    ((outN X.D R r).Nonempty ∨ Restart q X.D X.V w c a y r T)

def OnModel {q n} (X : ShortestCycleWeights.Model q n) : Prop :=
  ∀{w c},1<c → (∀i∈X.V,WeightedSD.row q X.D X.V w i=c) → (∀i∈X.V,0<w i) →
  (∀i∈X.V,(q:ℚ)^2*w i≤1) → ∀{a y p T v},a∈X.V → y∈inN X.D X.V a →
  p∈inN X.D X.V a → p∈T → T.card+1=q →
  Checks q X.D (outN X.D X.V a) (region q X.D X.V a) (X.V\{a,y}) ⟨X.V\{a,y},T,v⟩ →
  Terminal X w c a y T v

theorem on_model {q n} (X : ShortestCycleWeights.Model q n) (hq : 3≤q)
    (small : SmallerSmallRow q X.V.card) : OnModel X := by
  intro w c high flat pos cap a y p T v av yp pp pt sz checks
  have two : 2≤q := by omega
  obtain ⟨yv,ya⟩ := mem_inN.mp yp
  have ay : a≠y := fun eq=>loopfree X.free (by omega) av (eq.symm ▸ ya)
  have sub : ({a,y}:Finset ℕ)⊆X.V := insert_subset av (singleton_subset_iff.mpr yv)
  have erase := card_sdiff_of_subset sub
  have lb := card_le_card sub
  rw [card_pair ay] at erase lb
  have room : (X.V\{a,y}).card+1<X.V.card := by omega
  have count := native_degree two high flat cap av
  have hl := card_pos.mp (show 0<(outN X.D X.V a).card by omega)
  obtain ⟨checkK,toK,stable⟩ := common_cut two (X.free.mono_set sdiff_subset) small room hl pt checks
  refine ⟨checkK,toK,stable,?_⟩
  intro r rr miss
  obtain ⟨many,bill⟩ := inner_heads X hq high flat pos cap av checks.1.selected rr miss
  have outer : p∉region q X.D X.V a := fun pr=>
    ((saturated_region two X.free X.sat av (mem_inN.mp pp).1).mp pr).2 (mem_inN.mp pp).2
  change q+(T\region q X.D X.V a).card≤(outN X.D (region q X.D X.V a) r).card+(inN X.D X.V a).card at many
  have someT : 0<(T\region q X.D X.V a).card := card_pos.mpr ⟨p,mem_sdiff.mpr ⟨pt,outer⟩⟩
  have facts := on_terminal X hq small high flat cap av yp sz checks rr miss
  refine ⟨facts,many,bill,fun _=>card_pos.mp (by omega),fun _=>by omega,?_⟩
  by_cases live : (outN X.D (region q X.D X.V a) r).Nonempty
  · exact Or.inl live
  · exact Or.inr (restart X hq small pos high flat cap av rr facts (not_nonempty_iff_eq_empty.mp live))

theorem first_parents {q n w c} (X : ShortestCycleWeights.Model q n) (hq : 2≤q)
    (s : Seeds q X.D X.V w c) {x y} (orient : (x=s.x ∧ y=s.y) ∨ (x=s.y ∧ y=s.x)) :
    y∈inN X.D X.V s.a ∧ x∈inN X.D X.V s.a := by
  refine ⟨first_drop X hq s orient,first_drop X hq s (x:=y) ?_⟩
  rcases orient with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> simp

/-- The next trace is opened once, so its terminal tests apply to its own
missed row at its own prices and still expose the next restart alternative. -/
def ReplayedMiss {q n} (X : ShortestCycleWeights.Model q n) (w : ℕ→ℚ) (c : ℚ)
    (a p y : ℕ) (z : ℕ→ℚ) : Prop :=
  let U := X.V\{a,y}
  let H := outN X.D X.V a
  let R := region q X.D X.V a
  ∃T v,Relation.ReflTransGen (Edge q X.D H) ⟨U,{p},z⟩ ⟨U,T,v⟩ ∧
    p∈T ∧ T.card+1=q ∧ Checks q X.D H R U ⟨U,T,v⟩ ∧ Terminal X w c a y T v ∧
    ∃i∈R,(∀j∈T,X.D i j=false) ∧ ∃k∈outN X.D U i,k∉T

theorem replay_restart {q n w c a y r T} (X : ShortestCycleWeights.Model q n) (hq : 3≤q)
    (small : SmallerSmallRow q X.V.card) (high : 1<c) (flat : ∀i∈X.V,WeightedSD.row q X.D X.V w i=c)
    (pos : ∀i∈X.V,0<w i) (cap : ∀i∈X.V,(q:ℚ)^2*w i≤1)
    (av : a∈X.V) (rr : r∈region q X.D X.V a)
    (returns : ∀x∈inN X.D X.V a,∃j∈region q X.D X.V a,X.D x j=true)
    (data : Restart q X.D X.V w c a y r T) :
    let H := outN X.D X.V a
    ∃z,∃j∈outN X.D (X.V\{a,y}) r,∃k∈outN X.D (X.V\{a,y}) r,j≠k ∧ j∉T ∧ k∉T ∧
      CommonParentHeadRepair.Step q X.D X.V H (∅,w) ({j},z) ∧
      CommonParentHeadRepair.Step q X.D X.V H (∅,w) ({k},z) ∧
      ReplayedMiss X w c a j k z ∧ ReplayedMiss X w c a k j z := by
  intro H
  obtain ⟨z,j,jh,k,kh,ne,jt,kt,sj,sk,left,right⟩ := repeat_misses X hq av rr returns data
  have par {i} (hit : i∈outN X.D (X.V\{a,y}) r) : i∈inN X.D X.V a := by
    have io := (mem_sdiff.mp (data.2.2.2.1 hit)).1
    obtain ⟨iv,ir⟩ := mem_sdiff.mp (outN_subset io)
    have cross : a∈X.V.filter (fun b=>r∈region q X.D X.V b ∧ i∉region q X.D X.V b) := mem_filter.mpr ⟨av,rr,ir⟩
    rw [crossing (by omega : 2≤q) X.free X.sat (BRsub.ballSet_subset rr) iv (mem_outN.mp io).2] at cross
    exact mem_inN.mpr ⟨iv,(mem_outN.mp (mem_sdiff.mp cross).1).2⟩
  have again {p d} (pp : p∈inN X.D X.V a) (dp : d∈inN X.D X.V a)
      (m : Missed q X.D X.V H (region q X.D X.V a) a p d z) : ReplayedMiss X w c a p d z := by
    obtain ⟨S,v,path,pS,sz,checks,i,ir,quiet,f,fh,fs,_,_⟩ := m
    exact ⟨S,v,path,pS,sz,checks,on_model X hq small high flat pos cap av dp pp pS sz checks,
      i,ir,quiet,f,fh,fs⟩
  exact ⟨z,j,jh,k,kh,ne,jt,kt,sj,sk,again (par jh) (par kh) left,again (par kh) (par jh) right⟩

/-- Instantiate the puncture dual with the two labelled parents of the
reroot. The traded reserves live on V.erase b. -/
theorem withdrawal_on_returns {q n b p y t w c} (X : ShortestCycleWeights.Model q n)
    (hq : 2≤q) (small : SmallerSmallRow q X.V.card) (bv : b∈X.V)
    (par : inN X.D X.V b={p,y}) (ne : p≠y) (yp : y∈inN X.D X.V b)
    (backs : ∀j∈inN X.D X.V b,∃u∈region q X.D X.V b,X.D j u=true)
    (tr : t∈region q X.D X.V b) (pt : X.D p t=true)
    (wp : ∀i∈X.V,0<w i) (high : mass X.V w<c) (flat : ∀i∈X.V,WeightedSD.row q X.D X.V w i=c)
    (x : ℕ→ℝ) (xn : ∀i∈X.V.erase b,0≤x i) :
    let U := X.V.erase b
    let A := TwoParentWithdrawalDual.reserve q X.D U x
    (∀i∈U,i≠p → i≠y → 0≤A i) → 0≤A p →
      ((c:ℝ)-(mass X.V w:ℝ))*A p≤(w b:ℝ)*(-A y) ∧ (0≤A y → A p=0 ∧ A y=0) := by
  obtain ⟨u,ur,yu⟩ := backs y yp
  have survive {k} (kr : k∈region q X.D X.V b) : k∈X.V.erase b := by
    have kv : k∈X.V := BRsub.ballSet_subset kr
    exact mem_erase.mpr ⟨((saturated_region hq X.free X.sat bv kv).mp kr).1,kv⟩
  exact TwoParentWithdrawalDual.on_puncture hq X.free small bv par ne (survive tr) (survive ur) pt yu
    wp high flat x xn

#print axioms on_model
#print axioms first_parents
#print axioms common_cut
#print axioms inner_heads
#print axioms restart
#print axioms repeat_misses
#print axioms replay_restart
#print axioms withdrawal_on_returns
#print axioms native_degree
#print axioms first_drop
#print axioms on_terminal
end LeanCH.BR.Closure.MissedFreshCut
