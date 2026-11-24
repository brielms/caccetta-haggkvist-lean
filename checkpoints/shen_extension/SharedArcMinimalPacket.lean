import checkpoints.shen_extension.SharedArcAffordablePaths
import LeanCH.BR.BRWeightedDeletionThreshold

namespace LeanCH.BR.Closure.SharedArcMinimalPacket
open Finset BRq2 BRq3 BR45 WeightedSD ShenCycleSuccessor ShortestCycleWeights FirstPacketBarrier
open MarkedCyclePeeling SharedArcExpansion SharedArcBarrier

/-- In any strict graph of least support, every actual arc occurs on a shortest cycle
of the graph itself. The graph may be an intermediate edge edit. -/
theorem cycle_at_arc {q H V} (hq : 2≤q) (small : SmallerSmallRow q V.card) (free : QFree H V q)
    (bad : ¬SmallRow q H V) {i j} (iv : i∈V) (jv : j∈V) (ed : H i j=true) :
    ∃M,Cycle H V q M ∧ i∈M ∧ j∈M := by
  classical
  obtain ⟨w,wn,live,hi⟩ := strict_witness_of_not_smallRow bad
  obtain ⟨x,_,c,ch,xp,_,xm,_,rows,_⟩ := strict_pair_of_proper_smallRow (small.induced free) live w wn hi
  have cut : i∈V.erase j := mem_erase.mpr ⟨fun eq => loopfree free (by omega) jv (eq ▸ ed),iv⟩
  have high : 1<(c:ℝ) := by exact_mod_cast ch
  have cap := (FiniteHorizonHall.capacity (z:=fun v => (x v:ℝ)) hq high small free
    (by rw [realMass_rat,xm]; norm_num) (fun v vv => by exact_mod_cast xp v vv)
    (fun v vv => by rw [realRow_rat,rows v vv]) jv (singleton_subset_iff.mpr cut) (singleton_nonempty i)).1
  have hit : (FiniteHorizonHall.ports q H V j {i}).Nonempty := by
    by_contra! em
    rw [em] at cap
    simp [realMass] at cap
    have pos : 0<(x i:ℝ) := by exact_mod_cast xp i iv
    linarith
  obtain ⟨h,hh⟩ := hit
  obtain ⟨head,k,ks,reach⟩ := mem_filter.mp hh
  obtain rfl := mem_singleton.mp ks
  obtain ⟨M,cm,im,jm,_⟩ := FiniteHorizonHall.marked_of_port hq free jv head (mem_inN.mpr ⟨iv,ed⟩) reach
  exact ⟨M,cm,im,jm⟩

/-- Introduce the new cycle arcs only at the selected heads. -/
noncomputable def edit (D : CH.Digraph) (F : Family) (B J : Finset ℕ) : CH.Digraph :=
  fun i j => if j∈J then graph D (insert B F) i j else graph D F i j

private theorem native {D F i j} (a : graph D F i j=true) : D i j=true := by
  obtain ⟨_,k⟩ := active.mp a
  exact (mem_col.mp k).2.2.2

theorem lift_cycle {H D V q M} (hq : 1≤q) (free : QFree D V q)
    (sub : ∀{i j},H i j=true → D i j=true) (cm : Cycle H V q M) :
    Cycle D V q M ∧ ∀i∈M,∀j∈M,D i j=true → H i j=true := by
  have deg (i) (im : i∈M) : 1≤(outN D M i).card := by
    rw [←cm.heads i im]
    exact card_le_card fun j hj => mem_outN.mpr ⟨(mem_outN.mp hj).1,sub (mem_outN.mp hj).2⟩
  have reg := dt_reg hq (ball_q_one q hq) (free.mono_set cm.sub) deg (by simpa using cm.size)
  refine ⟨⟨cm.sub,cm.size,reg.1,reg.2⟩,?_⟩
  intro i im j jm ij
  obtain ⟨k,kh⟩ := card_pos.mp (show 0<(outN H M i).card by rw [cm.heads i im]; decide)
  obtain ⟨km,ik⟩ := mem_outN.mp kh
  obtain rfl : j=k := card_le_one.mp (reg.1 i im).le _ (mem_outN.mpr ⟨jm,ij⟩) _ (mem_outN.mpr ⟨km,sub ik⟩)
  exact ik

/-- Omitting one changed head destroys every shortest cycle through any of
the other newly inserted arcs, even if its cycle would use different labels. -/
theorem no_cycle_edit {q n} (X : Model q n) (hq : 2≤q) {F B} (step : Boundary X F B)
    (least : ∀M,Boundary X F M → (targets X.D X.V F B).card≤(targets X.D X.V F M).card)
    {J} (proper : J ⊂ targets X.D X.V F B)
    {i j M} (ij : X.D i j=true) (missing : graph X.D F i j=false)
    (cm : Cycle (edit X.D F B J) X.V q M) (im : i∈M) (jm : j∈M) : False := by
  classical
  let H := edit X.D F B J
  have cb : Cycle X.D X.V q B := (mem_filter.mp step.1).2
  have sub {a b} (ab : H a b=true) : X.D a b=true := by
    by_cases h : b∈J <;> simp only [H,edit,h,ite_true,ite_false] at ab <;> exact native ab
  obtain ⟨cd,kept⟩ := lift_cycle (by omega : 1≤q) X.free (fun a => sub a) cm
  have inside : targets X.D X.V F M⊆J := by
    intro v vt
    obtain ⟨_,vm,u,um,uv,no⟩ := mem_filter.mp vt
    by_contra out
    have yes := kept u um v vm uv
    simp [H,edit,out,no] at yes
  have smallJ : J.card<M.card := by
    have tb : targets X.D X.V F B⊆B := fun v hv => (mem_filter.mp hv).2.1
    have h := card_lt_card proper
    have b := card_le_card tb
    rw [cb.size] at b
    rw [cm.size]
    omega
  obtain ⟨v,vm,out⟩ : ∃v∈M,v∉J := by
    by_contra! allIn
    exact smallJ.not_ge (card_le_card allIn)
  obtain ⟨u,hu⟩ := card_pos.mp (show 0<(inN H M v).card by have h : (inN H M v).card=1 := cm.incoming v vm; omega)
  obtain ⟨um,uv⟩ := mem_inN.mp hu
  have oldArc : graph X.D F u v=true := by simpa [H,edit,out] using uv
  obtain ⟨A,hit⟩ := active.mp oldArc
  obtain ⟨af,ua,va,raw⟩ := mem_col.mp hit
  have off : M∉F := fun mf => Bool.noConfusion (missing.symm.trans
    (active.mpr ⟨M,mem_col.mpr ⟨mf,im,jm,ij⟩⟩))
  have boundary : Boundary X F M := ⟨mem_filter.mpr ⟨mem_powerset.mpr cd.sub,cd⟩,off,A,af,
    u,mem_inter.mpr ⟨ua,um⟩,v,mem_inter.mpr ⟨va,vm⟩,raw⟩
  exact (card_lt_card proper).not_ge ((least M boundary).trans (card_le_card inside))

/-- At a boundary cycle minimizing the number of new heads, every proper subset
of those heads can be attached simultaneously while preserving SmallRow. -/
theorem proper_edit {q n} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    {F B} (old : SmallRow q (graph X.D F) X.V) (step : Boundary X F B)
    (least : ∀M,Boundary X F M → (targets X.D X.V F B).card≤(targets X.D X.V F M).card)
    {J} (proper : J ⊂ targets X.D X.V F B) : SmallRow q (edit X.D F B J) X.V := by
  classical
  let H := edit X.D F B J
  by_cases empty : J=∅
  · have eq : edit X.D F B J=graph X.D F := by funext u v; simp [edit,empty]
    simpa only [eq] using old
  obtain ⟨j,jj⟩ := nonempty_iff_ne_empty.mpr empty
  obtain ⟨jv,jb,i,ib,ij,missing⟩ := mem_filter.mp (proper.subset jj)
  have cb : Cycle X.D X.V q B := (mem_filter.mp step.1).2
  have edge : H i j=true := by
    simpa [H,edit,jj] using (active.mpr ⟨B,mem_col.mpr ⟨mem_insert_self B F,ib,jb,ij⟩⟩ :
      graph X.D (insert B F) i j=true)
  have sub {a b} (ab : H a b=true) : X.D a b=true := by
    by_cases h : b∈J <;> simp only [H,edit,h,ite_true,ite_false] at ab <;> exact native ab
  have lift {u v l} (walk : Walk H X.V u v l) : Walk X.D X.V u v l := by
    induction walk with
    | refl => exact .refl _
    | step v ed _ ih => exact .step v (sub ed) ih
  have free : QFree H X.V q := fun u l lo hi walk => X.free u l lo hi (lift walk)
  by_contra bad
  obtain ⟨M,cm,im,jm⟩ := cycle_at_arc hq small free bad (cb.sub ib) jv edge
  exact no_cycle_edit X hq step least proper ij missing cm im jm

/-- The same old dual pays all the new columns except the prescribed one.
When the full attachment is strict that one column exceeds one. -/
theorem omit_one {q n} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    {F B} (old : SmallRow q (graph X.D F) X.V) (step : Boundary X F B)
    (least : ∀M,Boundary X F M → (targets X.D X.V F B).card≤(targets X.D X.V F M).card)
    (bad : ¬SmallRow q (graph X.D (insert B F)) X.V) {e} (et : e∈targets X.D X.V F B) :
    ∃p, RealDual q (graph X.D F) X.V 1 p ∧
      (∀v∈X.V,v≠e → realCol q (graph X.D (insert B F)) X.V p v≤1) ∧
      1<realCol q (graph X.D (insert B F)) X.V p e := by
  classical
  let T := targets X.D X.V F B
  let J := T.erase e
  have less : J ⊂ T := erase_ssubset et
  obtain ⟨p,dual⟩ := realDual_of_smallRow (proper_edit X hq small old step least less) X.live
  have cb : Cycle X.D X.V q B := (mem_filter.mp step.1).2
  have on {v} (vv : v∈X.V) (jv : v∈J) : realCol q (graph X.D (insert B F)) X.V p v≤1 := by
    simpa [realCol,realInW,edit,jv] using dual.columns v vv
  have off {v} (vv : v∈X.V) (jv : v∉J) : realCol q (graph X.D F) X.V p v≤1 := by
    simpa [realCol,realInW,edit,jv] using dual.columns v vv
  have oldDual : RealDual q (graph X.D F) X.V 1 p := by
    refine ⟨dual.nonneg,dual.normalized,fun v vv => ?_⟩
    by_cases jv : v∈J
    · obtain ⟨u,ub,_,_,_,col⟩ := (column (q:=q) (F:=F) cb p vv).2 (mem_erase.mp jv).2
      have cap := on vv jv
      rw [col] at cap
      linarith [mul_nonneg (Nat.cast_nonneg (α:=ℝ) q) (dual.nonneg u (cb.sub ub))]
    · exact off vv jv
  have other (v) (vv : v∈X.V) (ne : v≠e) : realCol q (graph X.D (insert B F)) X.V p v≤1 := by
    by_cases vt : v∈T
    · exact on vv (mem_erase.mpr ⟨ne,vt⟩)
    · rw [(column (q:=q) (F:=F) cb p vv).1 vt]
      exact oldDual.columns v vv
  refine ⟨p,oldDual,other,?_⟩
  by_contra! cap
  apply bad
  refine smallRow_of_realDual ⟨dual.nonneg,dual.normalized,fun v vv => ?_⟩
  by_cases eq : v=e
  · simpa [eq] using cap
  · exact other v vv eq

theorem select {q n} (X : Model q n) {F} (next : ∃B,Boundary X F B) :
    ∃B,Boundary X F B ∧ ∀M,Boundary X F M →
      (targets X.D X.V F B).card≤(targets X.D X.V F M).card := by
  classical
  let pool := (family X).filter (Boundary X F)
  obtain ⟨B,b⟩ := next
  obtain ⟨M,mm,least⟩ := pool.exists_min_image (fun A => (targets X.D X.V F A).card)
    ⟨B,mem_filter.mpr ⟨b.1,b⟩⟩
  exact ⟨M,(mem_filter.mp mm).2,fun A a => least A (mem_filter.mpr ⟨a.1,a⟩)⟩

/-- A different choice of omitted head can force a genuinely different
old dual. In particular, a unique old dual allows only one changed head. -/
theorem unique_old {q n} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    {F B} (old : SmallRow q (graph X.D F) X.V) (step : Boundary X F B)
    (least : ∀M,Boundary X F M → (targets X.D X.V F B).card≤(targets X.D X.V F M).card)
    (bad : ¬SmallRow q (graph X.D (insert B F)) X.V)
    (unique : ∀p r,RealDual q (graph X.D F) X.V 1 p → RealDual q (graph X.D F) X.V 1 r →
      ∀v∈X.V,p v=r v) : (targets X.D X.V F B).card≤1 := by
  classical
  apply card_le_one.mpr
  intro e he f hf
  by_contra ne
  have ev := (mem_filter.mp he).1
  obtain ⟨p,hp,_,high⟩ := omit_one X hq small old step least bad he
  obtain ⟨r,hr,pays,_⟩ := omit_one X hq small old step least bad hf
  have same := unique p r hp hr
  have col : realCol q (graph X.D (insert B F)) X.V p e=realCol q (graph X.D (insert B F)) X.V r e := by
    simp only [realCol,realInW,same e ev]
    congr 2
    apply sum_congr rfl
    intro v vv
    rw [same v vv]
  exact high.not_ge (col ▸ pays e ev ne)

/-- One common inverse of the strict child prices every changed arc above
the exact deletion threshold. It is the inverse on the actual child. -/
theorem charges {q n} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    {F B} (old : SmallRow q (graph X.D F) X.V) (step : Boundary X F B)
    (least : ∀M,Boundary X F M → (targets X.D X.V F B).card≤(targets X.D X.V F M).card)
    (bad : ¬SmallRow q (graph X.D (insert B F)) X.V) :
    ∃H : Matrix X.V X.V ℝ,FiniteCutInverse.CommonInverse (realMatrix q (graph X.D (insert B F)) X.V) H ∧
      ∀a b : X.V,(a:ℕ)∈B → (b:ℕ)∈B → X.D a b=true → graph X.D F a b=false → 1≤(q:ℝ)*H b a := by
  classical
  let G := graph X.D (insert B F)
  have free := PrivateArcEndpoints.graph_free X (insert B F)
  obtain ⟨w,wn,_,hi⟩ := strict_witness_of_not_smallRow bad
  obtain ⟨H,inv⟩ := strict_inverse_of_proper_smallRow (small.induced free) w wn hi
  refine ⟨H,inv,?_⟩
  intro a b ab bb uv no
  have cb : Cycle X.D X.V q B := (mem_filter.mp step.1).2
  have edge : G a b=true := active.mpr ⟨B,mem_col.mpr ⟨mem_insert_self B F,ab,bb,uv⟩⟩
  have bt : (b:ℕ)∈targets X.D X.V F B := mem_filter.mpr ⟨b.property,bb,a,ab,uv,no⟩
  obtain ⟨p,dual,pays,_⟩ := omit_one X hq small old step least bad bt
  apply (deletion_smallRow_iff inv a b edge).mp
  refine smallRow_of_realDual ⟨dual.nonneg,dual.normalized,fun v vv => ?_⟩
  have er := realCol_eraseArc (q:=q) a.property edge p v
  by_cases eq : v=b
  · subst v
    obtain ⟨i,ib,_,ibarc,_,bill⟩ := (column (q:=q) (F:=F) cb p b.property).2 bt
    have one : (inN X.D B b).card≤1 := (cb.incoming b bb).le
    have same : i=(a:ℕ) := card_le_one.mp one _ (mem_inN.mpr ⟨ib,ibarc⟩) _ (mem_inN.mpr ⟨ab,uv⟩)
    change realCol q G X.V p b = _ at bill
    rw [same] at bill
    simp only [ite_true,eq_self] at er
    linarith [dual.columns b b.property]
  · simp only [eq,ite_false,add_zero] at er
    exact er ▸ pays v vv eq

/-- Each individual changed head carries at least the full row margin.
Hence the number of changed heads multiplies the earlier mass floor. -/
theorem mass_floor {q n} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    {F B} (old : SmallRow q (graph X.D F) X.V) (step : Boundary X F B)
    (least : ∀M,Boundary X F M → (targets X.D X.V F B).card≤(targets X.D X.V F M).card)
    (bad : ¬SmallRow q (graph X.D (insert B F)) X.V)
    (sub : F⊆family X) (spans : support F=X.V) {x c}
    (xm : realMass X.V x=1) (xp : ∀v∈X.V,0<x v) (rows : ∀v∈X.V,realRow q (graph X.D (insert B F)) X.V x v=c) :
    let T := targets X.D X.V F B
    (∀e∈T,c-1≤x e) ∧ (T.card:ℝ)*(c-1)≤realMass T x := by
  classical
  intro T
  let G := graph X.D (insert B F)
  have cb : Cycle X.D X.V q B := (mem_filter.mp step.1).2
  have each (e) (et : e∈T) : c-1≤x e := by
    have ev := (mem_filter.mp et).1
    obtain ⟨p,dual,other,_⟩ := omit_one X hq small old step least bad et
    let val := realCol q G X.V p
    have total : (∑v∈X.V,x v*val v)=c := by
      rw [←real_cross_rows]
      calc
        _ = ∑i∈X.V,p i*c := sum_congr rfl (fun i iv => by rw [rows i iv])
        _ = c := by rw [←sum_mul]; change realMass X.V p*c=c; rw [dual.normalized,one_mul]
    obtain ⟨u,ub,_,_,_,bill⟩ := (column (q:=q) (F:=F) cb p ev).2 et
    obtain ⟨M,mf,um⟩ := mem_biUnion.mp (spans.symm ▸ cb.sub ub : u∈support F)
    have cm : Cycle X.D X.V q M := (mem_filter.mp (sub mf)).2
    obtain ⟨j,jh⟩ := card_pos.mp (show 0<(outN X.D M u).card by rw [cm.heads u um]; decide)
    obtain ⟨jm,uj⟩ := mem_outN.mp jh
    have kept : graph X.D F u j=true := active.mpr ⟨M,mem_col.mpr ⟨mf,um,jm,uj⟩⟩
    have tail := (realCol_edge_floor (q:=q) p dual.nonneg (cb.sub ub) (cm.sub jm) kept).trans (dual.columns j (cm.sub jm))
    have limit : val e≤2 := by change realCol q (graph X.D (insert B F)) X.V p e≤2; rw [bill]; linarith [dual.columns e ev]
    have rest := sum_le_sum (s:=X.V.erase e) (fun v hv => mul_le_mul_of_nonneg_left
      (other v (mem_erase.mp hv).2 (mem_erase.mp hv).1) (xp v (mem_erase.mp hv).2).le)
    simp only [mul_one] at rest
    have split := sum_erase_add X.V (fun v => x v*val v) ev
    have splitM := sum_erase_add X.V x ev
    change _+_=realMass X.V x at splitM
    rw [total] at split
    rw [xm] at splitM
    have cap := mul_le_mul_of_nonneg_left limit (xp e ev).le
    change (∑v∈X.V.erase e,x v*val v)≤_ at rest
    linarith
  refine ⟨each,?_⟩
  simpa only [realMass,sum_const,nsmul_eq_mul] using (sum_le_sum (s:=T) (fun v hv => each v hv))

#print axioms unique_old
#print axioms charges
#print axioms mass_floor

#print axioms omit_one
#print axioms select

#print axioms cycle_at_arc
#print axioms no_cycle_edit
#print axioms proper_edit
end LeanCH.BR.Closure.SharedArcMinimalPacket
