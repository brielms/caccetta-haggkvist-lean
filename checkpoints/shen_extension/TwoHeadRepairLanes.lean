import checkpoints.shen_extension.SoleExitWeightGap
import checkpoints.shen_extension.EndpointPrivateRows
import checkpoints.shen_extension.TwoExitOverlapCap

namespace LeanCH.BR.Closure.TwoHeadRepairLanes
open Finset BRq2 BRq3 BR45 WeightedSD CommonParentHeadRepair CommonParentReplay LabelledLeakageCapacity

theorem nested {q E H s t} (path : Relation.ReflTransGen (Edge q E H) s t) :
    s.heads⊆t.heads ∧ t.carrier⊆s.carrier := by
  induction path with
  | refl => exact ⟨Subset.rfl,Subset.rfl⟩
  | tail _ edge ih =>
    cases edge with
    | @repair W K L w z step =>
      obtain ⟨_,_,_,_,_,_,_,_,k,_,_,eq⟩ := step
      change L=insert k K at eq
      exact ⟨ih.1.trans (eq.symm ▸ subset_insert _ _),ih.2⟩
    | cut _ _ _ => exact ⟨ih.1,sdiff_subset.trans ih.2⟩

/-- Retaining one seed and cutting the other permanently separates even
descendants reached by a mixture of repairs and cuts. -/
theorem no_join {q E H} {s t : CommonParentReplay.State} {x : ℕ} (xs : x∈s.heads) (xt : x∉t.carrier)
    (sub : t.heads⊆t.carrier) {u : CommonParentReplay.State} (left : Relation.ReflTransGen (Edge q E H) s u)
    (right : Relation.ReflTransGen (Edge q E H) t u) : False := by
  have keeps {A B : CommonParentReplay.State} (p : Relation.ReflTransGen (Edge q E H) A B) (h : A.heads⊆A.carrier) :
      B.heads⊆B.carrier := by
    induction p with
    | refl => exact h
    | tail _ edge ih =>
      cases edge with
      | @repair W K L w z step =>
        obtain ⟨_,_,_,_,_,_,_,_,k,hit,_,eq⟩ := step
        change L=insert k K at eq
        exact eq.symm ▸ insert_subset (mem_outN.mp hit).1 ih
      | cut _ _ kept => exact kept
  exact xt ((nested right).2 (keeps right sub ((nested left).1 xs)))

/-- Raise one head missed by the paying row. Both empty-to-singleton steps
use this very row and the same increased prices. -/
theorem open_seeds {q E V H i} (hq : 3≤q) (hs : H⊆V)
    (ir : i∈BRsub.ballSet E V H (q-2)) (ih : i∉H) (free : QFree E V q)
    (w : ℕ→ℚ) (pos : ∀v∈V,0<w v) :
    ∃z : ℕ→ℚ,(∀v∈V,0<z v) ∧ mass V z<q*mass H z ∧
      WeightedSD.row q E V z i≤mass V z ∧
      ∀k∈outN E V i,CommonParentHeadRepair.Step q E V H (∅,w) ({k},z) := by
  classical
  obtain ⟨h,hh,reach⟩ := BRsub.mem_ballSet.mp ir
  have miss := no_back_arc free (hs hh) reach (by omega)
  have ne : i≠h := fun e=>ih (e ▸ hh)
  let L := mass V w+|WeightedSD.row q E V w i|+1
  let z := fun v=>w v+(if v=h then L else 0)
  have nn := mass_nonneg (fun v hv=>(pos v hv).le)
  have big : mass V w<L := by dsimp [L]; linarith [abs_nonneg (WeightedSD.row q E V w i)]
  have lp : 0<L := nn.trans_lt big
  have same (S : Finset ℕ) : mass S z=mass S w+(if h∈S then L else 0) := by
    simp [mass,z,sum_add_distrib]
  have hz : mass H z=mass H w+L := by simpa [hh] using same H
  have vz : mass V z=mass V w+L := by simpa [hs hh] using same V
  have heavy : mass V z<q*mass H z := by
    rw [vz,hz]
    have q2 : (2:ℚ)≤q := by exact_mod_cast (show 2≤q by omega)
    nlinarith [mul_le_mul_of_nonneg_right q2 lp.le,
      mul_nonneg (Nat.cast_nonneg q : (0:ℚ)≤q) (mass_nonneg (fun v hv=>(pos v (hs hv)).le))]
  have inc (v) : w v≤z v := by simp [z]; split_ifs <;> linarith
  have positive (v) (vv : v∈V) := (pos v vv).trans_le (inc v)
  have no : h∉outN E V i := fun e=>miss (mem_outN.mp e).2
  have row : WeightedSD.row q E V z i=WeightedSD.row q E V w i := by
    simp only [WeightedSD.row,outW_eq_mass,same,no,ite_false,add_zero]
    simp [z,ne]
  have low : WeightedSD.row q E V z i≤mass V z := by
    rw [row,vz]; dsimp [L]; linarith [le_abs_self (WeightedSD.row q E V w i)]
  refine ⟨z,positive,heavy,low,fun k hit=>?_⟩
  exact ⟨fun v _=>inc v,positive,heavy,by simp,i,ir,Or.inl low,by simp,k,hit,by simp,by simp⟩

def Lane (q : ℕ) (E : CH.Digraph) (V H R : Finset ℕ) (a x y : ℕ) (z : ℕ→ℚ) : Prop :=
  let U := V\{a,y}
  let s : CommonParentReplay.State := ⟨U,{x},z⟩
  Edge q E H ⟨V,{x},z⟩ s ∧
    ∃T v, Relation.ReflTransGen (Edge q E H) s ⟨U,T,v⟩ ∧
      x∈T ∧ y∉U ∧ T⊆U ∧ T.card+1=q ∧ Checks q E H R U ⟨U,T,v⟩ ∧
      ((EndpointPrivateRows.Covers E R T ∧ T\R={x} ∧ (∀r∈R,E x r=false) ∧
        ∃t : CommonParentReplay.State,Relation.ReflTransGen (Edge q E H) ⟨U,T,v⟩ t ∧
          t.carrier=insert x R ∧ t.heads=T ∧ t.weights=v ∧ outN E t.carrier x=∅ ∧
          Checks q E H R U t) ∨
       ∃r∈R,(∀k∈T,E r k=false) ∧ ∃j∈outN E U r,j∉T ∧
         (let W := R ∪ insert j T
          Relation.ReflTransGen (Edge q E H) ⟨U,T,v⟩ ⟨W,T,v⟩ ∧ Checks q E H R U ⟨W,T,v⟩ ∧
            (W=U ∨ W⊂U ∧ Edge q E H ⟨U,T,v⟩ ⟨W,T,v⟩)) ∧
         EndpointPrivateRows.Tests q E U H R T v)

theorem lane {q E V H R a x y} (hq : 3≤q) (free : QFree E V q)
    (small : SmallerSmallRow q V.card) (ay : a≠y)
    (cut : ({a,y}:Finset ℕ)⊆V\R) (xs : x∈V\{a,y}) (xr : x∉R)
    (hs : H⊆V\{a,y}) (hl : H.Nonempty) (same : R=BRsub.ballSet E V H (q-2))
    (live : ∀r∈R,(outN E (V\{a,y}) r).Nonempty)
    (z : ℕ→ℚ) (zp : ∀i∈V,0<z i) (heavy : mass V z<q*mass H z) :
    Lane q E V H R a x y z := by
  classical
  let U := V\{a,y}
  have us : U⊆V := sdiff_subset
  have bs : BRsub.ballSet E U H (q-2)=R := same ▸ RankedMerge.ball_delete (same ▸ cut)
  have room : U.card+1<V.card := by
    have sub : ({a,y}:Finset ℕ)⊆V := cut.trans sdiff_subset
    dsimp [U]; rw [card_sdiff_of_subset sub,card_pair ay]
    have le := card_le_card sub
    rw [card_pair ay] at le; omega
  have valid : CommonParentReplay.Valid q E H R U ⟨U,{x},z⟩ := ⟨Subset.rfl,hs,singleton_subset_iff.mpr xs,
    fun i hi=>zp i (us hi),(mass_mono us (fun i hi=>(zp i hi).le)).trans_lt heavy,bs⟩
  obtain ⟨T,v,ts,path,count|⟨r,rr,dead⟩⟩ :=
    iterate (by omega : 2≤q) (free.mono_set us) small room hs hl {x} (singleton_subset_iff.mpr xs)
      (by simp; omega) z valid.positive
  · let st := fun p : Finset ℕ × (ℕ→ℚ)=>CommonParentReplay.State.mk U p.1 p.2
    have edges := path.lift st (fun _ _ e=>Edge.repair e)
    have xt := (nested edges).1 (mem_singleton_self x)
    have exterior : ({a,y}:Finset ℕ)⊆V\CommonParentReplay.ball q E H V := by
      change _⊆V\BRsub.ballSet E V H (q-2)
      rw [←same]; exact cut
    refine ⟨Edge.cut ⟨a,mem_insert_self _ _⟩ exterior (singleton_subset_iff.mpr xs),
      T,v,edges,xt,by simp,ts,count,replay (by omega) (free.mono_set us) small room hl valid edges,?_⟩
    by_cases cov : EndpointPrivateRows.Covers E R T
    · obtain ⟨_,_,_,_,p,_,_,_,_,one,_,_,sink⟩ := CommonParentEndpointPath.full_cover
        (by omega : 2≤q) (free.mono_set us) hs hl ts (by omega) (bs.symm ▸ cov)
      rw [bs] at one sink
      have ex := mem_singleton.mp (one ▸ mem_sdiff.mpr ⟨xt,xr⟩)
      have atEnd := (replay (by omega : 2≤q) (free.mono_set us) small room hl valid edges).1
      obtain ⟨k,kt,kr,t,reach,heads,weights,only,dead,tests,_⟩ :=
        CommonParentEndpointPath.replay_one_exterior (by omega : 2≤q) (free.mono_set us) small room hl
          atEnd (by change T.card<q; omega) cov
      have kx : k=x := (mem_singleton.mp (one ▸ mem_sdiff.mpr ⟨kt,kr⟩)).trans ex.symm
      subst k
      have subR : R⊆t.carrier := tests.1.same ▸ BRsub.ballSet_subset
      exact Or.inl ⟨cov,by rw [one,←ex],fun r rr=>Bool.eq_false_iff.mpr (ex.symm ▸ sink r rr),
        t,reach,DeadExit.carrier_eq subR only,heads,weights,dead,tests⟩
    · unfold EndpointPrivateRows.Covers at cov
      push Not at cov
      obtain ⟨r,rr,miss⟩ := cov
      obtain ⟨j,hit⟩ := live r rr
      have validEnd := (replay (by omega : 2≤q) (free.mono_set us) small room hl valid edges).1
      refine Or.inr ⟨r,rr,fun k kt=>by simpa using miss k kt,j,hit,
        fun jt=>miss j jt (mem_outN.mp hit).2,
        CommonParentEndpointReplay.retain_fresh (by omega) (free.mono_set us) small room hl validEnd
          (mem_outN.mp hit).1,?_⟩
      rw [←bs]
      intro r₀ rr₀ miss₀ x' hit' out'
      exact EndpointPrivateRows.at_exterior (by omega) (free.mono_set us) small room hs hl ts count
        validEnd.positive validEnd.heavy (fun t ht=>live t (bs ▸ ht)) rr₀ miss₀ hit' out'
  · exact False.elim ((live r (bs ▸ rr)).ne_empty dead)

theorem live_after_two {q E V w c} (hq : 3≤q)
    (wp : ∀i∈V,0<w i) (flat : ∀i∈V,WeightedSD.row q E V w i=c) (high : 1<c)
    (cap : ∀i∈V,(q:ℚ)^2*w i≤1) {a y r} (av : a∈V) (yv : y∈V) (ay : a≠y) (rv : r∈V) :
    (outN E (V\{a,y}) r).Nonempty := by
  classical
  by_contra! dead
  have sub : outN E V r⊆{a,y} := by
    intro k kk
    by_contra off
    have hit : k∈outN E (V\{a,y}) r := mem_outN.mpr ⟨mem_sdiff.mpr ⟨(mem_outN.mp kk).1,off⟩,(mem_outN.mp kk).2⟩
    simp [dead] at hit
  have ss : ({a,y}:Finset ℕ)⊆V := insert_subset av (singleton_subset_iff.mpr yv)
  have m := mass_mono sub (fun i hi=>(wp i (ss hi)).le)
  have pair : mass {a,y} w=w a+w y := sum_pair ay
  rw [pair] at m
  have row := flat r rv
  rw [WeightedSD.row,outW_eq_mass] at row
  have non : (0:ℚ)≤q := Nat.cast_nonneg q
  have upper : c≤w r+(q:ℚ)*(w a+w y) := by linarith [mul_le_mul_of_nonneg_left m non]
  have sum : (q:ℚ)^2*(w a+w y)≤2 := by nlinarith only [cap a av,cap y yv]
  have three : (3:ℚ)≤q := by exact_mod_cast hq
  nlinarith only [mul_le_mul_of_nonneg_left upper (sq_nonneg (q:ℚ)),
    mul_le_mul_of_nonneg_left sum non,cap r rv,mul_lt_mul_of_pos_left high (sq_pos_of_pos (by linarith : (0:ℚ)<q)),
    mul_nonneg (sub_nonneg.mpr three) (by linarith : (0:ℚ)≤q+1),three]

/-- Repair from the specified native row and root. All pairs use one repricing. -/
def OpposedFrom (q : ℕ) (E : CH.Digraph) (V : Finset ℕ) (w : ℕ→ℚ) (a i : ℕ) : Prop :=
  let H := outN E V a
  let R := region q E V a
  let O := outN E (V\R) i
  ∃z : ℕ→ℚ,WeightedSD.row q E V z i≤mass V z ∧
    (∀x∈O,CommonParentHeadRepair.Step q E V H (∅,w) ({x},z)) ∧
    ∀x∈O,∀y∈O,x≠y →
      Lane q E V H R a x y z ∧ Lane q E V H R a y x z ∧
      ∀t : CommonParentReplay.State,¬(Relation.ReflTransGen (Edge q E H) ⟨V\{a,y},{x},z⟩ t ∧
        Relation.ReflTransGen (Edge q E H) ⟨V\{a,x},{y},z⟩ t)

def Packet (q : ℕ) (E : CH.Digraph) (V : Finset ℕ) (w : ℕ→ℚ) (c : ℚ) : Prop :=
  ∃a∈V,let R := region q E V a
       ∃i∈R,let O := outN E (V\R) i
            c-mass R w≤q*mass O w ∧ 2≤O.card ∧ OpposedFrom q E V w a i

theorem at_row {q E V w c a i} (hq : 3≤q) (free : QFree E V q) (sat : BRsub.Sat q E V)
    (small : SmallerSmallRow q V.card) (wp : ∀a∈V,0<w a) (high : 1<c)
    (rows : ∀a∈V,WeightedSD.row q E V w a=c) (cap : ∀a∈V,(q:ℚ)^2*w a≤1)
    (av : a∈V) (ir : i∈region q E V a) (size : 2≤(outN E (V\region q E V a) i).card) :
    OpposedFrom q E V w a i := by
  classical
  let H := outN E V a
  let R := region q E V a
  let O := outN E (V\R) i
  change 2≤O.card at size
  have rs : R⊆V := BRsub.ballSet_subset
  have hl : H.Nonempty := by obtain ⟨h,hh,_⟩ := BRsub.mem_ballSet.mp ir; exact ⟨h,hh⟩
  have head (x) (xx : x∈O) :
      x∈V ∧ x∉R ∧ x≠a ∧ E x a=true ∧ E i x=true := by
    obtain ⟨xd,edge⟩ := mem_outN.mp xx
    obtain ⟨xv,xr⟩ := mem_sdiff.mp xd
    have roots : a∈V.filter (fun v=>i∈region q E V v ∧ x∉region q E V v) := mem_filter.mpr ⟨av,ir,xr⟩
    rw [crossing (by omega : 2≤q) free sat (rs ir) xv edge] at roots
    have xa := (mem_outN.mp (mem_sdiff.mp roots).1).2
    exact ⟨xv,xr,fun eq=>loopfree free (by omega) av (eq ▸ xa),xa,edge⟩
  have notH : i∉H := by
    intro ih
    obtain ⟨x,xx⟩ := card_pos.mp (show 0<O.card by omega)
    obtain ⟨xv,xr,_,_,edge⟩ := head x xx
    exact xr (BRsub.mem_ballSet.mpr ⟨i,ih,ball_mono_radius (by omega : 1≤q-2) (ball_of_adj xv edge)⟩)
  obtain ⟨z,zp,heavy,low,seeds⟩ := open_seeds hq (H:=H) outN_subset ir notH free w wp
  have ar : a∉R := fun e=>(saturated_region (by omega) free sat av av |>.mp e).1 rfl
  have make (x) (xx : x∈O) (y) (yy : y∈O) (ne : x≠y) : Lane q E V H R a x y z := by
    obtain ⟨xv,xr,xa,_,_⟩ := head x xx
    obtain ⟨yv,yr,ya,_,_⟩ := head y yy
    have cut : ({a,y}:Finset ℕ)⊆V\R := insert_subset (mem_sdiff.mpr ⟨av,ar⟩)
      (singleton_subset_iff.mpr (mem_sdiff.mpr ⟨yv,yr⟩))
    have hs : H⊆V\{a,y} := by
      intro h hh
      have rh : h∈R := BRsub.subset_ballSet (Y:=H) outN_subset hh
      exact mem_sdiff.mpr ⟨rs rh,fun hk=>(mem_sdiff.mp (cut hk)).2 rh⟩
    exact lane hq free small ya.symm cut (by simp [xv,xa,ne]) xr hs hl rfl
      (fun r rr=>live_after_two hq wp rows high cap av yv ya.symm (rs rr)) z zp heavy
  refine ⟨z,low,fun x xx=>seeds x (mem_outN.mpr ⟨(head x xx).1,(head x xx).2.2.2.2⟩),?_⟩
  intro x xx y yy ne
  refine ⟨make x xx y yy ne,make y yy x xx ne.symm,?_⟩
  rintro t ⟨left,right⟩
  exact no_join (x:=x) (mem_singleton_self _) (by simp)
    (singleton_subset_iff.mpr (by simp [(head y yy).1,(head y yy).2.2.1,ne.symm])) left right

theorem paired {q E V w p c} (hq : 3≤q) (free : QFree E V q) (sat : BRsub.Sat q E V)
    (small : SmallerSmallRow q V.card) (wp : ∀a∈V,0<w a) (pp : ∀a∈V,0<p a)
    (wm : mass V w=1) (pm : mass V p=1) (high : 1<c)
    (rows : ∀a∈V,WeightedSD.row q E V w a=c) (cols : ∀a∈V,WeightedSD.col q E V p a=c)
    (cap : ∀a∈V,(q:ℚ)^2*w a≤1) : Packet q E V w c := by
  classical
  obtain ⟨a,av,_,i,ir,bill,size⟩ := SoleExitWeightGap.diffuse_witness hq free sat small wp pp wm pm high rows cols cap
  exact ⟨a,av,i,ir,bill,size,at_row hq free sat small wp high rows cap av ir size⟩

def NativeResult {q n} (X : ShortestCycleWeights.Model q n) : Prop :=
  ∃ (w : ℕ→ℚ) (c : ℚ),mass X.V w=1 ∧ 1<c ∧ (∀i∈X.V,0<w i) ∧
    (∀i∈X.V,WeightedSD.row q X.D X.V w i=c) ∧
    ((∃h∈X.V,1<(q:ℚ)^2*w h) ∨ ((∀a∈X.V,(q:ℚ)^2*w a≤1) ∧ Packet q X.D X.V w c))

theorem native {q n} (X : ShortestCycleWeights.Model q n) (hq : 3≤q)
    (small : SmallerSmallRow q X.V.card) : NativeResult X := by
  classical
  obtain ⟨w,p,c,high,wp,pp,wm,pm,rows,cols⟩ := strict_pair_of_proper_smallRow
    (small.induced X.free) X.live (fun i=>(X.weights i : ℚ)) (fun _ _=>Nat.cast_nonneg _) X.strict
  refine ⟨w,c,wm,high,wp,rows,?_⟩
  by_cases cap : ∀a∈X.V,(q:ℚ)^2*w a≤1
  · exact Or.inr ⟨cap,paired hq X.free X.sat small wp pp wm pm high rows cols cap⟩
  · push Not at cap; exact Or.inl cap

#print axioms no_join
#print axioms at_row
#print axioms paired
#print axioms native
end LeanCH.BR.Closure.TwoHeadRepairLanes
