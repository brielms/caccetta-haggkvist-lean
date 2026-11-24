import checkpoints.shen_extension.TwoHeadRepairLanes

namespace LeanCH.BR.Closure.TwoHeadRepairReplay
open Finset BRq2 BRq3 BR45 WeightedSD CommonParentReplay LabelledLeakageCapacity TwoHeadRepairLanes

structure Seeds (q : ℕ) (E : CH.Digraph) (V : Finset ℕ) (w : ℕ→ℚ) (c : ℚ) where
  a : ℕ
  i : ℕ
  x : ℕ
  y : ℕ
  price : ℕ→ℚ
  diffuse : ∀a∈V,(q:ℚ)^2*w a≤1
  av : a∈V
  ir : i∈region q E V a
  xhit : x∈outN E (V\region q E V a) i
  yhit : y∈outN E (V\region q E V a) i
  ne : x≠y
  bill : c-mass (region q E V a) w≤q*mass (outN E (V\region q E V a) i) w
  low : WeightedSD.row q E V price i≤mass V price
  first : ∀j∈({x,y}:Finset ℕ),CommonParentHeadRepair.Step q E V (outN E V a) (∅,w) ({j},price)

def Missed (q : ℕ) (E : CH.Digraph) (V H R : Finset ℕ) (a x y : ℕ) (z : ℕ→ℚ) : Prop :=
  let U := V\{a,y}
  ∃ T v,Relation.ReflTransGen (Edge q E H) ⟨U,{x},z⟩ ⟨U,T,v⟩ ∧ x∈T ∧ T.card+1=q ∧
    Checks q E H R U ⟨U,T,v⟩ ∧ ∃r∈R,(∀k∈T,E r k=false) ∧ ∃j∈outN E U r,j∉T ∧
      (let W := R ∪ insert j T
       Relation.ReflTransGen (Edge q E H) ⟨U,T,v⟩ ⟨W,T,v⟩ ∧ Checks q E H R U ⟨W,T,v⟩ ∧
         (W=U ∨ W⊂U ∧ Edge q E H ⟨U,T,v⟩ ⟨W,T,v⟩)) ∧ EndpointPrivateRows.Tests q E U H R T v

def ExitChild (q : ℕ) (E : CH.Digraph) (V H R : Finset ℕ) (a x y : ℕ) (z : ℕ→ℚ) : Prop :=
  let U := V\{a,y}
  ∃t : CommonParentReplay.State,Relation.ReflTransGen (Edge q E H) ⟨U,{x},z⟩ t ∧
    t.carrier=insert x R ∧ x∈t.heads ∧ t.heads.card+1=q ∧
    EndpointPrivateRows.Covers E R t.heads ∧ t.heads\R={x} ∧ outN E t.carrier x=∅ ∧
    Checks q E H R U t ∧ ∀v∈insert x R,E x v=false

theorem replay_lane {q E V H R a x y z} (l : Lane q E V H R a x y z) :
    Missed q E V H R a x y z ∨ ExitChild q E V H R a x y z := by
  obtain ⟨_,T,v,path,xt,_,_,cnt,ch,covered|miss⟩ := l
  · obtain ⟨cov,one,_,t,reach,car,heads,_,dead,test⟩ := covered
    right
    refine ⟨t,path.trans reach,car,heads.symm ▸ xt,heads.symm ▸ cnt,heads.symm ▸ cov,heads.symm ▸ one,dead,test,?_⟩
    intro j jv
    apply Bool.eq_false_iff.mpr
    intro hit
    have jo : j∈outN E t.carrier x := mem_outN.mpr ⟨car.symm ▸ jv,hit⟩
    simp [dead] at jo
  · exact Or.inl ⟨T,v,path,xt,cnt,ch,miss⟩

def Missing {q E V w c} (s : Seeds q E V w c) : Prop :=
  let H := outN E V s.a
  let R := region q E V s.a
  Missed q E V H R s.a s.x s.y s.price ∨ Missed q E V H R s.a s.y s.x s.price

def Covered {q E V w c} (s : Seeds q E V w c) : Prop :=
  let H := outN E V s.a
  let R := region q E V s.a
  ExitChild q E V H R s.a s.x s.y s.price ∧ ExitChild q E V H R s.a s.y s.x s.price ∧
    TwoExit.TwoExits q E V R H w c s.a s.x s.y ∧
    s.a∈outN E V s.x ∩ outN E V s.y ∧
    (q:ℚ)*mass (insert s.x (outN E V s.x) ∩ insert s.y (outN E V s.y)) w+min (w s.x) (w s.y)≤c

theorem classify {q E V w c} (hq : 3≤q) (free : QFree E V q) (sat : BRsub.Sat q E V)
    (wp : ∀a∈V,0<w a) (high : mass V w<c) (rows : ∀a∈V,WeightedSD.row q E V w a=c)
    (diffuse : ∀a∈V,(q:ℚ)^2*w a≤1) (p : Packet q E V w c) :
    (∃s : Seeds q E V w c,Missing s) ∨ ∃s : Seeds q E V w c,Covered s := by
  classical
  obtain ⟨a,av,i,ir,bill,size,z,low,start,lanes⟩ := p
  let R := region q E V a
  let H := outN E V a
  let O := outN E (V\R) i
  change 2≤O.card at size
  obtain ⟨x,xx,y,yy,ne⟩ := one_lt_card.mp (show 1<O.card by omega)
  let s : Seeds q E V w c := ⟨a,i,x,y,z,diffuse,av,ir,xx,yy,ne,bill,low,fun j hj=>by
    rcases mem_insert.mp hj with rfl|mem
    · exact start _ xx
    · exact mem_singleton.mp mem ▸ start _ yy⟩
  obtain ⟨left,right,_⟩ := lanes x xx y yy ne
  rcases replay_lane left with m|l
  · exact Or.inl ⟨s,Or.inl m⟩
  rcases replay_lane right with m|r
  · exact Or.inl ⟨s,Or.inr m⟩
  have parent (u) (uO : u∈O) : a∈outN E V u := by
    obtain ⟨ud,e⟩ := mem_outN.mp uO
    obtain ⟨uv,off⟩ := mem_sdiff.mp ud
    have roots : a∈V.filter (fun v=>i∈region q E V v ∧ u∉region q E V v) := mem_filter.mpr ⟨av,ir,off⟩
    rw [crossing (by omega : 2≤q) free sat (BRsub.ballSet_subset ir) uv e] at roots
    exact (mem_sdiff.mp roots).1
  have xout := mem_sdiff.mp (mem_outN.mp xx).1
  have yout := mem_sdiff.mp (mem_outN.mp yy).1
  have X : TwoExit.TwoExits q E V R H w c a x y := by
    obtain ⟨_,_,_,_,_,_,_,_,_,deadX⟩ := l
    obtain ⟨_,_,_,_,_,_,_,_,_,deadY⟩ := r
    exact ⟨wp,rows,high,BRsub.ballSet_subset,BRsub.subset_ballSet outN_subset,av,
      fun ar=>(saturated_region (by omega) free sat av av |>.mp ar).1 rfl,
      fun v vv=>⟨fun e=>mem_outN.mpr ⟨vv,e⟩,fun h=>(mem_outN.mp h).2⟩,
      xout.1,yout.1,xout.2,yout.2,ne,
      fun e=>loopfree free (by omega) av (e ▸ (mem_outN.mp (parent x xx)).2),
      fun e=>loopfree free (by omega) av (e ▸ (mem_outN.mp (parent y yy)).2),deadX,deadY⟩
  exact Or.inr ⟨s,l,r,X,mem_inter.mpr ⟨parent x xx,parent y yy⟩,TwoExitOverlapCap.overlap_cap (by omega) free X⟩

def Outcome {q n} (X : ShortestCycleWeights.Model q n) : Prop :=
  ∃w c,mass X.V w=1 ∧ 1<c ∧ (∀i∈X.V,0<w i) ∧ (∀i∈X.V,WeightedSD.row q X.D X.V w i=c) ∧
    ((∃h∈X.V,1<(q:ℚ)^2*w h) ∨ (∃s : Seeds q X.D X.V w c,Missing s) ∨ ∃s : Seeds q X.D X.V w c,Covered s)

theorem on_native {q n} (X : ShortestCycleWeights.Model q n) (hq : 3≤q) (result : NativeResult X) :
    Outcome X := by
  obtain ⟨w,c,wm,hi,wp,rows,choice⟩ := result
  exact ⟨w,c,wm,hi,wp,rows,choice.imp_right (fun ⟨cap,lanes⟩=>classify hq X.free X.sat wp (wm ▸ hi) rows cap lanes)⟩

#print axioms classify
#print axioms on_native

theorem missed_label {q E V w c} {s : Seeds q E V w c} (bad : Missing s) :
    ∃j b, ((j=s.x ∧ b=s.y) ∨ (j=s.y ∧ b=s.x)) ∧
      Missed q E V (outN E V s.a) (region q E V s.a) s.a j b s.price := by
  rcases bad with h|h
  · exact ⟨_,_,Or.inl ⟨rfl,rfl⟩,h⟩
  · exact ⟨_,_,Or.inr ⟨rfl,rfl⟩,h⟩

/-- After both terminal deletions, rerun the actual one-exit native tests on
each child. The two lists use identical w, ball, slack and head gap. -/
theorem covered_labels {q E V w c} {s : Seeds q E V w c} (hq : 3≤q)
    (free : QFree E V q) (small : SmallerSmallRow q V.card) (both : Covered s) :
    let R := region q E V s.a
    let L := TwoExit.leak E V R w
    let Q := (q:ℚ)*(c-mass V w+mass (V\R) w)-c
    let G := (q:ℚ)*mass (outN E V s.a) w-mass R w
    let k := (q:ℚ)-1
    ∀z∈({s.x,s.y}:Finset ℕ),(∃r∈R,E r z=false ∧ Q≤(q:ℚ)*k*L r) ∨
      (∃i∈R,E i z=true ∧ ∃j∈R,E j z=false ∧ Q≤k*(L i+k*L j)) ∨
      ∃i∈R,E i z=true ∧ k^2*G≤(q:ℚ)*k*L i-Q := by
  obtain ⟨l,r,X,_⟩ := both
  let R := region q E V s.a
  let H := outN E V s.a
  have facts {x y} (lane : ExitChild q E V H R s.a x y s.price) (yv : y∈V) (ay : s.a≠y) :
      insert x R⊆V ∧ (insert x R).card+1<V.card ∧ BRsub.ballSet E (insert x R) H (q-2)=R := by
    obtain ⟨t,_,car,_,_,_,_,_,check,_⟩ := lane
    have pair : ({s.a,y}:Finset ℕ)⊆V := insert_subset s.av (singleton_subset_iff.mpr yv)
    have inc := check.1.inside
    rw [car] at inc
    have cutsize := card_sdiff_of_subset pair
    have two := card_le_card pair
    rw [card_pair ay] at two cutsize
    have bound := card_le_card inc
    exact ⟨inc.trans sdiff_subset,by omega,car ▸ check.1.same⟩
  obtain ⟨il,rl,bl⟩ := facts l X.z₂v X.a₂
  obtain ⟨ir,rr,br⟩ := facts r X.z₁v X.a₁
  obtain ⟨h,hh,_⟩ := BRsub.mem_ballSet.mp s.ir
  exact TwoExit.both_exits_labels (by omega) X free small (fun _ _ e=>e) ⟨h,hh⟩ il rl bl ir rr br

/-- The paying row itself enters both exits, for every cutoff. -/
theorem covered_swapped {q E V w c} {s : Seeds q E V w c} (hq : 3≤q) (both : Covered s) :
    let R := region q E V s.a
    let L := TwoExit.leak E V R w
    let M := TwoExit.residual E V R w s.x s.y
    let Q := (q:ℚ)*(c-mass V w+mass (V\R) w)-c
    let k := (q:ℚ)-1
    ∀i j,E i s.x=true → E i s.y=false → E j s.x=false → E j s.y=true →
      M i=0 → M j=0 → Q≤k*(L i+k*L j) → Q≤k*(L j+k*L i) →
      2*(q:ℚ)*((q:ℚ)*(c-mass V w)+c-(q:ℚ)*mass
        (insert s.x (outN E V s.x)∩insert s.y (outN E V s.y)) w)≤k*((q:ℚ)-2)*(c-w s.i) := by
  intro R L M Q k i j
  exact TwoExitOverlapCap.swapped_joint_bound (x:=i) (y:=j) hq both.2.2.1 s.ir
    (mem_outN.mp s.xhit).2 (mem_outN.mp s.yhit).2

#print axioms covered_labels
#print axioms covered_swapped
end LeanCH.BR.Closure.TwoHeadRepairReplay
