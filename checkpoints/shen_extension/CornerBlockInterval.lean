import checkpoints.shen_extension.CornerBlockSubstitution
import LeanCH.BR.BRSubstitutionWalk
import Mathlib.Order.Interval.Finset.Nat

namespace LeanCH.BR.Closure.CornerBlockInterval
open Finset BRq2 BRq3 BR45 WeightedSD CornerBlockSubstitution

private theorem count {N : ℕ} {L : Finset ℕ} (f : ℕ→Fin N) (e : L≃Fin N)
    (onL : ∀i (il : i∈L),f i=e ⟨i,il⟩) (T : Finset ℕ) (sub : T⊆range N) :
    (L.filter (fun i=>(f i).val∈T)).card=T.card := by
  apply card_bij (fun i _=>(f i).val) (fun _ h=>(mem_filter.mp h).2)
  · intro i ih j jh eq
    have ik := (mem_filter.mp ih).1
    have jk := (mem_filter.mp jh).1
    exact congrArg Subtype.val (e.injective ((onL i ik).symm.trans ((Fin.ext eq).trans (onL j jk))))
  · intro b bt
    let j := e.symm ⟨b,mem_range.mp (sub bt)⟩
    have val : (f j.val).val=b := congrArg Fin.val ((onL j.val j.property).trans (e.apply_symm_apply _))
    exact ⟨j,mem_filter.mpr ⟨j.property,val ▸ bt⟩,val⟩

/-- For every smaller size qd+1 one may choose k parents and 2d+1-k
    heads. They occupy consecutive disjoint intervals of a flat circulant.
    The largest forward displacement in q-2 steps cannot wrap around
    from the head interval to the parent interval. -/
theorem interval {q d k : ℕ} (hq : 2≤q) (_hd : 1≤d) (_hk : 1≤k) (bound : k≤2*d)
    (L : Finset ℕ) (size : L.card=q*d+1) :
    ∃(A : CH.Digraph) (I O : Finset ℕ),I⊆L ∧ O⊆L ∧ I.card=k ∧ O.card=2*d+1-k ∧
      QFree A L q ∧ (∀i∈L,(outN A L i).card=d ∧ (inN A L i).card=d) ∧
      ∀v∈O,∀t∈I,∀l,l≤q-2 → ¬ Walk A L v t l := by
  classical
  let N := q*d+1
  let _ : NeZero N := ⟨Nat.succ_ne_zero _⟩
  have room : 2*d<N := Nat.lt_succ_of_le (Nat.mul_le_mul_right d hq)
  let e := Fintype.equivFinOfCardEq (α:=↥L) (n:=N) (by simpa using size)
  let f (i : ℕ) : Fin N := if il : i∈L then e ⟨i,il⟩ else 0
  have fe (i) (il : i∈L) : f i=e ⟨i,il⟩ := dite_eq_left il
  let T := Icc 1 d
  let A : CH.Digraph := fun i j=>decide ((f j-f i).val∈T)
  let I := L.filter (fun i=>(f i).val∈range k)
  let O := L.filter (fun i=>(f i).val∈Icc k (2*d))
  have tr : T⊆range N := fun _ h=>mem_range.mpr (by have := (mem_Icc.mp h).2; omega)
  have ic : I.card=k := (count f e fe _ (range_mono (by omega : k≤N))).trans (card_range k)
  have oc : O.card=2*d+1-k := (count f e fe _ (fun _ h=>mem_range.mpr ((mem_Icc.mp h).2.trans_lt room))).trans (Nat.card_Icc ..)
  have step (i) (_ : i∈L) (j) (_ : j∈L) (ed : A i j=true) :
      ∃s,1≤s ∧ s≤d ∧ Nat.ModEq N ((f i).val+s) (f j).val := by
    have valid := mem_Icc.mp (of_decide_eq_true ed)
    refine ⟨(f j-f i).val,valid.1,valid.2,?_⟩
    have eq : f i+(f j-f i)=f j := by abel
    change ((f i).val+(f j-f i).val)%N=(f j).val%N
    rw [←Fin.val_add,eq,Nat.mod_eq_of_lt (f j).isLt]
  refine ⟨A,I,O,filter_subset _ _,filter_subset _ _,ic,oc,
    qfree_of_bounded_modular_steps (by omega : q*d<N) (fun i=>(f i).val) step,?_,?_⟩
  · intro i _
    let r : Fin N≃Fin N := ⟨fun j=>j-f i,fun j=>j+f i,fun _=>by dsimp; abel,fun _=>by dsimp; abel⟩
    let s : Fin N≃Fin N := ⟨fun j=>f i-j,fun j=>f i-j,fun _=>by dsimp; abel,fun _=>by dsimp; abel⟩
    have tc : T.card=d := by simp [T]
    constructor
    · have eq := count (fun j=>f j-f i) (e.trans r) (fun j jl=>congrArg r (fe j jl)) T tr
      simpa [outN,A,decide_eq_true_eq] using eq.trans tc
    · have eq := count (fun j=>f i-f j) (e.trans s) (fun j jl=>congrArg s (fe j jl)) T tr
      simpa [inN,A,decide_eq_true_eq] using eq.trans tc
  · intro v vo t ti l short path
    obtain ⟨vl,vk,vb⟩ := (show v∈L ∧ k≤(f v).val ∧ (f v).val≤2*d by simpa only [O,mem_filter,mem_Icc] using vo)
    have tk := mem_range.mp (mem_filter.mp ti).2
    obtain ⟨m,_,md,modulo⟩ := path.bounded_modular_steps (fun i=>(f i).val) step vl
    have mulBound := Nat.mul_le_mul_right d short
    have eq : (q-2)*d+2*d=q*d := by rw [←Nat.add_mul,Nat.sub_add_cancel hq]
    change ((f v).val+m)%N=(f t).val%N at modulo
    rw [Nat.mod_eq_of_lt (by dsimp [N]; omega),Nat.mod_eq_of_lt (f t).isLt] at modulo
    omega

/-- Numeric capstone test for all available smaller degrees at once. -/
theorem threshold {q : ℕ} {D : CH.Digraph} {V S : Finset ℕ} {y : ℕ} {z p : ℕ→ℚ}
    (hq : 2≤q) (mz : 0<mass S z) (mp : 0<mass S p) (stop : CannotReplace q D V S y z p)
    {d k : ℕ} (hd : 1≤d) (room : q*d+1<S.card) (hk : 1≤k) (kb : k≤2*d) :
    let W := (V.erase y)\S
    let N : ℚ := (q*d+1 : ℕ)
    (q:ℚ)*(outW D W z y+(2*d+1-k:ℕ)*(mass S z/N))<1 ∨
      (q:ℚ)*(inW D W p y+k*(mass S p/N))<1 := by
  intro W N
  obtain ⟨L,ls,size⟩ := exists_subset_card_eq room.le
  have less : L⊂S := Finset.ssubset_iff_subset_ne.mpr ⟨ls,fun eq=>by rw [←eq,size] at room; omega⟩
  obtain ⟨A,I,O,il,ol,ic,oc,safe,degrees,apart⟩ := interval hq hd hk kb L size
  have npos : (0:ℚ)<N := by change (0:ℚ)<((q*d+1:ℕ):ℚ); positivity
  let uniform (m : ℚ) := fun _ : ℕ=>m/N
  have massU (T : Finset ℕ) (m : ℚ) : mass T (uniform m)=T.card*(m/N) := by simp [mass,uniform]
  have full (m : ℚ) : mass L (uniform m)=m := by rw [massU,size]; exact mul_div_cancel₀ _ npos.ne'
  have bill (B : CH.Digraph) (i) (deg : (outN B L i).card=d) (m : ℚ) :
      WeightedSD.row q B L (uniform m) i=m := by
    rw [WeightedSD.row,outW_eq_mass,massU,deg]
    change m/N+(q:ℚ)*(d*(m/N))=m
    have eq : N=1+(q:ℚ)*d := by dsimp [N]; push_cast; ring
    calc
      _ = (1+(q:ℚ)*d)*(m/N) := by ring
      _ = m := by rw [←eq]; exact mul_div_cancel₀ _ npos.ne'
  have cut := stop A L I O less il ol safe apart (uniform (mass S z)) (uniform (mass S p))
    (fun _ _=>⟨div_pos mz npos,div_pos mp npos⟩) (full _) (full _)
    (fun i ii=>⟨bill A i (degrees i ii).1 _,bill (fun i j=>A j i) i (degrees i ii).2 _⟩)
  simpa only [massU,ic,oc] using cut

open Matrix FiniteCutInverse
open scoped Matrix

/-- The puncture distribution and the native inverse row are the same ray.
    Its scale is exactly the excess at the missing pivot. -/
private theorem ray {q : ℕ} {D : CH.Digraph} {V : Finset ℕ} (y : V)
    {H : Matrix V V ℝ} (inv : CommonInverse (realMatrix q D V) H) {p : ℕ→ℚ}
    (pm : mass (V.erase y.val) p=1) (pc : ∀i∈V.erase y.val,WeightedSD.col q D (V.erase y.val) p i=1) :
    let U := V.erase y.val
    let g : ℝ := ((q:ℚ)*inW D U p y-1:ℚ)
    ∀i∈U,(p i:ℝ)=g*realExtendWeight V (H y) i := by
  intro U g
  let r := maskReal U (fun i=>(p i:ℝ))
  let v := fun i : V=>r i
  let R := realMatrix q D V
  let h := v ᵥ* excess R
  have sub : U⊆V := erase_subset .. 
  have norm : (∑i,v i)=1 := by
    rw [show (∑i,v i)=realMass V r from sum_coe_sort V r,maskReal_mass sub,realMass_rat,pm]; norm_num
  have atLabel (i : V) : h i=realCol q D V r i-1 := by
    change (v ᵥ* excess R) i=_
    rw [vecMul_excess,norm,realMatrix_col q D V r]
  have vanish (i : V) (ne : i≠y) : h i=0 := by
    have iu : i.val∈U := mem_erase.mpr ⟨fun eq=>ne (Subtype.ext eq),i.property⟩
    rw [atLabel,maskReal_col sub _ iu,realCol_rat,pc i iu]; norm_num
  have root : h y=g := by
    rw [atLabel,realCol,maskReal_inW sub,show r y=0 from ite_eq_right (notMem_erase y.val V),zero_add]
    simp [g,realInW,inW,apply_ite]
  have back : h ᵥ* H=v := by
    change (v ᵥ* excess R) ᵥ* H=v
    rw [vecMul_vecMul,inv.right,vecMul_one]
  intro i iu
  let j : V := ⟨i,sub iu⟩
  have same : (p i:ℝ)=v j := (ite_eq_left iu).symm
  rw [same,←congrFun back j]
  change (∑t,h t*H t j)=_
  rw [sum_eq_single y,root,realExtendWeight_on V (H y) j]
  · intro t _ ne; rw [vanish t ne,zero_mul]
  · simp

/-- A loss below the pivot threshold is more than one unit of the native
    inverse, measured entirely inside the block. The exterior cancels. -/
private theorem gap {q : ℕ} {D : CH.Digraph} {V S : Finset ℕ} (y : V)
    {H : Matrix V V ℝ} (inv : CommonInverse (realMatrix q D V) H) {p : ℕ→ℚ}
    (pm : mass (V.erase y.val) p=1) (pc : ∀i∈V.erase y.val,WeightedSD.col q D (V.erase y.val) p i=1)
    (sub : S⊆V.erase y.val) (heavy : 1<(q:ℚ)*inW D (V.erase y.val) p y) {a : ℚ}
    (light : (q:ℚ)*(inW D ((V.erase y.val)\S) p y+a*mass S p)<1) :
    let f := realExtendWeight V (H y)
    1<(q:ℝ)*(realInW D S f y-(a:ℝ)*realMass S f) := by
  intro f
  let U := V.erase y.val
  let g : ℝ := ((q:ℚ)*inW D U p y-1:ℚ)
  have positive : 0<g := by dsimp only [g,U]; exact_mod_cast sub_pos.mpr heavy
  have id := ray y inv pm pc
  have parts : inW D U p y=inW D S p y+inW D (U\S) p y := outW_split (D:=fun i j=>D j i) sub p y
  have bound : (q:ℚ)*inW D U p y-1 < (q:ℚ)*(inW D S p y-a*mass S p) := by
    rw [parts]; linarith only [light]
  have price (T : Finset ℕ) (tu : T⊆U) : (mass T p:ℝ)=g*realMass T f := by
    simp only [mass,realMass,Rat.cast_sum,mul_sum]
    exact sum_congr rfl fun i it=>id i (tu it)
  have si : (inW D S p y:ℝ)=g*realInW D S f y := by
    rw [show inW D S p y=mass (inN D S y) p from outW_eq_mass (fun i j=>D j i) S p y,
      realInW_eq_mass_inN]
    exact price _ ((filter_subset _ _).trans sub)
  have strict : g<(q:ℝ)*((inW D S p y:ℝ)-(a:ℝ)*(mass S p:ℝ)) := by
    dsimp only [g]; exact_mod_cast bound
  rw [si,price S sub] at strict
  apply lt_of_mul_lt_mul_left (a:=g) _ positive.le
  linarith only [strict]

open ShortestCycleWeights FirstPacketBarrier MarkedCyclePeeling SharedArcBarrier SharedArcComponentExchange

/-- The same native inverse tests the actual boundary attachments and all
    abstract interval replacements. For each legal interval one of the two
    internal contact sums must beat its interval price by over one unit. -/
theorem joint {q n} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    {J : Family} {r : ℕ→ℚ} (rp : ∀i∈X.V,0<r i)
    (back : ∀i∈X.V,mass X.V r<WeightedSD.col q (graph X.D J) X.V r i)
    {F B} (step : Boundary X F B)
    (least : ∀M,Boundary X F M → (targets X.D X.V F B).card≤(targets X.D X.V F M).card)
    (many : 1<(targets X.D X.V F B).card) {y h : X.V} (fresh : Fresh X F (y,h))
    (stuck : ¬SharedArcReachMargin.StrictColumns q (insertArc (graph X.D F) y h) X.V)
    {S} (block : CornerHeadRecurrence.OldBlockAt X.D (graph X.D F) X.V y S) :
    ∃H : Matrix X.V X.V ℝ,CommonInverse (realMatrix q X.D X.V) H ∧
      (∀M : Finset ℕ,let E := graph X.D (insert M F)
        let loss := realMatrix q X.D X.V-realMatrix q E X.V
        SmallRow q E X.V ↔ 1≤∑j,loss y j*H j y ∨ 1≤∑i,H y i*loss i y) ∧
      ∀d k : ℕ,1≤d → q*d+1<S.card → 1≤k → k≤2*d →
        let N : ℝ := (q*d+1:ℕ)
        let u := realExtendWeight X.V (fun i=>H i y)
        let v := realExtendWeight X.V (H y)
        1<(q:ℝ)*(realOutW X.D S u y-((2*d+1-k:ℕ):ℝ)/N*realMass S u) ∨
        1<(q:ℝ)*(realInW X.D S v y-(k:ℝ)/N*realMass S v) := by
  obtain ⟨H,inv,edits⟩ := SharedArcPivotLoopSums.all_competitors X hq small step least many fresh stuck
  obtain ⟨z,p,pos,zm,pm,flat,_,hh,hp,stop⟩ := CornerBlockSubstitution.on_source X hq small rp back step least many fresh stuck block
  obtain ⟨t,ts,_⟩ := block.2.2.1
  have mz : 0<mass S z := sum_pos (fun i si=>(pos i (block.1.1 si)).1) ⟨t,ts⟩
  have mp : 0<mass S p := sum_pos (fun i si=>(pos i (block.1.1 si)).2) ⟨t,ts⟩
  refine ⟨H,inv,edits,?_⟩
  intro d k hd room hk kb N u v
  rcases threshold hq mz mp stop hd room hk kb with low|low
  · have zlow := gap (D:=fun i j=>X.D j i) y (commonInverse_reverse inv) zm (fun i iu=>(flat i iu).1)
      block.1.1 hh (a:=((2*d+1-k:ℕ):ℚ)/(q*d+1:ℕ)) (by convert low using 1; unfold inW outW; ring)
    have transposeRow : H.transpose y=(fun i=>H i y) := by funext i; rfl
    left; simpa only [u,N,realOutW,realInW,transposeRow,Rat.cast_div,Rat.cast_natCast] using zlow
  · have plow := gap y inv pm (fun i iu=>(flat i iu).2) block.1.1 hp (a:=(k:ℚ)/(q*d+1:ℕ))
      (by convert low using 1; ring)
    right; simpa only [Rat.cast_div,Rat.cast_natCast] using plow

/-- An actual, centered block admitting one interval within both inverse
    budgets. All witnesses refer to the same marked pivot and host. -/
def Fits {q n} (X : Model q n) (F : Family) (B : Finset ℕ) : Prop :=
  1<(targets X.D X.V F B).card ∧ ∃ y h : X.V,Fresh X F (y,h) ∧
    ¬SharedArcReachMargin.StrictColumns q (insertArc (graph X.D F) y h) X.V ∧
    ∃S,CornerHeadRecurrence.OldBlockAt X.D (graph X.D F) X.V y S ∧
    ∃H : Matrix X.V X.V ℝ,CommonInverse (realMatrix q X.D X.V) H ∧
    ∃d k : ℕ,1≤d ∧ q*d+1<S.card ∧ 1≤k ∧ k≤2*d ∧
      let N : ℝ := (q*d+1:ℕ)
      let u := realExtendWeight X.V (fun i=>H i y)
      let v := realExtendWeight X.V (H y)
      (q:ℝ)*(realOutW X.D S u y-((2*d+1-k:ℕ):ℝ)/N*realMass S u)≤1 ∧
      (q:ℝ)*(realInW X.D S v y-(k:ℝ)/N*realMass S v)≤1

theorem excludes {q n} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    {J : Family} {r : ℕ→ℚ} (rp : ∀i∈X.V,0<r i)
    (back : ∀i∈X.V,mass X.V r<WeightedSD.col q (graph X.D J) X.V r i)
    {F B} (step : Boundary X F B)
    (least : ∀M,Boundary X F M → (targets X.D X.V F B).card≤(targets X.D X.V F M).card) :
    ¬Fits X F B := by
  rintro ⟨many,y,h,fresh,stuck,S,block,K,ki,d,k,hd,room,hk,kb,outB,inB⟩
  obtain ⟨H,inv,_,test⟩ := joint X hq small rp back step least many fresh stuck block
  have eq : H=K := calc
    H = H*(excess (realMatrix q X.D X.V)*K) := by rw [ki.right,mul_one]
    _ = K := by rw [←mul_assoc,mul_eq_one_comm.mp inv.right,one_mul]
  subst K
  exact (test d k hd room hk kb).elim (fun h=>h.not_ge outB) (fun h=>h.not_ge inB)

#print axioms interval
#print axioms threshold
#print axioms joint
#print axioms excludes
end LeanCH.BR.Closure.CornerBlockInterval
