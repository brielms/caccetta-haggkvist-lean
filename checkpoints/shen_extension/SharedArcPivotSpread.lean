import checkpoints.shen_extension.SharedArcPivotDetour

namespace LeanCH.BR.Closure.SharedArcPivotSpread
open Finset Matrix BRq2 BRq3 BR45 WeightedSD FiniteCutInverse ShortestCycleWeights
open SharedArcBarrier SharedArcComponentExchange FirstPacketBarrier MarkedCyclePeeling SharedArcPivotDetour
open scoped Matrix

/-- If one exceptional head is exchanged for an exterior vertex, the
whole diagonal term of the old row must fit in the weight difference. -/
private theorem switch_cost {α : Type*} [DecidableEq α] {S T A : Finset α} {h t : α}
    {w : α→ℝ} (wn : ∀i,0≤w i) (incl : S.erase h⊆T) (at' : A⊆T) (dis : Disjoint A S)
    {q Z : ℝ} (qn : 0≤q) (high : Z<q*∑i∈S,w i) (low : w t+q*∑i∈T,w i≤Z) :
    w t+q*(∑i∈A,w i)<q*w h := by
  have sub : A ∪ S.erase h⊆T := union_subset at' incl
  have count := sum_le_sum_of_subset_of_nonneg (f:=w) sub (fun i _ _ => wn i)
  rw [sum_union (dis.mono_right (erase_subset h S))] at count
  have erase : ∑i∈S,w i≤(∑i∈S.erase h,w i)+w h := by
    by_cases hh : h∈S
    · exact (sum_erase_add _ _ hh).ge
    · simp [erase_eq_of_notMem hh,wn]
  linarith [mul_le_mul_of_nonneg_left count qn,mul_le_mul_of_nonneg_left erase qn]

/-- Total outgoing and incoming costs of the two exterior cuts, in the
native column and row measures respectively. -/
def Costs {q n} (X : Model q n) (a t h : X.V) (H : Matrix X.V X.V ℝ) : Prop :=
  (H t a+q*(∑x∈(rest a).filter (fun x : X.V => X.D t x=true ∧ X.D a x=false),H x a)<q*H h a) ∧
  (H a h+q*(∑x∈(rest a).filter (fun x : X.V => X.D x h=true ∧ X.D x a=false),H a x)<q*H a t)

def Uncovered {V : Finset ℕ} (D J : CH.Digraph) (a : V) : Prop :=
  ∀v∈rest a,(∃x∈rest a,J a x=true ∧ D v x=false) ∧ (∃y∈rest a,J y a=true ∧ D y v=false)

private theorem escapes {α : Type*} [DecidableEq α] {S T : Finset α} {w : α→ℝ} {q Z : ℝ} {v : α}
    (wn : ∀j,0≤w j) (qn : 0≤q) (high : Z<q*∑j∈S,w j) (low : w v+q*∑j∈T,w j≤Z) :
    ∃x∈S,x∉T := by
  by_contra! all
  have bound := sum_le_sum_of_subset_of_nonneg (f:=w) (show S⊆T from all) (fun i _ _ => wn i)
  linarith [mul_le_mul_of_nonneg_left bound qn,wn v]

private theorem row_eval {q} {D : CH.Digraph} {V : Finset ℕ} (a i : V)
    (w : V→ℝ) (wa : w a=0) :
    (realMatrix q D V *ᵥ w) i=w i+q*∑j∈(rest a).filter (fun j : V => D i j=true),w j := by
  classical
  simp only [sum_filter]
  have zero : (if D i a=true then w a else 0)=0 := by simp [wa]
  have eq := sum_erase_add univ (fun j : V => if D i j=true then w j else 0) (mem_univ a)
  rw [zero,add_zero] at eq
  rw [show (∑j∈rest a, if D i j=true then w j else 0)=_ from eq]
  simp [mulVec,dotProduct,realMatrix_entry,add_mul,ite_mul,sum_add_distrib,mul_sum,mul_ite]

private theorem col_eval {q} {D : CH.Digraph} {V : Finset ℕ} (a i : V)
    (p : V→ℝ) (pa : p a=0) :
    (p ᵥ* realMatrix q D V) i=p i+q*∑j∈(rest a).filter (fun j : V => D j i=true),p j := by
  classical
  have flip : (p ᵥ* realMatrix q D V) i=(realMatrix q (fun u v => D v u) V *ᵥ p) i := by
    simp only [vecMul,mulVec,dotProduct,realMatrix_entry]
    apply sum_congr rfl
    intro j _
    by_cases e : i=j <;> simp [e,Ne.symm,mul_comm]
  exact flip.trans (row_eval a i p pa)

/-- On a stopped attachment a positive mass in the inverse column or
row grows by at least the diagonal contribution of the opposite endpoint.
The witness is a real vertex of the puncture outside the pivot's neighbours. -/
theorem native_spread {q n} (X : Model q n) (hq : 3≤q) (small : SmallerSmallRow q X.V.card)
    {F B} (step : Boundary X F B)
    (least : ∀M,Boundary X F M → (targets X.D X.V F B).card≤(targets X.D X.V F M).card)
    (stop : ¬SmallRow q (graph X.D (insert B F)) X.V)
    (multi : 1<(targets X.D X.V F B).card) {a b : X.V} (edge : Fresh X F (a,b))
    (no : ¬SharedArcReachMargin.StrictColumns q (insertArc (graph X.D F) a b) X.V)
    {H : Matrix X.V X.V ℝ} (inv : CommonInverse (realMatrix q X.D X.V) H) :
    ∃ t h : X.V, Fresh X F (t,a) ∧ Fresh X F (a,h) ∧ added X.D F B=SharedArcPivotChoice.pair a t h ∧
      Uncovered X.D (graph X.D (insert B F)) a ∧ Costs X a t h H ∧
      ((∃x∈rest a,X.D t x=true ∧ X.D a x=false ∧ H t a+q*H x a<q*H h a) ∨
       (∃x∈rest a,X.D x h=true ∧ X.D x a=false ∧ H a h+q*H a x<q*H a t)) := by
  classical
  let J := graph X.D (insert B F)
  let R := realMatrix q X.D X.V
  let S := realMatrix q J X.V
  let z := fun i : X.V => H i a
  let p := fun i : X.V => H a i
  have diag : H a a=0 := SharedArcPunctureExpansion.zero_diagonal X (by omega) small step least multi edge no inv
  obtain ⟨t,h,ta,ah,shape,outIn,inOut,escape⟩ := endpoint_escape X hq small step least multi edge no
  have ne {i j : X.V} (e : X.D i j=true) : i≠j := fun eq => loopfree X.free (by omega) j.property (eq ▸ e)
  have nt := ne ta.2.2.1
  have nh := (ne ah.2.2.1).symm
  have native {i j : ℕ} (e : J i j=true) : X.D i j=true := by
    obtain ⟨_,m⟩ := active.mp e
    exact (mem_col.mp m).2.2.2
  have sub (i j : X.V) : S i j≤R i j := realMatrix_mono_graph (fun _ _ _ _ e => native e) i j
  have row (i : X.V) (ni : i≠a) : (R *ᵥ z) i=∑j,z j := by
    have eq := congrArg (fun A : Matrix X.V X.V ℝ => A i a) inv.right
    change (excess R *ᵥ z) i=(1 : Matrix X.V X.V ℝ) i a at eq
    simpa [mulVec_excess,one_apply_ne ni,sub_eq_zero] using eq
  have col (i : X.V) (ni : i≠a) : (p ᵥ* R) i=∑j,p j := by
    have eq := congrArg (fun A : Matrix X.V X.V ℝ => A a i) (mul_eq_one_comm.mp inv.right)
    change (p ᵥ* excess R) i=(1 : Matrix X.V X.V ℝ) a i at eq
    simpa [vecMul_excess,one_apply_ne ni.symm,sub_eq_zero] using eq
  obtain ⟨w,wn,_,strict⟩ := strict_witness_of_not_smallRow stop
  obtain ⟨K,ki⟩ := strict_inverse_of_proper_smallRow (small.induced (PrivateArcEndpoints.graph_free X (insert B F))) w wn strict
  have zpos : 0<z t := InverseOffDiagonal.graph_positive (by omega) inv nt
  have ppos : 0<p h := InverseOffDiagonal.graph_positive (by omega) inv nh.symm
  have hiZ : (∑j,z j)<(S *ᵥ z) a := by
    by_contra! low
    have all (i) : (excess S *ᵥ z) i≤0 := by
      rw [mulVec_excess,sub_nonpos]
      by_cases eq : i=a
      · exact eq ▸ low
      · exact (sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (sub i j) (inv.nonneg j a))).trans (row i eq).le
    have hz : (K *ᵥ (excess S *ᵥ z)) t≤0 := sum_nonpos fun j _ => mul_nonpos_of_nonneg_of_nonpos (ki.nonneg t j) (all j)
    rw [mulVec_mulVec,mul_eq_one_comm.mp ki.right,one_mulVec] at hz
    exact zpos.not_ge hz
  have hiP : (∑j,p j)<(p ᵥ* S) a := by
    by_contra! low
    have all (i) : (p ᵥ* excess S) i≤0 := by
      rw [vecMul_excess,sub_nonpos]
      by_cases eq : i=a
      · exact eq ▸ low
      · exact (sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (sub j i) (inv.nonneg a j))).trans (col i eq).le
    have hp : ((p ᵥ* excess S) ᵥ* K) h≤0 := sum_nonpos fun j _ => mul_nonpos_of_nonpos_of_nonneg (all j) (ki.nonneg j h)
    rw [vecMul_vecMul,ki.right,vecMul_one] at hp
    exact ppos.not_ge hp
  rw [show (S *ᵥ z) a=_ from row_eval a a z diag,show z a=0 from diag,zero_add] at hiZ
  rw [show (p ᵥ* S) a=_ from col_eval a a p diag,show p a=0 from diag,zero_add] at hiP
  let A := (rest a).filter (fun x : X.V => X.D t x=true ∧ X.D a x=false)
  let Y := (rest a).filter (fun x : X.V => X.D x h=true ∧ X.D x a=false)
  have outA := switch_cost (A:=A) (fun i => inv.nonneg i a) outIn
    (fun x hx => mem_filter.mpr ⟨(mem_filter.mp hx).1,(mem_filter.mp hx).2.1⟩)
    (Finset.disjoint_left.mpr fun x hx jx => Bool.noConfusion ((mem_filter.mp hx).2.2.symm.trans (native (mem_filter.mp jx).2)))
    (Nat.cast_nonneg _) hiZ ((row_eval (q:=q) (D:=X.D) a t z diag).symm.trans (row t nt)).le
  have inY := switch_cost (A:=Y) (fun i => inv.nonneg a i) inOut
    (fun x hx => mem_filter.mpr ⟨(mem_filter.mp hx).1,(mem_filter.mp hx).2.1⟩)
    (Finset.disjoint_left.mpr fun x hx jx => Bool.noConfusion ((mem_filter.mp hx).2.2.symm.trans (native (mem_filter.mp jx).2)))
    (Nat.cast_nonneg _) hiP ((col_eval (q:=q) (D:=X.D) a h p diag).symm.trans (col h nh)).le
  have openAt : Uncovered X.D J a := by
    intro v vu
    have nv : v≠a := (mem_erase.mp vu).1
    constructor
    · have low := (row_eval (q:=q) (D:=X.D) a v z diag).symm.trans (row v nv)
      obtain ⟨x,sx,tx⟩ := escapes (fun i => inv.nonneg i a) (Nat.cast_nonneg _) hiZ low.le
      obtain ⟨xu,ax⟩ := mem_filter.mp sx
      exact ⟨x,xu,ax,Bool.eq_false_iff.mpr (fun e => tx (mem_filter.mpr ⟨xu,e⟩))⟩
    · have low := (col_eval (q:=q) (D:=X.D) a v p diag).symm.trans (col v nv)
      obtain ⟨x,sx,tx⟩ := escapes (fun i => inv.nonneg a i) (Nat.cast_nonneg _) hiP low.le
      obtain ⟨xu,xa⟩ := mem_filter.mp sx
      exact ⟨x,xu,xa,Bool.eq_false_iff.mpr (fun e => tx (mem_filter.mpr ⟨xu,e⟩))⟩
  refine ⟨t,h,ta,ah,shape,openAt,⟨outA,inY⟩,?_⟩
  rcases escape with ⟨x,xu,tx,ax⟩ | ⟨x,xu,xh,xa⟩
  · have bound := single_le_sum (s:=A) (f:=z) (fun j _ => inv.nonneg j a) (mem_filter.mpr ⟨xu,tx,ax⟩)
    exact Or.inl ⟨x,xu,tx,ax,(add_le_add_right (mul_le_mul_of_nonneg_left bound (Nat.cast_nonneg q)) _).trans_lt outA⟩
  · have bound := single_le_sum (s:=Y) (f:=p) (fun j _ => inv.nonneg a j) (mem_filter.mpr ⟨xu,xh,xa⟩)
    exact Or.inr ⟨x,xu,xh,xa,(add_le_add_right (mul_le_mul_of_nonneg_left bound (Nat.cast_nonneg q)) _).trans_lt inY⟩

#print axioms native_spread

/-- The same alternative holds for every prescribed fresh parent and
head, since a pair of exchanges realizes them in a minimum attachment. -/
theorem at_pair {q n} (X : Model q n) (hq : 3≤q) (small : SmallerSmallRow q X.V.card)
    {F B} (step : Boundary X F B)
    (least : ∀M,Boundary X F M → (targets X.D X.V F B).card≤(targets X.D X.V F M).card)
    (stop : ∀M,Boundary X F M → ¬SmallRow q (graph X.D (insert M F)) X.V)
    (multi : 1<(targets X.D X.V F B).card) {a b : X.V} (edge : Fresh X F (a,b))
    (no : ¬SharedArcReachMargin.StrictColumns q (insertArc (graph X.D F) a b) X.V)
    {H : Matrix X.V X.V ℝ} (inv : CommonInverse (realMatrix q X.D X.V) H)
    {t h : X.V} (ta : Fresh X F (t,a)) (ah : Fresh X F (a,h)) :
    ∃M, Boundary X F M ∧ added X.D F M=SharedArcPivotChoice.pair a t h ∧
      Uncovered X.D (graph X.D (insert M F)) a ∧ Costs X a t h H ∧ ((∃x∈rest a,X.D t x=true ∧ X.D a x=false ∧ H t a+q*H x a<q*H h a) ∨
    (∃x∈rest a,X.D x h=true ∧ X.D x a=false ∧ H a h+q*H a x<q*H a t)) := by
  classical
  obtain ⟨M,bm,pair⟩ := SharedArcPivotChoice.joint_pair X (by omega) small step least stop multi edge no ta ah
  have cyc : ShenCycleSuccessor.Cycle X.D X.V q M := (mem_filter.mp bm.1).2
  have two : (targets X.D X.V F M).card≤2 := by
    rw [←count cyc,pair]
    exact (card_insert_le _ _).trans (by simp)
  have minM (N) (bn : Boundary X F N) := two.trans (multi.trans_le (least N bn))
  obtain ⟨u,v,ua,av,sh,uncovered,hit⟩ := native_spread X hq small bm minM (stop M bm) (multi.trans_le (least M bm)) edge no inv
  have uaMem : (u.val,a.val)∈added X.D F M := sh ▸ mem_insert_self _ _
  have taMem : (t.val,a.val)∈added X.D F M := pair ▸ mem_insert_self _ _
  have avMem : (a.val,v.val)∈added X.D F M := sh ▸ mem_insert_of_mem (mem_singleton_self _)
  have ahMem : (a.val,h.val)∈added X.D F M := pair ▸ mem_insert_of_mem (mem_singleton_self _)
  have ut : u=t := Subtype.ext (congrArg Prod.fst (matching cyc uaMem taMem (Or.inr rfl)))
  have vh : v=h := Subtype.ext (congrArg Prod.snd (matching cyc avMem ahMem (Or.inl rfl)))
  exact ⟨M,bm,pair,uncovered,ut ▸ vh ▸ hit⟩

theorem every_pair {q n} (X : Model q n) (hq : 3≤q) (small : SmallerSmallRow q X.V.card)
    {F B} (step : Boundary X F B)
    (least : ∀M,Boundary X F M → (targets X.D X.V F B).card≤(targets X.D X.V F M).card)
    (stop : ∀M,Boundary X F M → ¬SmallRow q (graph X.D (insert M F)) X.V)
    (multi : 1<(targets X.D X.V F B).card) {a b : X.V} (edge : Fresh X F (a,b))
    (no : ¬SharedArcReachMargin.StrictColumns q (insertArc (graph X.D F) a b) X.V)
    {H : Matrix X.V X.V ℝ} (inv : CommonInverse (realMatrix q X.D X.V) H)
    {t h : X.V} (ta : Fresh X F (t,a)) (ah : Fresh X F (a,h)) :
    Costs X a t h H ∧ ((∃x∈rest a,X.D t x=true ∧ X.D a x=false ∧ H t a+q*H x a<q*H h a) ∨
    (∃x∈rest a,X.D x h=true ∧ X.D x a=false ∧ H a h+q*H a x<q*H a t)) := by
  obtain ⟨_,_,_,_,hit⟩ := at_pair X hq small step least stop multi edge no inv ta ah
  exact hit

#print axioms every_pair

/-- Every label covering all old heads misses every fresh head.
The transposed assertion holds simultaneously for the old parents. -/
theorem masks {q n} (X : Model q n) (hq : 3≤q) (small : SmallerSmallRow q X.V.card)
    {F B} (step : Boundary X F B)
    (least : ∀M,Boundary X F M → (targets X.D X.V F B).card≤(targets X.D X.V F M).card)
    (stop : ∀M,Boundary X F M → ¬SmallRow q (graph X.D (insert M F)) X.V)
    (multi : 1<(targets X.D X.V F B).card) {a b : X.V} (edge : Fresh X F (a,b))
    (no : ¬SharedArcReachMargin.StrictColumns q (insertArc (graph X.D F) a b) X.V)
    {t h : X.V} (ta : Fresh X F (t,a)) (ah : Fresh X F (a,h)) (v : X.V) (vu : v∈rest a) :
    ((∀x∈rest a, graph X.D F a x=true → X.D v x=true) → X.D v h=false) ∧
    ((∀x∈rest a, graph X.D F x a=true → X.D x v=true) → X.D t v=false) := by
  classical
  obtain ⟨K,inv⟩ := strict_inverse_of_proper_smallRow (small.induced X.free)
    (fun i => (X.weights i:ℚ)) (fun _ _ => Nat.cast_nonneg _) X.strict
  obtain ⟨M,_,pair,uncovered,_⟩ := at_pair X hq small step least stop multi edge no inv ta ah
  obtain ⟨⟨x,xu,ax,vx⟩,⟨y,yu,ya,yv⟩⟩ := uncovered v vu
  constructor
  · intro covers
    rcases union_arc.mp ax with old|added
    · exact Bool.noConfusion (vx.symm.trans (covers x xu old))
    · rw [pair] at added
      simp only [SharedArcPivotChoice.pair,mem_insert,mem_singleton,Prod.mk.injEq] at added
      rcases added with ⟨_,e⟩ | ⟨_,e⟩
      · exact ((mem_erase.mp xu).1 (Subtype.ext e)).elim
      · simpa [show x=h from Subtype.ext e] using vx
  · intro covers
    rcases union_arc.mp ya with old|added
    · exact Bool.noConfusion (yv.symm.trans (covers y yu old))
    · rw [pair] at added
      simp only [SharedArcPivotChoice.pair,mem_insert,mem_singleton,Prod.mk.injEq] at added
      rcases added with ⟨e,_⟩ | ⟨e,_⟩
      · simpa [show y=t from Subtype.ext e] using yv
      · exact ((mem_erase.mp yu).1 (Subtype.ext e)).elim

#print axioms masks

/-- On at least one side, every fresh endpoint exceeds the puncture
minimum by a factor strictly larger than 1+1/q. -/
theorem whole_side {q n} (X : Model q n) (hq : 3≤q) (small : SmallerSmallRow q X.V.card)
    {F B} (step : Boundary X F B)
    (least : ∀M,Boundary X F M → (targets X.D X.V F B).card≤(targets X.D X.V F M).card)
    (stop : ∀M,Boundary X F M → ¬SmallRow q (graph X.D (insert M F)) X.V)
    (multi : 1<(targets X.D X.V F B).card) {a b : X.V} (edge : Fresh X F (a,b))
    (no : ¬SharedArcReachMargin.StrictColumns q (insertArc (graph X.D F) a b) X.V) :
    ∃ H : Matrix X.V X.V ℝ, CommonInverse (realMatrix q X.D X.V) H ∧
      ((∀L : ℝ,(∀i∈rest a,L≤H i a) → ∀c : X.V,Fresh X F (a,c) → (q+1:ℝ)*L<q*H c a) ∨
       (∀L : ℝ,(∀i∈rest a,L≤H a i) → ∀u : X.V,Fresh X F (u,a) → (q+1:ℝ)*L<q*H a u)) := by
  obtain ⟨H,t,h,inv,ta,ah,minT,minH,_⟩ :=
    SharedArcPivotChoice.minimum_test X (by omega) small step least (stop B step) multi edge no
  have inside {i j : X.V} (e : X.D i j=true) : i≠j := fun eq => loopfree X.free (by omega) j.property (eq ▸ e)
  have tu : t∈rest a := mem_erase.mpr ⟨inside ta.2.2.1,mem_univ _⟩
  have hu : h∈rest a := mem_erase.mpr ⟨(inside ah.2.2.1).symm,mem_univ _⟩
  have qn : 0≤(q:ℝ) := Nat.cast_nonneg _
  refine ⟨H,inv,?_⟩
  rcases (every_pair X hq small step least stop multi edge no inv ta ah).2 with ⟨x,xu,_,_,lt⟩ | ⟨x,xu,_,_,lt⟩
  · left
    intro L low c fr
    linarith [low t tu,mul_le_mul_of_nonneg_left (low x xu) qn,mul_le_mul_of_nonneg_left (minH c fr) qn]
  · right
    intro L low u fr
    linarith [low h hu,mul_le_mul_of_nonneg_left (low x xu) qn,mul_le_mul_of_nonneg_left (minT u fr) qn]

#print axioms whole_side
end LeanCH.BR.Closure.SharedArcPivotSpread
