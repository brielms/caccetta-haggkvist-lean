import checkpoints.shen_extension.SharedArcCover

namespace LeanCH.BR.Closure.SharedArcFlatArithmetic
open Finset Matrix BRq2 BRq3 BR45 WeightedSD WeightedArithmetic ShortestCycleWeights FirstPacketBarrier MarkedCyclePeeling
open SharedArcExpansion SharedArcBarrier
open scoped Matrix

/-- After clearing three copies of the old determinant, every test numerator
is one modulo q. This works for composite q and for both diagonal and
off-diagonal label pairs. -/
theorem nonzero {q : ℕ} (hq : 2≤q) {E : CH.Digraph} {V : Finset ℕ} {w p : V→ℝ}
    (wr : realMatrix q E V *ᵥ w=fun _=>1) (pc : p ᵥ* realMatrix q E V=fun _=>1)
    (a b v k : V) :
    SharedArcFlatResponse.test (realMatrix q E V)⁻¹ w p q a b v k≠0 := by
  classical
  let _ : Fact (1<q) := ⟨by omega⟩
  let A := closedMatrix q (adjacencyMatrix E V)
  let d := A.det
  let R := realMatrix q E V
  let L := R⁻¹
  let W (i : V) := ∑j,A.adjugate i j
  let P (j : V) := ∑i,A.adjugate i j
  let g := Int.castRingHom ℝ
  let f := Int.castRingHom (ZMod q)
  have mapR : g.mapMatrix A=R := by
    ext i j
    change ((A i j:ℤ):ℝ)=((A i j:ℚ):ℝ)
    norm_cast
  have det : (d:ℝ)=R.det := by change g A.det=_; rw [g.map_det,mapR]
  have adj : g.mapMatrix A.adjugate=R.adjugate := by rw [g.map_adjugate,mapR]
  have unit := SharedArcFlatResponse.matrix_unit (E:=E) hq V
  have inv : R*L=1 := Matrix.mul_nonsing_inv _ unit
  have left := mul_eq_one_comm.mp inv
  have scale : (d:ℝ) • L=R.adjugate := by
    calc
      _=(R.adjugate*R)*L := by rw [Matrix.adjugate_mul,Matrix.smul_mul,one_mul,det]
      _=_ := by rw [Matrix.mul_assoc,inv,mul_one]
  have coefficient (i j : V) : (d:ℝ)*L i j=(A.adjugate i j:ℝ) :=
    (congrFun (congrFun scale i) j).trans (congrFun (congrFun adj i) j).symm
  have rowsum (i : V) : (∑j,L i j)=w i := by
    have h := congrArg (fun y => L *ᵥ y) wr
    change L *ᵥ (R *ᵥ w)=_ at h
    rw [Matrix.mulVec_mulVec,left,Matrix.one_mulVec] at h
    simpa [Matrix.mulVec,dotProduct] using (congrFun h i).symm
  have colsum (j : V) : (∑i,L i j)=p j := by
    have h := congrArg (fun y => y ᵥ* L) pc
    change (p ᵥ* R) ᵥ* L=_ at h
    rw [Matrix.vecMul_vecMul,inv,Matrix.vecMul_one] at h
    simpa [Matrix.vecMul,dotProduct] using (congrFun h j).symm
  have cw (i : V) : (W i:ℝ)=(d:ℝ)*w i := by
    change ((∑j,A.adjugate i j : ℤ):ℝ)=_
    rw [Int.cast_sum,←rowsum i,mul_sum]; exact sum_congr rfl (fun j _ => (coefficient i j).symm)
  have cp (i : V) : (P i:ℝ)=(d:ℝ)*p i := by
    change ((∑j,A.adjugate j i : ℤ):ℝ)=_
    rw [Int.cast_sum,←colsum i,mul_sum]; exact sum_congr rfl (fun j _ => (coefficient j i).symm)
  let z : ℤ := q*P a*W b*A.adjugate v k - q*P k*W b*A.adjugate v a +
    W v*(P k*d+q*P k*A.adjugate b a-q*P a*A.adjugate b k)
  have rep : (z:ℝ)=(d:ℝ)^3*SharedArcFlatResponse.test L w p q a b v k := by
    dsimp only [z,SharedArcFlatResponse.test]
    push_cast
    simp_rw [cw,cp,←coefficient]
    ring
  have modAdj : f.mapMatrix A.adjugate=1 := by
    rw [f.map_adjugate,show f.mapMatrix A=1 from closedMatrix_mod q _,Matrix.adjugate_one]
  have modEntry (i j : V) : (A.adjugate i j:ZMod q)=(1:Matrix V V (ZMod q)) i j :=
    congrFun (congrFun modAdj i) j
  have mw (i : V) : (W i:ZMod q)=1 := by simp [W,modEntry,Matrix.one_apply]
  have mp (i : V) : (P i:ZMod q)=1 := by simp [P,modEntry,Matrix.one_apply]
  have md : (d:ZMod q)=1 := det_mod q _
  have unitZ : (z:ZMod q)=1 := by dsimp only [z]; push_cast; simp [mw,mp,md]
  intro zero
  have zz : z=0 := by
    have eq : (z:ℝ)=0 := rep.trans (mul_eq_zero_of_right _ zero)
    exact_mod_cast eq
  rw [zz,Int.cast_zero] at unitZ
  exact zero_ne_one unitZ

def StrictTests {q n} (X : Model q n) (F : Family) (w p : ℕ→ℚ) : Prop :=
  ∀h : SharedArcFlatCut.Missing X F,∀v k : X.V,
    0<SharedArcFlatResponse.test (realMatrix q (graph X.D F) X.V)⁻¹
      (fun i : X.V => (w i:ℝ)) (fun i : X.V => (p i:ℝ)) q h.val.1 h.val.2 v k

theorem positive {q n} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    (F : Family) {w p : ℕ→ℚ} (wp : ∀i∈X.V,0<w i ∧ 0<p i) (wm : mass X.V w=1)
    (wr : ∀i∈X.V,WeightedSD.row q (graph X.D F) X.V w i=1)
    (pc : ∀i∈X.V,WeightedSD.col q (graph X.D F) X.V p i=1) : StrictTests X F w p := by
  intro f v k
  let a := f.val.1
  let b := f.val.2
  have sub {i j} (ed : insertArc (graph X.D F) a b i j=true) : X.D i j=true := by
    by_cases pair : i=(a:ℕ) ∧ j=(b:ℕ)
    · exact pair.1 ▸ pair.2 ▸ f.property.1
    have old : graph X.D F i j=true := by simpa [insertArc,pair] using ed
    obtain ⟨A,hit⟩ := active.mp old
    exact (mem_col.mp hit).2.2.2
  have low := SharedArcFlatResponse.safe_test hq small a b f.property.2
    (qfree_sub (fun _ _ e => sub e) X.free) wp wm wr pc v k
  exact lt_of_le_of_ne low (Ne.symm (nonzero hq
    (by simpa using funext (realMatrix_rational_rows w 1 wr))
    (by simpa using funext (realMatrix_rational_columns p 1 pc)) a b v k))


/-- Contract the four-index table with the actual old row of a and old
column of b. The contraction is strict because it includes the (a,b)
summand with both diagonal coefficients positive. -/
theorem aggregate {I : Type*} [Fintype I] [DecidableEq I]
    {R L : Matrix I I ℝ} (inv : R*L=1) {w p : I→ℝ}
    (wr : R *ᵥ w=fun _=>1) (pc : p ᵥ* R=fun _=>1)
    {a b : I} (miss : R a b=0) (rn : ∀i j,0≤R i j)
    (ra : 0<R a a) (rb : 0<R b b) {t : ℝ}
    (pos : ∀v k,0<SharedArcFlatResponse.test L w p t a b v k) :
    t*(w b+p a)<1+t*L b a := by
  let T := SharedArcFlatResponse.test L w p t a b
  have left := mul_eq_one_comm.mp inv
  have collapse (v : I) : (∑k,T v k*R k b) =
      t*p a*w b*(1:Matrix I I ℝ) v b - t*w b*L v a + w v*(1+t*L b a-t*p a) := by
    have eq (k : I) : T v k*R k b =
        t*p a*w b*(L v k*R k b)
        + (-t*w b*L v a+w v*(1+t*L b a))*(p k*R k b)
        - (w v*t*p a)*(L b k*R k b) := by dsimp [T,SharedArcFlatResponse.test]; ring
    rw [sum_congr rfl (fun k _ => eq k),sum_sub_distrib,sum_add_distrib,←mul_sum,←mul_sum,←mul_sum]
    change _*(L*R) v b+_*(p ᵥ* R) b-_*(L*R) b b=_
    rw [left,pc,Matrix.one_apply_eq]
    ring
  have final : (∑v,R a v*(∑k,T v k*R k b))=1+t*L b a-t*(w b+p a) := by
    have eq (v : I) : R a v*(∑k,T v k*R k b) =
        t*p a*w b*(R a v*(1:Matrix I I ℝ) v b)
        - t*w b*(R a v*L v a) + (1+t*L b a-t*p a)*(R a v*w v) := by rw [collapse]; ring
    rw [sum_congr rfl (fun v _ => eq v),sum_add_distrib,sum_sub_distrib,←mul_sum,←mul_sum,←mul_sum]
    change _*(R*(1:Matrix I I ℝ)) a b-_*(R*L) a a+_*(R *ᵥ w) a=_
    rw [mul_one,miss,inv,Matrix.one_apply_eq,wr]
    ring
  have inner (v) : 0<∑k,T v k*R k b := sum_pos' (fun k _ => mul_nonneg (pos v k).le (rn k b))
    ⟨b,mem_univ _,mul_pos (pos v b) rb⟩
  have result := sum_pos' (s:=univ) (fun v _ => mul_nonneg (rn a v) (inner v).le)
    ⟨a,mem_univ _,mul_pos ra (inner a)⟩
  rw [final] at result
  linarith

theorem endpoint {q n} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    (F : Family) {w p : ℕ→ℚ} (wp : ∀i∈X.V,0<w i ∧ 0<p i) (wm : mass X.V w=1)
    (wr : ∀i∈X.V,WeightedSD.row q (graph X.D F) X.V w i=1)
    (pc : ∀i∈X.V,WeightedSD.col q (graph X.D F) X.V p i=1) (f : SharedArcFlatCut.Missing X F) :
    let a := f.val.1
    let b := f.val.2
    let L := (realMatrix q (graph X.D F) X.V)⁻¹
    (q:ℝ)*((w b:ℝ)+(p a:ℝ))<1+(q:ℝ)*L b a := by
  intro a b L
  let R := realMatrix q (graph X.D F) X.V
  have distinct : a≠b := by
    intro same
    have edge : X.D a b=true := f.property.1
    rw [←same] at edge
    exact loopfree X.free (by omega) a.property edge
  have zero : R a b=0 := by simp [R,realMatrix_entry,distinct,show graph X.D F a b=false from f.property.2]
  have rn (i j : X.V) : 0≤R i j := by dsimp only [R]; rw [realMatrix_entry]; split_ifs <;> positivity
  have diag (i : X.V) : 0<R i i := by
    by_cases e : graph X.D F i i=true <;> simp [R,realMatrix_entry,e]
    positivity
  exact aggregate (Matrix.mul_nonsing_inv _ (SharedArcFlatResponse.matrix_unit hq _ _))
    (by simpa using funext (realMatrix_rational_rows w 1 wr)) (by simpa using funext (realMatrix_rational_columns p 1 pc))
    zero rn (diag a) (diag b) (positive X hq small F wp wm wr pc f)


/-- A negative entry is a concrete exit on the old graph with its actual
unit laws. Zero entries cannot occur even before testing safety. -/
def NegativeEntry {q n} (X : Model q n) (F : Family) : Prop :=
  ∃w p : ℕ→ℚ,(∀i∈X.V,0<w i ∧ 0<p i) ∧ mass X.V w=1 ∧
    (∀i∈X.V,WeightedSD.row q (graph X.D F) X.V w i=1) ∧
    (∀i∈X.V,WeightedSD.col q (graph X.D F) X.V p i=1) ∧
    ∃h : SharedArcFlatCut.Missing X F,∃v k : X.V,
      SharedArcFlatResponse.test (realMatrix q (graph X.D F) X.V)⁻¹
        (fun i : X.V => (w i:ℝ)) (fun i : X.V => (p i:ℝ)) q h.val.1 h.val.2 v k<0

def ProgressAt {q n} (X : Model q n) (F : Family) (B : Finset ℕ)
    (H : Matrix X.V X.V ℝ) (p : ℕ→ℚ) (c : ℚ) : Prop :=
  SharedArcPacketDescent.ProgressAt X F B H p c ∨ NegativeEntry X F

theorem blocks {q n} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    {F B H p c} (prior : ¬SharedArcPacketDescent.ProgressAt X F B H p c) : ¬ProgressAt X F B H p c := by
  rintro (done|⟨w,r,wp,wm,wr,pc,f,v,k,neg⟩)
  · exact prior done
  · exact (positive X hq small F wp wm wr pc f v k).asymm neg

/-- A strict positive transition between every two missing arcs, and a
common positive permutation, follow directly if no entry is negative. -/
theorem of_cut {q n} (X : Model q n) (hq : 2≤q) {F B H p c}
    (h : SharedArcFlatCut.ProgressAt X F B H p c) : ProgressAt X F B H p c := by
  classical
  rcases h with prior|⟨w,r,wp,wm,wr,pc,fail⟩
  · exact Or.inl prior
  · right
    refine ⟨w,r,wp,wm,wr,pc,?_⟩
    by_contra! none
    have pos : StrictTests X F w r := by
      intro f v k
      exact lt_of_le_of_ne (none f v k) (Ne.symm (nonzero hq
        (by simpa using funext (realMatrix_rational_rows w 1 wr))
        (by simpa using funext (realMatrix_rational_columns r 1 pc)) _ _ v k))
    apply fail
    unfold SharedArcFlatCut.Conditions
    intro T
    exact ⟨⟨Equiv.refl _,fun k f => pos f k k⟩,fun s t => .single (fun f => pos f s.val.2 t.val.1)⟩

/-- Combining the aggregate with the common terminal price bounds both
endpoint weights for every candidate, including unmarked components. -/
theorem mass_bound {q n} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    {F c} {w p : ℕ→ℚ} (wp : ∀i∈X.V,0<w i ∧ 0<p i) (wm : mass X.V w=1)
    (wr : ∀i∈X.V,WeightedSD.row q (graph X.D F) X.V w i=1)
    (pc : ∀i∈X.V,WeightedSD.col q (graph X.D F) X.V p i=1) (high : (1:ℚ)<c)
    (budget : SharedArcFlatChain.Budget X F c w p) (f : SharedArcFlatCut.Missing X F) :
    (c-1)*(w f.val.2+p f.val.1)<c*p f.val.1*w f.val.2 := by
  have l := endpoint X hq small F wp wm wr pc f
  have u := budget f
  dsimp only at l u
  have clim : (0:ℝ)<(c:ℝ)-1 := by exact_mod_cast sub_pos.mpr high
  have both := (mul_lt_mul_of_pos_left l clim).trans_le u
  have realBound : ((c:ℝ)-1)*((w f.val.2:ℝ)+(p f.val.1:ℝ))<(c:ℝ)*(p f.val.1:ℝ)*(w f.val.2:ℝ) := by
    apply lt_of_mul_lt_mul_left (a:=(q:ℝ))
    · convert both using 1 <;> ring
    · exact Nat.cast_nonneg q
  exact_mod_cast realBound


/-- A supplier for this single local law gives the literal CH theorem. -/
def Law {q n} (X : Model q n) : Prop :=
  ∀C F B,Built X.D C F → F⊆family X → support F=X.V → SmallRow q (graph X.D F) X.V →
    Boundary X F B → (∀M,Boundary X F M → (targets X.D X.V F B).card≤(targets X.D X.V F M).card) →
    ∀H : Matrix X.V X.V ℝ,FiniteCutInverse.CommonInverse (realMatrix q (graph X.D (insert B F)) X.V) H →
    (∀a b : X.V,(a:ℕ)∈B → (b:ℕ)∈B → X.D a b=true → graph X.D F a b=false → 1≤(q:ℝ)*H b a) →
    ∀p : ℕ→ℚ,∀c : ℚ,1<c → (∀v∈X.V,0<p v) → mass X.V p=1 →
    (∀v∈X.V,WeightedSD.col q (graph X.D (insert B F)) X.V p v=c) → ProgressAt X F B H p c

theorem ch_of_tensor (law : ∀q n,∀X : Model q n,2≤q → SmallerSmallRow q X.V.card → Law X) :
    CH.CaccettaHaggkvistConjecture := by
  apply SharedArcPacketDescent.ch_of_descent
  intro q n X hq small C F B built sub spans weak boundary least H inverse charge p c high wp mass cols
  by_contra no
  exact blocks X hq small no
    (law q n X hq small C F B built sub spans weak boundary least H inverse charge p c high wp mass cols)

#print axioms ch_of_tensor

namespace SevenControl
/-- On the interval circulant C7(1,2), these are 2107 times column zero
of the inverse. Cyclic translation gives every column. -/
private def col0 : Fin 7 → ℤ := ![1,-27,729,-720,477,-237,78]

theorem inverse_columns (i j : Fin 7) :
    col0 (i-j)+3*(col0 (i+1-j)+col0 (i+2-j))=if i=j then 2107 else 0 := by
  revert i j
  decide

/-- For the proposed chord 0→4, the row/column contraction is positive,
while the full tensor entry at (2,2) is negative. All four missing chords
give a negative tensor entry. All displayed tests have positive scaling. -/
theorem separates :
    7*(2107+3*col0 4)-6*2107=12124 ∧
    2107+3*(col0 0-col0 2+col0 4-col0 2)= -833 ∧
    ∀b : Fin 7,2<b.val → ∃v k : Fin 7,2107+3*(col0 (v-k)-col0 v+col0 b-col0 (b-k))<0 := by decide

private def localCost (i j : Fin 3) : ℤ :=
  let v : Fin 7 := ⟨i.val,by omega⟩
  let k : Fin 7 := 4-⟨j.val,by omega⟩
  2107+3*(col0 (v-k)-col0 v+col0 4-col0 (4-k))

/-- On this chord even an optimal coupling with the two prescribed
neighbourhood marginals has strictly positive cost. Keeping individual
entries detects the obstruction. Masses here are multiplied by seven. -/
theorem every_coupling (γ : Fin 3 → Fin 3 → ℝ)
    (nonneg : ∀i j,0≤γ i j)
    (row : ∀i,(∑j,γ i j)=if i=0 then 1 else 3)
    (col : ∀j,(∑i,γ i j)=if j=0 then 1 else 3) :
    7840 ≤ ∑i,∑j,γ i j*(localCost i j:ℝ) := by
  have costs : ∀i j : Fin 3,localCost i i+localCost j j≤2*localCost i j := by decide
  have low := sum_le_sum (s:=univ) (fun i _ => sum_le_sum (s:=univ) (fun j _ =>
    mul_le_mul_of_nonneg_left (show (localCost i i:ℝ)+localCost j j≤2*(localCost i j:ℝ) by exact_mod_cast costs i j) (nonneg i j)))
  have left : (∑i,∑j,γ i j*((localCost i i:ℝ)+localCost j j))=15680 := by
    simp_rw [mul_add,sum_add_distrib]
    rw [sum_comm (f:=fun i j => γ i j*(localCost j j:ℝ))]
    simp_rw [←sum_mul,row,col]
    norm_num [Fin.sum_univ_three,localCost,col0]
  rw [left] at low
  simp_rw [mul_left_comm (γ _ _) 2,←mul_sum] at low
  linarith

end SevenControl
#print axioms SevenControl.every_coupling
#print axioms SevenControl.separates

#print axioms of_cut
#print axioms blocks
#print axioms mass_bound
#print axioms endpoint
#print axioms positive
end LeanCH.BR.Closure.SharedArcFlatArithmetic
