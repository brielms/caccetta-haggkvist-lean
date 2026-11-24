import checkpoints.shen_extension.EndpointLayerWitness

namespace LeanCH.BR.Closure.ReturnRowPrices
open Finset Matrix BRq2 BRq3 BR45 WeightedSD FiniteCutInverse
open ShortestCycleWeights FirstPacketBarrier MarkedCyclePeeling SharedArcFlatResponse
open SingleArcPunctureSign OneStepColumnMerge EndpointLayerWitness
open scoped Matrix

section Finite
variable {V : Finset ℕ}

def incoming (D : CH.Digraph) (P : V→ℚ) (U : Finset V) (i : V) : ℚ :=
  ∑t∈U,if D t i then P t else 0

def weight (P : V→ℚ) (U : Finset V) : ℚ := ∑t∈U,P t

private theorem split_in (D : CH.Digraph) (P : V→ℚ) (U : Finset V) (i : V) :
    incoming D P (univ \ U) i+incoming D P U i=incoming D P univ i :=
  sum_sdiff (subset_univ U)

theorem flat_in (E : CH.Digraph) (q : ℕ) (p : ℕ→ℚ)
    (pc : ∀i∈V,WeightedSD.col q E V p i=1) (i : V) :
    p i+(q:ℚ)*incoming E (fun t : V=>p t) univ i=1 := by
  have h := pc i i.property
  unfold WeightedSD.col inW at h
  unfold incoming
  rw [sum_coe_sort V (fun t=>if E t i then p t else 0)]
  exact h

/-- The price of the old parents remaining in U, summed over B, with
edges entering multiple columns counted once per column. -/
theorem incidence_account (E : CH.Digraph) (q : ℕ) (p : ℕ→ℚ)
    (pc : ∀i∈V,WeightedSD.col q E V p i=1) (U B : Finset V) :
    let P := fun t : V=>p t
    (q:ℚ)*(∑i∈B,incoming E P U i) +
      (∑i∈B,(P i+q*incoming E P (univ \ U) i))=B.card := by
  intro P
  rw [mul_sum,←sum_add_distrib]
  have term (i : V) : (q:ℚ)*incoming E P U i+(P i+q*incoming E P (univ \ U) i)=1 := by
    have h := flat_in E q p pc i
    change P i+q*incoming E P univ i=1 at h
    rw [←split_in E P U i] at h
    linarith only [h]
  rw [sum_congr rfl (fun i _=>term i)]; simp

/-- A return row can be selected before naming it. The integer overlap
rebate counts extra incidences of rows hitting two or more dangerous heads. -/
def repeats (E : CH.Digraph) (P : V→ℚ) (U B : Finset V) : ℚ :=
  ∑t∈U,P t*((B.filter (fun i : V=>E t i=true)).card-1:ℕ)

theorem select_iff (E : CH.Digraph) (q : ℕ) (hq : 0<q) (p : ℕ→ℚ)
    (pos : ∀i∈V,0<p i) (pc : ∀i∈V,WeightedSD.col q E V p i=1) (U B : Finset V) :
    let P := fun t : V=>p t
    (∃t∈U,∀i∈B,E t i=false) ↔
      (B.card:ℚ)<(q:ℚ)*(weight P U+repeats E P U B)+
        ∑i∈B,(P i+q*incoming E P (univ \ U) i) := by
  intro P
  let hits (t : V) := (B.filter (fun i : V=>E t i=true)).card
  have double : (∑i∈B,incoming E P U i)=∑t∈U,P t*(hits t:ℕ) := by
    simp only [incoming,sum_comm (s:=B) (t:=U)]
    apply sum_congr rfl
    intro t _
    simp only [hits,←sum_filter,sum_const,nsmul_eq_mul,mul_comm]
  let avoided := U.filter (fun t=>hits t=0)
  have credit : weight P avoided+(∑i∈B,incoming E P U i)=weight P U+repeats E P U B := by
    rw [double]
    simp only [weight,avoided,sum_filter,repeats,←sum_add_distrib]
    apply sum_congr rfl
    intro t _
    change (if hits t=0 then P t else 0)+P t*(hits t:ℕ)=P t+P t*((hits t-1:ℕ):ℚ)
    cases h : hits t with
    | zero => simp
    | succ k => simp; ring
  have eq := incidence_account E q p pc U B
  change (q:ℚ)*(∑i∈B,incoming E P U i)+_= (B.card:ℚ) at eq
  have qp : 0<(q:ℚ) := by exact_mod_cast hq
  have bound : ((B.card:ℚ)<(q:ℚ)*(weight P U+repeats E P U B)+
      ∑i∈B,(P i+q*incoming E P (univ \ U) i)) ↔ 0<weight P avoided := by
    rw [←eq,←credit,mul_add]
    constructor
    · intro h; exact pos_of_mul_pos_right (by linarith only [h] : 0<(q:ℚ)*weight P avoided) qp.le
    · intro h; linarith only [mul_pos qp h]
  rw [bound]
  have clean (t : V) : hits t=0 ↔ ∀i∈B,E t i=false := by
    simp only [hits,card_eq_zero,eq_empty_iff_forall_notMem,mem_filter,not_and]
    exact forall_congr' fun i=>forall_congr' fun _=>Bool.eq_false_iff.symm
  constructor
  · rintro ⟨t,tm,miss⟩
    exact sum_pos' (fun i _=>(pos i i.property).le) ⟨t,mem_filter.mpr ⟨tm,(clean t).mpr miss⟩,pos _ t.property⟩
  · intro h
    obtain ⟨t,hit⟩ : avoided.Nonempty := nonempty_iff_ne_empty.mpr (fun emp=>by simp [weight,emp] at h)
    exact ⟨t,(mem_filter.mp hit).1,(clean t).mp (mem_filter.mp hit).2⟩

/-- A sufficient bound using only the total price, the old flat law and
the incoming mass outside the eligible set. It needs no overlap counts. -/
theorem select (E : CH.Digraph) (q : ℕ) (hq : 0<q) (p : ℕ→ℚ)
    (pos : ∀i∈V,0<p i) (pc : ∀i∈V,WeightedSD.col q E V p i=1) (U B : Finset V)
    (cheap : (B.card:ℚ)<(q:ℚ)*weight (fun i : V=>p i) U+
      ∑i∈B,(p i+q*incoming E (fun r : V=>p r) (univ \ U) i)) :
    ∃t∈U,∀i∈B,E t i=false := by
  apply (select_iff E q hq p pos pc U B).mpr
  have extra : 0≤repeats E (fun i : V=>p i) U B :=
    sum_nonneg (fun i _=>mul_nonneg (pos i i.property).le (Nat.cast_nonneg _))
  dsimp only
  linarith only [cheap,mul_nonneg (Nat.cast_nonneg q : (0:ℚ)≤q) extra]

/-- The same maximum-price eligible row avoids every head whose remaining
incoming mass is below the average eligible price. No sum over heads occurs. -/
theorem select_heavy (E : CH.Digraph) (q : ℕ) (p : ℕ→ℚ)
    (pos : ∀i∈V,0<p i) (pc : ∀i∈V,WeightedSD.col q E V p i=1) (U B : Finset V)
    (live : U.Nonempty)
    (light : ∀i∈B,(U.card:ℚ)*(1-p i-q*incoming E (fun s : V=>p s) (univ \ U) i)<
      (q:ℚ)*weight (fun s : V=>p s) U) :
    ∃t∈U,∀i∈B,E t i=false := by
  let P (i : V) := p i
  obtain ⟨t,tm,mx⟩ := exists_max_image U P live
  have mean : weight P U≤(U.card:ℚ)*P t := by
    calc
      _ ≤ ∑_i∈U,P t := sum_le_sum mx
      _ = _ := by simp
  refine ⟨t,tm,fun i im=>Bool.eq_false_iff.mpr (fun hit=>?_)⟩
  have piece : P t ≤ incoming E P U i := by
    have s := single_le_sum (s:=U) (f:=fun x : V=>if E x i then P x else 0)
      (fun x _=>by split <;> first | exact (pos x x.property).le | rfl) tm
    simpa only [incoming,hit,ite_true] using s
  have law := flat_in E q p pc i
  change P i+q*incoming E P univ i=1 at law
  rw [←split_in E P U i] at law
  have bal : 1-P i-q*incoming E P (univ \ U) i=(q:ℚ)*incoming E P U i := by linarith only [law]
  have cap := light i im
  change (U.card:ℚ)*(1-P i-q*incoming E P (univ \ U) i)<(q:ℚ)*weight P U at cap
  rw [bal] at cap
  have bound := mul_le_mul_of_nonneg_left
    (mean.trans (mul_le_mul_of_nonneg_left piece (Nat.cast_nonneg U.card))) (Nat.cast_nonneg q : 0≤(q:ℚ))
  linarith only [cap,bound]

def shift (y P : V→ℚ) (c : ℚ) : V→ℚ := y-c • P

theorem pick_parent (y P : V→ℚ) (c : ℚ) (K : Finset V) (live : K.Nonempty)
    (bank : c*weight P K≤weight y K) : ∃k∈K,0≤shift y P c k := by
  by_contra! none
  have low : (∑i∈K,y i)<∑i∈K,c*P i := by
    apply sum_lt_sum_of_nonempty live
    intro i im
    have neg := none i im
    change y i-c*P i<0 at neg
    linarith only [neg]
  rw [←mul_sum] at low
  exact (not_lt_of_ge bank) low

private theorem shift_action {A : Matrix V V ℚ} {P : V→ℚ} {b : V} {r : ℚ}
    (spike : ∀i,(P ᵥ* A) i=if i=b then r else 0) (y : V→ℚ) (c : ℚ) (i : V) :
    (shift y P c ᵥ* A) i=(y ᵥ* A) i-(if i=b then c*r else 0) := by
  simp [shift,sub_vecMul,smul_vecMul,spike,smul_eq_mul,mul_ite]

/-- After paying the other heads, the old law can pay b exactly as far
as the chosen parent's coefficient permits. This also describes every
possible scalar price shift, including the credit of a return row k=t. -/
theorem shift_iff {A : Matrix V V ℚ} {P : V→ℚ} {b : V} {r : ℚ}
    (spike : ∀i,(P ᵥ* A) i=if i=b then r else 0) (rp : 0<r) (y m : V→ℚ) (k : V) (pk : 0<P k) :
    (∃s : ℚ,0≤shift y P s k ∧ ∀i,(shift y P s ᵥ* A) i≤m i) ↔
      (∀i : V,i≠b → (y ᵥ* A) i≤m i) ∧ P k*((y ᵥ* A) b-m b)≤r*y k := by
  constructor
  · rintro ⟨s,yk,bound⟩
    have atB := bound b
    rw [shift_action spike,ite_eq_left rfl] at atB
    change 0≤y k-s*P k at yk
    refine ⟨fun i ib=>by simpa [shift_action spike,ib] using bound i,?_⟩
    nlinarith only [mul_le_mul_of_nonneg_left (show (y ᵥ* A) b-m b≤s*r by linarith only [atB]) pk.le,
      mul_le_mul_of_nonneg_left (show s*P k≤y k by linarith only [yk]) rp.le]
  · rintro ⟨off,pay⟩
    refine ⟨y k/P k,?_,fun i=>?_⟩
    · change 0≤y k-(y k/P k)*P k
      rw [div_mul_cancel₀ _ pk.ne']; simp
    rw [shift_action spike]
    by_cases ib : i=b
    · subst i; rw [ite_eq_left rfl]
      have h := (le_div_iff₀ pk).mpr (show ((y ᵥ* A) b-m b)*P k≤r*y k by linarith only [pay])
      have same : r*y k/P k=(y k/P k)*r := by ring
      rw [same] at h; linarith only [h]
    · simpa [ib] using off i ib

end Finite

section Geometry
variable {V : Finset ℕ}

def parents (D : CH.Digraph) (i : V) : Finset V := univ.filter (fun t : V=>D t i=true)

noncomputable def returns (q : ℕ) (D : CH.Digraph) (a j : V) : Finset V := by
  classical exact (parents D a).filter (fun t : V=>Walk D V j t (q-2))

noncomputable def late (q : ℕ) (D : CH.Digraph) (a j : V) : Finset V := by
  classical exact (parents D a).filter (fun t : V=>D t j=false ∧ ¬Walk D V j t (q-2))

private theorem parts {q : ℕ} {D : CH.Digraph} {a j t : V} (ht : t∈returns q D a j) :
    D t a=true ∧ Walk D V j t (q-2) := by
  classical
  obtain ⟨hp,walk⟩ := mem_filter.mp ht
  exact ⟨(mem_filter.mp hp).2,walk⟩

/-- All rows which make the short return miss the exterior column and
every one of its predecessors. The predecessor need not be a head of a. -/
theorem protects {q : ℕ} {D : CH.Digraph} (free : QFree D V q) (hq : 2≤q)
    {a j t : V} (ht : t∈returns q D a j) :
    D t j=false ∧ ∀i : V,D i j=true → t≠i ∧ D t i=false := by
  have walk := (parts ht).2
  refine ⟨Bool.eq_false_iff.mpr (fun ed=>free j ((q-2)+1) (by omega) (by omega) (walk.snoc j.property ed)),?_⟩
  intro i ij
  exact ⟨fun eq=>free j ((q-2)+1) (by omega) (by omega) (walk.snoc j.property (eq ▸ ij)),
    Bool.eq_false_iff.mpr (fun ti=>free j ((q-2)+1+1) (by omega) (by omega)
      ((walk.snoc i.property ti).snoc j.property ij))⟩

theorem late_length {q : ℕ} {D : CH.Digraph} (free : QFree D V q) (sat : BRsub.Sat q D V) (hq : 2≤q)
    {a j s t : V} (out : Exterior D a j) (as' : D a s=true) (sj : D s j=true) (ht : t∈late q D a j) :
    Walk D V j t (q-1) ∧ ∀l,Walk D V j t l → q-1≤l := by
  classical
  obtain ⟨pa,off,abs⟩ := mem_filter.mp ht
  have ta := (mem_filter.mp pa).2
  obtain ⟨_,l,le,walk⟩ := mem_ball.mp (sat j j.property t t.property (by simp [off]))
  have short := (shell D q a free sat hq out as' sj).2
  have low (r) (p : Walk D V j t r) : q-1≤r := by
    have h := short _ (p.snoc a.property ta)
    by_contra! small
    have eq : r=q-2 := by omega
    exact abs (eq ▸ p)
  exact ⟨(le_antisymm le (low l walk)) ▸ walk,low⟩

/-- The incoming flat laws at a and j price the entire return bank.
The sole intermediate distance correction is the price of the late rows. -/
theorem return_mass {q : ℕ} {D : CH.Digraph} (free : QFree D V q) (hq : 2≤q)
    (P : V→ℚ) (a j : V)
    (ca : P a+q*incoming D P univ a=1) (cj : P j+q*incoming D P univ j=1) :
    (q:ℚ)*weight P (returns q D a j)=P j-P a+
      q*incoming D P (univ \ parents D a) j-q*weight P (late q D a j) := by
  classical
  have par : weight P (parents D a)=incoming D P univ a := by simp only [weight,parents,sum_filter,incoming]
  have part : weight P (returns q D a j)+weight P (late q D a j)+incoming D P (parents D a) j=weight P (parents D a) := by
    simp only [returns,late,weight,incoming,sum_filter,←sum_add_distrib]
    apply sum_congr rfl
    intro t ta
    by_cases wt : Walk D V j t (q-2)
    · have ht : t∈returns q D a j := mem_filter.mpr ⟨ta,wt⟩
      simp [wt,(protects free hq ht).1]
    · cases tj : D t j <;> simp [wt]
  rw [par] at part
  have split := split_in D P (parents D a) j
  linarith only [ca,cj,congrArg (fun x : ℚ=>(q:ℚ)*x) part,congrArg (fun x : ℚ=>(q:ℚ)*x) split]

end Geometry

section Repair
variable {V : Finset ℕ}

/-- For a family of scalar inequalities, each negative slope imposes a
lower bound on the repair size. Their maximum (and zero) is the least
candidate, leaving only the inequalities of nonnegative slope. -/
def leastPush (r slope : V→ℚ) (anchor : V) : ℚ :=
  max 0 (univ.sup' (⟨anchor,mem_univ _⟩ : (univ : Finset V).Nonempty)
    (fun i=>if slope i<0 then r i/(-slope i) else 0))

theorem scalar_iff (r slope : V→ℚ) (anchor : V) :
    (∃h : ℚ,0≤h ∧ ∀i,r i+h*slope i≤0) ↔
      ∀i,0≤slope i → r i+leastPush r slope anchor*slope i≤0 := by
  constructor
  · rintro ⟨h,hp,paid⟩
    have least : leastPush r slope anchor≤h := by
      apply max_le hp; apply Finset.sup'_le
      intro i _
      split
      · rename_i neg
        apply (div_le_iff₀ (neg_pos.mpr neg)).mpr
        linarith only [paid i]
      · exact hp
    intro i nonneg
    linarith only [mul_le_mul_of_nonneg_right least nonneg,paid i]
  · intro check
    refine ⟨leastPush r slope anchor,le_max_left ..,fun i=>?_⟩
    by_cases neg : slope i<0
    · have e := (Finset.le_sup' (fun z : V=>if slope z<0 then r z/(-slope z) else 0) (mem_univ i)).trans
        (le_max_right (0:ℚ) _)
      rw [ite_eq_left neg] at e
      change r i/(-slope i)≤leastPush r slope anchor at e
      have lo := (div_le_iff₀ (neg_pos.mpr neg)).mp e
      linarith only [lo]
    · exact check i (le_of_not_gt neg)

def fee (D : CH.Digraph) (q : ℕ) (t i : V) : ℚ :=
  (if t=i then 1 else 0)+(if D t i then (q:ℚ) else 0)-1

/-- Eliminating the old column price shift and the return coefficient
gives a finite necessary and sufficient test for this two-vector repair. -/
theorem priced_iff (D : CH.Digraph) (q : ℕ) {P : V→ℚ} (b t k : V) {rate : ℚ}
    (spike : ∀i,(P ᵥ* SingleArcTensorMerge.center q D V) i=if i=b then rate else 0)
    (ratePos : 0<rate) (pk : 0<P k) (y m : V→ℚ) :
    let A := SingleArcTensorMerge.center q D V
    let r (i : V) := (y ᵥ* A) i-m i-(if i=b then (rate/P k)*y k else 0)
    let slope (i : V) := fee D q t i-(if i=b ∧ t=k then rate/P k else 0)
    (∃h : ℚ,0≤h ∧ ∃s : ℚ,0≤shift (bump y t h) P s k ∧ ∀i,(shift (bump y t h) P s ᵥ* A) i≤m i) ↔
      ∀i,0≤slope i → r i+leastPush r slope t*slope i≤0 := by
  intro A r slope
  rw [←scalar_iff]
  apply exists_congr; intro h
  apply and_congr_right; intro _
  rw [shift_iff spike ratePos _ m k pk]
  have val (i : V) : (bump y t h ᵥ* A) i=(y ᵥ* A) i+h*fee D q t i := bump_action D q y t h i
  have ordinary (i : V) (ib : i≠b) :
      r i+h*slope i≤0 ↔ (bump y t h ᵥ* A) i≤m i := by
    simp [r,slope,ib,val]; constructor <;> intro e <;> linarith only [e]
  have special : r b+h*slope b≤0 ↔
      P k*((bump y t h ᵥ* A) b-m b)≤rate*bump y t h k := by
    have cancel : (rate/P k)*P k=rate := div_mul_cancel₀ _ pk.ne'
    rw [val]
    by_cases tk : t=k
    · simp only [r,slope,bump,eq_self,ite_true,tk,true_and] at *
      constructor
      · intro e
        nlinarith only [mul_nonpos_of_nonpos_of_nonneg e pk.le,congrArg (fun v : ℚ=>v*y k) cancel,
          congrArg (fun v : ℚ=>v*h) cancel]
      · intro e
        apply nonpos_of_mul_nonpos_left _ pk
        nlinarith only [e,congrArg (fun v : ℚ=>v*y k) cancel,congrArg (fun v : ℚ=>v*h) cancel]
    · simp only [r,slope,bump,eq_self,ite_true,tk,Ne.symm tk,and_false,ite_false,add_zero,sub_zero]
      constructor
      · intro e
        nlinarith only [mul_nonpos_of_nonpos_of_nonneg e pk.le,congrArg (fun v : ℚ=>v*y k) cancel]
      · intro e
        apply nonpos_of_mul_nonpos_left _ pk
        nlinarith only [e,congrArg (fun v : ℚ=>v*y k) cancel]
  constructor
  · rintro ⟨off,atB⟩ i
    by_cases ib : i=b
    · exact ib ▸ special.mpr atB
    · exact (ordinary i ib).mpr (off i ib)
  · exact fun all=>⟨fun i ib=>(ordinary i ib).mp (all i),special.mp (all b)⟩

/-- A sufficiently cheap common parent supplies its own edited-head
credit: increasing its return coefficient creates no positive slope at b. -/
theorem own_head (D : CH.Digraph) (q : ℕ) (b t : V) (tb : D t b=true) (ne : t≠b)
    (P : V→ℚ) (pt : 0<P t) (rate : ℚ) :
    fee D q t b-rate/P t≤0 ↔ ((q:ℚ)-1)*P t≤rate := by
  simp only [fee,ne,ite_false,tb,ite_true,zero_add,sub_nonpos]
  exact le_div_iff₀ pt

/-- For the counting test, rows failing their own unchanged diagonal
are removed first. Heads protected by q-freeness cost no budget. -/
noncomputable def eligible (q : ℕ) (D : CH.Digraph) (a j : V) (e : V→ℚ) : Finset V := by
  classical exact (returns q D a j).filter (fun t=>e t≤0)

def danger (q : ℕ) (D : CH.Digraph) (j : V) (e : V→ℚ) (h : ℚ) : Finset V :=
  univ.filter (fun i : V=>i≠j ∧ D i j=false ∧ 0<e i+((q:ℚ)-1)*h)

theorem pay_selected (D : CH.Digraph) (q : ℕ) (free : QFree D V q) (hq : 2≤q)
    (a j : V) (y m : V→ℚ) (h : ℚ)
    (cap : ∀i,(y ᵥ* SingleArcTensorMerge.center q D V) i-m i≤h)
    (t : V) (chosen : t∈eligible q D a j (fun i=>(y ᵥ* SingleArcTensorMerge.center q D V) i-m i))
    (miss : ∀i∈danger q D j (fun i=>(y ᵥ* SingleArcTensorMerge.center q D V) i-m i) h,D t i=false) :
    ∀i,(bump y t h ᵥ* SingleArcTensorMerge.center q D V) i≤m i := by
  classical
  let A := SingleArcTensorMerge.center q D V
  let e (i : V) := (y ᵥ* A) i-m i
  obtain ⟨ret,diag⟩ := mem_filter.mp chosen
  obtain ⟨noJ,owner⟩ := protects free hq ret
  intro i
  rw [bump_action]
  by_cases ti : t=i
  · subst i
    have loop : D t t=false := Bool.eq_false_iff.mpr (loopfree free (by omega) t.property)
    simp [loop]; exact sub_nonpos.mp diag
  cases edge : D t i with
  | false => simp [ti]; have le := cap i; linarith only [le]
  | true =>
    have ij : i≠j := fun eq=>Bool.noConfusion (noJ.symm.trans (eq ▸ edge))
    have off : D i j=false := Bool.eq_false_iff.mpr (fun ed=>Bool.noConfusion ((owner i ed).2.symm.trans edge))
    have low : e i+((q:ℚ)-1)*h≤0 := le_of_not_gt (fun excess=>Bool.noConfusion
      ((miss i (mem_filter.mpr ⟨mem_univ _,ij,off,excess⟩)).symm.trans edge))
    change (y ᵥ* SingleArcTensorMerge.center q D V) i-m i+_≤0 at low
    simp [ti]; linarith only [low]

end Repair


section Native
variable {q n : ℕ} (X : Model q n) (hq : 2≤q) (F : Family)
  {w p : ℕ→ℚ} (pos : ∀i∈X.V,0<w i ∧ 0<p i) (wm : mass X.V w=1)
  (wr : ∀i∈X.V,WeightedSD.row q (graph X.D F) X.V w i=1)
  (pc : ∀i∈X.V,WeightedSD.col q (graph X.D F) X.V p i=1)

private theorem kept (f : SharedArcFlatCut.Missing X F)
    (single : ∀g : SharedArcFlatCut.Missing X F,g=f) (s i : X.V) (out : s≠f.val.1 ∨ i≠f.val.2) :
    graph X.D F s i=X.D s i := by
  by_cases old : graph X.D F s i=true
  · exact old.trans (mem_col.mp (active.mp old).choose_spec).2.2.2.symm
  · have off := Bool.eq_false_iff.mpr old
    refine off.trans (Bool.eq_false_iff.mpr (fun on=>?_)).symm
    let g : SharedArcFlatCut.Missing X F := ⟨(s,i),on,off⟩
    exact out.elim (fun ne=>ne (congrArg (fun u : SharedArcFlatCut.Missing X F=>u.val.1) (single g)))
      (fun ne=>ne (congrArg (fun u : SharedArcFlatCut.Missing X F=>u.val.2) (single g)))

include wm wr pc in
theorem old_mass : mass X.V p=1 := by
  have balance := rational_cross_rows q (graph X.D F) X.V w p
  rw [sum_congr rfl (fun i hi=>show p i*WeightedSD.row q (graph X.D F) X.V w i=p i by rw [wr i hi,mul_one]),
    sum_congr rfl (fun i hi=>show w i*WeightedSD.col q (graph X.D F) X.V p i=w i by rw [pc i hi,mul_one])] at balance
  exact balance.trans wm

include wm wr pc in
theorem old_spike (f : SharedArcFlatCut.Missing X F) :
    let E := graph X.D F
    let A := SingleArcTensorMerge.center q (insertArc E f.val.1 f.val.2) X.V
    ∀i : X.V,((fun s : X.V=>p s) ᵥ* A) i=if i=f.val.2 then q*p f.val.1 else 0 := by
  intro E A i
  let P (s : X.V) := p s
  let a := f.val.1
  let b := f.val.2
  have total : (∑s : X.V,P s)=1 := (sum_coe_sort X.V p).trans (old_mass X F wm wr pc)
  have oldCost := flat_in E q p pc i
  change P i+q*(∑t : X.V,if E t i then P t else 0)=1 at oldCost
  have price (s : X.V) : (if insertArc E a b s i then P s else 0)=
      (if E s i then P s else 0)+(if s=a ∧ i=b then P a else 0) := by
    by_cases atPair : s=a ∧ i=b
    · obtain ⟨rfl,rfl⟩ := atPair
      simp [insertArc,a,b,E,f.property.2]
    · have no : ¬(s.val=a.val ∧ i.val=b.val) := fun hit=>atPair ⟨Subtype.ext hit.1,Subtype.ext hit.2⟩
      rw [show insertArc E a b s i=E s i by unfold insertArc; rw [ite_eq_right no]]
      simp [atPair]
  change (P ᵥ* SingleArcTensorMerge.center q (insertArc E a b) X.V) i=if i=b then (q:ℚ)*P a else 0
  rw [apply_center]
  simp_rw [price]
  rw [sum_add_distrib,total]
  by_cases ib : i=b
  · subst i; simp only [and_true,eq_self,ite_true,sum_ite_eq',mem_univ] at *
    change P b+q*((∑s : X.V,if E s b then P s else 0)+P a)-1=q*P a
    linarith only [oldCost]
  · simp only [ib,and_false,ite_false,sum_const_zero,add_zero]
    change P i+q*(∑s : X.V,if E s i then P s else 0)-1=0
    linarith only [oldCost]

include hq pc in
theorem singleton_return_mass (f : SharedArcFlatCut.Missing X F) (single : ∀g : SharedArcFlatCut.Missing X F,g=f)
    (j : X.V) (out : Exterior X.D f.val.1 j) :
    let P := fun t : X.V=>p t
    let a := f.val.1
    (q:ℚ)*weight P (returns q X.D a j)=p j-p a+
      q*incoming X.D P (univ \ parents X.D a) j-q*weight P (late q X.D a j) := by
  intro P a
  have ab : a≠f.val.2 := by
    intro eq
    have edge : X.D a f.val.2=true := f.property.1
    rw [eq] at edge
    exact loopfree X.free (by omega) f.val.2.property edge
  have jb : j≠f.val.2 := fun eq=>Bool.noConfusion (out.2.symm.trans (eq ▸ f.property.1))
  have law (i : X.V) (ib : i≠f.val.2) : P i+q*incoming X.D P univ i=1 := by
    have same : incoming X.D P univ i=incoming (graph X.D F) P univ i := by
      apply sum_congr rfl; intro t _; rw [kept X F f single t i (.inr ib)]
    rw [same]; exact flat_in _ q p pc i
  exact return_mass X.free hq P a j (law a ab) (law j jb)

include hq pos wm wr pc in
/-- In the bipartite incidence relation "old parent of x misses i",
every nonempty proper set of other heads has strictly more parent
capacity than its price. The full set has equal capacity and price. -/
theorem missed_set_prices (small : SmallerSmallRow q X.V.card) (f : SharedArcFlatCut.Missing X F)
    (x : X.V) (J : Finset ℕ) (sub : J⊆X.V.erase x.val) (live : J.Nonempty) :
    let E := graph X.D F
    let N := inN E X.V x
    let M := N.filter (fun t=>∃i∈J,E t i=false)
    (J≠X.V.erase x.val → mass J p<(q:ℚ)*mass M p) ∧
      (J=X.V.erase x.val → mass J p=(q:ℚ)*mass M p) := by
  classical
  intro E N M
  have pm := old_mass X F wm wr pc
  have charge : p x+(q:ℚ)*mass N p=1 := by
    simpa [N,E,WeightedSD.col,inW,inN,mass,sum_filter] using pc x x.property
  have xj : x.val∉J := fun h=>(mem_erase.mp (sub h)).1 rfl
  have js : J⊆X.V := fun i hi=>(mem_erase.mp (sub hi)).2
  constructor
  · intro proper
    let S := insert x.val J
    let C := StrictFlatSubsetMerge.common (fun i t=>E t i) X.V S
    have old : C⊆N := fun _ tm=>mem_inN.mpr ⟨(mem_filter.mp tm).1,(mem_filter.mp tm).2 x.val (mem_insert_self ..)⟩
    have partition : M=N \ C := by
      ext t
      by_cases tn : t∈N
      · have ed := (mem_inN.mp tn).2
        have tv := (mem_inN.mp tn).1
        simp [M,C,StrictFlatSubsetMerge.common,S,tn,tv,ed,Bool.not_eq_true]
      · simp [M,tn]
    have split : mass M p+mass C p=mass N p := by rw [partition]; exact sum_sdiff old
    have prop : S≠X.V := by
      intro eq; apply proper
      exact (erase_insert xj).symm.trans (congrArg (fun Z : Finset ℕ=>Z.erase x.val) eq)
    have cut := (StrictFlatSubsetMerge.native X hq small F f pos (fun i im=>by rw [wm,wr i im])
      (fun i im=>by rw [pm,pc i im]) (insert_subset_iff.mpr ⟨x.property,js⟩)
      (by rw [card_insert_of_notMem xj]; have := live.card_pos; omega) prop).2
    change mass S p+q*mass C p<mass X.V p at cut
    rw [pm,show mass S p=p x+mass J p from sum_insert xj] at cut
    linarith only [cut,charge,congrArg (fun u : ℚ=>(q:ℚ)*u) split]
  · intro all
    have full : M=N := by
      apply filter_eq_self.mpr
      intro t tm
      obtain ⟨tv,edge⟩ := mem_inN.mp tm
      have loop := loopfree (PrivateArcEndpoints.graph_free X F) (by omega) tv
      have tx : t≠x.val := fun eq=>loop (eq ▸ edge)
      exact ⟨t,all ▸ mem_erase.mpr ⟨tx,tv⟩,Bool.eq_false_iff.mpr loop⟩
    have total := add_sum_erase X.V p x.property
    change p x+mass (X.V.erase x.val) p=mass X.V p at total
    rw [pm] at total
    rw [all,full]; linarith only [total,charge]

include hq pos wm wr pc in
/-- At an exterior head j the short-return and late rows together have
strictly more scaled price than j. The omitted late mass is the exact
loss when using this lower bound for short returns alone. -/
theorem return_reserve (small : SmallerSmallRow q X.V.card) (f : SharedArcFlatCut.Missing X F)
    (single : ∀g : SharedArcFlatCut.Missing X F,g=f) (j : X.V) (out : Exterior X.D f.val.1 j) :
    let a := f.val.1
    let P := fun s : X.V=>p s
    p j<(q:ℚ)*(weight P (returns q X.D a j)+weight P (late q X.D a j)) := by
  classical
  intro a P
  let E := graph X.D F
  let b := f.val.2
  have abEdge : X.D a b=true := f.property.1
  have ab : a≠b := by
    intro eq; rw [eq] at abEdge
    exact loopfree X.free (by omega) b.property abEdge
  have jb : j≠b := by
    intro eq; rw [←eq] at abEdge
    exact Bool.noConfusion (out.2.symm.trans abEdge)
  have ne : j.val≠a.val := fun eq=>out.1 (Subtype.ext eq)
  have sub : {j.val}⊆X.V.erase a.val := singleton_subset_iff.mpr (mem_erase.mpr ⟨ne,j.property⟩)
  have proper : {j.val}≠X.V.erase a.val := by
    intro eq
    have mem : b.val∈({j.val}:Finset ℕ) := eq ▸ mem_erase.mpr ⟨fun e=>ab (Subtype.ext e.symm),b.property⟩
    exact jb (Subtype.ext (mem_singleton.mp mem).symm)
  have law := (missed_set_prices X hq F pos wm wr pc small f a {j.val} sub (singleton_nonempty _)).1 proper
  let members := (inN E X.V a).filter (fun t=>∃i∈({j.val}:Finset ℕ),E t i=false)
  change mass {j.val} p<(q:ℚ)*mass members p at law
  rw [show mass {j.val} p=p j from sum_singleton ..] at law
  have natural : mass members p=∑t : X.V,if E t a=true ∧ E t j=false then P t else 0 := by
    rw [sum_coe_sort X.V (fun t=>if E t a=true ∧ E t j=false then p t else 0)]
    simp [members,inN,mass,sum_filter,ite_and]
  have account : weight P (returns q X.D a j)+weight P (late q X.D a j)=mass members p := by
    rw [natural]
    simp only [weight,returns,late,parents,sum_filter,←sum_add_distrib]
    apply sum_congr rfl
    intro t _
    have oldA : E t a=X.D t a := kept X F f single t a (.inr ab)
    have oldJ : E t j=X.D t j := kept X F f single t j (.inr jb)
    simp only [oldA,oldJ]
    by_cases ta : X.D t a=true
    · by_cases walk : Walk X.D X.V j t (q-2)
      · have rt : t∈returns q X.D a j := mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _,ta⟩,walk⟩
        simp [walk,ta,(protects X.free hq rt).1]
      · cases tj : X.D t j <;> simp [ta,walk]
    · simp [ta]
  rw [account]; exact law

include hq pos wm wr pc in
/-- A native rectangle of arcs with at least two heads has a strict
price budget. A row of the rectangle itself witnesses properness. -/
theorem rectangle_price (small : SmallerSmallRow q X.V.card)
    (S N : Finset ℕ) (sv : S⊆X.V) (nv : N⊆X.V) (two : 2≤S.card) (live : N.Nonempty)
    (edges : ∀t∈N,∀i∈S,X.D t i=true) : mass S p+(q:ℚ)*mass N p<1 := by
  have pm := old_mass X F wm wr pc
  obtain ⟨t,tm⟩ := live
  have proper : S≠X.V := fun eq=>loopfree X.free (by omega) (nv tm) (edges t tm t (eq ▸ nv tm))
  have cmp := (StrictFlatSubsetMerge.host X hq small F pos
    (fun i im=>by rw [wm,wr i im]) (fun i im=>by rw [pm,pc i im]) sv two proper).2
  rw [pm] at cmp
  have sub : N⊆StrictFlatSubsetMerge.common (fun i j=>X.D j i) X.V S := fun i im=>
    mem_filter.mpr ⟨nv im,edges i im⟩
  have le := mass_mono sub (fun i im=>(pos i (mem_filter.mp im).1).2.le)
  linarith only [cmp,mul_le_mul_of_nonneg_left le (Nat.cast_nonneg q : 0≤(q:ℚ))]

include hq pos wm wr pc in
theorem select_merge (small : SmallerSmallRow q X.V.card) (a : X.V) (U B : Finset X.V)
    (live : U.Nonempty) (base : ∀t∈U,X.D t a=true)
    (threshold : ∀i∈B,i≠a ∧ (U.card:ℚ)*(1-p a-p i)≤(q:ℚ)*weight (fun t : X.V=>p t) U) :
    ∃t∈U,∀i∈B,X.D t i=false := by
  let P (i : X.V) := p i
  obtain ⟨t,tm,mx⟩ := exists_max_image U P live
  have mean : weight P U≤(U.card:ℚ)*P t := by
    calc _ ≤ ∑_i∈U,P t := sum_le_sum mx
         _ = _ := by simp
  refine ⟨t,tm,fun i im=>Bool.eq_false_iff.mpr (fun hit=>?_)⟩
  obtain ⟨ne,limit⟩ := threshold i im
  have ai : a.val≠i.val := fun eq=>ne (Subtype.ext eq.symm)
  have forbid := rectangle_price X hq F pos wm wr pc small {a.val,i.val} {t.val}
    (insert_subset_iff.mpr ⟨a.property,singleton_subset_iff.mpr i.property⟩)
    (singleton_subset_iff.mpr t.property) (by simp [ai]) (singleton_nonempty _)
    (by simpa [and_comm] using And.intro (base t tm) hit)
  simp only [mass,sum_insert (notMem_singleton.mpr ai),sum_singleton] at forbid
  have pricelt : (q:ℚ)*P t<1-p a-p i := by linarith only [forbid]
  have strict := mul_lt_mul_of_pos_left pricelt (show (0:ℚ)<U.card by exact_mod_cast live.card_pos)
  have total := mul_le_mul_of_nonneg_left mean (Nat.cast_nonneg q : (0:ℚ)≤q)
  change _≤(q:ℚ)*weight P U at limit
  linarith only [strict,total,limit]

include hq pos wm wr pc in
/-- The strict merge bounds the entire eligible mass that can point at
each dangerous head. Summing those bounds gives one clean eligible row,
including at equality. With one bad head only the missing parent mass at
a needs to be compared with that head's price. -/
theorem select_merge_total (small : SmallerSmallRow q X.V.card) (a : X.V) (U B : Finset X.V)
    (live : U.Nonempty) (base : ∀t∈U,X.D t a=true) (ne : ∀i∈B,i≠a)
    (limit : (∑i∈B,(1-p a-p i))≤(q:ℚ)*weight (fun t : X.V=>p t) U) :
    ∃t∈U,∀i∈B,graph X.D F t i=false := by
  classical
  let E := graph X.D F
  let P (t : X.V) := p t
  let H (i : X.V) := U.filter (fun t : X.V=>E t i=true)
  let C := B.filter (fun i=> (H i).Nonempty)
  have sub : C⊆B := filter_subset ..
  have pair (i : X.V) (im : i∈B) : a.val≠i.val := fun eq=>ne i im (Subtype.ext eq.symm)
  have sv (i : X.V) : ({a.val,i.val}:Finset ℕ)⊆X.V :=
    insert_subset_iff.mpr ⟨a.property,singleton_subset_iff.mpr i.property⟩
  have cost (i : X.V) (im : i∈C) : (q:ℚ)*incoming E P U i<1-p a-p i := by
    let N := (H i).image Subtype.val
    have iv : N⊆X.V := by rintro _ hx; obtain ⟨t,_,rfl⟩ := mem_image.mp hx; exact t.property
    have eq : mass N p=incoming E P U i := by
      rw [mass,sum_image (fun x _ y _ h=>Subtype.ext h)]
      simp only [H,sum_filter,incoming,P]
    have rect := rectangle_price X hq F pos wm wr pc small {a.val,i.val} N (sv i) iv
      (by simp [pair i (sub im)]) ((mem_filter.mp im).2.image _) (by
        rintro _ en
        obtain ⟨t,ht,rfl⟩ := mem_image.mp en
        obtain ⟨tm,hit⟩ := mem_filter.mp ht
        have ed := (mem_col.mp (active.mp hit).choose_spec).2.2.2
        simpa using And.intro (base t tm) ed)
    rw [eq] at rect
    simp only [mass,sum_insert (notMem_singleton.mpr (pair i (sub im))),sum_singleton] at rect
    linarith only [rect]
  have cheap : (∑i∈C,(1-p a-p i))≤∑i∈B,(1-p a-p i) := by
    apply sum_le_sum_of_subset_of_nonneg sub
    intro i im _
    have le := mass_mono (sv i) (fun t tm=>(pos t tm).2.le)
    rw [old_mass X F wm wr pc] at le
    simp only [mass,sum_insert (notMem_singleton.mpr (pair i im)),sum_singleton] at le
    linarith only [le]
  have clear : ∃t∈U,∀i∈C,E t i=false := by
    by_cases nonempty : C.Nonempty
    · have total := sum_lt_sum_of_nonempty nonempty cost
      rw [←mul_sum] at total
      have balance := incidence_account E q p pc U C
      apply select E q (by omega) p (fun i im=>(pos i im).2) pc U C
      linarith only [balance,total,cheap,limit]
    · obtain ⟨t,tm⟩ := live
      exact ⟨t,tm,fun i im=>(nonempty ⟨i,im⟩).elim⟩
  obtain ⟨t,tm,miss⟩ := clear
  exact ⟨t,tm,fun i im=>Bool.eq_false_iff.mpr (fun hit=>Bool.noConfusion
    ((miss i (mem_filter.mpr ⟨im,⟨t,mem_filter.mpr ⟨tm,hit⟩⟩⟩)).symm.trans hit))⟩

include hq pos wm wr pc in
/-- The old column law and the strict merge select a single short return avoiding every unpaid
head. A separate average over the old parents supplies the coordinate of
the signed certificate. Both witnesses are chosen by the theorem. -/
theorem counted_return (small : SmallerSmallRow q X.V.card) (f : SharedArcFlatCut.Missing X F)
    (single : ∀g : SharedArcFlatCut.Missing X F,g=f) (j : X.V)
    (y : X.V→ℚ) (σ h : ℚ) (hp : 0≤h) (B₀ : Finset ℕ) (K₀ : Matrix X.V X.V ℝ)
    (prices : ℕ→ℚ) (c : ℚ) :
    let E := graph X.D F
    let a := f.val.1
    let b := f.val.2
    let P := fun t : X.V=>p t
    let A := SingleArcTensorMerge.center q X.D X.V
    let m := mergeCoefficient q X.D X.V {a.val,b.val}
    let z := shift y P σ
    let e := fun i=>(y ᵥ* A) i-m i-(if i=b then σ*((q:ℚ)*P a) else 0)
    let U := eligible q X.D a j e
    let B := danger q X.D j e h
    let T := test (realMatrix q E X.V)⁻¹ (fun i : X.V=>(w i:ℝ)) (fun i : X.V=>(p i:ℝ)) q a b
    σ*(1-P b)≤(q:ℚ)*weight y (parents E b) → (∀i,e i≤h) →
    ((B.card:ℚ)<(q:ℚ)*weight P U+∑i∈B,(P i+q*incoming E P (univ \ U) i) ∨
      (U.Nonempty ∧ ∀i∈B,(U.card:ℚ)*(1-P i-q*incoming E P (univ \ U) i)<(q:ℚ)*weight P U) ∨
      (U.Nonempty ∧ ∀i∈B,i≠a ∧ (U.card:ℚ)*(1-P a-P i)≤(q:ℚ)*weight P U) ∨
      (U.Nonempty ∧ (∀i∈B,i≠a) ∧ (∑i∈B,(1-P a-P i))≤(q:ℚ)*weight P U)) →
    ∃t∈U,Walk X.D X.V j t (q-2) ∧ X.D t a=true ∧
      (∀i,(bump z t h ᵥ* A) i≤m i) ∧
      (∃v k : X.V,E a v=true ∧ E k b=true ∧ 0≤bump z t h k ∧ T v k<0) ∧
      SharedArcPivotGate.ProgressAt X F B₀ K₀ prices c := by
  classical
  intro E a b P A m z e U B T bank cap testPrice
  have qp : (0:ℚ)<q := by exact_mod_cast (show 0<q by omega)
  have native : SingleArcTensorMerge.center q (insertArc E a b) X.V=A := center_singleton X F f single
  have spike : ∀i,(P ᵥ* A) i=if i=b then (q:ℚ)*P a else 0 := by
    rw [←native]; exact old_spike X F wm wr pc f
  have res : (fun i=>(z ᵥ* A) i-m i)=e := by
    funext i; rw [show (z ᵥ* A) i=_ from shift_action spike y σ i]; dsimp only [e]; ring
  have picked : ∃t∈U,∀i∈B,E t i=false := by
    rcases testPrice with union | ⟨live,each⟩ | ⟨live,each⟩ | ⟨live,ne,total⟩
    · exact select E q (by omega) p (fun i im=>(pos i im).2) pc U B union
    · exact select_heavy E q p (fun i im=>(pos i im).2) pc U B live each
    · obtain ⟨t,tm,miss⟩ := select_merge X hq F pos wm wr pc small a U B live
        (fun s sm=>(parts (show s∈returns q X.D a j from (mem_filter.mp sm).1)).1) each
      refine ⟨t,tm,fun i im=>Bool.eq_false_iff.mpr (fun old=>?_)⟩
      have nativeHit := (mem_col.mp (active.mp old).choose_spec).2.2.2
      exact Bool.noConfusion ((miss i im).symm.trans nativeHit)
    · exact select_merge_total X hq F pos wm wr pc small a U B live
        (fun s sm=>(parts (show s∈returns q X.D a j from (mem_filter.mp sm).1)).1) ne total
  obtain ⟨t,tm,miss⟩ := picked
  have ret : t∈returns q X.D a j := (mem_filter.mp tm).1
  obtain ⟨ta,walk⟩ := parts ret
  have ne : t≠a := fun eq=>loopfree X.free (by omega) a.property (eq ▸ ta)
  have paid : ∀i,(bump z t h ᵥ* A) i≤m i := by
    apply pay_selected X.D q X.free hq a j z m h
    · intro i; exact (congrFun res i).trans_le (cap i)
    · change t∈eligible q X.D a j (fun i=>(z ᵥ* A) i-m i)
      rw [res]; exact tm
    · change ∀i∈danger q X.D j (fun i=>(z ᵥ* A) i-m i) h,X.D t i=false
      rw [res]; intro i im
      rw [←kept X F f single t i (.inl ne)]; exact miss i im
  have col := flat_in E q p pc b
  have inc : weight P (parents E b)=incoming E P univ b := by simp only [weight,parents,sum_filter,incoming]
  change P b+q*incoming E P univ b=1 at col
  rw [←inc] at col
  have charge : (q:ℚ)*weight P (parents E b)=1-P b := by linarith only [col]
  have credit : σ*weight P (parents E b)≤weight y (parents E b) := by
    apply le_of_mul_le_mul_left _ qp
    calc
      (q:ℚ)*(σ*weight P (parents E b))=σ*((q:ℚ)*weight P (parents E b)) := by ring
      _ ≤ _ := charge ▸ bank
  obtain ⟨old,oldArc⟩ := parent X hq F pos wm wr pc f
  obtain ⟨k,km,good⟩ := pick_parent y P σ (parents E b) ⟨old.val,mem_filter.mpr ⟨mem_univ _,oldArc⟩⟩ credit
  have kb : E k b=true := (mem_filter.mp km).2
  have ka : k≠a := fun eq=>Bool.noConfusion ((eq ▸ kb).symm.trans f.property.2)
  have k_ne_b : k≠b := fun eq=>loopfree (PrivateArcEndpoints.graph_free X F) (by omega) b.property (eq ▸ kb)
  let k' : rest a b := ⟨k,mem_erase.mpr ⟨k_ne_b,mem_erase.mpr ⟨ka,mem_univ _⟩⟩⟩
  have good' : 0≤bump z t h k := add_nonneg good (by split <;> simp [hp])
  have child : ∀i,(bump z t h ᵥ* SingleArcTensorMerge.center q (insertArc E a b) X.V) i≤m i := by
    rw [native]; exact paid
  obtain ⟨v,av,bad⟩ := sign_of_bound X hq F pos wm wr pc small f k' kb _ good' child
  exact ⟨t,tm,walk,ta,paid,⟨v,k,av,kb,good',bad⟩,Or.inl (Or.inl (Or.inl (Or.inr ⟨w,p,pos,wm,wr,pc,f,v,k,bad⟩)))⟩

end Native

end LeanCH.BR.Closure.ReturnRowPrices

#print axioms LeanCH.BR.Closure.ReturnRowPrices.select_iff
#print axioms LeanCH.BR.Closure.ReturnRowPrices.select_heavy
#print axioms LeanCH.BR.Closure.ReturnRowPrices.select_merge_total
#print axioms LeanCH.BR.Closure.ReturnRowPrices.missed_set_prices
#print axioms LeanCH.BR.Closure.ReturnRowPrices.return_reserve
#print axioms LeanCH.BR.Closure.ReturnRowPrices.priced_iff
#print axioms LeanCH.BR.Closure.ReturnRowPrices.singleton_return_mass
#print axioms LeanCH.BR.Closure.ReturnRowPrices.counted_return

