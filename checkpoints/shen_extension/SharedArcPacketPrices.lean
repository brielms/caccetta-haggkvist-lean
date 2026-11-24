import checkpoints.shen_extension.SharedArcMinimalPacket

namespace LeanCH.BR.Closure.SharedArcPacketPrices
open Finset Matrix BRq2 BRq3 BR45 WeightedSD ShenCycleSuccessor ShortestCycleWeights FirstPacketBarrier
open MarkedCyclePeeling SharedArcExpansion SharedArcBarrier FiniteCutInverse
open scoped Matrix

/-- Any nonzero nonnegative excess profile on the changed heads is realized,
up to one positive scale, by prices that still pay all old columns. The
same inverse and the same support work for every profile. -/
theorem realize {D V q F B} (cb : Cycle D V q B)
    {H : Matrix V V ℝ} (inv : CommonInverse (realMatrix q (graph D (insert B F)) V) H)
    (charge : ∀a b : V,(a:ℕ)∈B → (b:ℕ)∈B → D a b=true → graph D F a b=false → 1≤(q:ℝ)*H b a)
    (t : ℕ→ℝ) (tn : ∀v∈V,0≤t v) (live : ∃v∈V,0<t v)
    (supp : ∀v∈V,v∉targets D V F B → t v=0) :
    ∃p : ℕ→ℝ, ∃m : ℝ,0<m ∧ RealDual q (graph D F) V 1 p ∧
      (∀v : V,m*p v=∑i : V,t i*H i v) ∧
      ∀v∈V,realCol q (graph D (insert B F)) V p v=1+t v/m := by
  classical
  let G := graph D (insert B F)
  let R := realMatrix q G V
  let f := fun v : V => t v
  let S := f ᵥ* H
  let m := ∑v,S v
  have sn (v : V) : 0≤S v := sum_nonneg (fun i _ => mul_nonneg (tn i i.property) (inv.nonneg i v))
  have restore : S ᵥ* excess R=f := by
    change (f ᵥ* H) ᵥ* excess R=f
    rw [vecMul_vecMul,mul_eq_one_comm.mp inv.right,vecMul_one]
  have mp : 0<m := by
    obtain ⟨v,vv,hi⟩ := live
    obtain ⟨j,hj⟩ : ∃j : V,0<H ⟨v,vv⟩ j := by
      by_contra! no
      exact (inverse_row_sum_pos inv (⟨v,vv⟩ : V)).not_ge (sum_nonpos (fun i _ => no i))
    have pos : 0<S j := lt_of_lt_of_le (mul_pos hi hj) (single_le_sum
      (f:=fun i : V => t i*H i j) (fun i _ => mul_nonneg (tn i i.property) (inv.nonneg i j)) (mem_univ (⟨v,vv⟩ : V)))
    exact sum_pos' (fun i _ => sn i) ⟨j,mem_univ j,pos⟩
  let p := realExtendWeight V (fun v => S v/m)
  have pv (v : V) : p v=S v/m := realExtendWeight_on V _ v
  have pm : realMass V p=1 := by
    rw [realMass_extendWeight,←sum_div]
    exact div_self mp.ne'
  have pn (v) (vv : v∈V) : 0≤p v := by rw [pv ⟨v,vv⟩]; exact div_nonneg (sn _) mp.le
  have scaled (v : V) : m*p v=∑i : V,t i*H i v := by
    rw [pv]; field_simp; rfl
  have value (v) (vv : v∈V) : realCol q G V p v=1+t v/m := by
    let j : V := ⟨v,vv⟩
    have rr := congrFun restore j
    rw [vecMul_excess] at rr
    change (S ᵥ* R) j-m=t v at rr
    rw [←realMatrix_col q G V p j]
    change (∑k : V,p k*R k j)=1+t v/m
    simp_rw [pv,div_mul_eq_mul_div]
    rw [←sum_div]
    apply (div_eq_iff mp.ne').mpr
    change (S ᵥ* R) j=_
    field_simp
    linarith
  refine ⟨p,m,mp,⟨pn,pm,fun v vv => ?_⟩,scaled,value⟩
  have cap := value v vv
  by_cases hit : v∈targets D V F B
  · obtain ⟨u,ub,vb,uv,no,eq⟩ := (column (q:=q) (F:=F) cb p vv).2 hit
    let a : V := ⟨u,cb.sub ub⟩
    let b : V := ⟨v,vv⟩
    have threshold := charge a b ub vb uv no
    have term : t v*H b a≤S a := single_le_sum (f:=fun i : V => t i*H i a)
      (fun i _ => mul_nonneg (tn i i.property) (inv.nonneg i a)) (mem_univ b)
    have paid : t v/m≤(q:ℝ)*p u := by
      rw [pv a,←mul_div_assoc]
      apply div_le_div_of_nonneg_right _ mp.le
      calc
        t v ≤ t v*((q:ℝ)*H b a) := by simpa using (mul_le_mul_of_nonneg_left threshold (tn v vv))
        _ = (q:ℝ)*(t v*H b a) := by ring
        _ ≤ (q:ℝ)*S a := mul_le_mul_of_nonneg_left term (Nat.cast_nonneg _)
    change realCol q G V p v= _ at eq
    linarith
  · rw [(column (q:=q) (F:=F) cb p vv).1 hit] at cap
    rw [supp v vv hit,zero_div,add_zero] at cap
    exact cap.le

/-- The row equalizer fixes the scale in the preceding construction exactly. -/
theorem scale {q G V} {x p t : ℕ→ℝ} {c m : ℝ} (mp : 0<m)
    (pm : realMass V p=1) (xm : realMass V x=1) (rows : ∀v∈V,realRow q G V x v=c)
    (cols : ∀v∈V,realCol q G V p v=1+t v/m) :
    (c-1)*m=∑v∈V,x v*t v := by
  have total := real_cross_rows q G V x p
  rw [sum_congr rfl (fun v vv => by rw [rows v vv]),←sum_mul] at total
  change realMass V p*c=_ at total
  rw [pm,one_mul,sum_congr rfl (fun v vv => by rw [cols v vv,mul_add,mul_one,←mul_div_assoc]),
    sum_add_distrib,←sum_div] at total
  change c=realMass V x+_/m at total
  rw [xm] at total
  field_simp at total
  linarith

/-- Compare the proposed incoming tail with the predecessor whose charge is
already reserved at this head. The zero alternative also handles heads
unchanged by the first cycle. All tests are linear in the chosen profile. -/
def compareTails {q : ℕ} {V : Finset ℕ} (D : CH.Digraph) (F : Family) (B M : Finset ℕ)
    (H : Matrix V V ℝ) (t : ℕ→ℝ) : Prop :=
  let score := fun i : V => ∑k : V,t k*H k i
  ∀i j : V,(i:ℕ)∈M → (j:ℕ)∈M → D i j=true → graph D F i j=false →
    (t j+(q:ℝ)*score i≤0 ∨ ∃a : V,(a:ℕ)∈B ∧ (j:ℕ)∈B ∧ D a j=true ∧ graph D F a j=false ∧
      t j+(q:ℝ)*score i≤(q:ℝ)*score a)

/-- For the constructed prices the componentwise comparison is exact,
including new targets outside the first cycle. -/
theorem compare_iff {q D V F B M} (cb : Cycle D V q B) (cm : Cycle D V q M)
    {H : Matrix V V ℝ} {t p : ℕ→ℝ} {m : ℝ} (mp : 0<m) (dual : RealDual q (graph D F) V 1 p)
    (scaled : ∀v : V,m*p v=∑k : V,t k*H k v)
    (cols : ∀v∈V,realCol q (graph D (insert B F)) V p v=1+t v/m) :
    compareTails (q:=q) D F B M H t ↔ RealDual q (graph D (insert M F)) V 1 p := by
  classical
  rw [SharedArcBudget.fits_iff cm dual]
  have same {a i j : V} (ab : (a:ℕ)∈B) (jb : (j:ℕ)∈B) (aj : D a j=true) (no : graph D F a j=false) :
      (t j+(q:ℝ)*(∑k : V,t k*H k i)≤(q:ℝ)*(∑k : V,t k*H k a)) ↔
        realCol q (graph D F) V p j+q*p i≤1 := by
    have jt : (j:ℕ)∈targets D V F B := mem_filter.mpr ⟨j.property,jb,a,ab,aj,no⟩
    obtain ⟨u,ub,_,uj,_,bill⟩ := (column (q:=q) (F:=F) cb p j.property).2 jt
    have one : (inN D B j).card≤1 := (cb.incoming j jb).le
    have eq : u=(a:ℕ) := card_le_one.mp one _ (mem_inN.mpr ⟨ub,uj⟩) _ (mem_inN.mpr ⟨ab,aj⟩)
    rw [eq,cols j j.property] at bill
    rw [←scaled i,←scaled a]
    have ident : m*(realCol q (graph D F) V p j+q*p i-1)=t j+(q:ℝ)*(m*p i)-(q:ℝ)*(m*p a) := by
      field_simp at bill
      linear_combination -bill
    constructor
    · intro l
      by_contra! fail
      have up := mul_pos mp (sub_pos.mpr fail)
      linarith only [ident,up,l]
    · intro pay
      have low := mul_nonpos_of_nonneg_of_nonpos mp.le (sub_nonpos.mpr pay)
      linarith only [ident,low]
  have plain {i j : V} (eq : realCol q (graph D F) V p j=1+t j/m) :
      (t j+(q:ℝ)*(∑k : V,t k*H k i)≤0) ↔ realCol q (graph D F) V p j+q*p i≤1 := by
    rw [eq,←scaled i]
    constructor <;> intro h
    · by_contra! hi
      have gain := mul_pos (sub_pos.mpr hi) mp
      field_simp at gain
      linarith
    · have loss := mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr h) mp.le
      field_simp at loss
      linarith
  constructor
  · intro comparisons i im j jm ij missing
    let a : V := ⟨i,cm.sub im⟩
    let b : V := ⟨j,cm.sub jm⟩
    rcases comparisons a b im jm ij missing with zero|⟨w,wb,jb,wj,off,le⟩
    · by_cases jt : j∈targets D V F B
      · obtain ⟨u,ub,jb,uj,no,_⟩ := (column (q:=q) (F:=F) cb p b.property).2 jt
        let w : V := ⟨u,cb.sub ub⟩
        apply (same (a:=w) (i:=a) (j:=b) ub jb uj no).mp
        exact zero.trans (mul_nonneg (Nat.cast_nonneg _) ((scaled w) ▸ mul_nonneg mp.le (dual.nonneg w w.property)))
      · exact (plain (i:=a) (j:=b) (((column (q:=q) (F:=F) cb p b.property).1 jt).symm.trans (cols b b.property))).mp zero
    · exact (same (a:=w) (i:=a) (j:=b) wb jb wj off).mp le
  · intro paid i j im jm ij off
    have fit := paid i im j jm ij off
    by_cases jt : (j:ℕ)∈targets D V F B
    · obtain ⟨u,ub,jb,uj,no,_⟩ := (column (q:=q) (F:=F) cb p j.property).2 jt
      let w : V := ⟨u,cb.sub ub⟩
      exact Or.inr ⟨w,ub,jb,uj,no,(same (a:=w) (i:=i) (j:=j) ub jb uj no).mpr fit⟩
    · exact Or.inl ((plain (i:=i) (j:=j) (((column (q:=q) (F:=F) cb p j.property).1 jt).symm.trans (cols j j.property))).mpr fit)

/-- A counterexample blocks every supported price profile and every competing
boundary cycle, in the coordinates of a single fixed inverse. -/
theorem barrier {q n} (X : Model q n) {F B} (step : Boundary X F B)
    {H : Matrix X.V X.V ℝ} (inv : CommonInverse (realMatrix q (graph X.D (insert B F)) X.V) H)
    (charge : ∀a b : X.V,(a:ℕ)∈B → (b:ℕ)∈B → X.D a b=true → graph X.D F a b=false → 1≤(q:ℝ)*H b a)
    (stop : ∀M,Boundary X F M → ¬SmallRow q (graph X.D (insert M F)) X.V)
    (t : ℕ→ℝ) (tn : ∀v∈X.V,0≤t v) (live : ∃v∈X.V,0<t v)
    (supp : ∀v∈X.V,v∉targets X.D X.V F B → t v=0) {M} (comp : Boundary X F M) :
    ¬compareTails (q:=q) X.D F B M H t := by
  classical
  have cb : Cycle X.D X.V q B := (mem_filter.mp step.1).2
  obtain ⟨p,m,mp,dual,scaled,cols⟩ := realize cb inv charge t tn live supp
  intro fits
  exact stop M comp (smallRow_of_realDual ((compare_iff cb (mem_filter.mp comp.1).2 mp dual scaled cols).mp fits))

#print axioms compare_iff
#print axioms barrier

#print axioms realize
#print axioms scale
end LeanCH.BR.Closure.SharedArcPacketPrices
