import checkpoints.shen_extension.SingleArcTensorMerge
import Mathlib.Algebra.Ring.GeomSum

namespace LeanCH.BR.Closure.PunctureWalkCertificate
open Finset Matrix FiniteCutInverse BRq2 BRq3 BR45 WeightedSD
open ShortestCycleWeights FirstPacketBarrier MarkedCyclePeeling SharedArcFlatResponse
open SingleArcPunctureSign
open scoped Matrix

theorem split_sum {I : Type*} [Fintype I] [DecidableEq I] (a b : I)
    (ab : a≠b) (g : I→ℝ) : (∑i,g i)=g a+g b+∑i : rest a b,g i.val := by
  rw [sum_coe_sort]
  have A := sum_erase_add (s:=univ) g (mem_univ a)
  have B := sum_erase_add (s:=univ.erase a) g (mem_erase.mpr ⟨ab.symm,mem_univ b⟩)
  unfold rest; linarith only [A,B]

/-- Eliminating the two endpoint rows from a signed full row. C is the old
centered matrix; the change of size q in its (a,b) entry is accounted for
by the balance equation on column b. -/
private theorem restrict_row {I : Type*} [Fintype I] [DecidableEq I]
    (C : Matrix I I ℝ) (a b : I) (ab : a≠b) (q : ℝ) (qn : q-1≠0)
    (aa : C a a=0) (bb : C b b=0) (off : C a b= -1) (back : C b a= -1)
    (x : I→ℝ) (bal : (x ᵥ* C) b= -q*x a) (j : rest a b) :
    ((fun i : rest a b => x i.val) ᵥ* reduced C a b (q-1)) j=
      (x ᵥ* C) j.val+(x ᵥ* C) a*C b j.val := by
  let inner (t : I) := ∑i : rest a b,x i.val*C i.val t
  have eq (t : I) : (x ᵥ* C) t=x a*C a t+x b*C b t+inner t := split_sum a b ab _
  have ea := eq a
  have eb := eq b
  rw [aa,back] at ea
  rw [bb,off,bal] at eb
  have ib : inner b/(q-1)= -x a := by
    apply (div_eq_iff qn).mpr; linarith only [eb]
  have expand : ((fun i : rest a b => x i.val) ᵥ* reduced C a b (q-1)) j=
      inner j+inner a*C b j.val-inner b/(q-1)*C a j.val := by
    change (∑i : rest a b,x i.val*(C i j+C i a*C b j-C i b/(q-1)*C a j))=_
    simp only [inner,mul_sub,mul_add,←mul_assoc,←mul_div_assoc,sum_sub_distrib,sum_add_distrib,←sum_mul,←sum_div]
  rw [expand,ib,eq j.val,show inner a=(x ᵥ* C) a+x b by linarith only [ea]]
  ring

section Walks
variable {V : Finset ℕ} (q : ℕ) (E : CH.Digraph)

/-- Each length-d walk contributes (-q)^d. -/
noncomputable def step (V : Finset ℕ) : Matrix V V ℝ := 1-realMatrix q E V

theorem step_entry (i j : V) : step q E V i j=if E i j=true then -(q:ℝ) else 0 := by
  simp only [step,Matrix.sub_apply,one_apply,realMatrix_entry]
  by_cases ed : E i j=true <;> simp [ed]

/-- Natural path counts, with multiplicities even when different walks
have the same endpoints. -/
def count (V : Finset ℕ) : ℕ→Matrix V V ℕ
  | 0 => 1
  | d+1 => fun i j => ∑h : V,if E i h=true then count V d h j else 0

theorem power_count (d : ℕ) (i j : V) :
    (step q E V ^ d) i j=(-(q:ℝ))^d*(count E V d i j:ℝ) := by
  induction d generalizing i with
  | zero => by_cases e : i=j <;> simp [count,one_apply,e]
  | succ d ih =>
    rw [pow_succ',mul_apply,count]
    push_cast
    rw [mul_sum]
    apply sum_congr rfl
    intro u _
    rw [step_entry,ih]
    by_cases ed : E i u=true <;> simp [ed,pow_succ',mul_assoc]

private theorem no_power (d : ℕ) (i j : V) (no : ¬Walk E V i j d) :
    (step q E V ^ d) i j=0 := by
  induction d generalizing i with
  | zero =>
    have ne : i≠j := by rintro rfl; exact no (.refl _)
    simp [ne]
  | succ d ih =>
    rw [pow_succ',mul_apply]
    apply sum_eq_zero
    intro u _
    by_cases ed : E i u=true
    · rw [ih u (fun path => no (.step u.property ed path)),mul_zero]
    · simp [step_entry,ed]

noncomputable def walkSum (V : Finset ℕ) (m : ℕ) : Matrix V V ℝ :=
  ∑d∈range m,step q E V ^ d

/-- A native approach of length s excludes every old return of length
less than m as soon as s+m≤q+1. The approach may use other native arcs. -/
theorem zero_after_path {D : CH.Digraph} (free : QFree D V q)
    (sub : ∀x y,E x y=true → D x y=true) {x y : V} {s m : ℕ}
    (path : Walk D V y x s) (sp : 0<s) (budget : s+m≤q+1) : walkSum q E V m x y=0 := by
  simp only [walkSum,Matrix.sum_apply]
  apply sum_eq_zero
  intro d hd
  apply no_power
  intro ret
  have len := mem_range.mp hd
  exact free _ (s+d) (by omega) (by omega) (path.append (walk_sub sub ret))

/-- A return along an existing host arc would close a globally forbidden
short walk. This applies to every coefficient before the chosen horizon. -/
theorem prefix_zero {D : CH.Digraph} (free : QFree D V q)
    (sub : ∀x y,E x y=true → D x y=true) {x y : V} (edge : D y x=true)
    {m : ℕ} (short : m≤q) : walkSum q E V m x y=0 := by
  exact zero_after_path q E free sub (Walk.step x.property edge (.refl _)) (by decide) (by omega)

/-- The full signed row obtained by launching from b with coefficient t
and from an old successor v with coefficient -1. -/
noncomputable def probe (m : ℕ) (t : ℝ) (v b : V) (j : V) :=
  t*walkSum q E V m b j-walkSum q E V m v j

/-- Its uncentered residual uses only length-m counts and the two seeds. -/
noncomputable def boundary (m : ℕ) (t : ℝ) (v b : V) (j : V) :=
  t*((1:Matrix V V ℝ) b j-(step q E V^m) b j)-
    ((1:Matrix V V ℝ) v j-(step q E V^m) v j)

theorem probe_row (m : ℕ) (t : ℝ) (v b j : V) :
    (probe q E m t v b ᵥ* realMatrix q E V) j=boundary q E m t v b j := by
  have tel : walkSum q E V m*realMatrix q E V=1-step q E V^m := by
    have h := geom_sum_mul_neg (step q E V) m
    simpa only [walkSum,step,sub_sub_cancel] using h
  change (∑i : V,(t*walkSum q E V m b i-walkSum q E V m v i)*realMatrix q E V i j)=_
  simp only [sub_mul,mul_assoc,sum_sub_distrib,←mul_sum]
  change t*(walkSum q E V m*realMatrix q E V) b j-(walkSum q E V m*realMatrix q E V) v j=_
  rw [tel]; rfl

/-- Signed mass to remove in the direction of the flat column law. -/
noncomputable def price (a b v : V) (m : ℕ) (t : ℝ) (p : ℕ→ℚ) :=
  (boundary q E m t v b b-∑i,probe q E m t v b i)/((q:ℝ)*(p a:ℝ))

/-- The projected row on the proper puncture. -/
noncomputable def candidate (a b v : V) (m : ℕ) (t : ℝ) (p : ℕ→ℚ) (i : rest a b) :=
  probe q E m t v b i.val-price q E a b v m t p*(p i.val:ℝ)

/-- The column residual after eliminating both endpoints. It uses the
old incidences and finite signed walk counts alone. -/
noncomputable def residual (a b v : V) (m : ℕ) (t : ℝ) (j : rest a b) :=
  boundary q E m t v b j.val-boundary q E m t v b a+
    (boundary q E m t v b a-∑i,probe q E m t v b i)*(if E b j.val=true then (q:ℝ) else 0)

end Walks

/-- Discharge all support equalities using only inverse signs on rows
outside the permitted source set. The coordinate at k can only increase. -/
theorem repair {I : Type*} [Fintype I] [DecidableEq I] {B J : Matrix I I ℝ} (right : B*J=1)
    (S : I→Prop) (k : I) (y : I→ℝ) (live : 0<y k) (le : ∀j,(y ᵥ* B) j≤0)
    (outside : ∀j,¬S j → 0≤J j k) :
    ∃z : I→ℝ,0<z k ∧ (∀j,(z ᵥ* B) j≤0) ∧ (∀j,¬S j → (z ᵥ* B) j=0) := by
  classical
  let h (i : I) := if S i then 0 else (y ᵥ* B) i
  let z := y-h ᵥ* J
  have hk : (h ᵥ* J) k≤0 := by
    apply sum_nonpos
    intro i _
    by_cases si : S i
    · simp [h,si]
    · simpa only [h,ite_eq_right si] using mul_nonpos_of_nonpos_of_nonneg (le i) (outside i si)
  have eq : z ᵥ* B=y ᵥ* B-h := by
    rw [show z=y-h ᵥ* J from rfl,sub_vecMul,vecMul_vecMul,mul_eq_one_comm.mp right,vecMul_one]
  refine ⟨z,lt_of_lt_of_le live (by change y k≤y k-(h ᵥ* J) k; linarith),?_,?_⟩
  · intro j; rw [eq]; by_cases sj : S j <;> simp [h,sj,le j]
  · intro j sj; rw [eq]; simp [h,sj]

section Native
variable {q n : ℕ} (X : Model q n) (hq : 2≤q) (F : Family)
  {w p : ℕ→ℚ} (pos : ∀i∈X.V,0<w i ∧ 0<p i) (wm : mass X.V w=1)
  (wr : ∀i∈X.V,WeightedSD.row q (graph X.D F) X.V w i=1)
  (pc : ∀i∈X.V,WeightedSD.col q (graph X.D F) X.V p i=1)

include hq pos wm wr pc in
/-- Both the coordinate at each old parent and the residual on every
puncture column are explicit. The projection formula has no terminal
inequality or vanishing assumption on the last walk layer. -/
theorem accounts (f : SharedArcFlatCut.Missing X F) (v : X.V) (m : ℕ) (short : m≤q) (t : ℝ)
    (reach : ∃s,0<s ∧ s+m≤q+1 ∧ Walk X.D X.V f.val.1 v s) :
    let E := graph X.D F
    let a := f.val.1
    let b := f.val.2
    let z := candidate q E a b v m t p
    (∀j,(z ᵥ* puncture q E a b) j=residual q E a b v m t j) ∧
      ∀k : rest a b,E k.val b=true → z k= -walkSum q E X.V m v k.val-price q E a b v m t p*(p k.val:ℝ) := by
  intro E a b z
  let R := realMatrix q E X.V
  let C := excess R
  let y := probe q E m t v b
  let u := boundary q E m t v b
  let P (i : X.V) : ℝ := p i
  let W (i : X.V) : ℝ := w i
  let M := ∑i,y i
  let d := price q E a b v m t p
  let x := y-d • P
  have edge (i j) (ed : E i j=true) : X.D i j=true := (mem_col.mp (active.mp ed).choose_spec).2.2.2
  have ab : a≠b := by
    intro e
    have ed : X.D a b=true := f.property.1
    rw [e] at ed
    exact loopfree X.free (by omega) b.property ed
  have qpos : (1:ℝ)<q := by exact_mod_cast (by omega : 1<q)
  have ua : y a=0 := by
    obtain ⟨s,sp,budget,path⟩ := reach
    dsimp only [y,probe]
    rw [prefix_zero q E X.free edge f.property.1 short,zero_after_path q E X.free edge path sp budget]
    ring
  have py : P ᵥ* R=1 := funext fun j => by simpa [P,R,E] using realMatrix_rational_columns p 1 pc j
  have wy : R *ᵥ W=1 := funext fun j => by simpa [W,R,E] using realMatrix_rational_rows w 1 wr j
  have pm : (∑i,P i)=1 := by
    have h := dotProduct_mulVec P R W
    rw [py,wy,dotProduct_one,one_dotProduct] at h
    exact h.trans (real_mass_of_rational_probability w wm)
  have pzero : P ᵥ* C=0 := funext fun j => by
    rw [show C=excess R from rfl,vecMul_excess,py,pm]; simp
  have prod (j : X.V) : (x ᵥ* C) j=u j-M := by
    rw [show x=y-d • P from rfl,sub_vecMul,smul_vecMul,pzero,smul_zero,sub_zero]
    exact (vecMul_excess R y j).trans (by rw [show (y ᵥ* R) j=u j from probe_row q E m t v b j])
  have pa : 0<P a := by change 0<(p a:ℝ); exact_mod_cast (pos a a.property).2
  have bill : d*((q:ℝ)*P a)=u b-M := div_mul_cancel₀ _ (mul_pos (by linarith only [qpos]) pa).ne'
  have bal : (x ᵥ* C) b= -(q:ℝ)*x a := by
    rw [prod]; change u b-M= -(q:ℝ)*(y a-d*P a); rw [ua]; linarith only [bill]
  have aa : E a a=false := Bool.eq_false_iff.mpr fun e => loopfree X.free (by omega) a.property (edge _ _ e)
  have bb : E b b=false := Bool.eq_false_iff.mpr fun e => loopfree X.free (by omega) b.property (edge _ _ e)
  have back : E b a=false := Bool.eq_false_iff.mpr fun e => digonfree X.free hq a.property b.property f.property.1 (edge _ _ e)
  constructor
  · intro j
    have h := restrict_row C a b ab q (by linarith only [qpos])
      (by simp [C,R,excess,realMatrix_entry,aa]) (by simp [C,R,excess,realMatrix_entry,bb])
      (by simp [C,R,excess,realMatrix_entry,ab,show E a b=false from f.property.2])
      (by simp [C,R,excess,realMatrix_entry,ab.symm,back]) x bal j
    change ((fun i : rest a b => x i.val) ᵥ* reduced C a b ((q:ℝ)-1)) j=_
    rw [h,prod,prod]
    have bj : b≠j.val := (inside j).2.symm
    change u j.val-M+(u a-M)*C b j.val=u j.val-u a+(u a-M)*_
    simp only [C,excess,R,realMatrix_entry,ite_eq_right bj,zero_add]
    ring
  · intro k kb
    change t*walkSum q E X.V m b k.val-walkSum q E X.V m v k.val-d*P k.val=_
    rw [prefix_zero q E X.free edge (edge _ _ kb) short]
    ring

include hq pos wm wr pc in
theorem native_right (f : SharedArcFlatCut.Missing X F) :
    let E := graph X.D F
    let a := f.val.1
    let b := f.val.2
    let T := test (realMatrix q E X.V)⁻¹ (fun i : X.V => (w i:ℝ)) (fun i : X.V => (p i:ℝ)) q a b
    puncture q E a b * Matrix.of (fun i j : rest a b => T i.val j.val/((q:ℝ)*(p a:ℝ)*(w b:ℝ)))=1 := by
  intro E a b
  have edge (i j) (ed : E i j=true) : X.D i j=true := (mem_col.mp (active.mp ed).choose_spec).2.2.2
  have ab : a≠b := by
    intro e
    have ed : X.D a b=true := f.property.1
    rw [e] at ed
    exact loopfree X.free (by omega) b.property ed
  exact graph_right hq a b ab
    (Bool.eq_false_iff.mpr fun e => loopfree X.free (by omega) a.property (edge _ _ e))
    (Bool.eq_false_iff.mpr fun e => loopfree X.free (by omega) b.property (edge _ _ e))
    f.property.2 (Bool.eq_false_iff.mpr fun e => digonfree X.free hq a.property b.property f.property.1 (edge _ _ e))
    pos wm wr pc

include hq pos wm wr pc in
/-- A one-sided terminal bound on explicit walk counts suffices for an
actual signed puncture certificate. No outside-support equalities need
to be supplied by the caller. -/
theorem certificate (small : SmallerSmallRow q X.V.card) (f : SharedArcFlatCut.Missing X F)
    (v : X.V) (m : ℕ) (short : m≤q) (t : ℝ)
    (reach : ∃s,0<s ∧ s+m≤q+1 ∧ Walk X.D X.V f.val.1 v s)
    (k : rest f.val.1 f.val.2) (kb : graph X.D F k.val f.val.2=true)
    (gain : 0< -walkSum q (graph X.D F) X.V m v k.val-price q (graph X.D F) f.val.1 f.val.2 v m t p*(p k.val:ℝ))
    (terminal : ∀j,residual q (graph X.D F) f.val.1 f.val.2 v m t j≤0) :
    let E := graph X.D F
    let a := f.val.1
    let b := f.val.2
    ∃z : rest a b→ℝ,0<z k ∧ (∀i,(z ᵥ* puncture q E a b) i≤0) ∧
      (∀i,E a i.val≠true → (z ᵥ* puncture q E a b) i=0) := by
  intro E a b
  have acc := accounts X hq F pos wm wr pc f v m short t reach
  apply repair (native_right X hq F pos wm wr pc f) (fun j => E a j.val=true) k (candidate q E a b v m t p)
    ((acc.2 k kb).symm ▸ gain) (fun j => (acc.1 j).trans_le (terminal j))
  intro j _
  exact div_nonneg (SharedArcFlatArithmetic.positive X hq small F pos wm wr pc f j.val k.val).le
    (mul_nonneg (mul_nonneg (Nat.cast_nonneg q) (by exact_mod_cast (pos a a.property).2.le))
      (by exact_mod_cast (pos b b.property).1.le))

include hq pos wm wr pc in
/-- The resulting negative entry lies in the column of the chosen old
parent k. Its old-successor row can differ from the launch vertex v. -/
theorem sign (small : SmallerSmallRow q X.V.card) (f : SharedArcFlatCut.Missing X F)
    (v : X.V) (m : ℕ) (short : m≤q) (t : ℝ)
    (reach : ∃s,0<s ∧ s+m≤q+1 ∧ Walk X.D X.V f.val.1 v s)
    (k : rest f.val.1 f.val.2) (kb : graph X.D F k.val f.val.2=true)
    (gain : 0< -walkSum q (graph X.D F) X.V m v k.val-price q (graph X.D F) f.val.1 f.val.2 v m t p*(p k.val:ℝ))
    (terminal : ∀j,residual q (graph X.D F) f.val.1 f.val.2 v m t j≤0) :
    ∃s : X.V, graph X.D F f.val.1 s=true ∧ test (realMatrix q (graph X.D F) X.V)⁻¹
      (fun i : X.V => (w i:ℝ)) (fun i : X.V => (p i:ℝ)) q f.val.1 f.val.2 s k.val<0 := by
  have cert := certificate X hq F pos wm wr pc small f v m short t reach k kb gain terminal
  obtain ⟨s,hs,neg⟩ := (row_certificate (native_right X hq F pos wm wr pc f)
    (fun i => graph X.D F f.val.1 i.val=true) k).mpr cert
  exact ⟨s.val,hs,neg_of_div_neg_left neg (mul_nonneg
    (mul_nonneg (Nat.cast_nonneg q) (by exact_mod_cast (pos _ f.val.1.property).2.le))
    (by exact_mod_cast (pos _ f.val.2.property).1.le))⟩



/-- One vector on the puncture must satisfy every row equation at
once. The graph data for t=0 and t=1 suffice for this finite test. -/
def Fits {V : Finset ℕ} (q : ℕ) (D E : CH.Digraph) (a b : V) (p : ℕ→ℚ)
    (k : rest a b) (μ : rest a b→ℝ) : Prop :=
  ∀v : V,∀m≤q,(∃s,0<s ∧ s+m≤q+1 ∧ Walk D V a v s) → ∀t : ℝ,t=0 ∨ t=1 →
    (∑j : rest a b,residual q E a b v m t j*μ j)=
      -walkSum q E V m v k.val-price q E a b v m t p*(p k.val:ℝ)

include hq pos wm wr pc in
/-- The scaled interior tensor column solves the walk moment system
identically, without any sign assumption or smaller-order inference. -/
theorem column_fits (f : SharedArcFlatCut.Missing X F)
    (k : rest f.val.1 f.val.2) (kb : graph X.D F k.val f.val.2=true) :
    let E := graph X.D F
    let a := f.val.1
    let b := f.val.2
    let T := test (realMatrix q E X.V)⁻¹ (fun i : X.V => (w i:ℝ)) (fun i : X.V => (p i:ℝ)) q a b
    Fits q X.D E a b p k (fun j => T j.val k.val/((q:ℝ)*(p a:ℝ)*(w b:ℝ))) := by
  intro E a b T v m short reach t _
  have acc := accounts X hq F pos wm wr pc f v m short t reach
  let z := candidate q E a b v m t p
  let J := Matrix.of (fun i j : rest a b => T i.val j.val/((q:ℝ)*(p a:ℝ)*(w b:ℝ)))
  have eq : ((z ᵥ* puncture q E a b) ᵥ* J) k=z k := by
    rw [vecMul_vecMul,show puncture q E a b*J=1 from native_right X hq F pos wm wr pc f,vecMul_one]
  change (∑j : rest a b,residual q E a b v m t j*J j k)=_
  exact (sum_congr rfl (fun j _ => congrArg (fun u => u*J j k) (acc.1 j).symm)).trans
    (eq.trans (acc.2 k kb))

include hq pos wm wr pc in
/-- Either the designated old parent has a negative entry at an old
successor, or one strictly positive vector simultaneously fits every
finite walk equation. Only positivity outside the target rectangle is
used to localize the first alternative. -/
theorem sign_or_fit (small : SmallerSmallRow q X.V.card) (f : SharedArcFlatCut.Missing X F)
    (k : rest f.val.1 f.val.2) (kb : graph X.D F k.val f.val.2=true) :
    let E := graph X.D F
    let a := f.val.1
    let b := f.val.2
    let T := test (realMatrix q E X.V)⁻¹ (fun i : X.V => (w i:ℝ)) (fun i : X.V => (p i:ℝ)) q a b
    (∃s : X.V,E a s=true ∧ T s k.val<0) ∨
      ∃μ : rest a b→ℝ,(∀j,0<μ j) ∧ Fits q X.D E a b p k μ := by
  intro E a b T
  by_cases neg : ∃s : X.V,E a s=true ∧ T s k.val<0
  · exact Or.inl neg
  right
  refine ⟨_,fun j => div_pos ?_ (mul_pos (mul_pos (by exact_mod_cast (by omega : 0<q))
    (by exact_mod_cast (pos a a.property).2)) (by exact_mod_cast (pos b b.property).1)),
    column_fits X hq F pos wm wr pc f k kb⟩
  by_cases ed : E a j.val=true
  · have nz := SharedArcFlatArithmetic.nonzero hq
      (by simpa using funext (realMatrix_rational_rows w 1 wr))
      (by simpa using funext (realMatrix_rational_columns p 1 pc)) a b j.val k.val
    exact lt_of_le_of_ne (le_of_not_gt (fun lt => neg ⟨j.val,ed,lt⟩)) (Ne.symm nz)
  · exact SharedArcFlatArithmetic.positive X hq small F pos wm wr pc f j.val k.val


include hq pos wm wr pc in
/-- The walk and strict merge tests use the same rational column. Its
coordinate at the inserted head is fixed by the old flat column law.
The feasibility statement itself contains no matrix inverse. -/
theorem common_column (small : SmallerSmallRow q X.V.card) (f : SharedArcFlatCut.Missing X F)
    (k : rest f.val.1 f.val.2) (kb : graph X.D F k.val f.val.2=true) :
    let E := graph X.D F
    let a := f.val.1
    let b := f.val.2
    ∃h : X.V→ℚ, (∀i,0<h i) ∧ (q:ℚ)*p a*h b=p k.val ∧
      Fits q X.D E a b p k (fun j => (h j.val:ℝ)) ∧
      ∀S⊆X.V,2≤S.card → S≠X.V → SingleArcTensorMerge.cut q X.D X.V S h<0 := by
  intro E a b
  let H := (SingleArcTensorMerge.center q (insertArc E a b) X.V)⁻¹
  let T := test (realMatrix q E X.V)⁻¹ (fun i : X.V => (w i:ℝ)) (fun i : X.V => (p i:ℝ)) q a b
  let d := (q:ℝ)*(p a:ℝ)*(w b:ℝ)
  have wb : 0<(w b:ℝ) := by exact_mod_cast (pos _ b.property).1
  have dp : 0<d := mul_pos (mul_pos (by exact_mod_cast (by omega : 0<q))
    (by exact_mod_cast (pos _ a.property).2)) wb
  have id (i : X.V) : T i k.val=d*(H i k.val:ℝ) := (SingleArcTensorMerge.identify X hq F pos wm wr pc f).2 i k.val
  refine ⟨fun i => H i k.val,?_,?_,?_,?_⟩
  · intro i
    have ht : 0<T i k.val := SharedArcFlatArithmetic.positive X hq small F pos wm wr pc f i k.val
    rw [id] at ht
    exact_mod_cast pos_of_mul_pos_right ht dp.le
  · have hb : T b k.val=(w b:ℝ)*(p k.val:ℝ) := by dsimp [T,test]; ring
    rw [id] at hb
    have hr : (q:ℝ)*(p a:ℝ)*(H b k.val:ℝ)=(p k.val:ℝ) := by
      apply mul_left_cancel₀ wb.ne'
      dsimp [d] at hb
      linear_combination hb
    exact_mod_cast hr
  · have h := column_fits X hq F pos wm wr pc f k kb
    have eq : (fun j : rest a b => T j.val k.val/d)=(fun j : rest a b => (H j.val k.val:ℝ)) := by
      funext j; rw [id]; field_simp [dp.ne']
    exact eq ▸ h
  · intro S sub size proper
    exact (SingleArcTensorMerge.all_cuts X hq small F pos wm wr pc f sub size proper k.val).1

noncomputable def degree {V : Finset ℕ} (E : CH.Digraph) (v : V) : ℕ :=
  (univ.filter (fun j : V => E v j=true)).card

private theorem walkSum_two {V : Finset ℕ} (q : ℕ) (E : CH.Digraph) (v j : V) :
    walkSum q E V 2 v j=(1:Matrix V V ℝ) v j+(if E v j=true then -(q:ℝ) else 0) := by
  simp [walkSum,sum_range_succ,step_entry]

private theorem mass_two {V : Finset ℕ} (q : ℕ) (E : CH.Digraph) (v b : V) :
    (∑j,probe q E 2 0 v b j)=(q:ℝ)*(degree E v:ℝ)-1 := by
  have eq (j : V) : probe q E 2 0 v b j=(if E v j=true then (q:ℝ) else 0)-(1:Matrix V V ℝ) v j := by
    simp only [probe,zero_mul,zero_sub,walkSum_two]
    by_cases ed : E v j=true <;> simp [ed]
    ring
  have heads : (∑j : V,if E v j=true then (q:ℝ) else 0)=(q:ℝ)*(degree E v:ℝ) := by
    rw [←sum_filter]; simp [degree,mul_comm]
  simp only [eq,sum_sub_distrib,heads,one_apply]
  simp

private theorem boundary_two {V : Finset ℕ} (q : ℕ) (E : CH.Digraph) (v b j : V) :
    boundary q E 2 0 v b j=(q:ℝ)^2*(count E V 2 v j:ℝ)-(1:Matrix V V ℝ) v j := by
  rw [boundary,zero_mul,zero_sub,power_count]; ring

include pos wm wr pc in
/-- A graph-only expansion obstruction at horizon two. A two-step head
other than the endpoints either escapes the heads of b, or is reached with
multiplicity at least the entire out-degree of v. This applies whenever
the fraction of v's first arcs that route to b is below 1/q. -/
theorem two_step_escape (three : 3≤q) (small : SmallerSmallRow q X.V.card)
    (f : SharedArcFlatCut.Missing X F) (v : X.V) (vb : v≠f.val.2)
    (reach : ∃s,0<s ∧ s+2≤q ∧ Walk X.D X.V f.val.1 v s)
    (k : rest f.val.1 f.val.2) (kb : graph X.D F k.val f.val.2=true) (vk : v≠k.val)
    (thin : q*count (graph X.D F) X.V 2 v f.val.2<degree (graph X.D F) v) :
    let E := graph X.D F
    ∃j : rest f.val.1 f.val.2,0<count E X.V 2 v j.val ∧
      (E f.val.2 j.val=false ∨ degree E v≤count E X.V 2 v j.val) := by
  intro E
  let a := f.val.1
  let b := f.val.2
  let d := degree E v
  have qpos : (1:ℝ)<q := by exact_mod_cast (by omega : 1<q)
  have q0 : (0:ℝ)<q := zero_lt_one.trans qpos
  have edge (i j) (ed : E i j=true) : X.D i j=true := (mem_col.mp (active.mp ed).choose_spec).2.2.2
  obtain ⟨s,sp,budget,path⟩ := reach
  have va : v≠a := by
    intro e
    have ret : Walk X.D X.V a v s := path
    rw [e] at ret
    exact X.free _ s sp (by omega) ret
  have ua : boundary q E 2 0 v b a=0 := by
    have back : (step q E X.V^2) v a=0 := no_power q E 2 v a (fun ret =>
      X.free _ (s+2) (by omega) budget (path.append (walk_sub edge ret)))
    simp [boundary,va,back]
  have ub := boundary_two q E v b b
  rw [one_apply_ne vb,sub_zero] at ub
  have den : 0<(q:ℝ)*(p a:ℝ) := mul_pos q0 (by exact_mod_cast (pos a a.property).2)
  have dlt : (q:ℝ)*(count E X.V 2 v b:ℝ)+1≤(d:ℝ) := by
    exact_mod_cast (show q*count E X.V 2 v b+1≤d from thin)
  have debit : price q E a b v 2 0 p<0 := by
    apply div_neg_of_neg_of_pos _ den
    rw [ub,mass_two]
    change (q:ℝ)^2*(count E X.V 2 v b:ℝ)-((q:ℝ)*d-1)<0
    nlinarith only [mul_le_mul_of_nonneg_left dlt q0.le,qpos]
  have gain : 0< -walkSum q E X.V 2 v k.val-price q E a b v 2 0 p*(p k.val:ℝ) := by
    have loss := mul_neg_of_neg_of_pos debit (show 0<(p k.val:ℝ) by exact_mod_cast (pos _ k.val.property).2)
    rw [walkSum_two,one_apply_ne vk,zero_add]
    by_cases ed : E v k.val=true <;> simp only [ed,ite_true,Bool.false_eq_true,ite_false] <;> linarith
  by_contra! none
  have terminal (j : rest a b) : residual q E a b v 2 0 j≤0 := by
    let c := count E X.V 2 v j.val
    have diag : 0≤(1:Matrix X.V X.V ℝ) v j.val := by simp only [one_apply]; split <;> norm_num
    rw [residual,ua,boundary_two,mass_two,sub_zero,zero_sub]
    by_cases hit : 0<c
    · have nj := none j hit
      have adj : E b j.val=true := by
        cases h : E b j.val with
        | false => exact (nj.1 h).elim
        | true => rfl
      have low : (c:ℝ)+1≤(d:ℝ) := by exact_mod_cast (show c+1≤d by simpa [c,d] using nj.2)
      rw [ite_eq_left adj]
      change (q:ℝ)^2*c-_+(-((q:ℝ)*d-1))*(q:ℝ)≤0
      nlinarith only [mul_le_mul_of_nonneg_left low (sq_nonneg (q:ℝ)),diag,
        mul_nonneg (sub_nonneg.mpr qpos.le) q0.le]
    · have zero : count E X.V 2 v j.val=0 := Nat.eq_zero_of_not_pos hit
      have dpos : (1:ℝ)≤d := by exact_mod_cast (show 1≤d from Nat.zero_lt_of_lt thin)
      have masspos : 0≤(q:ℝ)*d-1 := by nlinarith only [mul_le_mul_of_nonneg_left dpos q0.le,qpos]
      rw [zero,Nat.cast_zero,mul_zero]
      by_cases ed : E b j.val=true <;> simp only [ed,ite_true,Bool.false_eq_true,ite_false] <;>
        nlinarith only [diag,mul_nonneg masspos q0.le]
  obtain ⟨u,_,bad⟩ := sign X (by omega) F pos wm wr pc small f v 2 (by omega) 0
    ⟨s,sp,by omega,path⟩ k kb gain terminal
  exact bad.not_ge (SharedArcFlatArithmetic.positive X (by omega) small F pos wm wr pc f u k.val).le

end Native
end LeanCH.BR.Closure.PunctureWalkCertificate
#print axioms LeanCH.BR.Closure.PunctureWalkCertificate.power_count
#print axioms LeanCH.BR.Closure.PunctureWalkCertificate.accounts
#print axioms LeanCH.BR.Closure.PunctureWalkCertificate.certificate
#print axioms LeanCH.BR.Closure.PunctureWalkCertificate.sign
#print axioms LeanCH.BR.Closure.PunctureWalkCertificate.sign_or_fit
#print axioms LeanCH.BR.Closure.PunctureWalkCertificate.common_column
#print axioms LeanCH.BR.Closure.PunctureWalkCertificate.two_step_escape
