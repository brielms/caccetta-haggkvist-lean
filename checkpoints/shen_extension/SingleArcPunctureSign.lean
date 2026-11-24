import checkpoints.shen_extension.SingleArcSwitchSign
import checkpoints.shen_extension.SingleArcModuleBoundary
import checkpoints.shen_extension.SharedArcPivotGate

namespace LeanCH.BR.Closure.SingleArcPunctureSign
open Finset Matrix FiniteCutInverse BRq2 BRq3 BR45 WeightedSD
open ShortestCycleWeights FirstPacketBarrier MarkedCyclePeeling SharedArcFlatResponse
open scoped Matrix

section Algebra
variable {I : Type*} [Fintype I] [DecidableEq I]

def rest (a b : I) : Finset I := (univ.erase a).erase b

theorem inside {a b : I} (i : rest a b) : i.val≠a ∧ i.val≠b := by
  have h := i.property
  simpa [rest,and_comm] using h

private theorem sum_split (a b : I) (ab : a≠b) (g : I→ℝ) :
    (∑i,g i)=g a+g b+∑i : rest a b,g i.val := by
  rw [sum_coe_sort]
  have A := sum_erase_add (s:=univ) g (mem_univ a)
  have B := sum_erase_add (s:=univ.erase a) g (mem_erase.mpr ⟨ab.symm,mem_univ b⟩)
  unfold rest; linarith only [A,B]

/-- Schur complement of the two endpoint rows and columns when their centered
block has rows (0,t) and (-1,0). -/
noncomputable def reduced (C : Matrix I I ℝ) (a b : I) (t : ℝ) : Matrix (rest a b) (rest a b) ℝ :=
  fun i j => C i j + C i a*C b j - (C i b/t)*C a j

private theorem correction (C : Matrix I I ℝ) (a b : I) (t : ℝ) (z : rest a b→ℝ) (j : rest a b) :
    (z ᵥ* reduced C a b t) j = (z ᵥ* C.submatrix Subtype.val Subtype.val) j +
      (∑i,z i*C i.val a)*C b j.val - (∑i,z i*C i.val b)/t*C a j.val := by
  change (∑i,z i*(C i j+C i a*C b j-(C i b/t)*C a j))=_
  simp only [vecMul,dotProduct,submatrix_apply,mul_sub,mul_add,←mul_assoc,←mul_div_assoc,
    sum_sub_distrib,sum_add_distrib,←sum_mul,←sum_div]

theorem reduced_right {C H : Matrix I I ℝ} (right : C*H=1) (a b : I) (ab : a≠b)
    {t : ℝ} (tn : t≠0) (aa : C a a=0) (ab' : C a b=t) (ba : C b a= -1) (bb : C b b=0) :
    reduced C a b t * H.submatrix Subtype.val Subtype.val=1 := by
  ext i k
  let part (j : I) := ∑l : rest a b,C j l*H l k
  have row (j : I) : C j a*H a k+C j b*H b k+part j=(1:Matrix I I ℝ) j k := by
    rw [←right,mul_apply,sum_split a b ab]
  have x := row a
  have y := row b
  rw [aa,ab',one_apply_ne (inside k).1.symm] at x
  rw [ba,bb,one_apply_ne (inside k).2.symm] at y
  have eqd : (1:Matrix I I ℝ) i.val k.val=(1:Matrix (rest a b) (rest a b) ℝ) i k := by
    by_cases ik : i=k
    · subst k; simp
    · rw [one_apply_ne (show i.val≠k.val from fun h => ik (Subtype.ext h)),one_apply_ne ik]
  rw [←eqd,←row i,Matrix.mul_apply]
  simp only [reduced,submatrix_apply,sub_mul,add_mul,mul_assoc,sum_sub_distrib,sum_add_distrib,←mul_sum]
  change part i+C i a*part b-C i b/t*part a=C i a*H a k+C i b*H b k+part i
  have xa : part a= -t*H b k := by linarith only [x]
  have yb : part b=H a k := by linarith only [y]
  rw [xa,yb]; field_simp [tn]; ring

/-- The centered inverse is signed here. The graph need not be a legal
insertion. This also permits the test to produce an actual negative entry. -/
theorem signed_right {R S : Matrix I I ℝ} (unit : IsUnit R.det)
    {a b : I} {t : ℝ} (edit : ∀i j,S i j-R i j=if i=a ∧ j=b then t else 0)
    {w p : I→ℝ} (wr : R *ᵥ w=fun _=>1) (pc : p ᵥ* R=fun _=>1) (wm : ∑i,w i=1)
    (nz : t*p a*w b≠0) :
    excess S * Matrix.of (fun v k => test R⁻¹ w p t a b v k/(t*p a*w b))=1 := by
  ext i k
  have col := congrFun (rectangle_column (mul_nonsing_inv R unit) edit wr pc wm k) i
  change (∑j,excess S i j*(test R⁻¹ w p t a b j k/(t*p a*w b)))=_
  simp only [←mul_div_assoc,←sum_div]
  change ((excess S *ᵥ (fun v => test R⁻¹ w p t a b v k)) i) / _ = _
  rw [show (excess S *ᵥ (fun v => test R⁻¹ w p t a b v k)) i = _ from col]
  by_cases eq : k=i
  · subst k; simp [nz]
  · rw [ite_eq_right eq,zero_div,one_apply_ne (Ne.symm eq)]

/-- For a fixed column k, one signed weighting of the proper label set
suffices to force a negative entry at an actual member of U. Conversely
every such entry gives a weighting. -/
theorem row_certificate {K J : Matrix I I ℝ} (right : K*J=1) (U : I→Prop) (k : I) :
    (∃v,U v ∧ J v k<0) ↔
      ∃z : I→ℝ, 0<z k ∧ (∀i,(z ᵥ* K) i≤0) ∧ (∀i,¬U i → (z ᵥ* K) i=0) := by
  constructor
  · rintro ⟨v,uv,h⟩
    let z := fun i => -J v i
    have eq (i : I) : (z ᵥ* K) i= -(1:Matrix I I ℝ) v i := by
      change (∑j, -(J v j)*K j i)=_
      simp_rw [neg_mul,sum_neg_distrib]
      rw [←mul_apply,mul_eq_one_comm.mp right]
    refine ⟨z,neg_pos.mpr h,fun i => ?_,fun i out => ?_⟩
    · rw [eq,one_apply]; split <;> norm_num
    · rw [eq,one_apply_ne (show v≠i from fun same => out (same ▸ uv)),neg_zero]
  · rintro ⟨z,pos,le,off⟩
    by_contra! all
    have zn : ∑i,(z ᵥ* K) i*J i k≤0 := sum_nonpos fun i _ => by
      by_cases ui : U i
      · exact mul_nonpos_of_nonpos_of_nonneg (le i) (all i ui)
      · rw [off i ui,zero_mul]
    change ((z ᵥ* K) ᵥ* J) k≤0 at zn
    rw [vecMul_vecMul,right,vecMul_one] at zn
    exact pos.not_ge zn

end Algebra

/-- Threshold graph on the surviving labels. Off the diagonal the cutoff
is -1, on the diagonal it is 0. -/
noncomputable def threshold {V : Finset ℕ} (a b : V) (M : Matrix (rest a b) (rest a b) ℝ) : CH.Digraph :=
  fun x y => by
    classical
    exact decide (∃i j : rest a b,i.val.val=x ∧ j.val.val=y ∧ (if i=j then 0 else -1)<M i j)

theorem threshold_on {V : Finset ℕ} (a b : V) (M : Matrix (rest a b) (rest a b) ℝ) (i j : rest a b) :
    threshold a b M i.val j.val=true ↔ (if i=j then 0 else -1)<M i j := by
  classical
  simp only [threshold,decide_eq_true_eq]
  exact ⟨fun ⟨u,v,eq1,eq2,hit⟩ => (Subtype.ext (Subtype.ext eq1) : u=i) ▸
    (Subtype.ext (Subtype.ext eq2) : v=j) ▸ hit,fun hit => ⟨i,j,rfl,rfl,hit⟩⟩

/-- The matrix uses only old arcs among the remaining vertices and their
old incidences to a and b. No flat weights or inverse are used to form it. -/
noncomputable def puncture {V : Finset ℕ} (q : ℕ) (E : CH.Digraph) (a b : V) :=
  reduced (excess (realMatrix q E V)) a b ((q:ℝ)-1)

section Graph
variable {q : ℕ} {V : Finset ℕ} {E : CH.Digraph}

/-- The entire interior block of the signed four-index test, scaled by
q p(a) w(b), is a right inverse on the proper puncture. -/
theorem graph_right (hq : 2≤q) (a b : V) (ab : a≠b)
    (aa : E a a=false) (bb : E b b=false) (off : E a b=false) (back : E b a=false)
    {w p : ℕ→ℚ} (pos : ∀i∈V,0<w i ∧ 0<p i) (wm : mass V w=1)
    (wr : ∀i∈V,WeightedSD.row q E V w i=1) (pc : ∀i∈V,WeightedSD.col q E V p i=1) :
    let T := test (realMatrix q E V)⁻¹ (fun i : V => (w i:ℝ)) (fun i : V => (p i:ℝ)) q a b
    puncture q E a b * Matrix.of (fun i j : rest a b => T i.val j.val/((q:ℝ)*(p a:ℝ)*(w b:ℝ)))=1 := by
  intro T
  let R := realMatrix q E V
  let S := realMatrix q (insertArc E a b) V
  let H : Matrix V V ℝ := fun i j => T i j/((q:ℝ)*(p a:ℝ)*(w b:ℝ))
  have edit := realMatrix_insert_difference (q:=q) a b (show ¬E a b=true by simp [off])
  have p0 : (0:ℝ)<p a := by exact_mod_cast (pos a a.property).2
  have w0 : (0:ℝ)<w b := by exact_mod_cast (pos b b.property).1
  have q0 : (1:ℝ)<q := by exact_mod_cast (by omega : 1<q)
  have right : excess S * H=1 := signed_right (matrix_unit hq E V) edit
    (by simpa using funext (realMatrix_rational_rows w 1 wr))
    (by simpa using funext (realMatrix_rational_columns p 1 pc)) (real_mass_of_rational_probability w wm)
    (mul_pos (mul_pos (zero_lt_one.trans q0) p0) w0).ne'
  have val (i j : V) : excess S i j=excess R i j+(if i=a ∧ j=b then (q:ℝ) else 0) := by
    dsimp [R,S,excess]; linarith only [edit i j]
  have block := reduced_right right a b ab (sub_ne_zero.mpr q0.ne')
    (by rw [val]; simp [R,excess,realMatrix_entry,aa,ab])
    (by rw [val]; simp [R,excess,realMatrix_entry,off,ab]; ring)
    (by rw [val]; simp [R,excess,realMatrix_entry,back,ab.symm])
    (by rw [val]; simp [R,excess,realMatrix_entry,bb,ab.symm])
  have same : reduced (excess S) a b ((q:ℝ)-1)=puncture q E a b := by
    ext i j
    simp [reduced,puncture,val,R,(inside i).1,(inside j).2,ab.symm]
  rw [same] at block
  exact block

/-- A graph-only, linear certificate for a negative entry somewhere on the
old-successor by old-parent rectangle. All variables are on the proper
puncture. Neither direction uses a small-order or legal-insertion premise. -/
theorem graph_iff (hq : 2≤q) (a b : V) (ab : a≠b)
    (aa : E a a=false) (bb : E b b=false) (off : E a b=false) (back : E b a=false)
    {w p : ℕ→ℚ} (pos : ∀i∈V,0<w i ∧ 0<p i) (wm : mass V w=1)
    (wr : ∀i∈V,WeightedSD.row q E V w i=1) (pc : ∀i∈V,WeightedSD.col q E V p i=1) :
    let T := test (realMatrix q E V)⁻¹ (fun i : V => (w i:ℝ)) (fun i : V => (p i:ℝ)) q a b
    (∃v k : V,E a v=true ∧ E k b=true ∧ T v k≤0) ↔
      ∃k : rest a b,E k.val b=true ∧ ∃z : rest a b→ℝ, 0<z k ∧
        (∀i,(z ᵥ* puncture q E a b) i≤0) ∧ (∀i,E a i.val≠true → (z ᵥ* puncture q E a b) i=0) := by
  intro T
  let d := (q:ℝ)*(p a:ℝ)*(w b:ℝ)
  have dp : 0<d := mul_pos (mul_pos (by exact_mod_cast (by omega : 0<q))
    (by exact_mod_cast (pos a a.property).2)) (by exact_mod_cast (pos b b.property).1)
  have right := graph_right hq a b ab aa bb off back pos wm wr pc
  let J : Matrix (rest a b) (rest a b) ℝ := fun i j => T i.val j.val/d
  have iff' (k : rest a b) := row_certificate (J:=J) right (fun v => E a v.val=true) k
  have nz (v k : V) : T v k≠0 := SharedArcFlatArithmetic.nonzero hq
    (by simpa using funext (realMatrix_rational_rows w 1 wr))
    (by simpa using funext (realMatrix_rational_columns p 1 pc)) a b v k
  constructor
  · rintro ⟨v,k,av,kb,h⟩
    have vi : v∈rest a b := by
      have x : v≠a := by rintro rfl; simp [aa] at av
      have y : v≠b := by rintro rfl; simp [off] at av
      simp [rest,x,y]
    have ki : k∈rest a b := by
      have x : k≠a := by rintro rfl; simp [off] at kb
      have y : k≠b := by rintro rfl; simp [bb] at kb
      simp [rest,x,y]
    exact ⟨⟨k,ki⟩,kb,(iff' ⟨k,ki⟩).mp ⟨⟨v,vi⟩,av,div_neg_of_neg_of_pos (lt_of_le_of_ne h (nz v k)) dp⟩⟩
  · rintro ⟨k,kb,z⟩
    obtain ⟨v,av,lt⟩ := (iff' k).mpr z
    exact ⟨v.val,k.val,av,kb,(neg_of_div_neg_left lt dp.le).le⟩

end Graph

private theorem trim {q a b i k l m : ℕ} {V : Finset ℕ} {D E : CH.Digraph}
    (free : QFree D V q) (bv : b∈V) (kb : D k b=true)
    (keep : ∀x∈V,x≠a → ∀y∈V,D x y=true → E x y=true)
    (w : Walk D V i k m) (iv : i∈V) (pre : Walk D V a i l) (pos : 0<l) (len : l+m≤q) :
    Walk E ((V.erase a).erase b) i k m := by
  induction w generalizing l with
  | refl => exact .refl _
  | @step i x k m xv ed tail ih =>
    have ia : i≠a := by rintro rfl; exact free _ l pos (by omega) pre
    have xa : x≠a := by rintro rfl; exact free _ (l+1) (by omega) (by omega) (pre.snoc xv ed)
    have xb : x≠b := by rintro rfl; exact free _ (m+1) (by omega) (by omega) (tail.snoc bv kb)
    exact .step (mem_erase.mpr ⟨xb,mem_erase.mpr ⟨xa,xv⟩⟩) (keep i iv ia x xv ed)
      (ih kb xv (pre.snoc xv ed) (by omega) (by omega))

/-- At a global singleton, reverse adjacency across the whole rectangle
is read from short walks in the same proper puncture used for the sign. -/
theorem returns {q n} (X : Model q n) (hq : 2≤q) (F : Family) (f : SharedArcFlatCut.Missing X F)
    (single : ∀g : SharedArcFlatCut.Missing X F,g=f) (v k : X.V)
    (av : graph X.D F f.val.1 v=true) (kb : graph X.D F k f.val.2=true) :
    let E := graph X.D F
    let W := (X.V.erase f.val.1.val).erase f.val.2.val
    E k v=false ↔ ∃m<q,Walk E W v k m := by
  intro E W
  let a := f.val.1
  let b := f.val.2
  have sub (i j) (ed : E i j=true) : X.D i j=true := (mem_col.mp (active.mp ed).choose_spec).2.2.2
  have keep (x) (xv : x∈X.V) (xa : x≠(a:ℕ)) (y) (yv : y∈X.V) (ed : X.D x y=true) : E x y=true := by
    by_contra fail
    let g : SharedArcFlatCut.Missing X F := ⟨(⟨x,xv⟩,⟨y,yv⟩),ed,Bool.eq_false_iff.mpr fail⟩
    exact xa (congrArg (fun z : SharedArcFlatCut.Missing X F => z.val.1.val) (single g))
  have ka : k.val≠a.val := by intro eq; have edge : E a b=true := eq ▸ kb; exact Bool.noConfusion (f.property.2.symm.trans edge)
  constructor
  · intro off
    have absent : ¬X.D k v=true := fun ed => Bool.noConfusion (off.symm.trans (keep k k.property ka v v.property ed))
    obtain ⟨_,m,le,path⟩ := mem_ball.mp (X.sat v v.property k k.property absent)
    exact ⟨m,by omega,trim X.free b.property (sub _ _ kb) keep path v.property
      (.step v.property (sub _ _ av) (.refl _)) (by decide) (by omega)⟩
  · rintro ⟨m,lt,path⟩
    apply Bool.eq_false_iff.mpr
    intro edge
    have incl : W⊆X.V := (erase_subset _ _).trans (erase_subset _ _)
    have lift {i j l} (w : Walk E W i j l) : Walk X.D X.V i j l := by
      induction w with
      | refl => exact .refl _
      | step jv ed _ ih => exact .step (incl jv) (sub _ _ ed) ih
    exact X.free _ (m+1) (by omega) (by omega) (.step v.property (sub _ _ edge) (lift path))

section Native
variable {q n : ℕ} (X : Model q n) (hq : 2≤q) (F : Family)

include hq in
private theorem endpoints (f : SharedArcFlatCut.Missing X F) :
    let E := graph X.D F
    let a := f.val.1
    let b := f.val.2
    a≠b ∧ E a a=false ∧ E b b=false ∧ E b a=false := by
  intro E a b
  have sub (i j) (ed : E i j=true) : X.D i j=true := (mem_col.mp (active.mp ed).choose_spec).2.2.2
  have edge : X.D a b=true := f.property.1
  refine ⟨?_,Bool.eq_false_iff.mpr (fun e => loopfree X.free (by omega) a.property (sub _ _ e)),
    Bool.eq_false_iff.mpr (fun e => loopfree X.free (by omega) b.property (sub _ _ e)),
    Bool.eq_false_iff.mpr (fun e => digonfree X.free hq a.property b.property edge (sub _ _ e))⟩
  intro eq
  rw [eq] at edge
  exact loopfree X.free (by omega) b.property edge

include hq in
private theorem rest_live (f : SharedArcFlatCut.Missing X F) : (rest f.val.1 f.val.2).Nonempty := by
  obtain ⟨M,cycle,_,_⟩ := edge_cycle X hq f.val.1.property f.val.2.property f.property.1
  have size := card_le_card cycle.sub
  rw [cycle.size] at size
  have ab := (endpoints X hq F f).1
  apply card_pos.mp
  rw [rest,card_erase_of_mem (mem_erase.mpr ⟨ab.symm,mem_univ _⟩),card_erase_of_mem (mem_univ _),
    card_univ,Fintype.card_coe]
  omega

/-- Smaller-order induction pays all ordinary columns on the two-vertex
puncture. This uses only the induced graph on surviving vertices. -/
theorem ordinary_prices (small : SmallerSmallRow q X.V.card) (G : CH.Digraph) (a b : X.V) (ab : a≠b)
    (live : (rest a b).Nonempty) (free : QFree G ((X.V.erase a.val).erase b.val) q) :
    let C := excess (realMatrix q G X.V)
    ∃z : rest a b→ℝ,(∀i,0≤z i) ∧ (∑i,z i)=1 ∧ ∀j : rest a b,(z ᵥ* C.submatrix Subtype.val Subtype.val) j≤0 := by
  intro C
  let U := (X.V.erase a.val).erase b.val
  have sub : U⊆X.V := (erase_subset _ _).trans (erase_subset _ _)
  have mem (i : X.V) : i.val∈U ↔ i∈rest a b := by
    simp only [U,rest,mem_erase,i.property,mem_univ,and_true]
    exact and_congr (not_congr (show i.val=b.val ↔ i=b from ⟨Subtype.ext,congrArg Subtype.val⟩))
      (not_congr (show i.val=a.val ↔ i=a from ⟨Subtype.ext,congrArg Subtype.val⟩))
  have gone : a.val∉U := by simp [U]
  have proper : U≠X.V := fun e => gone (by rw [e]; exact a.property)
  obtain ⟨i,hi⟩ := live
  obtain ⟨d,paid⟩ := realDual_of_smallRow (small G U (card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨sub,proper⟩)) free)
    ⟨i.val,(mem i).mpr hi⟩
  let z (i : X.V) := maskReal U d i
  obtain ⟨nonneg,mass1,supp,cols⟩ := cutCertificate_of_realDual sub paid
  have host (i : X.V) : i∈hostCut X.V U ↔ i∈rest a b := by simpa [hostCut] using mem i
  have za : z a=0 := supp a (by simp [hostCut,gone])
  have zb : z b=0 := supp b (by simp [hostCut,U])
  have sums (g : X.V→ℝ) : (∑i,z i*g i)=∑i : rest a b,z i.val*g i.val := by
    rw [sum_split a b ab,za,zb]; ring
  refine ⟨fun i : rest a b => z i.val,fun i => nonneg i.val,?_,?_⟩
  · have h := sums (fun _=>1)
    simp only [mul_one] at h
    exact h.symm.trans mass1
  · intro j
    have all : (z ᵥ* C) j.val≤0 := by
      rw [show C=excess (realMatrix q G X.V) from rfl,vecMul_excess]
      exact sub_nonpos.mpr ((cols j.val ((host j.val).mpr j.property)).trans_eq mass1.symm)
    change (∑i,z i*C i j.val)≤0 at all
    rwa [sums (fun i=>C i j.val)] at all

variable (B : Finset ℕ) (H : Matrix X.V X.V ℝ) (prices : ℕ→ℚ) (c : ℚ)
  {w p : ℕ→ℚ} (pos : ∀i∈X.V,0<w i ∧ 0<p i) (wm : mass X.V w=1)
  (wr : ∀i∈X.V,WeightedSD.row q (graph X.D F) X.V w i=1)
  (pc : ∀i∈X.V,WeightedSD.col q (graph X.D F) X.V p i=1)

include hq pos wm wr pc in
/-- Every ordinary puncture price with some positive coordinate must exceed
its available slack after the two endpoint terms are restored. Both terms
use only old incidences. This holds for every choice of the proper dual. -/
theorem price_pressure (small : SmallerSmallRow q X.V.card) (f : SharedArcFlatCut.Missing X F)
    (z : rest f.val.1 f.val.2→ℝ) (live : ∃k,0<z k) :
    let a := f.val.1
    let b := f.val.2
    let C := excess (realMatrix q (graph X.D F) X.V)
    ∃j : rest a b, -(z ᵥ* C.submatrix Subtype.val Subtype.val) j <
      (∑i,z i*C i.val a)*C b j.val - (∑i,z i*C i.val b)/((q:ℝ)-1)*C a j.val := by
  intro a b C
  obtain ⟨ab,aa,bb,back⟩ := endpoints X hq F f
  have right := graph_right hq a b ab aa bb f.property.2 back pos wm wr pc
  obtain ⟨k,hk⟩ := live
  by_contra! none
  have le (j : rest a b) : (z ᵥ* puncture q (graph X.D F) a b) j≤0 := by
    rw [puncture,correction]
    linarith only [none j]
  have eq := congrFun (congrArg (fun M : Matrix (rest a b) (rest a b) ℝ => z ᵥ* M) right) k
  rw [←vecMul_vecMul,vecMul_one] at eq
  apply hk.not_ge
  rw [←eq]
  apply sum_nonpos
  intro i _
  apply mul_nonpos_of_nonpos_of_nonneg (le i)
  exact (div_pos (SharedArcFlatArithmetic.positive X hq small F pos wm wr pc f i.val k.val)
    (mul_pos (mul_pos (by exact_mod_cast (by omega : 0<q)) (by exact_mod_cast (pos a a.property).2))
      (by exact_mod_cast (pos b b.property).1))).le

include hq pos wm wr pc in
/-- If a smaller q-free comparison graph dominates the scaled reduced
matrix, some interior tensor entry is strictly negative. This proof does
not use positivity of the child, even outside the endpoint rectangle. -/
theorem comparison_negative (small : SmallerSmallRow q X.V.card) (f : SharedArcFlatCut.Missing X F)
    (G : CH.Digraph)
    (free : QFree G ((X.V.erase f.val.1.val).erase f.val.2.val) q)
    (l r : rest f.val.1 f.val.2→ℝ) (lp : ∀i,0<l i) (rp : ∀j,0<r j)
    (upper : ∀i j,l i*puncture q (graph X.D F) f.val.1 f.val.2 i j*r j≤excess (realMatrix q G X.V) i.val j.val) :
    let T := test (realMatrix q (graph X.D F) X.V)⁻¹ (fun i : X.V => (w i:ℝ)) (fun i : X.V => (p i:ℝ)) q f.val.1 f.val.2
    ∃i k : rest f.val.1 f.val.2,T i.val k.val<0 := by
  intro T
  let a := f.val.1
  let b := f.val.2
  let K := puncture q (graph X.D F) a b
  obtain ⟨ab,aa,bb,back⟩ := endpoints X hq F f
  obtain ⟨z,zn,zm,zc⟩ := ordinary_prices X small G a b ab (rest_live X hq F f) free
  obtain ⟨k,pk⟩ : ∃k,0<z k := by
    by_contra! none
    exact (show (∑i,z i)≤0 from sum_nonpos fun i _ => none i).not_gt (zm ▸ zero_lt_one)
  let y (i : rest a b) := z i*l i
  have le (j : rest a b) : (y ᵥ* K) j≤0 := by
    apply nonpos_of_mul_nonpos_left _ (rp j)
    change (∑i,(z i*l i)*K i j)*r j≤0
    rw [sum_mul]
    apply le_trans _ (zc j)
    apply sum_le_sum
    intro i _
    simpa only [K,a,b,mul_assoc,submatrix_apply] using mul_le_mul_of_nonneg_left (upper i j) (zn i)
  have right := graph_right hq a b ab aa bb f.property.2 back pos wm wr pc
  have eq := congrFun (congrArg (fun M : Matrix (rest a b) (rest a b) ℝ => y ᵥ* M) right) k
  rw [←vecMul_vecMul,vecMul_one] at eq
  by_contra! none
  apply (mul_pos pk (lp k)).not_ge
  change y k≤0
  rw [←eq]
  exact sum_nonpos fun i _ => mul_nonpos_of_nonpos_of_nonneg (le i) (div_nonneg (none i k)
    (mul_nonneg (mul_nonneg (Nat.cast_nonneg q) (by exact_mod_cast (pos a a.property).2.le))
      (by exact_mod_cast (pos b b.property).1.le)))

include hq pos wm wr pc in
/-- A legal flat insertion forces a short directed closed walk in each
scaled threshold graph on the proper puncture. -/
theorem threshold_cycle (small : SmallerSmallRow q X.V.card) (f : SharedArcFlatCut.Missing X F)
    (l r : rest f.val.1 f.val.2→ℝ)
    (lp : ∀i,0<l i) (rp : ∀j,0<r j)
    (cap : ∀i j,l i*puncture q (graph X.D F) f.val.1 f.val.2 i j*r j≤(q:ℝ)-1) :
    let a := f.val.1
    let b := f.val.2
    let M : Matrix (rest a b) (rest a b) ℝ := fun i j => l i*puncture q (graph X.D F) a b i j*r j
    ¬QFree (threshold a b M) ((X.V.erase a.val).erase b.val) q := by
  intro a b M free
  have upper (i j : rest a b) : M i j≤excess (realMatrix q (threshold a b M) X.V) i.val j.val := by
    rw [excess,realMatrix_entry]
    have eq : i.val=j.val ↔ i=j := Subtype.val_injective.eq_iff
    by_cases edge : threshold a b M i.val j.val=true
    · have bound := cap i j
      change M i j≤(q:ℝ)-1 at bound
      rw [ite_eq_left edge]
      split <;> linarith only [bound]
    · have bound := le_of_not_gt (fun h => edge ((threshold_on a b M i j).mpr h))
      rw [ite_eq_right edge]
      by_cases ij : i=j <;> simpa [eq,ij] using bound
  obtain ⟨i,k,bad⟩ := comparison_negative X hq F pos wm wr pc small f _ free l r lp rp upper
  exact bad.not_gt (SharedArcFlatArithmetic.positive X hq small F pos wm wr pc f i.val k.val)

include hq pos wm wr pc in
/-- Localize the shorter-order comparison on the requested rectangle.
Only signs outside the rectangle are used in this localization. -/
theorem comparison_rectangle (small : SmallerSmallRow q X.V.card) (f : SharedArcFlatCut.Missing X F)
    (G : CH.Digraph) (free : QFree G ((X.V.erase f.val.1.val).erase f.val.2.val) q)
    (l r : rest f.val.1 f.val.2→ℝ) (lp : ∀i,0<l i) (rp : ∀j,0<r j)
    (upper : ∀i j,l i*puncture q (graph X.D F) f.val.1 f.val.2 i j*r j≤excess (realMatrix q G X.V) i.val j.val) :
    let a := f.val.1
    let b := f.val.2
    let E := graph X.D F
    let T := test (realMatrix q E X.V)⁻¹ (fun i : X.V => (w i:ℝ)) (fun i : X.V => (p i:ℝ)) q a b
    ∃v k : X.V,E a v=true ∧ E k b=true ∧ T v k<0 := by
  intro a b E T
  obtain ⟨i,k,lt⟩ := comparison_negative X hq F pos wm wr pc small f G free l r lp rp upper
  by_cases edges : E a i.val=true ∧ E k.val b=true
  · exact ⟨i.val,k.val,edges.1,edges.2,lt⟩
  · have outside : ∀u j : X.V, ¬(E a u=true ∧ E j b=true) → 0≤T u j :=
      fun u j _ => (SharedArcFlatArithmetic.positive X hq small F pos wm wr pc f u j).le
    exact (lt.not_ge (outside _ _ edges)).elim

include hq pos wm wr pc in
private theorem exit_of_sign (f : SharedArcFlatCut.Missing X F) (v k : X.V)
    (le : test (realMatrix q (graph X.D F) X.V)⁻¹ (fun i : X.V => (w i:ℝ)) (fun i : X.V => (p i:ℝ))
      q f.val.1 f.val.2 v k≤0) : SharedArcPivotGate.ProgressAt X F B H prices c := by
  apply Or.inl; apply Or.inl; apply Or.inl; apply Or.inr
  exact ⟨w,p,pos,wm,wr,pc,f,v,k,lt_of_le_of_ne le (SharedArcFlatArithmetic.nonzero hq
    (by simpa using funext (realMatrix_rational_rows w 1 wr))
    (by simpa using funext (realMatrix_rational_columns p 1 pc)) _ _ v k)⟩

include hq pos wm wr pc in
theorem progress (f : SharedArcFlatCut.Missing X F)
    (certificate : let a := f.val.1; let b := f.val.2; let E := graph X.D F
      ∃k : rest a b,E k.val b=true ∧ ∃z : rest a b→ℝ, 0<z k ∧
        (∀i,(z ᵥ* puncture q E a b) i≤0) ∧ (∀i,E a i.val≠true → (z ᵥ* puncture q E a b) i=0)) :
    SharedArcPivotGate.ProgressAt X F B H prices c := by
  obtain ⟨ab,aa,bb,back⟩ := endpoints X hq F f
  obtain ⟨v,k,_,_,le⟩ := (graph_iff hq _ _ ab aa bb f.property.2 back pos wm wr pc).mpr certificate
  exact exit_of_sign X hq F B H prices c pos wm wr pc f v k le

include hq pos wm wr pc in
theorem progress_of_switch (f : SharedArcFlatCut.Missing X F) (v k : X.V)
    (root : ∃s : ℝ, 0<s ∧ s≤1 ∧ (SingleArcSwitchSign.switch (realMatrix q (graph X.D F) X.V)
      (fun i : X.V => (w i:ℝ)) (fun i : X.V => (p i:ℝ)) (s*q) f.val.1 f.val.2 v k).det=0) :
    SharedArcPivotGate.ProgressAt X F B H prices c := by
  apply exit_of_sign X hq F B H prices c pos wm wr pc f v k
  apply (SingleArcSwitchSign.sign_iff (matrix_unit hq _ _) _ _ _ _ _ _ _ ?_ ?_).mpr root
  · exact_mod_cast (pos v v.property).1
  · exact_mod_cast (pos k k.property).2

end Native
end LeanCH.BR.Closure.SingleArcPunctureSign
#print axioms LeanCH.BR.Closure.SingleArcPunctureSign.graph_iff
#print axioms LeanCH.BR.Closure.SingleArcPunctureSign.reduced_right
#print axioms LeanCH.BR.Closure.SingleArcPunctureSign.row_certificate
#print axioms LeanCH.BR.Closure.SingleArcPunctureSign.returns
#print axioms LeanCH.BR.Closure.SingleArcPunctureSign.progress
#print axioms LeanCH.BR.Closure.SingleArcPunctureSign.progress_of_switch
#print axioms LeanCH.BR.Closure.SingleArcPunctureSign.ordinary_prices
#print axioms LeanCH.BR.Closure.SingleArcPunctureSign.price_pressure
#print axioms LeanCH.BR.Closure.SingleArcPunctureSign.comparison_negative
#print axioms LeanCH.BR.Closure.SingleArcPunctureSign.threshold_cycle
#print axioms LeanCH.BR.Closure.SingleArcPunctureSign.comparison_rectangle
