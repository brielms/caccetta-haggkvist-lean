import checkpoints.shen_extension.SharedArcFlatResponse

namespace LeanCH.BR.Closure.SharedArcFlatCut
open Finset Matrix BRq2 BRq3 BR45 WeightedSD FiniteCutInverse ShortestCycleWeights FirstPacketBarrier MarkedCyclePeeling SharedArcBarrier ShenCycleSuccessor
open scoped Matrix

section Algebra
variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Two complementary arc sets cannot be uncoupled through the inverse of
their union. If the mixed product vanished, the flat matrix itself would
factor into three invertible matrices. -/
theorem mixed_ne_zero {A C B D K HC HB : Matrix I I ℝ}
    (dk : D*K=1) (ch : C*HC=1) (bh : B*HB=1) (split : C+B=D+A)
    {w : I→ℝ} (live : w≠0) (flat : A *ᵥ w=0) : (D-C)*K*(D-B)≠0 := by
  intro zero
  have kd := mul_eq_one_comm.mp dk
  have expand : (D-C)*K*(D-B) = D-C-B+C*K*B := by
    rw [sub_mul,mul_sub,sub_mul,sub_mul,dk,one_mul,one_mul,Matrix.mul_assoc C K D,kd,mul_one]
    abel
  have factor : A=C*K*B := by
    rw [expand] at zero
    linear_combination (norm := abel) -zero - split
  have right : (C*K*B)*(HB*D*HC)=1 := by
    calc
      _ = C*K*(B*HB)*D*HC := by noncomm_ring
      _ = 1 := by rw [bh,mul_one,Matrix.mul_assoc C K D,kd,mul_one,ch]
  rw [factor] at flat
  have e := congrArg (fun z => (HB*D*HC) *ᵥ z) flat
  rw [Matrix.mulVec_mulVec,mul_eq_one_comm.mp right,Matrix.one_mulVec,Matrix.mulVec_zero] at e
  exact live e

private theorem positive_perm {D K : Matrix I I ℝ} (dk : D*K=1) (pos : ∀i j,0≤K i j) :
    ∃σ : Equiv.Perm I,∀i,0<K (σ i) i := by
  classical
  by_contra! no
  have zero : K.det=0 := by
    rw [Matrix.det_apply]
    apply sum_eq_zero
    intro σ _
    obtain ⟨i,hi⟩ := no σ
    rw [prod_eq_zero (f:=fun j => K (σ j) j) (mem_univ i) (le_antisymm hi (pos _ _)),smul_zero]
  have one := congrArg Matrix.det dk
  rw [Matrix.det_mul,zero,mul_zero,Matrix.det_one] at one
  exact zero_ne_one one
end Algebra

private def selectArcs (E D : CH.Digraph) (pick : ℕ→ℕ→Bool) : CH.Digraph :=
  fun i j => E i j || (D i j && pick i j)

private theorem splitEntry (e d c : Bool) (x t : ℝ) (ed : e=true → d=true) :
    (x+(if (e || (d && !c)) then t else 0)-1)+(x+(if (e || (d && c)) then t else 0)-1)
      =(x+(if d then t else 0)-1)+(x+(if e then t else 0)-1) := by
  cases e <;> cases d <;> cases c <;> simp_all
  ring

private theorem keep (e d c : Bool) (ed : e=true → d=true) (no : ¬(d=true ∧ e=false ∧ c=false)) :
    (e || (d && c))=d := by cases e <;> cases d <;> cases c <;> simp_all

private theorem keepOther (e d c : Bool) (ed : e=true → d=true) (no : ¬(d=true ∧ e=false ∧ c=true)) :
    (e || (d && !c))=d := by cases e <;> cases d <;> cases c <;> simp_all

private theorem old_native {q n} (X : Model q n) (F : Family) {i j}
    (h : graph X.D F i j=true) : X.D i j=true := by
  obtain ⟨A,hit⟩ := active.mp h
  exact (mem_col.mp hit).2.2.2

private theorem insert_native {q n} (X : Model q n) (F : Family) (a b : X.V)
    (ab : X.D a b=true) {i j} (ed : insertArc (graph X.D F) a b i j=true) : X.D i j=true := by
  by_cases pair : i=(a:ℕ) ∧ j=(b:ℕ)
  · exact pair.1 ▸ pair.2 ▸ ab
  exact old_native X F (by simpa [insertArc,pair] using ed)

/-- Every partition into two nonempty classes of new arcs has a positive
transition from the head of the first class to the tail of the second in
one fixed native inverse. The partition may depend on the labelled graph. -/
theorem crosses {q n} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    (F : Family) {w : ℕ→ℚ} (wp : ∀i∈X.V,0<w i) (wm : mass X.V w=1)
    (wr : ∀i∈X.V,WeightedSD.row q (graph X.D F) X.V w i=1)
    {K : Matrix X.V X.V ℝ} (native : CommonInverse (realMatrix q X.D X.V) K)
    (pick : ℕ→ℕ→Bool)
    (yes : ∃a b : X.V,X.D a b=true ∧ graph X.D F a b=false ∧ pick a b=true)
    (no : ∃a b : X.V,X.D a b=true ∧ graph X.D F a b=false ∧ pick a b=false) :
    ∃a b u v : X.V,(X.D a b=true ∧ graph X.D F a b=false ∧ pick a b=true) ∧
      (X.D u v=true ∧ graph X.D F u v=false ∧ pick u v=false) ∧ 0<K b u := by
  classical
  let E := graph X.D F
  let red := selectArcs E X.D pick
  let blue := selectArcs E X.D (fun i j => !(pick i j))
  let m := fun G => excess (realMatrix q G X.V)
  have get (col : ℕ→ℕ→Bool) (hit : ∃a b : X.V,X.D a b=true ∧ E a b=false ∧ col a b=true) :
      ∃H,CommonInverse (realMatrix q (selectArcs E X.D col) X.V) H := by
    let J := selectArcs E X.D col
    have sub {i j} (ed : J i j=true) : X.D i j=true := by
      change (_ || _) = true at ed
      simp only [Bool.or_eq_true,Bool.and_eq_true] at ed
      rcases ed with e|c
      · exact old_native X F e
      · exact c.1
    obtain ⟨a,b,ab,off,incl⟩ := hit
    have bad : ¬SmallRow q J X.V := positive_feasible_extension_not_smallRow (D:=E) (E:=J) hq
      (fun i _ j _ h => by simp [J,selectArcs,h]) w wp (fun i hi => by rw [wm,wr i hi])
      a.property b.property (by simp [off]) (by simp [J,selectArcs,ab,incl])
    obtain ⟨z,zn,_,high⟩ := strict_witness_of_not_smallRow bad
    exact strict_inverse_of_proper_smallRow (small.induced (qfree_sub (fun _ _ h => sub h) X.free)) z zn high
  obtain ⟨HR,hr⟩ := get pick yes
  obtain ⟨HB,hb⟩ := get (fun i j => !(pick i j)) (by
    obtain ⟨a,b,ab,off,miss⟩ := no
    exact ⟨a,b,ab,off,by simp [miss]⟩)
  have split : m blue + m red=m X.D+m E := by
    ext i j
    have incl := @old_native q n X F i j
    simp only [m,Matrix.add_apply,excess,realMatrix_entry,red,blue,selectArcs]
    exact splitEntry _ _ _ _ _ incl
  have flat : m E *ᵥ (fun i : X.V => (w i : ℝ))=0 := by
    funext i
    rw [show m E=excess (realMatrix q E X.V) from rfl,mulVec_excess,real_mass_of_rational_probability w wm,
      realMatrix_rational_rows w 1 wr]
    simp
  have live : (fun i : X.V => (w i:ℝ))≠0 := by
    obtain ⟨i,iv⟩ := X.live
    intro eq
    have e := congrFun eq ⟨i,iv⟩
    exact (show (0:ℝ)<w i by exact_mod_cast wp i iv).ne' e
  have nz := mixed_ne_zero (C:=m blue) (B:=m red) native.right hb.right hr.right split live flat
  by_contra! none
  apply nz
  ext i j
  rw [Matrix.mul_apply]
  change (∑u, _ * _) = (0:ℝ)
  apply sum_eq_zero
  intro u _
  rw [Matrix.mul_apply,sum_mul]
  apply sum_eq_zero
  intro b _
  by_cases r : X.D i b=true ∧ E i b=false ∧ pick i b=true
  · by_cases s : X.D u j=true ∧ E u j=false ∧ pick u j=false
    · have z := le_antisymm (none i b u j r s) (native.nonneg b u)
      simp [z]
    · have same : red u j=X.D u j := by
        exact keep _ _ _ (@old_native q n X F u j) s
      simp [m,excess,realMatrix_entry,same]
  · have same : blue i b=X.D i b := by
      exact keepOther _ _ _ (@old_native q n X F i b) r
    simp [m,excess,realMatrix_entry,same]


abbrev Missing {q n} (X : Model q n) (F : Family) :=
  {e : X.V × X.V // X.D e.1 e.2=true ∧ graph X.D F e.1 e.2=false}

def PositiveStep {q n} {X : Model q n} {F : Family} (K : Matrix X.V X.V ℝ)
    (e f : Missing X F) : Prop := 0<K e.val.2 f.val.1

theorem communicates {q n} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    (F : Family) {w : ℕ→ℚ} (wp : ∀i∈X.V,0<w i) (wm : mass X.V w=1)
    (wr : ∀i∈X.V,WeightedSD.row q (graph X.D F) X.V w i=1)
    {K : Matrix X.V X.V ℝ} (native : CommonInverse (realMatrix q X.D X.V) K)
    (s t : Missing X F) : Relation.ReflTransGen (PositiveStep K) s t := by
  classical
  let reach := Relation.ReflTransGen (PositiveStep (X:=X) (F:=F) K) s
  let pick (i j : ℕ) := decide (∃e : Missing X F,(e.val.1:ℕ)=i ∧ (e.val.2:ℕ)=j ∧ reach e)
  have mark (e : Missing X F) : pick e.val.1 e.val.2=true ↔ reach e := by
    change decide _=true ↔ _
    rw [decide_eq_true_eq]
    constructor
    · rintro ⟨g,h,l,r⟩
      have equ : g=e := Subtype.ext (Prod.ext (Subtype.ext h) (Subtype.ext l))
      exact equ ▸ r
    · exact fun r => ⟨e,rfl,rfl,r⟩
  by_contra miss
  have st : pick s.val.1 s.val.2=true := (mark s).mpr .refl
  have en := Bool.eq_false_iff.mpr (fun hit => miss ((mark t).mp hit))
  obtain ⟨a,b,u,v,⟨ab,old,pab⟩,⟨uv,off,puv⟩,edge⟩ := crosses X hq small F wp wm wr native pick
    ⟨s.val.1,s.val.2,s.property.1,s.property.2,st⟩ ⟨t.val.1,t.val.2,t.property.1,t.property.2,en⟩
  let f : Missing X F := ⟨(a,b),ab,old⟩
  let g : Missing X F := ⟨(u,v),uv,off⟩
  have hit := (mark g).mpr (((mark f).mp pab).tail (show PositiveStep K f g from edge))
  exact Bool.noConfusion (puv.symm.trans hit)

/-- The native inverse supplies a common lower bound on every candidate's
four-index test, including on a single permutation independent of the edit. -/
def Conditions {q n} (X : Model q n) (F : Family) (w p : ℕ→ℚ) : Prop :=
    let T := fun (h : Missing X F) (v k : X.V) =>
      SharedArcFlatResponse.test (realMatrix q (graph X.D F) X.V)⁻¹
        (fun i : X.V => (w i : ℝ)) (fun i : X.V => (p i : ℝ)) q h.val.1 h.val.2 v k
    (∃σ : Equiv.Perm X.V,∀k,∀h,0<T h (σ k) k) ∧
    ∀s t : Missing X F,Relation.ReflTransGen (fun e f => ∀h,0<T h e.val.2 f.val.1) s t

theorem global {q n} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    (F : Family) {w p : ℕ→ℚ} (wp : ∀i∈X.V,0<w i ∧ 0<p i) (wm : mass X.V w=1)
    (wr : ∀i∈X.V,WeightedSD.row q (graph X.D F) X.V w i=1)
    (pc : ∀i∈X.V,WeightedSD.col q (graph X.D F) X.V p i=1) :
    Conditions X F w p := by
  unfold Conditions
  intro T
  obtain ⟨K,native⟩ := strict_inverse_of_proper_smallRow (small.induced X.free)
    (fun i => (X.weights i : ℚ)) (fun _ _ => Nat.cast_nonneg _) X.strict
  have lt (h : Missing X F) (v k : X.V) (pos : 0<K v k) : 0<T h v k := by
    let a := h.val.1
    let b := h.val.2
    let J := insertArc (graph X.D F) a b
    have sub : ∀i j,J i j=true → X.D i j=true := fun _ _ e => insert_native X F a b h.property.1 e
    obtain ⟨H,inv,eq⟩ := SharedArcFlatResponse.inverse_test hq small a b h.property.2
      (qfree_sub sub X.free) wp wm wr pc
    have hh := pos.trans_le (graph_inverse_antitone (fun i _ j _ => sub i j) inv native v k)
    have hp : (0:ℝ)<p a := by exact_mod_cast (wp a a.property).2
    have hw : (0:ℝ)<w b := by exact_mod_cast (wp b b.property).1
    change 0<SharedArcFlatResponse.test _ _ _ _ a b v k
    rw [eq]
    exact mul_pos (mul_pos (mul_pos (by exact_mod_cast (show 0<q by omega)) hp) hw) hh
  obtain ⟨σ,pos⟩ := positive_perm native.right native.nonneg
  refine ⟨⟨σ,fun k h => lt h _ _ (pos k)⟩,?_⟩
  intro s t
  have path := communicates X hq small F (fun i iv => (wp i iv).1) wm wr native s t
  induction path with
  | refl => exact .refl
  | tail prior edge ih => exact ih.tail (fun h => lt h _ _ edge)


/-- A failed matching or a failed return between fresh arcs is a sufficient
obstruction expressed entirely in the old tensor and the native arc set. -/
def Obstruction {q n} (X : Model q n) (F : Family) : Prop :=
  ∃w p : ℕ→ℚ,(∀i∈X.V,0<w i ∧ 0<p i) ∧ mass X.V w=1 ∧
    (∀i∈X.V,WeightedSD.row q (graph X.D F) X.V w i=1) ∧
    (∀i∈X.V,WeightedSD.col q (graph X.D F) X.V p i=1) ∧ ¬Conditions X F w p

def ProgressAt {q n} (X : Model q n) (F : Family) (B : Finset ℕ)
    (H : Matrix X.V X.V ℝ) (p : ℕ→ℚ) (c : ℚ) : Prop :=
  SharedArcPacketDescent.ProgressAt X F B H p c ∨ Obstruction X F

theorem blocks {q n} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    {F B H p c} (prior : ¬SharedArcPacketDescent.ProgressAt X F B H p c) :
    ¬ProgressAt X F B H p c := by
  rintro (done|⟨w,r,wp,wm,wr,pc,fail⟩)
  · exact prior done
  · exact fail (global X hq small F wp wm wr pc)

/-- All components see the same terminal floor. Each candidate value is
determined by the uncentered inverse of the old graph. -/
theorem competitors {q n} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    (F : Family) (c : ℚ) (lower : ∀M,SharedArcBarrier.Boundary X F M →
      (targets X.D X.V F M).card=1 → ∃x : ℕ→ℚ,∃d : ℚ,
      c≤d ∧ mass X.V x=1 ∧ ∀v∈X.V,WeightedSD.row q (graph X.D (insert M F)) X.V x v=d)
    {w p : ℕ→ℚ} (wp : ∀i∈X.V,0<w i ∧ 0<p i) (wm : mass X.V w=1)
    (wr : ∀i∈X.V,WeightedSD.row q (graph X.D F) X.V w i=1)
    (pc : ∀i∈X.V,WeightedSD.col q (graph X.D F) X.V p i=1) (f : Missing X F) :
    let a := f.val.1
    let b := f.val.2
    let L := (realMatrix q (graph X.D F) X.V)⁻¹
    ∃M,SharedArcBarrier.Boundary X F M ∧ SharedArcComponentExchange.added X.D F M={(a.val,b.val)} ∧
      ∃x : ℕ→ℚ,∃d : ℚ,c≤d ∧ mass X.V x=1 ∧
      (∀v∈X.V,WeightedSD.row q (graph X.D (insert M F)) X.V x v=d) ∧
      ((d:ℝ)-1)*(1+(q:ℝ)*L b a)=(q:ℝ)*d*(p a:ℝ)*(w b:ℝ) := by
  classical
  intro a b L
  let E := graph X.D F
  let J := insertArc E a b
  have bad : ¬SmallRow q J X.V := positive_feasible_extension_not_smallRow (D:=E) hq
    (fun i _ j _ h => insertArc_mono E a b i j h) w (fun i hi => (wp i hi).1)
    (fun i hi => by rw [wm,wr i hi]) a.property b.property (Bool.eq_false_iff.mp f.property.2)
    (by simp [J,insertArc])
  obtain ⟨M,bm,only,eq⟩ := SharedArcFlatResponse.realize X hq small
    (f:=(a.val,b.val)) ⟨a.property,b.property,f.property⟩ bad
  have cm : ShenCycleSuccessor.Cycle X.D X.V q M := (mem_filter.mp bm.1).2
  have count : (targets X.D X.V F M).card=1 := by rw [←SharedArcComponentExchange.count cm,only,card_singleton]
  obtain ⟨x,d,le,xm,rows⟩ := lower M bm count
  refine ⟨M,bm,only,x,d,le,xm,rows,?_⟩
  have same : graph X.D (insert M F)=J := eq
  have edited : ∀v∈X.V,WeightedSD.row q J X.V x v=d := by rwa [←same]
  exact SharedArcFlatResponse.response (Matrix.mul_nonsing_inv _ (SharedArcFlatResponse.matrix_unit hq E X.V))
    (realMatrix_insert_difference (q:=q) a b (Bool.eq_false_iff.mp f.property.2))
    (by simpa using funext (realMatrix_rational_rows w 1 wr)) (by simpa using funext (realMatrix_rational_columns p 1 pc))
    (real_mass_of_rational_probability w wm) (real_mass_of_rational_probability x xm)
    (funext (realMatrix_rational_rows x d edited))

#print axioms crosses
#print axioms communicates
#print axioms global
#print axioms competitors
#print axioms blocks
end LeanCH.BR.Closure.SharedArcFlatCut
