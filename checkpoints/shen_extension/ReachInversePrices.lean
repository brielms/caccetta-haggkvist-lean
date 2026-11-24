import checkpoints.shen_extension.FlatPeelReach
import checkpoints.shen_extension.SingleArcTensorMerge

namespace LeanCH.BR.Closure.ReachInversePrices
open Finset Matrix BRq2 BRq3 BR45 WeightedSD FiniteCutInverse FlatPeelReach
open scoped Matrix

/-- The same geometric cut holds separately for each actual inverse
    column. No constant-row assumption on that column is needed. -/
theorem column_budget {q : ℕ} {D : CH.Digraph} {V U : Finset ℕ} {H : Matrix V V ℝ}
    (hq : 2≤q) (free : QFree D V q) (small : SmallerSmallRow q V.card) (bad : ¬SmallRow q D V)
    (inv : CommonInverse (realMatrix q D V) H) (us : U⊆V) (room : U.card+1<V.card) (k : V) :
    let f := realExtendWeight V (fun i=>H i k)
    (q:ℝ)*realMass (interior D V U (q-1)) f≤realMass U f := by
  intro f
  obtain ⟨u,_,pos,paid,eq⟩ := SingleArcTensorMerge.rational_rays inv k
  have same {S : Finset ℕ} (sv : S⊆V) : realMass S f=(mass S u:ℝ) := by
    simp only [realMass,mass,Rat.cast_sum]; apply sum_congr rfl
    intro i si
    let v : V := ⟨i,sv si⟩
    exact (realExtendWeight_on V (fun j=>H j k) v).trans (eq v).1.symm
  rw [same (S:=interior D V U (q-1)) (filter_subset _ _),same us]
  by_cases live : U.Nonempty
  · exact_mod_cast weak_budget hq free small bad us room live (fun i iv=>(pos i iv).1) (fun i iv=>(paid i iv).1)
  · have empty := not_nonempty_iff_eq_empty.mp live
    have none : interior D V U (q-1)=∅ := eq_empty_iff_forall_notMem.mpr fun i ih=>
      live ⟨i,(mem_filter.mp ih).2 (self_mem_ball (mem_filter.mp ih).1)⟩
    rw [none,empty]; simp [mass]

private theorem impulse {q : ℕ} {D : CH.Digraph} {V : Finset ℕ} {H : Matrix V V ℝ}
    (inv : CommonInverse (realMatrix q D V) H) (a k : V) :
    let f := realExtendWeight V (H k)
    f a+(q:ℝ)*realMass (inN D V a) f=realMass V f+(if k=a then 1 else 0) := by
  intro f
  have left : H*excess (realMatrix q D V)=1 := mul_eq_one_comm.mp inv.right
  have eq := congrArg (fun M : Matrix V V ℝ=>M k a) left
  change (H k ᵥ* excess (realMatrix q D V)) a=(1 : Matrix V V ℝ) k a at eq
  have id : (fun i : V=>f i)=H k := funext (fun i=>realExtendWeight_on V (H k) i)
  rw [←id,vecMul_excess,realMatrix_col q D V f,one_apply,realCol,realInW_eq_mass_inN] at eq
  have norm : (∑i : V,f i)=realMass V f := sum_coe_sort V f
  rw [norm] at eq
  exact sub_eq_iff_eq_add'.mp eq

/-- Heads of a that can return to b within the specified radius. -/
noncomputable def returning (D : CH.Digraph) (V : Finset ℕ) (a b r : ℕ) :=
  (outN D V a).filter (fun h=>b∈ball D V h r)

/-- For every arc b→a and inverse column k, exact-length returns from
    heads of a must cover b's entry and an extra unit when k=a. -/
theorem arc_price {q : ℕ} {D : CH.Digraph} {V : Finset ℕ} {H : Matrix V V ℝ}
    (hq : 2≤q) (free : QFree D V q) (small : SmallerSmallRow q V.card) (bad : ¬SmallRow q D V)
    (inv : CommonInverse (realMatrix q D V) H) {b a : V} (edge : D b a=true) (k : V) :
    H b k+(if k=a then 1 else 0)≤
      (q:ℝ)*realMass (returning D V a b (q-1)) (realExtendWeight V (fun i=>H i k)) := by
  classical
  let U := (V.erase a.val).erase b.val
  let N := outN D V a
  let R := interior D V U (q-1)
  let P := returning D V a b (q-1)
  let f := realExtendWeight V (fun i=>H i k)
  have ba : b.val≠a.val := fun same=>loopfree free (by omega) a.property (same ▸ edge)
  have bu : b.val∈V.erase a.val := mem_erase.mpr ⟨ba,b.property⟩
  have cap := column_budget hq free small bad inv (U:=U)
    ((erase_subset ..).trans (erase_subset ..)) (by
      dsimp [U]; have x := card_erase_add_one a.property; have y := card_erase_add_one bu; omega) k
  change (q:ℝ)*realMass R f≤realMass U f at cap
  have impulseA : f a+(q:ℝ)*realMass N f=realMass V f+(if k=a then 1 else 0) :=
    impulse (commonInverse_reverse inv) a k
  have massEq : realMass U f+f b+f a=realMass V f := by
    change (∑i∈(V.erase a.val).erase b.val,f i)+f b+f a=∑i∈V,f i
    rw [sum_erase_add _ _ bu,sum_erase_add _ _ a.property]
  have sub : N\P⊆R := by
    intro i ih
    have nh := (mem_sdiff.mp ih).1
    exact (head_geometry hq free edge nh).2.mpr (fun hit=>(mem_sdiff.mp ih).2 (mem_filter.mpr ⟨nh,hit⟩))
  have nn (i) (ir : i∈R) : 0≤f i := by
    let t : V := ⟨i,(mem_filter.mp ir).1⟩
    change 0≤realExtendWeight V (fun j=>H j k) t
    rw [realExtendWeight_on]; exact inv.nonneg t k
  have subsetMass : realMass (N\P) f≤realMass R f := sum_le_sum_of_subset_of_nonneg sub (fun i ir _=>nn i ir)
  have pieces : realMass (N\P) f+realMass P f=realMass N f := sum_sdiff (filter_subset _ _)
  change H b k+(if k=a then 1 else 0)≤(q:ℝ)*realMass P f
  rw [←show f b=H b k from realExtendWeight_on V _ b]
  linarith only [cap,impulseA,massEq,mul_le_mul_of_nonneg_left subsetMass (Nat.cast_nonneg (α:=ℝ) q),
    congrArg (fun x : ℝ=>(q:ℝ)*x) pieces]

/-- If a designated zero-diagonal vertex is the only candidate to
    continue b→a into a shortest return, the inverse prices contradict
    positivity off the diagonal. -/
theorem alternate {q : ℕ} {D : CH.Digraph} {V : Finset ℕ} {H : Matrix V V ℝ}
    (hq : 2≤q) (free : QFree D V q) (small : SmallerSmallRow q V.card) (bad : ¬SmallRow q D V)
    (inv : CommonInverse (realMatrix q D V) H) {b a : V} (edge : D b a=true)
    (v : V) (bv : b≠v) (zero : H v v=0) :
    ∃h∈outN D V a,h≠v.val ∧ Walk D V h b (q-1) := by
  classical
  let P := returning D V a b (q-1)
  let f := realExtendWeight V (fun j=>H j v)
  have enough := arc_price hq free small bad inv edge v
  change H b v+(if v=a then 1 else 0)≤(q:ℝ)*realMass P f at enough
  have extra : (0:ℝ)≤(if v=a then 1 else 0) := by split <;> norm_num
  have live : 0<realMass P f := by
    by_contra! low
    linarith only [mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg (α:=ℝ) q) low,
      enough,extra,InverseOffDiagonal.graph_positive hq inv bv]
  have some : ∃h∈P,0<f h := by
    by_contra! nonpos
    exact live.not_ge (sum_nonpos nonpos)
  obtain ⟨h,ph,hp⟩ := some
  obtain ⟨ah,reach⟩ := mem_filter.mp ph
  have ne : h≠v.val := by
    intro eq; subst h
    change 0<realExtendWeight V (fun j=>H j v) v at hp
    rw [realExtendWeight_on,zero] at hp; exact (lt_irrefl _ hp)
  obtain ⟨_,l,bound,path⟩ := mem_ball.mp reach
  have len : l=q-1 := by
    by_contra neq
    exact free b (l+1+1) (by omega) (by omega) (.step a.property edge (.step (mem_outN.mp ah).1 (mem_outN.mp ah).2 path))
  exact ⟨h,ah,ne,len ▸ path⟩

/-- Failure of an exact return bill in either orientation gives an
    explicit family excluded by the smaller-host law. -/
def Underpaid {q : ℕ} (D : CH.Digraph) (V : Finset ℕ) (H : Matrix V V ℝ) : Prop :=
  ∃b a k : V,D b a=true ∧
    (q:ℝ)*realMass (returning D V a b (q-1)) (realExtendWeight V (fun i=>H i k)) <
      H b k+(if k=a then 1 else 0)

theorem excludes {q : ℕ} {D : CH.Digraph} {V : Finset ℕ} {H : Matrix V V ℝ}
    (hq : 2≤q) (free : QFree D V q) (small : SmallerSmallRow q V.card) (bad : ¬SmallRow q D V)
    (inv : CommonInverse (realMatrix q D V) H) :
    ¬(Underpaid (q:=q) D V H ∨ Underpaid (q:=q) (fun x y=>D y x) V H.transpose) := by
  rintro (⟨b,a,k,ed,low⟩|⟨b,a,k,ed,low⟩)
  · exact low.not_ge (arc_price hq free small bad inv ed k)
  · exact low.not_ge (arc_price hq free.reverse small (not_smallRow_reverse_of_global small free bad)
      (commonInverse_reverse inv) ed k)

#print axioms alternate
#print axioms excludes

#print axioms column_budget
#print axioms arc_price
end LeanCH.BR.Closure.ReachInversePrices
