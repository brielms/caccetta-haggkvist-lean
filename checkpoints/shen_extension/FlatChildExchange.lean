import checkpoints.shen_extension.CoupledArcTrajectory

namespace LeanCH.BR.Closure.FlatChildExchange
open Finset BRq2 BRq3 BR45 WeightedSD
open OpposedPairPrices FirstPacketBarrier PairedFamilyLoop

/-- Reversing the smaller graph supplies a row law. The given strictly
positive column law forces every inequality of this row law to be exact. -/
theorem opposite_law {q E V U p} (hq : 2 ≤ q) (free : QFree E V q)
    (small : SmallerSmallRow q V.card) (sub : U ⊆ V) (proper : U ≠ V)
    (pm : realMass U p = 1) (pp : ∀ i ∈ U, 0 < p i)
    (uc : ∀ i ∈ U, realCol q E U p i = 1) :
    ∃ z, realMass U z = 1 ∧ ∀ i ∈ U, 0 < z i ∧ realRow q E U z i = 1 := by
  classical
  have live : U.Nonempty := by
    by_contra! empty
    simp [empty,realMass] at pm
  obtain ⟨z,hz⟩ := realDual_of_smallRow (small.reverse_induced free U sub proper) live
  have le (i) (hi : i ∈ U) : realRow q E U z i ≤ 1 := hz.columns i hi
  have eqn := real_cross_rows q E U z p
  rw [sum_congr rfl (fun i hi => show z i*realCol q E U p i = z i by rw [uc i hi,mul_one]),
    show (∑ i ∈ U,z i) = 1 from hz.normalized] at eqn
  have zero : (∑ i ∈ U,p i*(1-realRow q E U z i))=0 := by
    simp_rw [mul_sub,mul_one,sum_sub_distrib,eqn,show (∑ i ∈ U,p i)=1 from pm,sub_self]
  have ur (i) (hi : i∈U) : realRow q E U z i=1 := by
    have e := (sum_eq_zero_iff_of_nonneg (fun j hj => mul_nonneg (pp j hj).le (sub_nonneg.mpr (le j hj)))).mp zero i hi
    rcases mul_eq_zero.mp e with h | h
    · exact ((pp i hi).ne' h).elim
    · linarith
  have pos := real_unit_columns_positive (D:=fun a b => E b a) hq z hz.nonneg ur
  exact ⟨z,hz.normalized,fun i hi => ⟨pos i hi,ur i hi⟩⟩

/-- Cross a column law on S with a row law on T. Both diagonal contributions
use exactly the common vertices. The two edge sums count the same arcs. -/
private theorem rectangular (q : ℕ) (E : CH.Digraph) (S T : Finset ℕ) (p z : ℕ→ℝ) :
    (∑ i ∈ S,p i*price q (fun a b => E b a) T z i) =
      ∑ j ∈ T,z j*price q E S p j := by
  classical
  simp only [price,mul_add,sum_add_distrib]
  congr 1
  · simp only [mul_ite,mul_zero,←sum_filter]
    have same : S.filter (· ∈ T)=T.filter (· ∈ S) := by ext; simp [and_comm]
    rw [same]
    exact sum_congr rfl fun i _ => mul_comm _ _
  · calc
      _ = q*(∑ i∈S,p i*realOutW E T z i) := by
        rw [mul_sum]; apply sum_congr rfl; intro i _; change _=↑q*(p i*realInW (fun a b => E b a) T z i); ring
      _ = q*(∑ j∈T,z j*realInW E S p j) := by rw [real_cross_out]
      _ = _ := by rw [mul_sum]; exact sum_congr rfl fun _ _ => by ring

private theorem split_price {S T : Finset ℕ} {p h : ℕ→ℝ} {c : ℝ}
    (pm : realMass S p=1) (flat : ∀ i∈T,h i=c) :
    (∑ i∈S,p i*h i)=c+∑ i∈S\T,p i*(h i-c) := by
  have rem : (∑i∈S\T,p i*(h i-c))=∑i∈S,p i*(h i-c) := by
    apply sum_subset sdiff_subset
    intro i hi no
    have inT : i∈T := by_contra fun h => no (mem_sdiff.mpr ⟨hi,h⟩)
    rw [flat i inT,sub_self,mul_zero]
  rw [rem]
  simp_rw [mul_sub,sum_sub_distrib,←sum_mul,show (∑ i∈S,p i)=1 from pm,one_mul]
  ring

/-- All orders, all pairs of children, and the parent as a special case. -/
theorem exchange {q E S T p z} {c d : ℝ} (pm : realMass S p=1) (zm : realMass T z=1)
    (col : ∀i∈S,realCol q E S p i=c) (row : ∀i∈T,realRow q E T z i=d) :
    (∑j∈T\S,z j*((q:ℝ)*realInW E S p j-c)) -
      (∑i∈S\T,p i*((q:ℝ)*realOutW E T z i-d)) = d-c := by
  have h := rectangular q E S T p z
  rw [split_price (T:=T) (h:=price q (fun a b => E b a) T z) pm (fun i hi => by rw [price,ite_eq_left hi]; exact row i hi),
      split_price (T:=S) (h:=price q E S p) zm (fun i hi => by rw [price,ite_eq_left hi]; exact col i hi)] at h
  have leftEq := sum_congr (s₁:=S\T) rfl (fun i hi =>
    show p i*(price q (fun a b => E b a) T z i-d)=p i*((q:ℝ)*realOutW E T z i-d) by
      simp only [price,ite_eq_right (mem_sdiff.mp hi).2,zero_add]; try rfl)
  have rightEq := sum_congr (s₁:=T\S) rfl (fun j hj =>
    show z j*(price q E S p j-c)=z j*((q:ℝ)*realInW E S p j-c) by
      simp only [price,ite_eq_right (mem_sdiff.mp hj).2,zero_add])
  rw [leftEq,rightEq] at h
  linarith


/-- Pair the actual incidences after any bijective relabelling of the two
sets. The sums use the column weights of S and the row weights of T. -/
theorem relabel {q E} {S T : Finset ℕ} {p z : ℕ→ℝ} (e : ↥S ≃ ↥T)
    (pm : realMass S p=1) (zm : realMass T z=1)
    (col : ∀i∈S,realCol q E S p i=1) (row : ∀i∈T,realRow q E T z i=1) :
    (∑i : ↥S, ∑j : ↥S,p i*(realMatrix q E S i j)*z (e j)) =
      ∑i : ↥S, ∑j : ↥S,p i*(realMatrix q E T (e i) (e j))*z (e j) := by
  classical
  have cold (j : ↥S) : (∑i : ↥S,p i*realMatrix q E S i j)=1 :=
    (realMatrix_col q E S p j).trans (col j j.property)
  have rowd (i : ↥T) : (∑j : ↥T,realMatrix q E T i j*z j)=1 := by
    have h := (realMatrix_col q (fun a b => E b a) T z i).trans (row i i.property)
    change (∑j : ↥T,z j*realMatrix q (fun a b => E b a) T j i)=1 at h
    rw [←h]
    apply sum_congr rfl
    intro j _
    rw [mul_comm,realMatrix_entry,realMatrix_entry]
    simp only [eq_comm]
  calc
    _ = ∑j : ↥S, ∑i : ↥S,p i*realMatrix q E S i j*z (e j) := sum_comm
    _ = ∑j : ↥S,z (e j) := sum_congr rfl fun j _ => by rw [←sum_mul,cold,one_mul]
    _ = 1 := (e.sum_comp (fun j : ↥T => z j)).trans ((sum_coe_sort T z).trans zm)
    _ = ∑i : ↥S,p i := ((sum_coe_sort S p).trans pm).symm
    _ = _ := by
      apply sum_congr rfl
      intro i _
      simp_rw [mul_assoc,←mul_sum,e.sum_comp (fun j : ↥T => realMatrix q E T (e i) j*z j),rowd,mul_one]

/-- A bijection preserving all arcs between flat children preserves
non-arcs as well. A strict embedding on the same number of labels fails. -/
theorem rigid_relabel {q E} {S T : Finset ℕ} {p z : ℕ→ℝ} (hq : 2 ≤ q) (e : ↥S ≃ ↥T)
    (pm : realMass S p=1) (zm : realMass T z=1) (pp : ∀i∈S,0<p i) (zp : ∀i∈T,0<z i)
    (col : ∀i∈S,realCol q E S p i=1) (row : ∀i∈T,realRow q E T z i=1)
    (pres : ∀i j : ↥S,E i j=true → E (e i) (e j)=true) :
    ∀i j : ↥S,E i j=E (e i) (e j) := by
  classical
  let diff (i j : ↥S) := realMatrix q E T (e i) (e j)-realMatrix q E S i j
  have formula (i j : ↥S) : diff i j =
      (if E (e i) (e j)=true then (q:ℝ) else 0)-(if E i j=true then (q:ℝ) else 0) := by
    simp only [diff,realMatrix_entry,e.injective.eq_iff]
    ring
  have nonneg (i j : ↥S) : 0≤diff i j := by
    rw [formula]
    by_cases h : E i j=true
    · simp [h,pres i j h]
    · simp [h]; split <;> positivity
  have sumZero : (∑i : ↥S,∑j : ↥S,p i*diff i j*z (e j))=0 := by
    simp only [diff,mul_sub,sub_mul,sum_sub_distrib,←relabel e pm zm col row,sub_self]
  have term (i j : ↥S) : 0≤p i*diff i j*z (e j) :=
    mul_nonneg (mul_nonneg (pp i i.property).le (nonneg i j)) (zp _ (e j).property).le
  have rowZero := (sum_eq_zero_iff_of_nonneg (fun i _ => sum_nonneg (fun j _ => term i j))).mp sumZero
  intro i j
  have zero := (sum_eq_zero_iff_of_nonneg (fun k _ => term i k)).mp (rowZero i (mem_univ _)) j (mem_univ _)
  by_contra ne
  cases h : E i j <;> cases h' : E (e i) (e j)
  all_goals try simp [h,h'] at ne
  · have d : 0<diff i j := by rw [formula,h,h']; simp; omega
    exact (mul_pos (mul_pos (pp i i.property) d) (zp _ (e j).property)).ne' zero
  · have := pres i j h
    simp [h'] at this

/-- The strict parent pays a positive bill on its omissions. If two
children agree on an alignment fixing their overlap, a heavy omitted
column needs an actual parent from the other differing block. -/
private theorem crossing {q E} {V S T : Finset ℕ} {p x : ℕ→ℝ} {c : ℝ} (high : 1<c)
    (xp : ∀ i∈V,0≤x i) (pp : ∀ i∈S,0≤p i) (col : ∀ i∈S,realCol q E S p i=1)
    (bill : (∑i∈V\S,x i*((q:ℝ)*realInW E S p i-1))=c-1)
    (cover : V ⊆ S ∪ T) (e : ↥S ≃ ↥T)
    (fix : ∀i : ↥S,(i:ℕ)∈T → (e i:ℕ)=i)
    (same : ∀i j : ↥S,E i j=E (e i) (e j)) :
    ∃i∈S\T,∃y∈T\S,E i y=true := by
  classical
  obtain ⟨y,hy,hyH⟩ : ∃y∈V\S,1<(q:ℝ)*realInW E S p y := by
    by_contra! low
    have non := sum_nonpos (s:=V\S) (fun i hi => mul_nonpos_of_nonneg_of_nonpos
      (xp i (mem_sdiff.mp hi).1) (sub_nonpos.mpr (low i hi)))
    linarith
  have yt := (mem_union.mp (cover (mem_sdiff.mp hy).1)).resolve_left (mem_sdiff.mp hy).2
  let j := e.symm ⟨y,yt⟩
  have image : (e j:ℕ)=y := congrArg Subtype.val (e.apply_symm_apply ⟨y,yt⟩)
  by_contra! no
  have dom (i) (hi : i∈S) (edge : E i y=true) : E i j=true := by
    by_cases it : i∈T
    · have eqn := same ⟨i,hi⟩ j
      rw [fix ⟨i,hi⟩ it,image] at eqn
      exact eqn.trans edge
    · have bad := no i (mem_sdiff.mpr ⟨hi,it⟩) y (mem_sdiff.mpr ⟨yt,(mem_sdiff.mp hy).2⟩)
      simp [edge] at bad
  have le : realInW E S p y ≤ realInW E S p j := by
    apply sum_le_sum
    intro i hi
    by_cases iy : E i y=true
    · simp [iy,dom i hi iy]
    · by_cases ij : E i j=true <;> simp [iy,ij,pp i hi]
  have hj := col j j.property
  change p j+q*realInW E S p j=1 at hj
  linarith [mul_le_mul_of_nonneg_left le (Nat.cast_nonneg (α:=ℝ) q),pp j j.property]

/-- Either the matching changes an arc in each direction, or it is an
isomorphism and there are actual cross arcs in *both* directions. -/
def ExchangePattern (E : CH.Digraph) {S T : Finset ℕ} (e : ↥S ≃ ↥T) : Prop :=
  ((∃i j : ↥S,E i j=true ∧ E (e i) (e j)=false) ∧
   (∃i j : ↥S,E i j=false ∧ E (e i) (e j)=true)) ∨
  ((∀i j : ↥S,E i j=E (e i) (e j)) ∧
   (∃i∈S\T,∃j∈T\S,E i j=true) ∧ (∃j∈T\S,∃i∈S\T,E j i=true))

theorem compare_blocks {q E V} {S T : Finset ℕ} {p r z w x : ℕ→ℝ} {c : ℝ}
    (hq : 2≤q) (high : 1<c) (xp : ∀ i∈V,0≤x i) (cover : V⊆S∪T)
    (ps : realMass S p=1) (rt : realMass T r=1) (zs : realMass S z=1) (wt : realMass T w=1)
    (pc : ∀i∈S,0<p i ∧ realCol q E S p i=1) (rc : ∀i∈T,0<r i ∧ realCol q E T r i=1)
    (zr : ∀i∈S,0<z i ∧ realRow q E S z i=1) (wr : ∀i∈T,0<w i ∧ realRow q E T w i=1)
    (bs : (∑i∈V\S,x i*((q:ℝ)*realInW E S p i-1))=c-1)
    (bt : (∑i∈V\T,x i*((q:ℝ)*realInW E T r i-1))=c-1)
    (e : ↥S ≃ ↥T) (fix : ∀i : ↥S,(i:ℕ)∈T → (e i:ℕ)=i) : ExchangePattern E e := by
  classical
  by_cases same : ∀i j : ↥S,E i j=E (e i) (e j)
  · have inv (i j : ↥T) : E i j=E (e.symm i) (e.symm j) := by simpa using (same (e.symm i) (e.symm j)).symm
    have fix' (i : ↥T) (h : (i:ℕ)∈S) : (e.symm i:ℕ)=i := by
      have hj : e ⟨i,h⟩=i := Subtype.ext (fix ⟨i,h⟩ i.property)
      exact congrArg Subtype.val (e.symm_apply_eq.mpr hj.symm)
    exact Or.inr ⟨same,crossing high xp (fun i hi => (pc i hi).1.le) (fun i hi => (pc i hi).2) bs cover e fix same,
      crossing high xp (fun i hi => (rc i hi).1.le) (fun i hi => (rc i hi).2) bt
        (by rwa [union_comm]) e.symm fix' inv⟩
  · left
    constructor
    · by_contra! h
      exact same (rigid_relabel hq e ps wt (fun i hi => (pc i hi).1) (fun i hi => (wr i hi).1)
        (fun i hi => (pc i hi).2) (fun i hi => (wr i hi).2) (fun i j hit => by simpa using h i j hit))
    · by_contra! h
      have pres (i j : ↥T) (edge : E i j=true) : E (e.symm i) (e.symm j)=true := by
        cases he : E (e.symm i) (e.symm j)
        · have v := h (e.symm i) (e.symm j) he
          simp [edge] at v
        · rfl
      have inv := rigid_relabel hq e.symm rt zs (fun i hi => (rc i hi).1) (fun i hi => (zr i hi).1)
        (fun i hi => (rc i hi).2) (fun i hi => (zr i hi).2) pres
      exact same fun i j => by simpa using (inv (e i) (e j)).symm

/-- With one exchanged vertex on each side the second alternative would
be a directed digon in the parent. -/
theorem singleton_trade {E V S T q} (free : QFree E V q) (hq : 2≤q) (sv : S ⊆ V) (tv : T ⊆ V)
    {a b : ℕ} (one : S\T={a}) (two : T\S={b}) (e : ↥S ≃ ↥T) (choice : ExchangePattern E e) :
    (∃i j : ↥S,E i j=true ∧ E (e i) (e j)=false) ∧
    (∃i j : ↥S,E i j=false ∧ E (e i) (e j)=true) := by
  rcases choice with done | ⟨_,⟨i,hi,j,hj,ij⟩,⟨k,hk,l,hl,kl⟩⟩
  · exact done
  · have iv := sv (mem_sdiff.mp hi).1
    have jv := tv (mem_sdiff.mp hj).1
    rw [one,mem_singleton] at hi hl
    rw [two,mem_singleton] at hj hk
    subst i; subst j; subst k; subst l
    exact (free a 2 (by decide) hq (.step jv ij (.step iv kl (.refl _)))).elim


/-- One row law per recurrent child works for all ordered comparisons.
The parent excess and the inter-child transfers use those same laws. -/
theorem on_family {ι : Type*} {q E V} (hq : 2 ≤ q) (free : QFree E V q)
    (small : SmallerSmallRow q V.card) (U : ι → Finset ℕ) (p : ι → ℕ → ℝ)
    (sub : ∀ a,U a ⊆ V) (pm : ∀ a,realMass (U a) (p a)=1)
    (flat : ∀a i, i∈U a → 0<p a i ∧ realCol q E (U a) (p a) i=1)
    {x t : ℕ→ℝ} {c : ℝ} (high : 1<c) (xp : ∀i∈V,0≤x i) (xm : realMass V x=1) (tm : realMass V t=1)
    (rows : ∀i∈V, realRow q E V x i=c) (cols : ∀i∈V,realCol q E V t i=c) :
    ∃ z : ι → ℕ → ℝ,
      (∀a,realMass (U a) (z a)=1 ∧ ∀ i∈U a,0<z a i ∧ realRow q E (U a) (z a) i=1) ∧
      (∀a,(∑i∈V\U a,x i*((q:ℝ)*realInW E (U a) (p a) i-1))=c-1 ∧
        (∑i∈V\U a,t i*((q:ℝ)*realOutW E (U a) (z a) i-1))=c-1) ∧
      (∀a b,(∑j∈U b\U a,z b j*((q:ℝ)*realInW E (U a) (p a) j-1))=
        ∑i∈U a\U b,p a i*((q:ℝ)*realOutW E (U b) (z b) i-1)) ∧
      (∀a b (e : ↥(U a) ≃ ↥(U b)), (∀i j : ↥(U a), E i j=true → E (e i) (e j)=true) →
        ∀i j : ↥(U a),E i j=E (e i) (e j)) ∧
      ∀a b, V ⊆ U a ∪ U b → ∀e : ↥(U a) ≃ ↥(U b),
        (∀i : ↥(U a),(i:ℕ)∈U b → (e i:ℕ)=i) → ExchangePattern E e := by
  classical
  have col (a i) (hi : i∈U a) := (flat a i hi).2
  have first (a) := exchange (pm a) xm (col a) rows
  have bill (a) : (∑i∈V\U a,x i*((q:ℝ)*realInW E (U a) (p a) i-1))=c-1 := by
    simpa only [sdiff_eq_empty_iff_subset.mpr (sub a),sum_empty,sub_zero] using first a
  have proper (a) : U a≠V := by
    intro eq
    have impossible := bill a
    simp [eq] at impossible
    linarith
  choose z hm states using fun a => opposite_law hq free small (sub a) (proper a)
    (pm a) (fun i hi => (flat a i hi).1) (col a)
  have row (a i) (hi : i∈U a) := (states a i hi).2
  refine ⟨z,fun a => ⟨hm a,states a⟩,fun a => ⟨bill a,?_⟩,?_,?_,?_⟩
  · have h := exchange tm (hm a) cols (row a)
    rw [sdiff_eq_empty_iff_subset.mpr (sub a),sum_empty] at h
    linarith
  · intro a b
    exact sub_eq_zero.mp (by simpa only [sub_self] using exchange (pm a) (hm b) (col a) (row b))
  · intro a b e
    exact rigid_relabel hq e (pm a) (hm b) (fun i hi => (flat a i hi).1)
      (fun i hi => (states b i hi).1) (col a) (row b)

  · intro a b cover e fix
    exact compare_blocks hq high xp cover (pm a) (pm b) (hm a) (hm b) (flat a) (flat b)
      (states a) (states b) (bill a) (bill b) e fix

#print axioms singleton_trade
#print axioms compare_blocks
#print axioms opposite_law
#print axioms exchange
#print axioms rigid_relabel
#print axioms on_family

private theorem fixed_bijection {S T : Finset ℕ} (size : S.card=T.card) :
    ∃e : ↥S ≃ ↥T,∀i : ↥S,(i:ℕ)∈T → (e i:ℕ)=i := by
  classical
  let f := Finset.equivOfCardEq size
  let l (i : ↥(S∩T)) : ↥S := ⟨i, (mem_inter.mp i.property).1⟩
  let r (i : ↥(S∩T)) : ↥T := ⟨i, (mem_inter.mp i.property).2⟩
  have li : Function.Injective l := fun _ _ h => Subtype.ext (congrArg (fun y : ↥S => y.val) h)
  have ri : Function.Injective r := fun _ _ h => Subtype.ext (congrArg (fun y : ↥T => y.val) h)
  obtain ⟨g,hg⟩ := Equiv.Perm.exists_extending_pair (f ∘ l) r (f.injective.comp li) ri
  exact ⟨f.trans g,fun i hi => congrArg Subtype.val (hg ⟨i,mem_inter.mpr ⟨i.property,hi⟩⟩)⟩

/-- The two children of an actual recurring step cover the parent. There
is an overlap-fixing matching, and every such matching obeys the rule. -/
theorem adjacent {F} {V : Finset ℕ} {E : CH.Digraph}
    (go : PairedFamilyLoop.State F → PairedFamilyLoop.State F)
    (joint : ∀ a,previous (go a)=current a) (inside : ∀a : PairedFamilyLoop.State F, previous a⊆V)
    (size : ∀a b : Function.periodicPts go,(RawRepairAlternative.gone a.val).card=(RawRepairAlternative.gone b.val).card)
    (rule : ∀a b : Function.periodicPts go,
      let S := V\RawRepairAlternative.gone a.val
      let T := V\RawRepairAlternative.gone b.val
      V⊆S∪T → ∀e : ↥S ≃ ↥T,(∀i : ↥S,(i:ℕ)∈T → (e i:ℕ)=i) → ExchangePattern E e)
    (a : Function.periodicPts go) :
    let S := V\RawRepairAlternative.gone a.val
    let T := V\RawRepairAlternative.gone (go a.val)
    (∃e : ↥S ≃ ↥T,∀i : ↥S,(i:ℕ)∈T → (e i:ℕ)=i) ∧
      ∀e : ↥S ≃ ↥T,(∀i : ↥S,(i:ℕ)∈T → (e i:ℕ)=i) → ExchangePattern E e := by
  classical
  intro S T
  let b := CycleSlotOrbit.base go a
  have bval : b.val=go a.val := rfl
  have insideD (v : PairedFamilyLoop.State F) : RawRepairAlternative.gone v⊆V := sdiff_subset.trans (inside v)
  have eq := size a b
  rw [bval] at eq
  have counts : S.card=T.card := by
    dsimp only [S,T]
    rw [card_sdiff_of_subset (insideD a.val),card_sdiff_of_subset (insideD (go a.val)),eq]
  have covers : V⊆S∪T := by
    intro i iv
    by_cases h : i∈RawRepairAlternative.gone a.val
    · apply mem_union_right
      apply mem_sdiff.mpr
      refine ⟨iv,fun gone => (mem_sdiff.mp h).2 ?_⟩
      rw [←joint a.val]
      exact (mem_sdiff.mp gone).1
    · exact mem_union_left _ (mem_sdiff.mpr ⟨iv,h⟩)
  exact ⟨fixed_bijection counts,rule a b covers⟩

#print axioms adjacent

end LeanCH.BR.Closure.FlatChildExchange
