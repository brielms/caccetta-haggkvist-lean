import checkpoints.shen_extension.SharedArcPunctureExpansion

namespace LeanCH.BR.Closure.SharedArcIntervalPuncture
open Finset Matrix BRq2 BRq3 BR45 WeightedSD FiniteCutInverse ShortestCycleWeights
open scoped Matrix

private theorem indicator_row {q : ℕ} (D : CH.Digraph) (V : Finset ℕ) (U : Finset V) (i : V) :
    (excess (realMatrix q D V) *ᵥ (fun j => if j∈U then (1:ℝ) else 0)) i =
      (if i∈U then 1 else 0) + q*((U.filter (fun j : V => D i j=true)).card:ℝ) - U.card := by
  classical
  rw [mulVec_excess]
  simp only [mulVec,dotProduct,mul_ite,mul_one,mul_zero,←sum_filter,filter_mem_eq_inter,univ_inter,
    realMatrix_entry,sum_add_distrib]
  have diag : U.filter (fun j => i=j) = (if i∈U then {i} else ∅) := by
    ext j; by_cases h : i∈U <;> by_cases e : i=j <;> simp_all [eq_comm]
  by_cases h : i∈U <;> simp [diag,h,mul_comm]

private theorem indicator_col {q : ℕ} (D : CH.Digraph) (V : Finset ℕ) (U : Finset V) (i : V) :
    ((fun j => if j∈U then (1:ℝ) else 0) ᵥ* excess (realMatrix q D V)) i =
      (if i∈U then 1 else 0) + q*((U.filter (fun j : V => D j i=true)).card:ℝ) - U.card := by
  classical
  rw [vecMul_excess]
  simp only [vecMul,dotProduct,ite_mul,one_mul,zero_mul,←sum_filter,filter_mem_eq_inter,univ_inter,
    realMatrix_entry,sum_add_distrib]
  have diag : U.filter (fun j => i=j) = (if i∈U then {i} else ∅) := by
    ext j; by_cases h : i∈U <;> by_cases e : i=j <;> simp_all [eq_comm]
  have diag' : U.filter (fun j => j=i) = (if i∈U then {i} else ∅) := by simpa only [eq_comm] using diag
  by_cases h : i∈U <;> simp [diag',h,mul_comm]

theorem inverse_degree_floors {q k : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    {H : Matrix V V ℝ} (inv : CommonInverse (realMatrix q D V) H)
    (a : V) (U : Finset V) (size : q*k+1≤U.card)
    (rows : ∀i : V,i≠a → (U.filter (fun j : V => D i j=true)).card≤k)
    (cols : ∀i : V,i≠a → (U.filter (fun j : V => D j i=true)).card≤k) :
    k < (U.filter (fun j : V => D a j=true)).card ∧ k < (U.filter (fun j : V => D j a=true)).card := by
  classical
  let R := realMatrix q D V
  let w : V → ℝ := fun j => if j∈U then 1 else 0
  obtain ⟨u,hu⟩ := card_pos.mp (show 0<U.card by omega)
  have wu : w u=1 := by simp [w,hu]
  have cap (i : V) (c : ℕ) (le : c≤k) : (if i∈U then (1:ℝ) else 0)+q*(c:ℝ)-U.card≤0 := by
    have bound : q*c≤q*k := Nat.mul_le_mul_left _ le
    have realBound : (q:ℝ)*c≤(q:ℝ)*k := by exact_mod_cast bound
    have cardBound : (q:ℝ)*k+1≤U.card := by exact_mod_cast size
    split_ifs <;> linarith
  constructor
  · by_contra! low
    have all (i : V) : (excess R *ᵥ w) i≤0 := by
      rw [show (excess R *ᵥ w) i=_ from indicator_row D V U i]
      exact cap i _ (by by_cases h : i=a; exact h ▸ low; exact rows i h)
    have back : H *ᵥ (excess R *ᵥ w)=w := by
      rw [mulVec_mulVec,mul_eq_one_comm.mp inv.right,one_mulVec]
    have neg : (H *ᵥ (excess R *ᵥ w)) u≤0 := sum_nonpos fun i _ => mul_nonpos_of_nonneg_of_nonpos (inv.nonneg u i) (all i)
    rw [back,wu] at neg; norm_num at neg
  · by_contra! low
    have all (i : V) : (w ᵥ* excess R) i≤0 := by
      rw [show (w ᵥ* excess R) i=_ from indicator_col D V U i]
      exact cap i _ (by by_cases h : i=a; exact h ▸ low; exact cols i h)
    have back : (w ᵥ* excess R) ᵥ* H=w := by rw [vecMul_vecMul,inv.right,vecMul_one]
    have neg : ((w ᵥ* excess R) ᵥ* H) u≤0 := sum_nonpos fun i _ => mul_nonpos_of_nonpos_of_nonneg (all i) (inv.nonneg i u)
    rw [back,wu] at neg; norm_num at neg

/-- If the puncture has qk+1 labels and all its native in- and out-degrees
are at most k, then the deleted root needs at least k+1 actual heads and
k+1 actual parents there. Both directions use the same source inverse. -/
theorem degree_floors {q n k} (X : Model q n) (small : SmallerSmallRow q X.V.card)
    (a : X.V) (U : Finset X.V) (size : U.card=q*k+1)
    (rows : ∀i : X.V,i≠a → (U.filter (fun j : X.V => X.D i j=true)).card≤k)
    (cols : ∀i : X.V,i≠a → (U.filter (fun j : X.V => X.D j i=true)).card≤k) :
    k < (U.filter (fun j : X.V => X.D a j=true)).card ∧ k < (U.filter (fun j : X.V => X.D j a=true)).card := by
  obtain ⟨H,inv⟩ := strict_inverse_of_proper_smallRow (small.induced X.free)
    (fun i => (X.weights i:ℚ)) (fun _ _ => Nat.cast_nonneg _) X.strict
  exact inverse_degree_floors inv a U size.ge rows cols

#print axioms degree_floors

def band {α : Type*} [DecidableEq α] (f : α → α) (S : Finset α) (m : ℕ) : Finset α :=
  S.biUnion fun h => (range (m+1)).image fun i => f^[i] h

theorem in_band {α : Type*} [DecidableEq α] {f : α → α} {S : Finset α} {m : ℕ} {v : α} :
    v∈band f S m ↔ ∃h∈S,∃i≤m,f^[i] h=v := by
  simp [band]

private theorem stays {α : Type*} {f : α → α} {U : Finset α}
    (closed : ∀x∈U,f x∈U) {x} (inside : x∈U) (m : ℕ) : f^[m] x∈U := by
  induction m with
  | zero => exact inside
  | succ m ih => rw [Function.iterate_succ_apply']; exact closed _ ih

/-- Each successor step adds a label until a finite cyclic orbit is full.
This also holds at composite orbit sizes. -/
theorem band_growth {α : Type*} [DecidableEq α] {f : α → α} {U S : Finset α}
    (sub : S⊆U) (live : S.Nonempty) (cyclic : ∀x∈U,∀y∈U,∃m,f^[m] x=y)
    {t : α} (inside : t∈U) {L} (miss : t∉band f S L) : S.card+L ≤ (band f S L).card := by
  classical
  have mono {i j : ℕ} (le : i≤j) : band f S i ⊆ band f S j := by
    intro v hv; obtain ⟨h,hs,k,ki,endp⟩ := in_band.mp hv
    exact in_band.mpr ⟨h,hs,k,ki.trans le,endp⟩
  have seed {i : ℕ} : S⊆band f S i := fun x hx => in_band.mpr ⟨x,hx,0,Nat.zero_le _,rfl⟩
  suffices ∀i≤L,S.card+i ≤ (band f S i).card from this L le_rfl
  intro i
  induction i with
  | zero => intro _; simpa using card_le_card (seed (i:=0))
  | succ i ih =>
    intro le
    have away : t∉band f S i := fun h => miss (mono (by omega) h)
    obtain ⟨s,hs⟩ := live
    obtain ⟨m,endp⟩ := cyclic s (sub hs) t inside
    have escapes : ∃x∈band f S i,f x∉band f S i := by
      by_contra! stable
      exact away (endp ▸ stays stable (seed hs) m)
    obtain ⟨x,hx,out⟩ := escapes
    obtain ⟨h,hs,k,ki,hk⟩ := in_band.mp hx
    have hit : f x∈band f S (i+1) :=
      in_band.mpr ⟨h,hs,k+1,by omega,by rw [Function.iterate_succ_apply',hk]⟩
    have more := card_lt_card (ssubset_of_subset_of_ne (mono (Nat.le_succ i))
      (by intro eq; exact out (eq ▸ hit)))
    have prev := ih (by omega)
    exact Nat.succ_le_of_lt (prev.trans_lt more)

private theorem jumps {q n k} (X : Model q n) {U : Finset X.V} (f : X.V → X.V)
    (closed : ∀x∈U,f x∈U) (arcs : ∀x∈U,∀j,0<j → j≤k → X.D x (f^[j] x)=true)
    {h : X.V} (hu : h∈U) {r m : ℕ} (bound : m≤r*k) :
    ∃l≤r,Walk X.D X.V h (f^[m] h) l := by
  induction r generalizing m with
  | zero =>
    have : m=0 := by simpa using bound
    subst m
    exact ⟨0,le_rfl,.refl _⟩
  | succ r ih =>
    by_cases early : m≤r*k
    · obtain ⟨l,le,p⟩ := ih early; exact ⟨l,by omega,p⟩
    obtain ⟨l,le,p⟩ := ih (m:=r*k) le_rfl
    let d := m-r*k
    have pay : d≤k := by dsimp [d]; rw [Nat.succ_mul] at bound; omega
    have ed := arcs _ (stays closed hu (r*k)) d (by dsimp [d]; omega) pay
    have eq : (f^[d] (f^[r*k] h))=f^[m] h := by
      rw [←Function.iterate_add_apply,show d+r*k=m by dsimp [d]; omega]
    rw [eq] at ed
    exact ⟨l+1,by omega,p.snoc (f^[m] h).property ed⟩

/-- A normalized least source cannot have a qk+1 regular puncture whose
cyclic order supplies every jump of sizes 1 through k. All root arcs
are unrestricted. The set U can even omit more than the root if the
displayed degree caps still hold on all other rows and columns. -/
theorem interval_false {q n k} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    (a : X.V) (U : Finset X.V) (size : U.card=q*k+1)
    (rows : ∀i : X.V,i≠a → (U.filter (fun j : X.V => X.D i j=true)).card≤k)
    (cols : ∀i : X.V,i≠a → (U.filter (fun j : X.V => X.D j i=true)).card≤k)
    (f : X.V → X.V) (closed : ∀x∈U,f x∈U)
    (cyclic : ∀x∈U,∀y∈U,∃m,f^[m] x=y)
    (arcs : ∀x∈U,∀j,0<j → j≤k → X.D x (f^[j] x)=true) : False := by
  classical
  let C := U.filter (fun j : X.V => X.D a j=true)
  let I := U.filter (fun j : X.V => X.D j a=true)
  let L := (q-2)*k
  obtain ⟨heads,parents⟩ := degree_floors X small a U size rows cols
  change k<C.card at heads
  change k<I.card at parents
  have inside : band f C L⊆U := by
    intro v hv; obtain ⟨h,hc,m,_,rfl⟩ := in_band.mp hv
    exact stays closed (mem_filter.mp hc).1 m
  have dis : Disjoint I (band f C L) := by
    apply Finset.disjoint_left.mpr
    intro t ti hit
    obtain ⟨h,hc,m,le,rfl⟩ := in_band.mp hit
    obtain ⟨l,low,path⟩ := jumps X f closed arcs (mem_filter.mp hc).1 le
    exact SharedArcPunctureExpansion.far_parent X hq a h _ (mem_filter.mp hc).2 (mem_filter.mp ti).2
      (mem_ball.mpr ⟨(f^[m] h).property,l,low,path⟩)
  obtain ⟨t,ti⟩ := card_pos.mp (show 0<I.card by omega)
  have grow : C.card+L ≤ (band f C L).card := band_growth (f:=f) (S:=C) (filter_subset _ U) (card_pos.mp (show 0<C.card by omega)) cyclic
    (mem_filter.mp ti).1 (L:=L) (fun hit => Finset.disjoint_left.mp dis ti hit)
  have budget := card_le_card (union_subset (filter_subset _ U : I⊆U) inside)
  rw [card_union_of_disjoint dis,size] at budget
  have split : q*k=L+2*k := by
    dsimp [L]; rw [←Nat.add_mul,show q-2+2=q by omega]
  omega

#print axioms interval_false

/-- The graph has exactly the listed successors on the puncture; the
degree bounds in the previous theorem follow from this single arc table. -/
theorem cyclic_puncture_false {q n k} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    (a : X.V) (f : Equiv.Perm X.V) (size : (univ.erase a).card=q*k+1)
    (closed : ∀x∈univ.erase a,f x∈univ.erase a)
    (cyclic : ∀x∈univ.erase a,∀y∈univ.erase a,∃m,(f : X.V → X.V)^[m] x=y)
    (table : ∀x∈univ.erase a,∀y∈univ.erase a,X.D x y=true ↔
      ∃m<k,(f : X.V → X.V)^[m+1] x=y) : False := by
  classical
  let U := univ.erase a
  have mem {i : X.V} (ne : i≠a) : i∈U := mem_erase.mpr ⟨ne,mem_univ _⟩
  apply interval_false X hq small a U size _ _ f closed cyclic
  · intro x hx j pos le
    exact (table x hx _ (stays closed hx j)).mpr ⟨j-1,by omega,by rw [show j-1+1=j by omega]⟩
  · intro i ne
    let T := (range k).image (fun m => (f : X.V → X.V)^[m+1] i)
    have sub : U.filter (fun j : X.V => X.D i j=true)⊆T := by
      intro j hj
      obtain ⟨ju,ij⟩ := mem_filter.mp hj
      obtain ⟨m,mk,hit⟩ := (table i (mem ne) j ju).mp ij
      exact mem_image.mpr ⟨m,mem_range.mpr mk,hit⟩
    exact (card_le_card sub).trans (by simpa [T] using (card_image_le (f:=fun m => (f : X.V → X.V)^[m+1] i) (s:=range k)))
  · intro i ne
    let T := (range k).image (fun m => ((f^(m+1)).symm) i)
    have sub : U.filter (fun j : X.V => X.D j i=true)⊆T := by
      intro j hj
      obtain ⟨ju,ji⟩ := mem_filter.mp hj
      obtain ⟨m,mk,hit⟩ := (table j ju i (mem ne)).mp ji
      refine mem_image.mpr ⟨m,mem_range.mpr mk,?_⟩
      apply (f^(m+1)).injective
      rw [Equiv.apply_symm_apply]
      simpa only [Equiv.Perm.coe_pow] using hit.symm
    exact (card_le_card sub).trans (by simpa [T] using (card_image_le (f:=fun m => ((f^(m+1)).symm) i) (s:=range k)))

#print axioms cyclic_puncture_false

/-- Every regular unit-size puncture in a least source has a directed
vertex separator of size strictly less than its degree. Its two shores
have more than k vertices each. The separator occurs at an actual layer
of the forward search started simultaneously at all the root's heads. -/
theorem deficient_layer {q n k} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    (a : X.V) (U : Finset X.V) (size : U.card=q*k+1)
    (rows : ∀i : X.V,i≠a → (U.filter (fun j : X.V => X.D i j=true)).card≤k)
    (cols : ∀i : X.V,i≠a → (U.filter (fun j : X.V => X.D j i=true)).card≤k) :
    let C := U.filter (fun j : X.V => X.D a j=true)
    let I := U.filter (fun j : X.V => X.D j a=true)
    let R := fun r => U.filter (fun v : X.V => ∃h∈C,v.val∈ball X.D X.V h.val r)
    ∃r<q-2, C⊆R r ∧ Disjoint I (R (r+1)) ∧ ((R (r+1)) \ (R r)).card<k ∧
      (∀x∈R r,∀y∈U,X.D x y=true → y∈R (r+1)) ∧ k<(R r).card ∧ k<(U \ R (r+1)).card := by
  classical
  intro C I R
  obtain ⟨heads,parents⟩ := degree_floors X small a U size rows cols
  change k<C.card at heads
  change k<I.card at parents
  have start (r) : C⊆R r := by
    intro h hc
    exact mem_filter.mpr ⟨(mem_filter.mp hc).1,h,hc,mem_ball.mpr ⟨h.property,0,Nat.zero_le _,.refl _⟩⟩
  have mono {i j : ℕ} (le : i≤j) : R i⊆R j := by
    intro v hv
    obtain ⟨vu,h,hc,hit⟩ := mem_filter.mp hv
    obtain ⟨vv,l,lo,path⟩ := mem_ball.mp hit
    exact mem_filter.mpr ⟨vu,h,hc,mem_ball.mpr ⟨vv,l,lo.trans le,path⟩⟩
  have apart : Disjoint I (R (q-2)) := by
    apply Finset.disjoint_left.mpr
    intro t ti tr
    obtain ⟨_,h,hc,hit⟩ := mem_filter.mp tr
    exact SharedArcPunctureExpansion.far_parent X hq a h t (mem_filter.mp hc).2 (mem_filter.mp ti).2 hit
  have room := card_le_card (union_subset (filter_subset _ U : I⊆U) (filter_subset _ U : R (q-2)⊆U))
  rw [card_union_of_disjoint apart,size] at room
  obtain ⟨r,less,low⟩ : ∃r<q-2,(R (r+1)).card < (R r).card+k := by
    by_contra! grow
    have total (r) (bound : r≤q-2) : C.card+r*k ≤ (R r).card := by
      induction r with
      | zero => simpa using card_le_card (start 0)
      | succ r ih =>
        have old := ih (by omega)
        have new := grow r (by omega)
        rw [Nat.succ_mul]
        omega
    have budget := total (q-2) le_rfl
    have decomp : q*k=(q-2)*k+2*k := by rw [←Nat.add_mul,show q-2+2=q by omega]
    omega
  have dis : Disjoint I (R (r+1)) := apart.mono_right (mono (by omega))
  have count := card_sdiff_add_card_eq_card (mono (Nat.le_succ r))
  change (R (r+1) \ R r).card+(R r).card=(R (r+1)).card at count
  have outside : I⊆U \ R (r+1) := fun t ti =>
    mem_sdiff.mpr ⟨(mem_filter.mp ti).1,fun hit => Finset.disjoint_left.mp dis ti hit⟩
  refine ⟨r,less,start r,dis,by omega,?_,heads.trans_le (card_le_card (start r)),parents.trans_le (card_le_card outside)⟩
  intro x hx y yu ed
  obtain ⟨_,h,hc,hit⟩ := mem_filter.mp hx
  obtain ⟨_,l,le,path⟩ := mem_ball.mp hit
  exact mem_filter.mpr ⟨yu,h,hc,mem_ball.mpr ⟨y.property,l+1,by omega,path.snoc y.property ed⟩⟩

#print axioms deficient_layer
end LeanCH.BR.Closure.SharedArcIntervalPuncture
