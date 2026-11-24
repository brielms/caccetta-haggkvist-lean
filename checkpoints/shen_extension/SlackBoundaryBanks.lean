import checkpoints.shen_extension.SlackPairOrbit

namespace LeanCH.BR.Closure.SlackBoundaryBanks
open Finset BRq2 BRq3 BR45 WeightedSD

/-- The common vertices can receive from and send to the replacement bank
wherever they could receive from or send to a member of the old bank. -/
def Dominates (E : CH.Digraph) (J X Y : Finset ℕ) : Prop :=
  (∀ i∈J,∀ x∈X,E i x=true → ∀y∈Y,E i y=true) ∧
  (∀ i∈J,∀ x∈X,E x i=true → ∀y∈Y,E y i=true)

def terminals (E : CH.Digraph) (X : Finset ℕ) := X.filter (fun x => outN E X x=∅)

private theorem out_union {E : CH.Digraph} {J X : Finset ℕ} (dis : Disjoint J X)
    (w : ℕ→ℝ) (u : ℕ) : realOutW E (J∪X) w u=realOutW E J w u+realOutW E X w u :=
  sum_union dis

private theorem out_eq (E : CH.Digraph) (X : Finset ℕ) (w : ℕ→ℝ) (u : ℕ) :
    realOutW E X w u=∑i∈outN E X u,w i := by simp only [realOutW,outN,sum_filter]

/-- An exact private-bank test. If the shared arcs allow the replacement,
any positive deposit of the same mass must underpay a private row compared
with some row of the flat bank. -/
theorem underpaid {q E J X Y p z b} (dx : Disjoint J X) (dy : Disjoint J Y)
    (law : RealDual q E (J∪Y) 1 p) (bu : b∈J∪Y) (slack : realCol q E (J∪Y) p b<1)
    (unit : realMass (J∪X) z=1) (pos : ∀i∈J∪X,0<z i)
    (rows : ∀i∈J∪X,realRow q E (J∪X) z i=1) (dom : Dominates E J X Y)
    (x : ℕ) (hx : x∈X) (d : ℕ→ℝ) (dp : ∀i∈Y,0<d i) (dm : realMass Y d=realMass X z) :
    ∃y∈Y,realRow q E Y d y<realRow q E X z x := by
  classical
  let w := fun i => if i∈J then z i else d i
  have wj (i) (hi : i∈J) : w i=z i := ite_eq_left hi
  have wy (i) (hi : i∈Y) : w i=d i := ite_eq_right (fun hj => disjoint_left.mp dy hj hi)
  have posj (i) (hi : i∈J) := pos i (mem_union_left X hi)
  have posx (i) (hi : i∈X) := pos i (mem_union_right J hi)
  have wp (i) (hi : i∈J∪Y) : 0<w i := by
    rcases mem_union.mp hi with h|h
    · rw [wj i h]; exact posj i h
    · rw [wy i h]; exact dp i h
  have mass : realMass (J∪Y) w=1 := by
    rw [←unit,realMass,realMass,sum_union dy,sum_union dx,sum_congr rfl wj,sum_congr rfl wy]
    exact congrArg _ dm
  have woJ (i) : realOutW E J w i=realOutW E J z i := by
    rw [out_eq,out_eq]; exact sum_congr rfl fun j h => wj j (mem_outN.mp h).1
  have woY (i) : realOutW E Y w i=realOutW E Y d i := by
    rw [out_eq,out_eq]; exact sum_congr rfl fun j h => wy j (mem_outN.mp h).1
  obtain ⟨δ,hδ,test⟩ := SlackPairOrbit.margin law bu slack
  obtain ⟨u,hu,lt⟩ := test w (fun i hi => (wp i hi).le)
  rw [mass] at lt
  have lost : realRow q E (J∪Y) w u<1 := by linarith [mul_pos hδ (wp b bu)]
  rcases mem_union.mp hu with hj|hy
  · exfalso
    have paid : realOutW E X z u≤realOutW E Y d u := by
      by_cases hp : (outN E X u).Nonempty
      · obtain ⟨v,hv⟩ := hp
        have all : outN E Y u=Y := by
          ext j
          exact ⟨fun h => (mem_outN.mp h).1,fun h => mem_outN.mpr ⟨h,dom.1 u hj v (mem_outN.mp hv).1 (mem_outN.mp hv).2 j h⟩⟩
        rw [out_eq,out_eq,all]
        change _≤realMass Y d
        rw [dm]
        exact sum_le_sum_of_subset_of_nonneg (fun _ h => (mem_outN.mp h).1) (fun j h _ => (posx j h).le)
      · rw [out_eq,out_eq,not_nonempty_iff_eq_empty.mp hp,sum_empty]
        exact sum_nonneg fun j h => (dp j (mem_outN.mp h).1).le
    have old := rows u (mem_union_left X hj)
    rw [realRow,out_union dx] at old
    rw [realRow,wj u hj,out_union dy,woJ,woY] at lost
    linarith [mul_le_mul_of_nonneg_left paid (Nat.cast_nonneg q : (0:ℝ)≤q)]
  · refine ⟨u,hy,?_⟩
    have paid : realOutW E J z x≤realOutW E J z u := by
      rw [out_eq,out_eq]
      apply sum_le_sum_of_subset_of_nonneg
      · intro j h
        exact mem_outN.mpr ⟨(mem_outN.mp h).1,dom.2 j (mem_outN.mp h).1 x hx (mem_outN.mp h).2 u hy⟩
      · exact fun j h _ => (posj j (mem_outN.mp h).1).le
    have old := rows x (mem_union_right J hx)
    rw [realRow,out_union dx] at old
    rw [realRow,wy u hy,out_union dy,woJ,woY] at lost
    unfold realRow
    linarith [mul_le_mul_of_nonneg_left paid (Nat.cast_nonneg q : (0:ℝ)≤q)]

#print axioms underpaid
/-- On a smaller host, a strictly positive distribution weakly paying
every row pays every row exactly. -/
private theorem paid_exact {q E W w} (hq : 2≤q) (small : SmallRow q E W) (live : W.Nonempty)
    (wp : ∀i∈W,0<w i) (wm : realMass W w=1) (paid : ∀i∈W,1≤realRow q E W w i) :
    ∀i∈W,realRow q E W w i=1 := by
  classical
  obtain ⟨p,law⟩ := realDual_of_smallRow small live
  have tight (j) (hj : j∈W) : realCol q E W p j=1 := by
    apply le_antisymm (law.columns j hj)
    by_contra! lo
    obtain ⟨δ,hδ,test⟩ := SlackPairOrbit.margin law hj lo
    obtain ⟨i,hi,lt⟩ := test w (fun a ha => (wp a ha).le)
    rw [wm] at lt
    linarith [paid i hi,mul_pos hδ (wp j hj)]
  have pp := real_unit_columns_positive hq p law.nonneg tight
  have bal := real_cross_rows q E W w p
  rw [sum_congr rfl (fun i hi => show w i*realCol q E W p i=w i by rw [tight i hi,mul_one]),show (∑i∈W,w i)=1 from wm] at bal
  have eq : (∑i∈W,p i*1)=(∑i∈W,p i*realRow q E W w i) := by
    rw [bal]; simpa only [realMass,mul_one] using law.normalized
  have terms (i) (hi : i∈W) := mul_le_mul_of_nonneg_left (paid i hi) (law.nonneg i hi)
  exact fun i hi => (mul_left_cancel₀ (pp i hi).ne' ((sum_eq_sum_iff_of_le terms).mp eq i hi)).symm

/-- Folding all of T minus J onto y bounds the total weight of y's heads in J.
At equality every parent of y in J has to see every folded label. -/
theorem fold_comparison {q E F T z} {V : Finset ℕ} {c : ℝ} (high : 1≤c) (hq : 2≤q) (small : SmallerSmallRow q V.card)
    (unit : realMass T z=1) (pos : ∀i∈T,0<z i) (rows : ∀i∈T,realRow q E T z i=c)
    {J : Finset ℕ} (part : J⊂T) {y} (fresh : y∉J) (room : J.card+1<V.card)
    (safe : QFree F (insert y J) q) (inside : ∀i∈J,∀j∈J,F i j=E i j)
    (cut : ∀i∈J,∀x∈T\J,E i x=true → F i y=true) :
    (q:ℝ)*realOutW F J z y≤realMass J z ∧
    ((q:ℝ)*realOutW F J z y=realMass J z →
      (J.Nonempty → c=1) ∧ (J.card : ZMod q)=0 ∧ ∀i∈J,F i y=true → ∀x∈T\J,E i x=true) := by
  classical
  let X := T\J
  let W := insert y J
  let m := realMass X z
  let w := fun i => if i=y then m else z i
  have js : J⊆T := part.subset
  have split : J∪X=T := union_sdiff_of_subset js
  have dis : Disjoint J X := disjoint_sdiff
  have xp (i) (hi : i∈X) := pos i (mem_sdiff.mp hi).1
  have liveX : X.Nonempty := sdiff_nonempty.mpr (not_subset.mpr (exists_of_ssubset part))
  have mp : 0<m := sum_pos xp liveX
  have msum : realMass J z+m=1 := by
    simpa only [←split,realMass,sum_union dis,m] using unit
  have wj (i) (hi : i∈J) : w i=z i := ite_eq_right (fun (eq : i=y) => fresh (eq ▸ hi))
  have wy : w y=m := ite_eq_left rfl
  have wp (i) (hi : i∈W) : 0<w i := by
    rcases mem_insert.mp hi with rfl|h
    · exact wy ▸ mp
    · rw [wj i h]; exact pos i (js h)
  have wm : realMass W w=1 := by
    change (∑i∈insert y J,w i)=1
    rw [sum_insert fresh,wy,sum_congr rfl wj,add_comm]
    exact msum
  have wo (i) : realOutW F W w i=(if F i y=true then m else 0)+realOutW F J z i := by
    unfold realOutW
    rw [show W=insert y J from rfl,sum_insert fresh,wy]
    congr 1
    exact sum_congr rfl fun j hj => by rw [wj j hj]
  have yloop : F y y=false := by
    cases h : F y y
    · rfl
    · exact (safe y 1 (by omega) (by omega) (.step (mem_insert_self y J) h (.refl y))).elim
  have yr : realRow q F W w y=m+(q:ℝ)*realOutW F J z y := by simp [realRow,wy,wo,yloop]
  have compare (i) (hi : i∈J) :
      realOutW E X z i≤(if F i y=true then m else 0) := by
    by_cases ed : F i y=true
    · simp only [ed,ite_true,out_eq]
      exact sum_le_sum_of_subset_of_nonneg (fun _ h => (mem_outN.mp h).1) (fun j h _ => (xp j h).le)
    · have no : outN E X i=∅ := eq_empty_iff_forall_notMem.mpr
        (fun j hj => ed (cut i hi j (mem_outN.mp hj).1 (mem_outN.mp hj).2))
      simp [ed,out_eq,no]
  have prior (i) (hi : i∈J) :
      z i+(q:ℝ)*(realOutW E J z i+realOutW E X z i)=c := by
    have h := rows i (js hi)
    rwa [←split,realRow,out_union dis] at h
  have oldInside (i) (hi : i∈J) : realOutW F J z i=realOutW E J z i :=
    sum_congr rfl (fun j hj => by rw [inside i hi j hj])
  have jp (i) (hi : i∈J) : c≤realRow q F W w i := by
    rw [←prior i hi,realRow,wj i hi,wo,oldInside i hi,add_comm (if F i y=true then m else 0) (realOutW E J z i)]
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (add_le_add le_rfl (compare i hi)) (Nat.cast_nonneg q))
  have size : W.card<V.card := by
    rw [show W=insert y J from rfl,card_insert_of_notMem fresh]
    exact room
  have exactRows (yp : 1≤realRow q F W w y) := paid_exact hq
    (small F W size safe) (insert_nonempty y J) wp wm
    (fun i hi => (mem_insert.mp hi).elim (fun e => e ▸ yp) (fun hi => high.trans (jp i hi)))
  constructor
  · by_contra! high
    have heavy : 1<realRow q F W w y := by rw [yr]; linarith
    exact heavy.ne' (exactRows heavy.le y (mem_insert_self _ _))
  · intro eqn
    have same := exactRows (by rw [yr,eqn]; linarith)
    have flat := (CanonicalCycleLaw.unit_columns (E:=fun a b => F b a) hq same).1 wm
    change ((insert y J).card : ZMod q)=1 at flat
    rw [card_insert_of_notMem fresh,Nat.cast_add,Nat.cast_one] at flat
    have level (i) (hi : i∈J) : c=1 := le_antisymm ((jp i hi).trans_eq (same i (mem_insert_of_mem hi))) high
    refine ⟨fun ⟨i,hi⟩ => level i hi,by linear_combination flat,?_⟩
    intro i hi ed x hx
    have eq := same i (mem_insert_of_mem hi)
    simp only [realRow,wj i hi,wo,oldInside i hi,ed,ite_true] at eq
    have qq : (0:ℝ)<q := by exact_mod_cast (show 0<q by omega)
    have massEq : realOutW E X z i=m := by
      have e := (prior i hi).trans (level i hi)
      have prod : (q:ℝ)*realOutW E X z i=(q:ℝ)*m := by linarith [show (q:ℝ)*(realOutW E J z i+realOutW E X z i)=q*realOutW E J z i+q*realOutW E X z i by ring,show (q:ℝ)*(m+realOutW E J z i)=q*m+q*realOutW E J z i by ring]
      exact mul_left_cancel₀ qq.ne' prod
    by_contra missing
    have inX : x∈X := hx
    have rest : x∉outN E X i := fun h => missing (mem_outN.mp h).2
    have bound : realOutW E X z i ≤ ∑j∈X.erase x,z j := by
      rw [out_eq]
      exact sum_le_sum_of_subset_of_nonneg (fun j hj => mem_erase.mpr
        ⟨fun h => rest (h ▸ hj),(mem_outN.mp hj).1⟩) (fun j hj _ => (xp j (mem_erase.mp hj).2).le)
    have all := sum_erase_add (s:=X) z inX
    change _=m at all
    linarith [xp x hx]

theorem fold_bound {q E V T z} {c : ℝ} (high : 1≤c) (hq : 2≤q) (small : SmallerSmallRow q V.card)
    (free : QFree E V q) (sub : T⊆V)
    (unit : realMass T z=1) (pos : ∀i∈T,0<z i) (rows : ∀i∈T,realRow q E T z i=c)
    {J : Finset ℕ} (part : J⊂T) {y} (yv : y∈V) (fresh : y∉J) (room : J.card+1<V.card)
    (cut : ∀i∈J,∀x∈T\J,E i x=true → E i y=true) :
    (q:ℝ)*realOutW E J z y≤realMass J z ∧
    ((q:ℝ)*realOutW E J z y=realMass J z →
      (J.Nonempty → c=1) ∧ (J.card : ZMod q)=0 ∧ ∀i∈J,E i y=true → ∀x∈T\J,E i x=true) :=
  fold_comparison high hq small unit pos rows part fresh room
    (free.mono_set (insert_subset yv (part.subset.trans sub))) (fun _ _ _ _ => rfl) cut

#print axioms fold_bound
/-- Merging a nontrivial bank onto one label must break an actual boundary
arc if the bank has a terminal. The label is tested individually. -/
theorem terminal_contact {q E V T z} (hq : 2≤q) (small : SmallerSmallRow q V.card)
    (free : QFree E V q) (sub : T⊆V) (proper : T.card<V.card)
    (unit : realMass T z=1) (pos : ∀i∈T,0<z i) (rows : ∀i∈T,realRow q E T z i=1)
    {J : Finset ℕ} (part : J⊂T) {y} (yv : y∈V) (yt : y∉T) {x}
    (hx : x∈terminals E (T\J)) (other : ∃v∈T\J,v≠x) :
    (∃i∈J,∃v∈T\J,E i v=true ∧ E i y=false) ∨
      ∃i∈J,E x i=true ∧ E y i=false := by
  classical
  by_contra! no
  have js := part.subset
  have cut (i) (hi : i∈J) (v) (hv : v∈T\J) (ed : E i v=true) : E i y=true := by
    cases h : E i y
    · exact (no.1 i hi v hv ed h).elim
    · rfl
  have keep (i) (hi : i∈outN E J x) : i∈outN E J y := by
    obtain ⟨ij,ed⟩ := mem_outN.mp hi
    refine mem_outN.mpr ⟨ij,?_⟩
    cases h : E y i
    · exact (no.2 i ij ed h).elim
    · rfl
  have room : J.card+1<V.card := by have := card_lt_card part; omega
  have bd := (fold_bound (c:=1) le_rfl hq small free sub unit pos rows part yv (fun h => yt (js h)) room cut).1
  have cmp : realOutW E J z x≤realOutW E J z y := by
    rw [out_eq,out_eq]
    exact sum_le_sum_of_subset_of_nonneg keep (fun i hi _ => (pos i (js (mem_outN.mp hi).1)).le)
  have xt := mem_filter.mp hx
  have dis : Disjoint J (T\J) := disjoint_sdiff
  have split : J∪(T\J)=T := union_sdiff_of_subset js
  have r := rows x (mem_sdiff.mp xt.1).1
  have zero : realOutW E (T\J) z x=0 := by simp [out_eq,xt.2]
  rw [←split,realRow,out_union dis,zero,add_zero] at r
  obtain ⟨v,hv,ne⟩ := other
  have lower : z v≤∑j∈(T\J).erase x,z j := single_le_sum
    (fun j hj => (pos j (mem_sdiff.mp (mem_erase.mp hj).2).1).le) (mem_erase.mpr ⟨ne,hv⟩)
  have er := sum_erase_add (T\J) z xt.1
  have mass : realMass J z+(∑i∈T\J,z i)=1 := by
    change (∑i∈J,z i)+(∑i∈T\J,z i)=1
    rw [←sum_union dis,split]; exact unit
  linarith [pos v (mem_sdiff.mp hv).1,mul_le_mul_of_nonneg_left cmp (Nat.cast_nonneg q : (0:ℝ)≤q)]

/-- The bound applies at the actual flat successor, and for each choice of
shared set and exterior vertex at that successor. -/
theorem on_child {F q E V} (hq : 2≤q) (free : QFree E V q) (small : SmallerSmallRow q V.card)
    (cycles : ∀M∈F,ShenCycleSuccessor.Cycle E V q M)
    {raw : PairedFamilyLoop.State F → ℕ→ℝ}
    (laws : ∀s,RealDual q E (V\RawRepairAlternative.gone s) 1 (raw s))
    {d : PairedFamilyLoop.State F} (flat : FlatTransientReturn.Tight q E V raw d) :
    let T := V\RawRepairAlternative.gone d
    ∀J⊂T,∀y∈V,y∉T → ∀x∈terminals E (T\J),(∃v∈T\J,v≠x) →
      (∃i∈J,∃v∈T\J,E i v=true ∧ E i y=false) ∨ ∃i∈J,E x i=true ∧ E y i=false := by
  classical
  intro T
  have mem := mem_product.mp (mem_filter.mp d.property).1
  have ca := cycles _ mem.1
  have cb := cycles _ mem.2
  have ne : PairedFamilyLoop.previous d≠PairedFamilyLoop.current d := (mem_filter.mp d.property).2
  obtain ⟨v,vh⟩ := sdiff_nonempty.mpr (show ¬PairedFamilyLoop.previous d⊆PairedFamilyLoop.current d from fun sub =>
    ne (eq_of_subset_of_card_le sub (cb.size.trans ca.size.symm).le))
  have sub : T⊆V := sdiff_subset
  have proper : T⊂V := Finset.ssubset_iff_subset_ne.mpr ⟨sub,fun eq =>
    (mem_sdiff.mp (show v∈T from eq.symm ▸ ca.sub (mem_sdiff.mp vh).1)).2 vh⟩
  have live : T.Nonempty := by
    by_contra! zero
    have one := (laws d).normalized
    change realMass T (raw d)=1 at one
    simp [zero,realMass] at one
  obtain ⟨z,unit,pos,rows,_⟩ := FlatChildClosure.rigidity hq small (card_lt_card proper) (free.mono_set sub) live (laws d) flat
  exact fun _ part _ yv yt _ hx more => terminal_contact hq small free sub (card_lt_card proper) unit pos rows part yv yt hx more

#print axioms terminal_contact
#print axioms on_child
end LeanCH.BR.Closure.SlackBoundaryBanks
