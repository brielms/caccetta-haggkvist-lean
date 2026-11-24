import checkpoints.shen_extension.PairedReturnCuts

namespace LeanCH.BR.Closure.ForwardShortcutLayers
open Finset BRq2 BRq3 BR45 WeightedSD StrictReturnLayers ShortestCycleWeights

abbrev RowRule := ℕ → Finset ℕ → Prop

open Classical in
noncomputable def layer (D : CH.Digraph) (V T : Finset ℕ) (ok : RowRule) : ℕ → Finset ℕ
  | 0 => T
  | k+1 =>
    let S := layer D V T ok k
    S ∪ V.filter (fun i => ¬ok i (outN D V i \ S))

private theorem grow {D V T ok} (k) : layer D V T ok k ⊆ layer D V T ok (k+1) :=
  subset_union_left

private theorem start {D V T ok} (k) : T ⊆ layer D V T ok k := by
  induction k with
  | zero => exact Subset.rfl
  | succ k ih => exact ih.trans (grow k)

private theorem bounded' {D V T ok} (ts : T⊆V) (k) : layer D V T ok k⊆V := by
  classical
  induction k with
  | zero => exact ts
  | succ k ih => exact union_subset ih (filter_subset _ _)

/-- Any admissible thinning must realize the returns predicted by the recursion. -/
theorem forced_return {D E V T ok} (ts : T⊆V)
    (mono : ∀i∈V,∀A B : Finset ℕ,B⊆V → A⊆B → ok i A → ok i B)
    (sub : ∀i j,E i j=true → D i j=true) (paid : ∀i∈V,ok i (outN E V i))
    (k) {v} (hit : v∈layer D V T ok k) : Returns E V T k v := by
  classical
  induction k generalizing v with
  | zero => exact ⟨v,hit,0,by omega,.refl _⟩
  | succ k ih =>
    rcases mem_union.mp hit with old|newRow
    · obtain ⟨t,tt,l,le,p⟩ := ih old
      exact ⟨t,tt,l,by omega,p⟩
    obtain ⟨vv,no⟩ := mem_filter.mp newRow
    have arc : ∃j∈layer D V T ok k,E v j=true := by
      by_contra missing
      apply no
      apply mono v vv (outN E V v) _ (sdiff_subset.trans outN_subset) _ (paid v vv)
      intro j jm
      obtain ⟨jv,e⟩ := mem_outN.mp jm
      exact mem_sdiff.mpr ⟨mem_outN.mpr ⟨jv,sub _ _ e⟩,fun js => missing ⟨j,js,e⟩⟩
    obtain ⟨j,js,ed⟩ := arc
    obtain ⟨t,tt,l,le,p⟩ := ih js
    exact ⟨t,tt,l+1,by omega,.step (bounded' ts k js) ed p⟩

/-- One admissible thinning attains every forced return layer up to k. -/
theorem realize_layers {D V T ok} (base : ∀i∈V,ok i (outN D V i)) (k) :
    ∃E : CH.Digraph,(∀i j,E i j=true → D i j=true) ∧ (∀i∈V,ok i (outN E V i)) ∧
      (∀i∈T,∀j,E i j=D i j) ∧ (∀i j,j∉layer D V T ok k → E i j=D i j) ∧
      ∀l≤k,∀v∈V,Returns E V T l v → v∈layer D V T ok l := by
  classical
  induction k with
  | zero =>
    refine ⟨D,fun _ _ e => e,base,by simp,by simp,?_⟩
    rintro l le v _ ⟨t,tt,d,dl,p⟩
    obtain rfl : l=0 := by omega
    obtain rfl : d=0 := by omega
    cases p
    exact tt
  | succ k ih =>
    obtain ⟨E,sub,paid,target,outside,detect⟩ := ih
    let S := layer D V T ok k
    let N := layer D V T ok (k+1)
    let K : CH.Digraph := fun i j => if i∉N ∧ j∈S then false else E i j
    have incl {i j} (ed : K i j=true) : E i j=true := by
      unfold K at ed; split at ed <;> simp_all
    have keep {i} (inside : i∈N) (j) : K i j=E i j := by simp [K,inside]
    have fits (i) (iv : i∈V) : ok i (outN K V i) := by
      by_cases inside : i∈N
      · have same : outN K V i=outN E V i := by ext j; simp only [mem_outN,keep inside]
        exact same ▸ paid i iv
      · have same : outN K V i=outN D V i \ S := by
          ext j
          by_cases js : j∈S <;> simp [mem_outN,K,inside,js]
          rw [outside i j js]
          exact fun _ => rfl
        rw [same]
        by_contra fail
        exact inside (mem_union_right _ (mem_filter.mpr ⟨iv,fail⟩))
    refine ⟨K,fun i j e => sub i j (incl e),fits,?_,?_,?_⟩
    · intro i it j
      exact (keep (start (k+1) it) j).trans (target i it j)
    · intro i j jn
      have js : j∉S := fun m => jn (grow k m)
      simp [K,js,outside i j js]
    · rintro l le v vv ⟨t,tt,d,dl,p⟩
      by_cases before : l≤k
      · exact detect l before v vv ⟨t,tt,d,dl,walk_sub (fun _ _ e => incl e) p⟩
      obtain rfl : l=k+1 := by omega
      by_contra miss
      cases p with
      | refl => exact miss (start (k+1) tt)
      | @step _ j _ m jv ed tail =>
        have js : j∈S := detect k le_rfl j jv ⟨t,tt,m,by omega,walk_sub (fun _ _ e => incl e) tail⟩
        have vn : v∉N := miss
        simp [K,vn,js] at ed

def shortcut (D : CH.Digraph) (T H : Finset ℕ) : CH.Digraph := fun i j =>
  D i j || decide (i∈T ∧ j∈H)

private theorem split_walk {D E : CH.Digraph} {V i j k} (p : Walk E V i j k) :
    Walk D V i j k ∨ ∃x y l r,l+1+r=k ∧ E x y=true ∧ D x y=false ∧
      Walk E V i x l ∧ Walk E V y j r := by
  induction p with
  | refl => exact Or.inl (.refl _)
  | @step i v j k vv ed tail ih =>
    cases old : D i v
    · exact Or.inr ⟨i,v,0,k,by omega,ed,old,.refl _,tail⟩
    · rcases ih with back|⟨x,y,l,r,eq,e,no,first,last⟩
      · exact Or.inl (.step vv old back)
      · exact Or.inr ⟨x,y,l+1,r,by omega,e,no,.step vv ed first,last⟩

theorem realize_edit {q D V T H ok} (free : QFree D V q) (hs : H⊆V)
    (base : ∀i∈V,ok i (outN (shortcut D T H) V i))
    (dis : Disjoint H (layer (shortcut D T H) V T ok (q-1))) :
    ∃E : CH.Digraph,(∀i j,E i j=true → shortcut D T H i j=true) ∧
      (∀t∈T,∀j,E t j=shortcut D T H t j) ∧ (∀i∈V,ok i (outN E V i)) ∧ QFree E V q := by
  classical
  obtain ⟨E,sub,paid,keep,_,detect⟩ := realize_layers base (q-1)
  refine ⟨E,sub,keep,paid,?_⟩
  intro i k positive le p
  rcases split_walk (D:=D) p with old|⟨t,h,l,r,eq,ed,miss,first,last⟩
  · exact free i k positive le old
  · have rect : t∈T ∧ h∈H := by simpa [shortcut,miss] using sub t h ed
    exact disjoint_left.mp dis rect.2 (detect (q-1) le_rfl h (hs rect.2)
      ⟨t,rect.1,r+l,by omega,last.append first⟩)

/-- Exact test for a q-free edit keeping the whole shortcut rectangle and
    satisfying any monotone row rules, on one graph and at every order. -/
theorem edit_iff {q D V T H ok} (hq : 1≤q) (free : QFree D V q) (ts : T⊆V) (hs : H⊆V)
    (mono : ∀i∈V,∀A B : Finset ℕ,B⊆V → A⊆B → ok i A → ok i B)
    (base : ∀i∈V,ok i (outN (shortcut D T H) V i)) :
    (∃E : CH.Digraph,(∀i j,E i j=true → shortcut D T H i j=true) ∧
      (∀t∈T,∀h∈H,E t h=true) ∧ (∀i∈V,ok i (outN E V i)) ∧ QFree E V q) ↔
      Disjoint H (layer (shortcut D T H) V T ok (q-1)) := by
  classical
  constructor
  · rintro ⟨E,sub,rect,paid,safe⟩
    apply disjoint_left.mpr
    intro h hh hit
    obtain ⟨t,tt,k,le,p⟩ := forced_return ts mono sub paid (q-1) hit
    exact safe h (k+1) (by omega) (by omega) (p.snoc (hs hh) (rect t tt h hh))
  · intro dis
    obtain ⟨E,sub,keep,paid,safe⟩ := realize_edit free hs base dis
    exact ⟨E,sub,fun t tt h hh => by simp [keep t tt h,shortcut,tt,hh],paid,safe⟩

/-- The forced layers are independent of outgoing decisions at the targets. -/
theorem shortcut_layer (D V T H ok) (k) :
    layer (shortcut D T H) V T ok k=layer D V T ok k := by
  classical
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [layer,ih]
    ext i
    by_cases inside : i∈T
    · simp [start (D:=D) (V:=V) (ok:=ok) k inside]
    · have same : outN (shortcut D T H) V i=outN D V i := by
        ext j; simp [mem_outN,shortcut,inside]
      simp [same]

def offTargets (T : Finset ℕ) (ok : RowRule) : RowRule := fun i S => i∈T ∨ ok i S

/-- All vertices outside the computed layer can receive shortcuts from
    every target simultaneously. Each target also retains its native row. -/
theorem maximum_edit {q D V T ok} (free : QFree D V q)
    (base : ∀i∈V,i∉T → ok i (outN D V i)) :
    let H := V \ layer D V T (offTargets T ok) (q-1)
    ∃E : CH.Digraph,(∀i j,E i j=true → shortcut D T H i j=true) ∧
      (∀t∈T,∀j,E t j=shortcut D T H t j) ∧
      (∀i∈V,i∉T → ok i (outN E V i)) ∧ QFree E V q := by
  classical
  intro H
  have ready (i) (iv : i∈V) : offTargets T ok i (outN (shortcut D T H) V i) := by
    by_cases target : i∈T
    · exact Or.inl target
    · have same : outN (shortcut D T H) V i=outN D V i := by ext j; simp [mem_outN,shortcut,target]
      exact Or.inr (same ▸ base i iv target)
  have dis : Disjoint H (layer (shortcut D T H) V T (offTargets T ok) (q-1)) := by
    rw [shortcut_layer]; exact disjoint_left.mpr (fun _ hx => (mem_sdiff.mp hx).2)
  obtain ⟨E,sub,keep,paid,safe⟩ := realize_edit free (show H⊆V from sdiff_subset) ready dis
  exact ⟨E,sub,keep,fun i iv it => (paid i iv).resolve_left it,safe⟩

def weakRow (q : ℕ) (V : Finset ℕ) (w : ℕ→ℚ) : RowRule :=
  fun i S => mass V w ≤ w i+q*mass S w

noncomputable def outsideLayer (q : ℕ) (D : CH.Digraph) (U T : Finset ℕ) (w : ℕ→ℚ) :=
  U \ layer D U T (offTargets T (weakRow q U w)) (q-1)

/-- This bound works for any proper carrier and any nonempty target bank
    containing every row which initially fails its budget. -/
theorem set_price {q n} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    {U T : Finset ℕ} (us : U⊆X.V) (less : U.card<X.V.card)
    (ts : T⊆U) (live : T.Nonempty) (w : ℕ→ℚ) (positive : ∀i∈U,0<w i)
    (outside : ∀i∈U,i∉T → mass U w ≤ WeightedSD.row q X.D U w i) :
    ∃t∈T, w t+q*mass (outN X.D U t ∪ outsideLayer q X.D U T w) w ≤ mass U w := by
  classical
  let A := layer X.D U T (offTargets T (weakRow q U w)) (q-1)
  have old (i) (iv : i∈U) (it : i∉T) : weakRow q U w i (outN X.D U i) := by
    simpa only [weakRow,WeightedSD.row,outW_eq_mass] using outside i iv it
  obtain ⟨E,_,keep,paid,safe⟩ := maximum_edit (X.free.mono_set us) old
  have same (t) (tt : t∈T) : outN E U t=outN X.D U t ∪ (U \ A) := by
    ext j
    simp only [mem_outN,keep t tt j,shortcut,mem_union,Bool.or_eq_true,decide_eq_true_eq,mem_sdiff]
    tauto
  change ∃t∈T,w t+q*mass (outN X.D U t ∪ (U \ A)) w ≤ mass U w
  by_contra! all
  have weak (i) (iv : i∈U) : mass U w≤WeightedSD.row q E U w i := by
    rw [WeightedSD.row,outW_eq_mass]
    by_cases it : i∈T
    · rw [same i it]; exact (all i it).le
    · exact paid i iv it
  obtain ⟨t,tt⟩ := live
  have eq := positive_feasible_rows_tight_of_smallRow hq
    (small E U less safe) w positive weak t (ts tt)
  rw [WeightedSD.row,outW_eq_mass,same t tt] at eq
  exact (all t tt).ne' eq

def lowRows (q : ℕ) (D : CH.Digraph) (U : Finset ℕ) (w : ℕ→ℚ) : Finset ℕ :=
  U.filter (fun i => WeightedSD.row q D U w i≤mass U w)

private theorem union_mass (N H : Finset ℕ) (w : ℕ→ℚ) :
    mass (N∪H) w=mass N w+mass (H \ N) w := by
  have eq : (N∪H) \ N = H \ N := by ext j; simp only [mem_union,mem_sdiff]; tauto
  have add := sum_sdiff (f:=w) (show N⊆N∪H from subset_union_left)
  rw [eq] at add
  exact add.symm.trans (add_comm ..)

/-- A single row compares the missing safe shortcut mass with its actual
    outweight into the erased set, with the full native strict surplus. -/
theorem removed_budget {q n} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    {U : Finset ℕ} (us : U⊆X.V) (less : U.card<X.V.card) (live : U.Nonempty)
    (w : ℕ→ℚ) (positive : ∀i∈X.V,0<w i) :
    let T := lowRows q X.D U w
    let H := outsideLayer q X.D U T w
    ∃t∈T, q*mass (H \ outN X.D U t) w + mass (X.V \ U) w +
      (WeightedSD.row q X.D X.V w t-mass X.V w) ≤ q*outW X.D (X.V \ U) w t := by
  classical
  intro T H
  obtain ⟨i,iv,low⟩ := small X.D U less (X.free.mono_set us) w (fun j jv => (positive j (us jv)).le) live
  have anyRow : T.Nonempty := ⟨i,mem_filter.mpr ⟨iv,low⟩⟩
  have outside (i) (iv : i∈U) (it : i∉T) : mass U w ≤ WeightedSD.row q X.D U w i :=
    le_of_not_ge (fun low => it (mem_filter.mpr ⟨iv,low⟩))
  obtain ⟨t,tt,cap⟩ := set_price X hq small us less (filter_subset _ _) anyRow w
    (fun i iv => positive i (us iv)) outside
  change w t+q*mass (outN X.D U t ∪ H) w≤mass U w at cap
  rw [union_mass] at cap
  have total : mass (X.V \ U) w + mass U w = mass X.V w := sum_sdiff us
  rw [←outW_eq_mass] at cap
  refine ⟨t,tt,?_⟩
  rw [WeightedSD.row,outW_split us,mul_add,←total]
  linarith only [cap,show (q:ℚ)*(outW X.D U w t+mass (H \ outN X.D U t) w)=
    q*outW X.D U w t+q*mass (H \ outN X.D U t) w by ring]

/-- At a minimum-weight pivot the resulting parent covers the entire
    safe exterior. Both the target bank and exterior are computed from w. -/
theorem minimum_covers {q n} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    (a : X.V) (w : ℕ→ℚ) (positive : ∀i∈X.V,0<w i)
    (strict : ∀i∈X.V,mass X.V w < WeightedSD.row q X.D X.V w i)
    (minimum : ∀i∈X.V,w a≤w i) :
    let U := X.V.erase a.val
    let T := lowRows q X.D U w
    let H := outsideLayer q X.D U T w
    ∃t∈T,X.D t a=true ∧ H⊆outN X.D U t := by
  classical
  intro U T H
  obtain ⟨C,_,cyc,ac,_⟩ := ShortestReturnCertificate.on_model X hq a.property
  obtain ⟨y,hy⟩ := card_pos.mp (show 0<(outN X.D C a).card by rw [cyc.heads a ac]; decide)
  obtain ⟨yc,ay⟩ := mem_outN.mp hy
  have diff : y≠a.val := fun eq => loopfree X.free (by omega) a.property (eq ▸ ay)
  have live : U.Nonempty := ⟨y,mem_erase.mpr ⟨diff,cyc.sub yc⟩⟩
  obtain ⟨t,tt,cap⟩ := removed_budget X hq small (erase_subset a.val X.V)
    (card_erase_lt_of_mem a.property) live w positive
  have W : X.V \ U = {a.val} := by ext i; simp [U,mem_sdiff,mem_erase]; grind [a.property]
  change (q:ℚ)*mass (H \ outN X.D U t) w+mass (X.V \ U) w+
    (WeightedSD.row q X.D X.V w t-mass X.V w) ≤ q*outW X.D (X.V \ U) w t at cap
  rw [W] at cap
  have tv : t∈X.V := mem_of_mem_erase (mem_filter.mp tt).1
  have gain := sub_pos.mpr (strict t tv)
  have hu : H⊆U := sdiff_subset
  have pos (x) (xm : x∈H \ outN X.D U t) : 0≤w x :=
    (positive x (mem_of_mem_erase (hu (mem_sdiff.mp xm).1))).le
  have nn : 0≤(q:ℚ)*mass (H \ outN X.D U t) w :=
    mul_nonneg (Nat.cast_nonneg q) (sum_nonneg pos)
  have ta : X.D t a=true := by
    cases edge : X.D t a
    · simp [outW,edge,mass] at cap
      change 0≤(q:ℚ)*(∑i∈H \ outN X.D U t,w i) at nn
      unfold mass at gain
      linarith [positive a a.property]
    · rfl
  simp only [outW,sum_singleton,ta,ite_true,show mass {a.val} w=w a by simp [mass]] at cap
  refine ⟨t,tt,ta,?_⟩
  intro x xh
  by_contra miss
  have xm : x∈H \ outN X.D U t := mem_sdiff.mpr ⟨xh,miss⟩
  have lo : w a≤mass (H \ outN X.D U t) w :=
    (minimum x (mem_of_mem_erase (hu xh))).trans (single_le_sum pos xm)
  linarith [mul_le_mul_of_nonneg_left lo (Nat.cast_nonneg q),positive a a.property]

#print axioms edit_iff
#print axioms maximum_edit
#print axioms set_price
#print axioms removed_budget
#print axioms minimum_covers
end LeanCH.BR.Closure.ForwardShortcutLayers
