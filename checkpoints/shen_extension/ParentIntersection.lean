import checkpoints.shen_extension.TransversalExchange

namespace LeanCH.BR.ShenParentIntersection
open BRq2 BRq3 WeightedSD ShenPrimeTransition Finset

/-- Among all realizations of minimum total mass on the input, choose a smallest
support as well. The comparison includes arbitrary positive weights on the
competing support. -/
def Rigid {q D V b} (X : Witness q D V b) : Prop :=
  ∀ U ⊆ V, U.Nonempty → ∀ w : ℕ → ℕ, (∀ x∈U, 0<w x) → Strict q D U w →
    (∑ x∈U, w x) ≤ ∑ x∈X.carrier, X.weights x → X.carrier.card ≤ U.card

theorem choose_rigid {q n s D} (hn : 0<n) (order : n≤q*s) (loop : CH.Loopless D n)
    (degree : CH.MinOutdegreeAtLeast D n s) :
    ∃ X : Witness q D (range n) n, X.Minimal ∧ Rigid X := by
  classical
  obtain ⟨A,least⟩ := minimum_of_input hn order loop degree
  let P (k : ℕ) := ∃ U ⊆ range n, U.Nonempty ∧ ∃ w : ℕ → ℕ,
    (∀ x∈U, 0<w x) ∧ Strict q D U w ∧ (∑ x∈U, w x) ≤ ∑ x∈A.carrier, A.weights x ∧ U.card=k
  have ex : ∃ k, P k := ⟨_,A.carrier,A.subset,A.nonempty,A.weights,A.positive,A.strict,le_rfl,rfl⟩
  obtain ⟨U,sub,ne,w,pos,strict,total,sz⟩ := Nat.find_spec ex
  obtain ⟨B⟩ := prime_descent (fun x hx => loop x (mem_range.mp (sub hx))) ne pos strict
  let X : Witness q D (range n) n :=
    { B with subset := B.subset.trans sub, bounded := B.bounded.trans (total.trans A.bounded) }
  have mass : (∑ x∈X.carrier, X.weights x) ≤ ∑ x∈A.carrier, A.weights x := B.bounded.trans total
  refine ⟨X,fun k h => mass.trans (least k h),?_⟩
  intro T tv tn v vp vs vm
  exact (card_le_card B.subset).trans (sz ▸ Nat.find_min' ex
    (show P T.card from ⟨T,tv,tn,v,vp,vs,vm.trans mass,rfl⟩))

/-- A deposited packet may be distributed across any of the surviving labels. -/
theorem packet_deficit {q D V b} {X : Witness q D V b} (rigid : Rigid X)
    {t r : ℕ} (ht : t∈X.carrier) (hr : r∈X.carrier) (diff : r≠t)
    (d : ℕ → ℕ) (balance : (∑ y∈X.carrier.erase t, d y) = X.weights t) :
    ∃ x∈X.carrier.erase t, D x t=true ∧
      score q D X.carrier X.weights x + d x +
        q*(∑ y∈X.carrier.erase t, if D x y=true then d y else 0) ≤
        (∑ y∈X.carrier, X.weights y) + q*X.weights t := by
  classical
  let U := X.carrier.erase t
  let v := fun y => X.weights y + d y
  have mass : (∑ y∈U, v y) = ∑ y∈X.carrier, X.weights y := by
    simp only [v,U,sum_add_distrib,balance,sum_erase_add _ _ ht]
  have fail : ¬ Strict q D U v := by
    intro strict
    have wrong := rigid U ((erase_subset _ _).trans X.subset)
      ⟨r,mem_erase.mpr ⟨diff,hr⟩⟩ v (fun y hy => Nat.lt_of_lt_of_le
        (X.positive y (mem_of_mem_erase hy)) (Nat.le_add_right _ _)) strict mass.le
    exact (card_erase_lt_of_mem ht).not_ge wrong
  rw [nat_strict] at fail
  push Not at fail
  obtain ⟨x,hx,low⟩ := fail
  have high := nat_strict.mp X.strict x (mem_of_mem_erase hx)
  have split := sum_erase_add X.carrier (fun y => if D x y=true then X.weights y else 0) ht
  have heads : (∑ y∈U, if D x y=true then v y else 0) =
      (∑ y∈U, if D x y=true then X.weights y else 0) +
      ∑ y∈U, if D x y=true then d y else 0 := by
    rw [←sum_add_distrib]
    apply sum_congr rfl
    intro y _
    by_cases h : D x y=true <;> simp [h,v]
  rw [mass] at low
  simp only [score,heads,Nat.mul_add,v] at low
  unfold score at high
  change (∑ y∈U, _) + _ = _ at split
  rw [←split,Nat.mul_add] at high
  by_cases arc : D x t=true
  · refine ⟨x,hx,arc,?_⟩
    unfold score
    rw [←split,Nat.mul_add]
    simp only [arc,ite_true]
    change _ + d x + q*(∑ y∈U, _) ≤ _ + _
    omega
  · simp [arc] at high
    omega

/-- Each other label is missed by an actual parent which can lose at most the
source packet's q-fold mass. Depositing at that parent credits its own row. -/
theorem distinguishing_parent {q D V b} {X : Witness q D V b} (rigid : Rigid X)
    {t r : ℕ} (ht : t∈X.carrier) (hr : r∈X.carrier) (diff : r≠t) :
    ∃ x∈X.carrier.erase t, D x t=true ∧ D x r=false ∧
      score q D X.carrier X.weights x + (if x=r then X.weights t else 0) ≤
        (∑ y∈X.carrier, X.weights y) + q*X.weights t := by
  classical
  have rin : r∈X.carrier.erase t := mem_erase.mpr ⟨diff,hr⟩
  obtain ⟨x,hx,arc,paid⟩ := packet_deficit rigid ht hr diff
    (fun y => if y=r then X.weights t else 0) (by simp [rin])
  have eq : (∑ y∈X.carrier.erase t, if D x y=true then (if y=r then X.weights t else 0) else 0) =
      (if D x r=true then X.weights t else 0) := by
    rw [sum_eq_single r]
    · simp
    · intro y _ ne; simp [ne]
    · simp [rin]
  rw [eq] at paid
  cases edge : D x r with
  | false => exact ⟨x,hx,arc,edge,by simpa [edge] using paid⟩
  | true =>
    have high := nat_strict.mp X.strict x (mem_of_mem_erase hx)
    simp only [edge,ite_true] at paid
    omega

/-- Incidence in the ambient row set V distinguishes every ordered pair of
columns in U. Thus their incoming neighbourhoods are an inclusion antichain. -/
def Separated (D : CH.Digraph) (V U : Finset ℕ) : Prop :=
  ∀ t∈U, ∀ r∈U, r≠t → ∃ x∈V, D x t=true ∧ D x r=false

theorem separated {q D V b} {X : Witness q D V b} (rigid : Rigid X) :
    Separated D X.carrier X.carrier := by
  intro t ht r hr diff
  obtain ⟨x,hx,yes,no,_⟩ := distinguishing_parent rigid ht hr diff
  exact ⟨x,mem_of_mem_erase hx,yes,no⟩

/-- Read in reverse time. The parent reaches its own child and misses the
other child on this same step. The last inequality uses the original weights. -/
def ParentStep {q D V b} (X : Witness q D V b) (parent child other : ℕ) : Prop :=
  D parent child=true ∧ D parent other=false ∧
    score q D X.carrier X.weights parent + (if parent=other then X.weights child else 0) ≤
      (∑ y∈X.carrier, X.weights y) + q*X.weights child

theorem paired_itinerary {q D V b} {X : Witness q D V b} (rigid : Rigid X)
    {t r : ℕ} (ht : t∈X.carrier) (hr : r∈X.carrier) (diff : t≠r) :
    ∃ f g : ℕ → ℕ, f 0=t ∧ g 0=r ∧ ∀ i,
      f i∈X.carrier ∧ g i∈X.carrier ∧ f i≠g i ∧
      ParentStep X (f (i+1)) (f i) (g i) ∧ ParentStep X (g (i+1)) (g i) (f i) := by
  classical
  let P := {z : ℕ × ℕ // z.1∈X.carrier ∧ z.2∈X.carrier ∧ z.1≠z.2}
  have parents (z : P) : ∃ p : P, ParentStep X p.val.1 z.val.1 z.val.2 ∧
      ParentStep X p.val.2 z.val.2 z.val.1 := by
    obtain ⟨x,hx,yes,no,px⟩ := distinguishing_parent rigid z.property.1 z.property.2.1 z.property.2.2.symm
    obtain ⟨y,hy,yes',no',py⟩ := distinguishing_parent rigid z.property.2.1 z.property.1 z.property.2.2
    have xy : x≠y := by rintro rfl; simp [yes] at no'
    exact ⟨⟨(x,y),mem_of_mem_erase hx,mem_of_mem_erase hy,xy⟩,⟨yes,no,px⟩,⟨yes',no',py⟩⟩
  let seq : ℕ → P := Nat.rec ⟨(t,r),ht,hr,diff⟩ (fun _ z => (parents z).choose)
  exact ⟨fun i => (seq i).val.1,fun i => (seq i).val.2,rfl,rfl,fun i =>
    ⟨(seq i).property.1,(seq i).property.2.1,(seq i).property.2.2,(parents (seq i)).choose_spec⟩⟩

def PairClique (relation : ℕ → ℕ → Prop) (U : Finset ℕ) : Prop :=
  ∀ a∈U, ∀ b∈U, a≠b → relation a b

/-- At each round the two parents and the two children must all be compatible
with each other from the preceding round. A label can occur in both generations. -/
def Compatible (D : CH.Digraph) (V : Finset ℕ) : ℕ → ℕ → ℕ → Prop
  | 0, t, r => t∈V ∧ r∈V ∧ t≠r
  | k+1, t, r => Compatible D V k t r ∧ ∃ x∈V, ∃ y∈V,
      D x t=true ∧ D x r=false ∧ D y r=true ∧ D y t=false ∧
      PairClique (Compatible D V k) {t,r,x,y}

/-- No two distinct members can belong to the same surviving support at this round. -/
def Thin (D : CH.Digraph) (V : Finset ℕ) (k : ℕ) (A : Finset ℕ) : Prop :=
  ∀ x∈A, ∀ y∈A, x≠y → ¬Compatible D V k x y

theorem thin_of_nested {D V A} (nested : ∀ a∈A, ∀ b∈A,
    (∀ x∈V, D x a=true → D x b=true) ∨ (∀ x∈V, D x b=true → D x a=true)) :
    Thin D V 1 A := by
  intro a ha b hb _ yes
  obtain ⟨_,x,hx,y,hy,xa,xb,yb,ya,_⟩ := yes
  rcases nested a ha b hb with ab | ba
  · simp [ab x hx xa] at xb
  · simp [ba y hy yb] at ya

theorem propagate_thin {D V A B k} (thin : Thin D V k A)
    (parents : ∀ x∈V, ∀ t∈B, ∀ r∈B, D x t=true → D x r=false → x∈A) :
    Thin D V (k+1) B := by
  intro t ht r hr diff compat
  obtain ⟨_,x,hx,y,hy,xt,xr,yr,yt,clique⟩ := compat
  have xy : x≠y := by rintro rfl; simp [xt] at yt
  exact thin x (parents x hx t ht r hr xt xr) y (parents y hy r hr t ht yr yt) xy
    (clique x (by simp) y (by simp) xy)

theorem compatible_all_rounds {q D V b} {X : Witness q D V b} (rigid : Rigid X) (k : ℕ) :
    PairClique (Compatible D V k) X.carrier := by
  induction k with
  | zero => exact fun _ ht _ hr diff => ⟨X.subset ht,X.subset hr,diff⟩
  | succ k ih =>
    intro t ht r hr diff
    obtain ⟨x,hx,yes,no,_⟩ := distinguishing_parent rigid ht hr diff.symm
    obtain ⟨y,hy,yes',no',_⟩ := distinguishing_parent rigid hr ht diff
    have xc := mem_of_mem_erase hx
    have yc := mem_of_mem_erase hy
    have all : {t,r,x,y} ⊆ X.carrier := by simp [insert_subset_iff,ht,hr,xc,yc]
    exact ⟨ih t ht r hr diff,x,X.subset xc,y,X.subset yc,yes,no,yes',no',
      fun a ha b hb ab => ih a (all ha) b (all hb) ab⟩

theorem cycle_of_pair_round {q n s D} (hq : 2≤q) (hn : 0<n) (order : n≤q*s)
    (loop : CH.Loopless D n) (degree : CH.MinOutdegreeAtLeast D n s) (k : ℕ)
    (classified : ∀ U ⊆ range n, Prime D U → PairClique (Compatible D (range n) k) U →
      U.card≤q+2 ∨ (4≤q ∧ U.card≤q+3) ∨ ShenCircle.Consecutive D U) :
    CH.HasDirectedCycleAtMost D n q := by
  by_contra no
  obtain ⟨X,_,rigid⟩ := choose_rigid hn order loop degree
  have free := (qfree_of_noShort loop no).mono_set X.subset
  have bad (h : SmallRow q D X.carrier) : False :=
    h.no_strict X.nonempty _ (fun _ _ => Nat.cast_nonneg _) X.strict
  rcases classified _ X.subset X.prime (compatible_all_rounds rigid k) with a | ⟨four,b⟩ | c
  · exact bad (smallRow_of_card_le_add_two hq free a)
  · exact bad (smallRow_of_card_le_add_three four free b)
  · exact ShenCircle.no_consecutive hq free X.nonempty X.positive X.strict c

theorem Separated.enlarge {D V U S} (h : Separated D S U) (sub : S⊆V) :
    Separated D V U := by
  intro t ht r hr diff
  obtain ⟨x,hx,yes,no⟩ := h t ht r hr diff
  exact ⟨x,sub hx,yes,no⟩

theorem cycle_of_separated_classes {q n s D} (hq : 2≤q) (hn : 0<n) (order : n≤q*s)
    (loop : CH.Loopless D n) (degree : CH.MinOutdegreeAtLeast D n s)
    (classified : ∀ U ⊆ range n, Prime D U → Separated D U U →
      U.card≤q+2 ∨ (4≤q ∧ U.card≤q+3) ∨ ShenCircle.Consecutive D U) :
    CH.HasDirectedCycleAtMost D n q := by
  by_contra no
  obtain ⟨X,_,rigid⟩ := choose_rigid hn order loop degree
  have free := (qfree_of_noShort loop no).mono_set X.subset
  have bad (h : SmallRow q D X.carrier) : False :=
    h.no_strict X.nonempty _ (fun _ _ => Nat.cast_nonneg _) X.strict
  rcases classified _ X.subset X.prime (separated rigid) with a | ⟨four,b⟩ | c
  · exact bad (smallRow_of_card_le_add_two hq free a)
  · exact bad (smallRow_of_card_le_add_three four free b)
  · exact ShenCircle.no_consecutive hq free X.nonempty X.positive X.strict c

/-- This sufficient test uses only the original incoming columns. -/
theorem cycle_of_column_width {q n s D} (hq : 2≤q) (hn : 0<n) (order : n≤q*s)
    (loop : CH.Loopless D n) (degree : CH.MinOutdegreeAtLeast D n s)
    (width : ∀ U ⊆ range n, Separated D (range n) U →
      U.card≤q+2 ∨ (4≤q ∧ U.card≤q+3)) : CH.HasDirectedCycleAtMost D n q := by
  apply cycle_of_separated_classes hq hn order loop degree
  intro U sub _ sep
  exact (width U sub (sep.enlarge sub)).elim Or.inl (fun h => Or.inr (Or.inl h))

/-- An explicit coloring of the input columns suffices when the columns of
each color are nested under inclusion. -/
theorem cycle_of_column_chains {q n s m D} (hq : 2≤q) (hn : 0<n) (order : n≤q*s)
    (loop : CH.Loopless D n) (degree : CH.MinOutdegreeAtLeast D n s)
    (size : m≤q+2 ∨ (4≤q ∧ m≤q+3)) (color : ℕ → Fin m)
    (nested : ∀ a∈range n, ∀ b∈range n, color a=color b →
      (∀ x∈range n, D x a=true → D x b=true) ∨
      (∀ x∈range n, D x b=true → D x a=true)) : CH.HasDirectedCycleAtMost D n q := by
  apply cycle_of_column_width hq hn order loop degree
  intro U sub sep
  have inj : Set.InjOn color U := by
    intro a ha b hb eq
    by_contra dif
    rcases nested a (sub ha) b (sub hb) eq with ab | ba
    · obtain ⟨x,hx,yes,no⟩ := sep a ha b hb (Ne.symm dif)
      simp [ab x hx yes] at no
    · obtain ⟨x,hx,yes,no⟩ := sep b hb a ha dif
      simp [ba x hx yes] at no
  have le := card_le_card_of_injOn (t:=univ) color (fun x _ => mem_univ _) inj
  simp only [card_univ,Fintype.card_fin] at le
  omega

theorem rigid_survivor {q n s D} (hq : 2≤q) (hn : 0<n) (order : n≤q*s)
    (loop : CH.Loopless D n) (degree : CH.MinOutdegreeAtLeast D n s)
    (no : ¬CH.HasDirectedCycleAtMost D n q) :
    ∃ X : Witness q D (range n) n, X.Minimal ∧ Rigid X ∧ QFree D X.carrier q ∧
      q+2<X.carrier.card ∧ (4≤q → q+3<X.carrier.card) ∧ ¬ShenCircle.Consecutive D X.carrier ∧
      ∀ B : ShenCircle.Blocks q X.carrier X.weights, X.carrier.card ≤ (ShenCircle.holes B D).card := by
  obtain ⟨X,least,rigid⟩ := choose_rigid hn order loop degree
  have free := (qfree_of_noShort loop no).mono_set X.subset
  have bad (h : SmallRow q D X.carrier) : False :=
    h.no_strict X.nonempty _ (fun _ _ => Nat.cast_nonneg _) X.strict
  refine ⟨X,least,rigid,free,?_,?_,ShenCircle.no_consecutive hq free X.nonempty X.positive X.strict,
    ShenCircle.holes_lower hq free X.positive X.strict⟩
  · by_contra! sm
    exact bad (smallRow_of_card_le_add_two hq free sm)
  · intro four
    by_contra! sm
    exact bad (smallRow_of_card_le_add_three four free sm)

/-- Sets in the cover may overlap and may need different numbers of rounds. -/
def ThinCover (q : ℕ) (D : CH.Digraph) (V : Finset ℕ) : Prop :=
  ∃ m : ℕ, (m≤q+2 ∨ (4≤q ∧ m≤q+3)) ∧ ∃ A : Fin m → Finset ℕ,
    (∀ x∈V, ∃ i, x∈A i) ∧ ∀ i, ∃ k, Thin D V k (A i)

theorem cycle_of_thin_cover {q n s D} (hq : 2≤q) (hn : 0<n) (order : n≤q*s)
    (loop : CH.Loopless D n) (degree : CH.MinOutdegreeAtLeast D n s)
    (cover : ThinCover q D (range n)) : CH.HasDirectedCycleAtMost D n q := by
  classical
  by_contra no
  obtain ⟨X,_,rigid,_,large,larger,_⟩ := rigid_survivor hq hn order loop degree no
  obtain ⟨m,size,A,full,rounds⟩ := cover
  let pieces := fun i => X.carrier ∩ A i
  have sub : X.carrier ⊆ univ.biUnion pieces := by
    intro x hx
    obtain ⟨i,hi⟩ := full x (X.subset hx)
    exact mem_biUnion.mpr ⟨i,mem_univ _,mem_inter.mpr ⟨hx,hi⟩⟩
  have one (i : Fin m) (_ : i∈univ) : (pieces i).card≤1 := by
    obtain ⟨k,thin⟩ := rounds i
    apply card_le_one.mpr
    intro a ha b hb
    obtain ⟨ac,ai⟩ := mem_inter.mp ha
    obtain ⟨bc,bi⟩ := mem_inter.mp hb
    by_contra ab
    exact thin a ai b bi ab (compatible_all_rounds rigid k a ac b bc ab)
  have cap := (card_le_card sub).trans (card_biUnion_le.trans (sum_le_sum one))
  simp only [sum_const,card_univ,Fintype.card_fin,smul_eq_mul,mul_one] at cap
  omega

#print axioms cycle_of_thin_cover
#print axioms choose_rigid
#print axioms packet_deficit
#print axioms distinguishing_parent
#print axioms paired_itinerary
#print axioms propagate_thin
#print axioms compatible_all_rounds
#print axioms cycle_of_pair_round
#print axioms cycle_of_separated_classes
#print axioms cycle_of_column_width
#print axioms cycle_of_column_chains
#print axioms rigid_survivor
end LeanCH.BR.ShenParentIntersection
