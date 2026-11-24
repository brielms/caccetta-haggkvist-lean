import checkpoints.shen_extension.CornerBlockRegular

namespace LeanCH.BR.Closure.CornerBlockTower
open Finset BRq2 BRq3 BR45 WeightedSD

/-- A positive flat graph with one distinguished vertex of weight one.
    Its two contact sets have identical mass, by the two equations there. -/
structure Point (q : ℕ) (L : Finset ℕ) (m : ℚ) where
  graph : CH.Digraph
  free : QFree graph L q
  w : ℕ → ℚ
  positive : ∀i∈L,0<w i
  total : mass L w=m
  flat : ∀i∈L,WeightedSD.row q graph L w i=m ∧ WeightedSD.col q graph L w i=m
  root : ℕ
  member : root∈L
  unit : w root=1

private theorem layer {q : ℕ} (hq : 2≤q) {L T : Finset ℕ} (tl : T⊆L)
    (size : (L\T).card=q) {m : ℚ} (inner : Point q T m) :
    Nonempty (Point q L ((q+1)*m)) := by
  classical
  let r := inner.root
  have rt : r∈T := inner.member
  let Q := representativeSet L T r
  have sz : Q.card=q*1+1 := by
    simp [Q,representativeSet,card_insert_of_notMem (show r∉L\T from fun h=>(mem_sdiff.mp h).2 rt),size]
  obtain ⟨E,_,_,_,_,_,_,ef,deg,_⟩ := CornerBlockInterval.interval (d:=1) (k:=1) hq (by decide) (by decide) (by decide) Q sz
  let π := fun i : ℕ=>if i∈T then r else i
  let A : CH.Digraph := fun i j=>if i∈T ∧ j∈T then inner.graph i j else if π i=π j then false else E (π i) (π j)
  let b := fun i : ℕ=>if i∈T then inner.w i else m
  have qmem (i) (il : i∈L) : π i∈Q := by
    by_cases it : i∈T
    · simp [π,it,Q,representativeSet]
    · rw [show π i=i from ite_eq_right it]
      exact mem_insert_of_mem (mem_sdiff.mpr ⟨il,it⟩)
  have free : QFree A L q := by
    refine qfree_of_quotient_blocks π qmem ?_ ef ?_
    · intro x y _ ed
      by_cases eq : π x=π y
      · exact Or.inl eq
      · have no : ¬(x∈T ∧ y∈T) := fun h=>eq (by simp [π,h.1,h.2])
        exact Or.inr (by simpa [A,no,eq] using ed)
    · intro i a l pos bound path
      have transfer {x y k} (p : Walk A (L.filter (fun v=>π v=i)) x y k) (xi : π x=i) :
          Walk inner.graph T x y k := by
        induction p with
        | refl x => exact .refl _
        | @step x v y k vi ed _ ih =>
          have eq := (mem_filter.mp vi).2
          have both : x∈T ∧ v∈T := by
            by_contra no
            simp [A,no,xi.trans eq.symm] at ed
          exact .step both.2 (by simpa [A,both] using ed) (ih eq)
      cases l with
      | zero => omega
      | succ k => exact inner.free a _ pos bound (transfer path (mem_filter.mp path.unsnoc.choose_spec.2.1).2)
  let emptyGraph : CH.Digraph := fun _ _=>false
  let base := moduleSubstitution (D:=emptyGraph) tl rt (fun _ _ _ _ _ _ _=>rfl)
    (fun _ _ _ _ _ _ _=>rfl) (fun _ _=>rfl)
  have rep {i a : ℕ} (hi : i∈Q) (ai : a∈representativeFiber T r i) : π a=i := by
    by_cases eq : i=r
    · subst i; exact ite_eq_left (by simpa [representativeFiber] using ai)
    · have same : a=i := by simpa [representativeFiber,eq] using ai
      subst a; exact ite_eq_right (representative_outside hi eq).2
  let P : Substitution A E L Q := {
    fiber := representativeFiber T r
    cover := base.cover
    nonempty := base.nonempty
    disjoint := base.disjoint
    loopless := fun i hi=>Bool.eq_false_iff.mpr fun ed=>ef i 1 (by decide) (by omega) (.step hi ed (.refl _))
    cross := by
      intro i hi j hj ne a ai c cj
      have pa := rep hi ai
      have pc := rep hj cj
      have no : ¬(a∈T ∧ c∈T) := by
        rintro ⟨at',ct⟩; exact ne (pa.symm.trans ((by simp [π,at',ct] : π a=π c).trans pc))
      simp [A,no,pa,pc,ne] }
  have fibMass {i} (hi : i∈Q) : mass (P.fiber i) b=m := by
    change mass (representativeFiber T r i) b=m
    by_cases eq : i=r
    · subst i; simp only [representativeFiber,ite_true]
      exact (sum_congr rfl fun j jt=>ite_eq_left jt).trans inner.total
    · simp [representativeFiber,eq,mass,b,(representative_outside hi eq).2]
  have outside (C : CH.Digraph) (i : ℕ) (one : (outN C Q i).card=1) :
      outW C Q (fun j=>mass (P.fiber j) b) i=m := by
    rw [outW_eq_mass]
    calc
      _ = ∑_∈outN C Q i,m := sum_congr rfl (fun j jh=>fibMass (mem_filter.mp jh).1)
      _ = m := by simp [one]
  have flat {i a} (hi : i∈Q) (ai : a∈P.fiber i) :
      WeightedSD.row q A (P.fiber i) b a=m ∧ WeightedSD.col q A (P.fiber i) b a=m := by
    change a∈representativeFiber T r i at ai
    by_cases eq : i=r
    · subst i
      have at' : a∈T := by simpa [representativeFiber] using ai
      have part : P.fiber r=T := ite_eq_left rfl
      have rb : ∀j∈T,b j=inner.w j := fun j jt=>ite_eq_left jt
      rw [part]
      have eqO : outW A T b a=outW inner.graph T inner.w a := sum_congr rfl
        (fun j jt=>by simp [A,at',jt,rb j jt])
      have eqI : inW A T b a=inW inner.graph T inner.w a := sum_congr rfl
        (fun j jt=>by simp [A,at',jt,rb j jt])
      simpa only [WeightedSD.row,WeightedSD.col,rb a at',eqO,eqI] using
        (show WeightedSD.row q inner.graph T inner.w a=m ∧ WeightedSD.col q inner.graph T inner.w a=m from inner.flat a at')
    · have same : a=i := by simpa [representativeFiber,eq] using ai
      subst a
      have part : P.fiber i={i} := ite_eq_right eq
      simp [part,WeightedSD.row,WeightedSD.col,outW,inW,A,b,(representative_outside hi eq).2]
  have mpos : 0<m := inner.total ▸ sum_pos inner.positive ⟨r,rt⟩
  refine ⟨⟨A,free,b,?_,?_,?_,r,tl rt,?_⟩⟩
  · intro i _
    by_cases it : i∈T <;> simp [b,it,inner.positive i,mpos]
  · rw [P.mass_partition]
    calc
      _ = ∑_∈Q,m := sum_congr rfl (fun _ hi=>fibMass hi)
      _ = _ := by simp [sz]
  · intro a al
    obtain ⟨i,hi,ai⟩ := mem_biUnion.mp (P.cover ▸ al)
    have ic : inW E Q (fun j=>mass (P.fiber j) b) i=m := outside (fun x y=>E y x) i (deg i hi).2
    rw [P.row_partition q b hi ai,P.col_partition q b hi ai,(flat hi ai).1,(flat hi ai).2,
      outside E i (deg i hi).1,ic]
    constructor <;> ring
  · simpa [b,rt,r] using inner.unit

/-- The order grows linearly with depth. The total mass grows exponentially,
    and the distinguished point keeps unit weight at every depth. -/
theorem tower {q : ℕ} (hq : 2≤q) (j : ℕ) (L : Finset ℕ) (size : L.card=q*j+1) :
    Nonempty (Point q L ((q+1:ℚ)^j)) := by
  classical
  induction j generalizing L with
  | zero =>
    have one : L.card=1 := by simpa using size
    obtain ⟨r,rfl⟩ := card_eq_one.mp one
    let E : CH.Digraph := fun _ _=>false
    refine ⟨⟨E,?_,fun _=>1,by simp,by simp [mass],?_,r,by simp,rfl⟩⟩
    · intro a k pos _ path
      cases path with
      | refl => omega
      | step _ ed _ => cases ed
    · intro i _; simp [WeightedSD.row,WeightedSD.col,outW,inW,E]
  | succ j ih =>
    have room : q*j+1≤L.card := by rw [size,Nat.mul_succ]; omega
    obtain ⟨T,tl,ts⟩ := exists_subset_card_eq room
    obtain ⟨point⟩ := ih T ts
    have diff : (L\T).card=q := by rw [card_sdiff_of_subset tl,size,ts,Nat.mul_succ]; omega
    simpa only [pow_succ',Nat.cast_add,Nat.cast_one] using layer hq tl diff point

#print axioms tower
end LeanCH.BR.Closure.CornerBlockTower
