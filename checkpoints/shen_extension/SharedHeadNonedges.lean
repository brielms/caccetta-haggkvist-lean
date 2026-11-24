import checkpoints.shen_extension.SharedHeadFeedback

namespace LeanCH.BR.ShenSharedHead
open BRq2 BRq3 BR45
open Classical

/-- The symmetric relation of distinct, mutually nonadjacent vertices. -/
def absent (D : CH.Digraph) : CH.Digraph := fun x y =>
  decide (x≠y ∧ D x y≠true ∧ D y x≠true)

/-- Ordered pairs of distinct vertices that are adjacent in neither direction. -/
def missingPairs (D : CH.Digraph) (U : Finset ℕ) := ∑ x∈U,(outN (absent D) U x).card

private theorem rectangular_sum (D : CH.Digraph) (A B : Finset ℕ) :
    (∑ x∈A,(outN D B x).card)=∑ y∈B,(inN D A y).card := by
  simp only [outN,inN,Finset.card_filter]
  exact Finset.sum_comm

private theorem absent_symm (D : CH.Digraph) (x y) : absent D x y=absent D y x := by
  apply Bool.eq_iff_iff.mpr
  simp only [absent,decide_eq_true_eq]
  exact ⟨fun h => ⟨h.1.symm,h.2.2,h.2.1⟩,fun h => ⟨h.1.symm,h.2.2,h.2.1⟩⟩

private theorem erase_missing (D : CH.Digraph) {U : Finset ℕ} {x} (hx : x∈U) :
    missingPairs D U=missingPairs D (U.erase x)+2*(outN (absent D) U x).card := by
  let W := U.erase x
  let F := absent D
  have union : {x}∪W=U := by simp [W,hx]
  have dis : Disjoint {x} W := by simp [W]
  have symm : inN F W x=outN F W x := by
    ext z; simp only [mem_inN,mem_outN,F,absent_symm D z x]
  have row (y) : (outN F U y).card=(outN F {x} y).card+(outN F W y).card := by
    rw [←union,card_outN_union dis]
  have diag : outN F {x} x=∅ := by simp [outN,F,absent]
  have noLoop := row x
  rw [diag,Finset.card_empty,zero_add] at noLoop
  have sum := Finset.sum_congr (s₁:=W) rfl (fun y _ => row y)
  rw [Finset.sum_add_distrib,rectangular_sum F W {x},Finset.sum_singleton,symm] at sum
  have split := Finset.sum_erase_add (s:=U) (fun y => (outN F U y).card) hx
  change (∑ y∈W,(outN F U y).card)+_= _ at split
  change (∑ y∈U,(outN F U y).card)=(∑ y∈W,(outN F W y).card)+2*(outN F U x).card
  omega

theorem missing_mono {D : CH.Digraph} {T U : Finset ℕ} (sub : T⊆U) :
    missingPairs D T≤missingPairs D U :=
  (Finset.sum_le_sum (fun x _ => Finset.card_le_card (outN_mono sub x))).trans
    (Finset.sum_le_sum_of_subset_of_nonneg sub (fun _ _ _ => Nat.zero_le _))

theorem orientation_exact {D : CH.Digraph} {U : Finset ℕ} (hf : QFree D U 3) :
    2*(∑ x∈U,(outN D U x).card)+U.card+missingPairs D U=U.card*U.card := by
  have row (x) (hx : x∈U) :
      (outN D U x).card+(inN D U x).card+1+(outN (absent D) U x).card=U.card := by
    let O := outN D U x
    let I := inN D U x
    have dis : Disjoint O I := Finset.disjoint_left.mpr (fun y ho hi =>
      digonfree hf (by decide) hx (mem_outN.mp ho).1 (mem_outN.mp ho).2 (mem_inN.mp hi).2)
    have no : x∉O∪I := by
      intro h; rcases Finset.mem_union.mp h with a|a
      · exact loopfree hf (by decide) hx (mem_outN.mp a).2
      · exact loopfree hf (by decide) hx (mem_inN.mp a).2
    have eq : outN (absent D) U x=U \ insert x (O∪I) := by
      ext y
      simp only [O,I,mem_outN,mem_inN,absent,decide_eq_true_eq,Finset.mem_sdiff,Finset.mem_insert,Finset.mem_union]
      constructor
      · rintro ⟨hy,diff,a,b⟩
        exact ⟨hy,by rintro (rfl|h|h); exact diff rfl; exact a h.2; exact b h.2⟩
      · rintro ⟨hy,h⟩
        exact ⟨hy,fun e => h (Or.inl e.symm),fun a => h (Or.inr (Or.inl ⟨hy,a⟩)),fun b => h (Or.inr (Or.inr ⟨hy,b⟩))⟩
    have sub : insert x (O∪I)⊆U := Finset.insert_subset hx
      (Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _))
    have c := Finset.card_sdiff_add_card_eq_card sub
    rw [←eq,Finset.card_insert_of_notMem no,Finset.card_union_of_disjoint dis] at c
    dsimp only [O,I] at c; omega
  have sum := Finset.sum_congr rfl row
  simp only [Finset.sum_add_distrib,Finset.sum_const_nat (fun _ _ => rfl),Nat.mul_one,
    ←rectangular_sum D U U] at sum
  dsimp only [missingPairs]; omega

/-- A triangle-free induced bank of minimum degree d forces quadratically
many absent pairs. Peeling a minimum row records disjoint pairs at each step. -/
theorem bank_missing_bound {D : CH.Digraph} {U : Finset ℕ} {d}
    (hf : QFree D U 3) (ne : U.Nonempty) (deg : ∀ x∈U,d≤(outN D U x).card) :
    d*d+3*d≤2*missingPairs D U := by
  induction d generalizing U with
  | zero => simp
  | succ d ih =>
    obtain ⟨x,hx,minimum⟩ := U.exists_min_image (fun x => (outN D U x).card) ne
    let O := outN D U x
    let H := outN (absent D) U x
    have pos : 0<O.card := by have := deg x hx; dsimp only [O]; omega
    have pay (y) (hy : y∈O) : O.card≤(outN D O y).card+H.card := by
      have inc : outN D U y⊆outN D O y ∪ H := by
        intro z hz
        obtain ⟨zU,yz⟩ := mem_outN.mp hz
        obtain ⟨yU,xy⟩ := mem_outN.mp hy
        by_cases zo : z∈O
        · exact Finset.mem_union_left _ (mem_outN.mpr ⟨zo,yz⟩)
        · apply Finset.mem_union_right
          apply mem_outN.mpr
          refine ⟨zU,decide_eq_true ?_⟩
          exact ⟨fun eq => digonfree hf (by decide) hx yU xy (eq.symm ▸ yz),
            fun xz => zo (mem_outN.mpr ⟨zU,xz⟩),fun zx =>
              hf x 3 (by decide) le_rfl (.step yU xy (.step zU yz (.step hx zx (.refl _))))⟩
      exact (minimum y (mem_outN.mp hy).1).trans ((Finset.card_le_card inc).trans (Finset.card_union_le _ _))
    have sums := Finset.sum_le_sum pay
    rw [Finset.sum_const_nat (fun _ _ => rfl),Finset.sum_add_distrib,Finset.sum_const_nat (fun _ _ => rfl)] at sums
    have ori := orientation_exact (hf.mono_set (Finset.filter_subset _ _ : O⊆U))
    change 2*(∑ y∈O,(outN D O y).card)+O.card+missingPairs D O=O.card*O.card at ori
    have hole : O.card+1≤2*H.card := by
      apply Nat.le_of_mul_le_mul_left _ pos
      nlinarith only [sums,ori,Nat.zero_le (missingPairs D O)]
    have sub : U.erase x⊆U := Finset.erase_subset _ _
    obtain ⟨y,hy⟩ := Finset.card_pos.mp pos
    have rest : (U.erase x).Nonempty := ⟨y,Finset.mem_erase.mpr
      ⟨fun e => loopfree hf (by decide) hx (e ▸ (mem_outN.mp hy).2),(mem_outN.mp hy).1⟩⟩
    have step (y) (hy : y∈U.erase x) : d≤(outN D (U.erase x) y).card := by
      have inc : outN D U y⊆insert x (outN D (U.erase x) y) := by
        intro z hz
        by_cases eq : z=x
        · exact Finset.mem_insert.mpr (Or.inl eq)
        · exact Finset.mem_insert_of_mem (mem_outN.mpr ⟨Finset.mem_erase.mpr ⟨eq,(mem_outN.mp hz).1⟩,(mem_outN.mp hz).2⟩)
      have := (deg y (sub hy)).trans ((Finset.card_le_card inc).trans (Finset.card_insert_le _ _))
      omega
    have tail := ih (hf.mono_set sub) rest step
    have eq := erase_missing D hx
    have initial : d+1≤O.card := deg x hx
    dsimp only [H] at hole
    nlinarith only [hole,eq,tail,initial]

#print axioms bank_missing_bound

/-- The number of shared heads still unpaid after all distinct new endpoints
of the arc have been counted. -/
noncomputable def residual (D : CH.Digraph) (V : Finset ℕ) (u v : ℕ) :=
  (commonOut D V u v).card-(endpoints D V u v).card

private theorem residual_missing {D : CH.Digraph} {V : Finset ℕ} {u v s}
    (hf : QFree D V 3) (hm : OutEq s D V) (hv : v∈V) :
    let d := residual D V u v
    d*d+3*d≤2*missingPairs D (commonOut D V u v) := by
  intro d
  let T := commonOut D V u v
  by_cases nt : T.Nonempty
  · apply bank_missing_bound (hf.mono_set (Finset.inter_subset_left.trans (Finset.filter_subset _ _))) nt
    intro w hw
    have := bank_payment hm hv hw
    change (commonOut D V u v).card-(endpoints D V u v).card≤(outN D (commonOut D V u v) w).card
    omega
  · have zero : d=0 := by change T.card-_=0; rw [Finset.not_nonempty_iff_eq_empty.mp nt]; simp
    simp [zero]

/-- The multiplicity of an absent ordered pair in all child banks is exactly
the number of parent rows that actually feed both of its labels. -/
theorem missing_reuse_on (D : CH.Digraph) (U P : Finset ℕ) :
    (∑ v∈P,missingPairs D (outN D U v))=
      ∑ i∈U,∑ j∈outN (absent D) U i,(commonIn D P i j).card := by
  have ci (i j) : commonIn D P i j=P.filter (fun v => D v i=true ∧ D v j=true) := by
    ext v; simp [commonIn,inN]; tauto
  let f := fun v i j => if D v i=true ∧ D v j=true ∧ absent D i j=true then 1 else 0
  have left (v) : missingPairs D (outN D U v)=∑ i∈U,∑ j∈U,f v i j := by
    simp only [missingPairs,outN,Finset.card_filter,Finset.sum_filter,Finset.ite_sum_zero]
    apply Finset.sum_congr rfl; intro i _
    by_cases h : D v i=true
    · simp [f,h,ite_and]
    · simp [f,h]
  have right (i j) : (if absent D i j=true then (commonIn D P i j).card else 0)=∑ v∈P,f v i j := by
    rw [ci,Finset.card_filter]
    by_cases h : absent D i j=true <;> simp [f,h]
  calc
    _ = ∑ v∈P,∑ i∈U,∑ j∈U,f v i j := Finset.sum_congr rfl (fun v _ => left v)
    _ = ∑ i∈U,∑ v∈P,∑ j∈U,f v i j := Finset.sum_comm
    _ = ∑ i∈U,∑ j∈U,∑ v∈P,f v i j := Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)
    _ = _ := by simp only [outN,Finset.sum_filter,←right]

noncomputable def activeParents (D : CH.Digraph) (V : Finset ℕ) (u : ℕ) :=
  (outN D V u).filter (fun v => 0<residual D V u v)

theorem residual_pair_budget {D : CH.Digraph} {V : Finset ℕ} {u s}
    (hf : QFree D V 3) (hm : OutEq s D V) :
    let U := outN D V u
    (∑ v∈U,let d := residual D V u v; d*d+3*d)≤
      2*∑ i∈U,∑ j∈outN (absent D) U i,(commonIn D (activeParents D V u) i j).card := by
  intro U
  let P := activeParents D V u
  have sub : P⊆U := Finset.filter_subset _ _
  let f := residual D V u
  let cost := fun v => f v*f v+3*f v
  have eqSum : (∑ v∈U,cost v)=∑ v∈P,cost v := by
    symm
    apply Finset.sum_subset sub
    intro v hv no
    have zero : f v=0 := by
      by_contra! h
      exact no (Finset.mem_filter.mpr ⟨hv,Nat.pos_of_ne_zero h⟩)
    simp [cost,zero]
  have eq (v) : commonOut D V u v=outN D U v := by ext z; simp [commonOut,U,outN]; tauto
  have budget := Finset.sum_le_sum (fun v (hv : v∈P) => residual_missing (u:=u) hf hm (mem_outN.mp (sub hv)).1)
  change (∑ v∈U,cost v)≤_
  rw [eqSum]
  simpa only [eq,←Finset.mul_sum,missing_reuse_on] using budget

#print axioms residual_pair_budget

/-- Count ordered quadruples u,v,i,j: the arc u→v has positive residual,
both parents point to i and j, and those distinct heads are mutually nonadjacent. -/
noncomputable def sharedMissing (D : CH.Digraph) (V : Finset ℕ) :=
  ∑ u∈V,let U := outN D V u
         ∑ i∈U,∑ j∈outN (absent D) U i,(commonIn D (activeParents D V u) i j).card

theorem endpoint_shortfall {D : CH.Digraph} {V : Finset ℕ} {s}
    (hf : QFree D V 3) (hm : OutEq s D V) :
    V.card*s*(3*s+1)≤V.card*s*V.card+edges D V (residual D V) := by
  let t := fun u v => (commonOut D V u v).card
  let c := fun u v => (endpoints D V u v).card
  have one (u v) : t u v≤c u v+residual D V u v := by change t u v≤c u v+(t u v-c u v); omega
  have all := Finset.sum_le_sum (fun u (_ : u∈V) => Finset.sum_le_sum (fun v (_ : v∈outN D V u) => one u v))
  change edges D V t≤edges D V (fun u v => c u v+residual D V u v) at all
  rw [edges_add] at all
  have cap : V.card*s*(3*s+1)+edges D V c≤V.card*s*V.card+edges D V t := endpoint_balance hf hm
  omega

/-- Positive arc shortfalls retain the gaps on arcs with the opposite sign,
all uncovered columns, and the original in-degree variance. -/
theorem residual_balance {D : CH.Digraph} {V : Finset ℕ} {s g}
    (hf : QFree D V 3) (hm : OutEq s D V) (gap : V.card+g=3*s+1) :
    edges D V (residual D V)=V.card*s*g+
      edges D V (fun u v => (endpoints D V u v).card-(commonOut D V u v).card)+
      edges D V (fun u v => (uncovered D V 1 u v).card)+(∑ x∈V,indegreeDeviation D V s x) := by
  let t := fun u v => (commonOut D V u v).card
  let c := fun u v => (endpoints D V u v).card
  have one (u v) : t u v+(c u v-t u v)=c u v+residual D V u v := by
    change t u v+(c u v-t u v)=c u v+(t u v-c u v); omega
  have all := Finset.sum_congr (s₁:=V) rfl (fun u _ => Finset.sum_congr (s₁:=outN D V u) rfl
    (fun v _ => one u v))
  change edges D V (fun u v => t u v+(c u v-t u v))=edges D V (fun u v => c u v+residual D V u v) at all
  rw [edges_add,edges_add] at all
  have eq := exact_balance hf hm
  rw [←gap,Nat.mul_add] at eq
  dsimp only [t,c] at all; omega

noncomputable def activeCount (D : CH.Digraph) (V : Finset ℕ) :=
  edges D V (fun u v => if 0<residual D V u v then 1 else 0)

/-- The tangent parameter is arbitrary. Only parents with a positive
shortfall are allowed to absorb its square. -/
theorem active_reuse_budget {D : CH.Digraph} {V : Finset ℕ} {s}
    (hf : QFree D V 3) (hm : OutEq s D V) (k : ℕ) :
    (2*k+3)*edges D V (residual D V)≤2*sharedMissing D V+k*k*activeCount D V := by
  let f := residual D V
  let active := fun u v => if 0<f u v then 1 else 0
  let cost := fun u v => f u v*f u v+3*f u v
  have one (u v) : (2*k+3)*f u v≤cost u v+k*k*active u v := by
    by_cases pos : 0<f u v
    · simp only [active,pos,ite_true,Nat.mul_one,cost]
      rcases le_total k (f u v) with le|le
      · obtain ⟨j,eq⟩ := Nat.exists_eq_add_of_le le
        rw [eq]; nlinarith only [Nat.zero_le (j*j)]
      · obtain ⟨j,eq⟩ := Nat.exists_eq_add_of_le le
        rw [eq]; nlinarith only [Nat.zero_le (j*j)]
    · simp [cost,active,show f u v=0 by omega]
  have total := Finset.sum_le_sum (fun u (_ : u∈V) => Finset.sum_le_sum (fun v (_ : v∈outN D V u) => one u v))
  simp only [Finset.sum_add_distrib,←Finset.mul_sum] at total
  have pay := Finset.sum_le_sum (fun u (_ : u∈V) => residual_pair_budget (u:=u) hf hm)
  simp only [←Finset.mul_sum] at pay
  change edges D V cost≤2*sharedMissing D V at pay
  exact total.trans (Nat.add_le_add_right pay _)

#print axioms residual_balance
#print axioms active_reuse_budget

/-- Any candidate at the triangle cutoff needs this many shared quadruples
in every exact-degree trimming. At top order g=1. -/
theorem shared_missing_lower {D : CH.Digraph} {V : Finset ℕ} {s g}
    (hf : QFree D V 3) (hm : OutEq s D V) (gap : V.card+g=3*s+1) :
    V.card*s*(g*g+3*g)≤2*sharedMissing D V := by
  let f := residual D V
  let N := V.card*s
  have minMass := endpoint_shortfall hf hm
  rw [←gap,Nat.mul_add] at minMass
  have pay : N*g≤edges D V f := by dsimp only [N,f]; omega
  have one (u v) : 2*g*f u v+3*f u v≤(f u v*f u v+3*f u v)+g*g := by
    rcases le_total g (f u v) with le|le
    · obtain ⟨j,eq⟩ := Nat.exists_eq_add_of_le le
      rw [eq]; nlinarith only [Nat.zero_le (j*j)]
    · obtain ⟨j,eq⟩ := Nat.exists_eq_add_of_le le
      rw [eq]; nlinarith only [Nat.zero_le (j*j)]
  have total := Finset.sum_le_sum (fun u (_ : u∈V) => Finset.sum_le_sum (fun v (_ : v∈outN D V u) => one u v))
  let cost := fun u v => f u v*f u v+3*f u v
  change edges D V (fun u v => 2*g*f u v+3*f u v)≤edges D V (fun u v => cost u v+g*g) at total
  rw [edges_add,edges_add,edges_const hm] at total
  have scale (k) : edges D V (fun u v => k*f u v)=k*edges D V f := by simp only [edges,Finset.mul_sum]
  rw [scale,scale] at total
  have budget := Finset.sum_le_sum (fun u (_ : u∈V) => residual_pair_budget (u:=u) hf hm)
  simp only [←Finset.mul_sum] at budget
  change edges D V cost≤2*sharedMissing D V at budget
  have weighted := Nat.mul_le_mul_left (2*g+3) pay
  change _≤edges D V cost+N*(g*g) at total
  change N*(g*g+3*g)≤_
  nlinarith only [weighted,total,budget]

#print axioms shared_missing_lower

private theorem parent_row {D : CH.Digraph} {V : Finset ℕ} {s a b h u}
    (hf : QFree D V 3) (hm : OutEq s D V) (hu : u∈V) (hs : 0<s)
    (localBound : ∀ v∈outN D V u,a*residual D V u v≤b*(commonOut D V u v).card) :
    (4*a*b+2*b*h)*(∑ v∈outN D V u,residual D V u v)+2*b*b*s≤(2*b*b+h*h)*s*s := by
  let U := outN D V u
  let f := residual D V u
  let L := ∑ v∈U,f v
  have card : U.card=s := hm u hu
  have ne : U.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨v,hv,high⟩ := U.exists_max_image f ne
  let T := commonOut D V u v
  have sub : T⊆U := Finset.inter_subset_left
  have freeU := hf.mono_set (Finset.filter_subset _ _ : U⊆V)
  have miss : f v*f v≤2*missingPairs D U := by
    have bound := residual_missing (u:=u) hf hm (mem_outN.mp hv).1
    change f v*f v+3*f v≤2*missingPairs D T at bound
    have mono := missing_mono (D:=D) sub
    omega
  have maxSum := Finset.sum_le_sum high
  rw [Finset.sum_const_nat (fun _ _ => rfl),card] at maxSum
  change L≤s*f v at maxSum
  have degree := Finset.sum_le_sum localBound
  rw [← Finset.mul_sum,← Finset.mul_sum] at degree
  have eq (w) : commonOut D V u w=outN D U w := by ext z; simp [commonOut,U,outN]; tauto
  simp only [eq] at degree
  change a*L≤b*∑ w∈U,(outN D U w).card at degree
  have ori := orientation_exact (U:=U) freeU
  rw [card] at ori
  have tangent : 2*(b*f v)*(h*s)≤(b*f v)*(b*f v)+(h*s)*(h*s) := by
    rcases le_total (b*f v) (h*s) with le|le
    · obtain ⟨j,eq⟩ := Nat.exists_eq_add_of_le le
      rw [eq]; nlinarith only [Nat.zero_le (j*j)]
    · obtain ⟨j,eq⟩ := Nat.exists_eq_add_of_le le
      rw [eq]; nlinarith only [Nat.zero_le (j*j)]
  have useMax := Nat.mul_le_mul_left (2*b*h) maxSum
  have useMissing := Nat.mul_le_mul_left (b*b) miss
  have useDegree := Nat.mul_le_mul_left (4*b) degree
  have useOrient := congrArg (fun z : ℕ => (2*b*b)*z) ori
  change (4*a*b+2*b*h)*L+2*b*b*s≤(2*b*b+h*h)*s*s
  nlinarith only [tangent,useMax,useMissing,useDegree,useOrient]

/-- The same coefficients are applied recursively inside every common bank.
The parent pays for the nonedges forced inside its most deficient bank. -/
theorem nonedge_order_bound {D : CH.Digraph} {V : Finset ℕ} {s a b h}
    (hb : 0<b) (coeff : a+h=3*b) (quadratic : 2*b*b≤4*a*h+h*h)
    (hf : QFree D V 3) (degree : ∀ x∈V,s≤(outN D V x).card) (ne : V.Nonempty) (hs : 0<s) :
    a*s+b<b*V.card := by
  generalize size : V.card=n at *
  induction n using Nat.strong_induction_on generalizing V D s with
  | h n ih =>
    obtain ⟨F,sub,reg⟩ := exists_outEq degree
    have free := qfree_sub sub hf
    let Z := 4*a*b+2*b*h
    let H := 2*b*b+h*h
    let N := V.card*s
    let f := residual F V
    have localBound (u) (hu : u∈V) (v) (hv : v∈outN F V u) :
        a*f u v≤b*(commonOut F V u v).card := by
      let T := commonOut F V u v
      by_cases gp : 0<f u v
      · have gt : 0<T.card := by
          change 0<T.card-(endpoints F V u v).card at gp; omega
        have tv : T⊆V := Finset.inter_subset_left.trans (Finset.filter_subset _ _)
        have no : u∉T := fun h => loopfree free (by decide) hu (mem_outN.mp (Finset.mem_inter.mp h).1).2
        have less := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨tv,fun e => no (e ▸ hu)⟩)
        have inDeg (w) (hw : w∈T) : f u v≤(outN F T w).card := by
          have := bank_payment reg (mem_outN.mp hv).1 hw
          change T.card≤_+(outN F T w).card at this
          change T.card-(endpoints F V u v).card≤_; omega
        have smaller := ih T.card (by omega) (free.mono_set tv) inDeg (Finset.card_pos.mp gt) gp rfl
        change a*f u v≤b*T.card; omega
      · rw [show f u v=0 by omega,Nat.mul_zero]; exact Nat.zero_le _
    have row (u) (hu : u∈V) := parent_row (h:=h) free reg hu hs (localBound u hu)
    have total := Finset.sum_le_sum row
    simp only [Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_const_nat (fun _ _ => rfl)] at total
    change Z*edges F V f+V.card*(2*b*b*s)≤V.card*(H*s*s) at total
    have owe : N*(3*s+1)≤N*V.card+edges F V f := endpoint_shortfall free reg
    have scaled := Nat.mul_le_mul_left Z owe
    have pos : 0<N := Nat.mul_pos (Finset.card_pos.mpr ne) hs
    have bound : Z*(3*s+1)+2*b*b≤Z*V.card+H*s := by
      apply Nat.le_of_mul_le_mul_left _ pos
      dsimp only [N] at scaled ⊢
      nlinarith only [total,scaled]
    have polynomial : b*H≤Z*h := by
      dsimp only [Z,H]
      nlinarith only [Nat.mul_le_mul_left b quadratic]
    by_contra! short
    rw [←size] at short
    have c1 := congrArg (fun t : ℕ => Z*t*s) coeff
    have c2 := Nat.mul_le_mul_right s polynomial
    have c3 := Nat.mul_le_mul_left Z short
    have c4 := Nat.mul_le_mul_left b bound
    have pos3 : 0<2*b*b*b := by positivity
    nlinarith only [c1,c2,c3,c4,pos3]

theorem cycle_of_nonedge_ratio {D : CH.Digraph} {n s a b h}
    (hb : 0<b) (coeff : a+h=3*b) (quadratic : 2*b*b≤4*a*h+h*h)
    (hn : 0<n) (hs : 0<s) (order : b*n≤a*s+b)
    (hl : CH.Loopless D n) (hm : CH.MinOutdegreeAtLeast D n s) : CH.HasDirectedCycleAtMost D n 3 := by
  by_contra no
  have cap := nonedge_order_bound hb coeff quadratic (qfree_of_noShort hl no)
    (fun x hx => Compose.FloorSix.out_card hm (Finset.mem_range.mp hx)) ⟨0,Finset.mem_range.mpr hn⟩ hs
  rw [Finset.card_range] at cap; omega

#print axioms nonedge_order_bound
#print axioms cycle_of_nonedge_ratio

end LeanCH.BR.ShenSharedHead
