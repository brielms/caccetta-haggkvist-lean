import checkpoints.shen_extension.SharedHeadTriangle

namespace LeanCH.BR.ShenSharedHead
open BRq2 BRq3 BR45 ShenFirstStrip
open Classical

/-- Distinct second-step endpoints beyond v's outgoing row, retaining the
same intermediate common successor of u and v on both paths. -/
noncomputable def endpoints (D : CH.Digraph) (V : Finset ℕ) (u v : ℕ) :=
  V.filter (fun z => z∉outN D V v ∧ ∃ w∈commonOut D V u v,D w z=true)

noncomputable def uncovered (D : CH.Digraph) (V : Finset ℕ) (k u v : ℕ) :=
  V \ ((reverseBall D V u k ∪ reverseBall D V v k) ∪ (outN D V v ∪ endpoints D V u v))

/-- All predecessors within k steps of either parent avoid these endpoints
and the outgoing row of v. This statement applies at every cutoff. -/
theorem endpoint_exact {D : CH.Digraph} {V : Finset ℕ} {q k u v : ℕ}
    (hf : QFree D V q) (room : k+2≤q) (hv : v∈V) (uv : D u v=true) :
    (reverseBall D V u k ∪ reverseBall D V v k).card+
      (outN D V v).card+(endpoints D V u v).card+(uncovered D V k u v).card=V.card := by
  let P := reverseBall D V u k ∪ reverseBall D V v k
  let R := outN D V v ∪ endpoints D V u v
  have pV : P⊆V := Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have rV : R⊆V := Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have walks (z) (hz : z∈R) :
      Walk D V u z 2 ∧ (Walk D V v z 1 ∨ Walk D V v z 2) := by
    rcases Finset.mem_union.mp hz with direct|extra
    · obtain ⟨hz,arc⟩ := mem_outN.mp direct
      exact ⟨.step hv uv (.step hz arc (.refl z)),Or.inl (.step hz arc (.refl z))⟩
    · obtain ⟨hz,_,w,hw,arc⟩ := Finset.mem_filter.mp extra
      obtain ⟨uw,vw⟩ := Finset.mem_inter.mp hw
      obtain ⟨hw,uw⟩ := mem_outN.mp uw
      exact ⟨.step hw uw (.step hz arc (.refl z)),Or.inr (.step hw (mem_outN.mp vw).2 (.step hz arc (.refl z)))⟩
  have dis : Disjoint P R := by
    apply Finset.disjoint_left.mpr
    intro z hz hr
    obtain ⟨uz,vz⟩ := walks z hr
    rcases Finset.mem_union.mp hz with left|right
    · obtain ⟨_,j,hj,zu⟩ := mem_ball.mp (Finset.mem_filter.mp left).2
      exact hf u (2+j) (by omega) (by omega) (uz.append zu)
    · obtain ⟨_,j,hj,zv⟩ := mem_ball.mp (Finset.mem_filter.mp right).2
      rcases vz with direct|two
      · exact hf v (1+j) (by omega) (by omega) (direct.append zv)
      · exact hf v (2+j) (by omega) (by omega) (two.append zv)
  have disR : Disjoint (outN D V v) (endpoints D V u v) :=
    Finset.disjoint_left.mpr (fun _ ho he => (Finset.mem_filter.mp he).2.1 ho)
  have cap := Finset.card_sdiff_add_card_eq_card (Finset.union_subset pV rV)
  change (uncovered D V k u v).card+(P∪R).card=V.card at cap
  rw [Finset.card_union_of_disjoint dis] at cap
  dsimp only [P,R] at cap
  rw [Finset.card_union_of_disjoint disR] at cap
  omega

theorem endpoint_table {D : CH.Digraph} {V : Finset ℕ} {q k u v : ℕ}
    (hf : QFree D V q) (room : k+2≤q) (hv : v∈V) (uv : D u v=true) :
    (reverseBall D V u k ∪ reverseBall D V v k).card+
      (outN D V v).card+(endpoints D V u v).card≤V.card := by
  have := endpoint_exact hf room hv uv
  omega

private theorem unit_exact {D : CH.Digraph} {V : Finset ℕ} {s u v : ℕ}
    (hf : QFree D V 3) (hm : OutEq s D V) (hu : u∈V) (hv : v∈V) (uv : D u v=true) :
    (inN D V u).card+(inN D V v).card+s+1+(endpoints D V u v).card+(uncovered D V 1 u v).card =
      V.card+(commonIn D V u v).card := by
  have cap := endpoint_exact (k:=1) hf (by decide) hv uv
  let I := inN D V u ∪ inN D V v
  have eq : reverseBall D V u 1 ∪ reverseBall D V v 1=insert v I := by
    ext x
    have rb (w) (hwV : w∈V) : x∈reverseBall D V w 1 ↔ x∈V ∧ (w=x ∨ D x w=true) := by
      simp only [reverseBall,Finset.mem_filter]
      constructor
      · rintro ⟨hx,reach⟩
        rcases (mem_ball_one hx).mp reach with h|h
        · exact ⟨hx,Or.inl h⟩
        · exact ⟨hx,Or.inr (mem_outN.mp h).2⟩
      · rintro ⟨hx,hw|edge⟩
        · exact ⟨hx,(mem_ball_one hx).mpr (Or.inl hw)⟩
        · exact ⟨hx,ball_of_adj hwV edge⟩
    simp only [Finset.mem_union,rb u hu,rb v hv,Finset.mem_insert,I,mem_inN]
    constructor
    · rintro (⟨hx,hu'|arc⟩|⟨hx,hv'|arc⟩)
      · exact Or.inr (Or.inr ⟨hx,hu' ▸ uv⟩)
      · exact Or.inr (Or.inl ⟨hx,arc⟩)
      · exact Or.inl hv'.symm
      · exact Or.inr (Or.inr ⟨hx,arc⟩)
    · rintro (rfl|⟨hx,arc⟩|⟨hx,arc⟩)
      · exact Or.inr ⟨hv,Or.inl rfl⟩
      · exact Or.inl ⟨hx,Or.inr arc⟩
      · exact Or.inr ⟨hx,Or.inr arc⟩
  have fresh : v∉I := by
    intro h
    rcases Finset.mem_union.mp h with h|h
    · exact digonfree hf (by decide) hu hv uv (mem_inN.mp h).2
    · exact loopfree hf (by decide) hv (mem_inN.mp h).2
  rw [eq,Finset.card_insert_of_notMem fresh,hm v hv] at cap
  have size : I.card+(commonIn D V u v).card=(inN D V u).card+(inN D V v).card :=
    Finset.card_union_add_card_inter _ _
  omega

private theorem unit_row {D : CH.Digraph} {V : Finset ℕ} {s u v : ℕ}
    (hf : QFree D V 3) (hm : OutEq s D V) (hu : u∈V) (hv : v∈V) (uv : D u v=true) :
    (inN D V u).card+(inN D V v).card+s+1+(endpoints D V u v).card ≤
      V.card+(commonIn D V u v).card := by
  have := unit_exact hf hm hu hv uv
  omega

/-- A sufficient condition for the triangle conclusion, expressed on
ordered arcs. Every endpoint is counted once for its pair of parents. -/
theorem endpoint_balance {D : CH.Digraph} {V : Finset ℕ} {s : ℕ} (hf : QFree D V 3) (hm : OutEq s D V) :
    V.card*s*(3*s+1)+edges D V (fun u v => (endpoints D V u v).card)≤
    V.card*s*V.card+edges D V (fun u v => (commonOut D V u v).card) := by
  let din := fun u => (inN D V u).card
  let c := fun u v => (endpoints D V u v).card
  let t := fun u v => (commonOut D V u v).card
  let z := fun u v => (commonIn D V u v).card
  have row := Finset.sum_le_sum (fun u hu => Finset.sum_le_sum (fun v hv =>
    unit_row hf hm hu (mem_outN.mp hv).1 (mem_outN.mp hv).2))
  change edges D V (fun u v => din u+din v+s+1+c u v)≤edges D V (fun u v => V.card+z u v) at row
  obtain ⟨tails,heads⟩ := indegree_contractions hm
  change edges D V (fun u _ => din u)=V.card*s*s at tails
  change V.card*s*s≤edges D V (fun _ v => din v) at heads
  simp only [edges_add,edges_const hm,tails] at row
  have same : edges D V t=edges D V z := triple_balance D V
  change V.card*s*(3*s+1)+edges D V c≤V.card*s*V.card+edges D V t
  nlinarith only [row,heads,same]

/-- At n≤3s an actual arc has more shared heads than distinct new endpoints.
Its common heads support an induced graph at the stated minimum degree. -/
theorem deficient_arc {D : CH.Digraph} {V : Finset ℕ} {s : ℕ} (hf : QFree D V 3)
    (hm : OutEq s D V) (ne : V.Nonempty) (hs : 0<s) (ord : V.card≤3*s) :
    ∃ u∈V,∃ v∈outN D V u, let T := commonOut D V u v
      T.Nonempty ∧ T.card<s ∧ (endpoints D V u v).card+(3*s+1-V.card)≤T.card ∧
      ∀ w∈T,3*s+1-V.card≤(outN D T w).card := by
  let g := 3*s+1-V.card
  have gap : g+V.card=3*s+1 := by dsimp [g]; omega
  have pos : 0<V.card*s := Nat.mul_pos (Finset.card_pos.mpr ne) hs
  obtain ⟨u,hu,v,hv,small⟩ : ∃ u∈V,∃ v∈outN D V u,(endpoints D V u v).card+g≤(commonOut D V u v).card := by
    by_contra! bad
    have row := Finset.sum_le_sum (fun u hu => Finset.sum_le_sum (fun v hv =>
      (show (commonOut D V u v).card+1≤(endpoints D V u v).card+g from bad u hu v hv)))
    change edges D V (fun u v => (commonOut D V u v).card+1)≤
      edges D V (fun u v => (endpoints D V u v).card+g) at row
    simp only [edges_add,edges_const hm] at row
    have cap := endpoint_balance hf hm
    have cancel := congrArg (fun j => V.card*s*j) gap
    nlinarith only [row,cap,cancel,pos]
  let T := commonOut D V u v
  have ts : T⊆outN D V v := Finset.inter_subset_right
  have tv : T⊆V := ts.trans (Finset.filter_subset _ _)
  have vV := (mem_outN.mp hv).1
  have no : v∉T := fun h => loopfree hf (by decide) vV (mem_outN.mp (ts h)).2
  have strict := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
    ⟨(Finset.inter_subset_left : T⊆outN D V u), fun he => no (by change v∈outN D V u ∩ outN D V v; rwa [he])⟩)
  rw [hm u hu] at strict
  change (endpoints D V u v).card+g≤T.card at small
  have gp : 0<g := by dsimp [g]; omega
  have nonempty : T.Nonempty := Finset.card_pos.mp (by omega)
  refine ⟨u,hu,v,hv,nonempty,strict,small,?_⟩
  intro w hw
  have incl : outN D V w⊆outN D T w ∪ ((outN D V v \ T) ∪ endpoints D V u v) := by
    intro y hy
    obtain ⟨hyV,wy⟩ := mem_outN.mp hy
    by_cases ht : y∈T
    · exact Finset.mem_union_left _ (mem_outN.mpr ⟨ht,wy⟩)
    by_cases h : y∈outN D V v
    · exact Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨h,ht⟩))
    · exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hyV,h,w,hw,wy⟩))
  have bound := (Finset.card_le_card incl).trans (Finset.card_union_le _ _)
  have := Finset.card_union_le (outN D V v \ T) (endpoints D V u v)
  have width := Finset.card_sdiff_add_card_eq_card ts
  rw [hm v vV] at width
  rw [hm w (tv hw)] at bound
  change g≤(outN D T w).card
  omega

#print axioms endpoint_table
#print axioms endpoint_balance
#print axioms deficient_arc

/-- In the original graph, every counterexample of order at most 3s has
a proper common-head bank carrying a positive minimum internal degree. -/
theorem cyclic_bank {D : CH.Digraph} {V : Finset ℕ} {s : ℕ} (hf : QFree D V 3)
    (hm : ∀ x∈V,s≤(outN D V x).card) (ne : V.Nonempty) (hs : 0<s) (ord : V.card≤3*s) :
    ∃ u∈V,∃ v∈outN D V u,∃ T⊆commonOut D V u v,
      T.Nonempty ∧ T.card<s ∧ (∀ w∈T,3*s+1-V.card≤(outN D T w).card) ∧ ¬QFree D T T.card := by
  obtain ⟨F,sub,reg⟩ := exists_outEq hm
  obtain ⟨u,hu,v,hv,neT,lt,_,inside⟩ := deficient_arc (qfree_sub sub hf) reg ne hs ord
  let T := commonOut F V u v
  have lift {W : Finset ℕ} {x : ℕ} : outN F W x⊆outN D W x := by
    intro y hy
    obtain ⟨hy,arc⟩ := mem_outN.mp hy
    exact mem_outN.mpr ⟨hy,sub x y arc⟩
  have bank : T⊆commonOut D V u v := Finset.inter_subset_inter lift lift
  have deg (w) (hw : w∈T) : 3*s+1-V.card≤(outN D T w).card :=
    (inside w hw).trans (Finset.card_le_card lift)
  refine ⟨u,hu,v,lift hv,T,bank,neT,lt,deg,?_⟩
  intro free
  obtain ⟨w,hw,sink⟩ := exists_sink free neT le_rfl
  obtain ⟨y,hy⟩ := Finset.card_pos.mp (show 0<(outN D T w).card by have := deg w hw; omega)
  exact sink y (mem_outN.mp hy).1 (mem_outN.mp hy).2

#print axioms cyclic_bank

/-- Squared deviation of incoming degree from the common outgoing degree. -/
def indegreeDeviation (D : CH.Digraph) (V : Finset ℕ) (s x : ℕ) :=
  let j := (inN D V x).card
  (j-s)^2+(s-j)^2

private theorem degree_square (j s : ℕ) : ((j-s)^2+(s-j)^2)+2*s*j=j*j+s*s := by
  rcases le_total s j with ge|le
  · obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le ge
    rw [Nat.add_sub_cancel_left,Nat.sub_eq_zero_of_le (by omega)]
    ring
  · obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le le
    rw [Nat.sub_eq_zero_of_le (by omega : j≤j+k),Nat.add_sub_cancel_left]
    ring

/-- Exact arc contraction, retaining the incoming-degree deviations and
every column outside the two predecessor rows and the endpoint union. -/
theorem exact_balance {D : CH.Digraph} {V : Finset ℕ} {s : ℕ} (hf : QFree D V 3) (hm : OutEq s D V) :
    V.card*s*(3*s+1)+edges D V (fun u v => (endpoints D V u v).card)+
      edges D V (fun u v => (uncovered D V 1 u v).card)+(∑ x∈V,indegreeDeviation D V s x)=
    V.card*s*V.card+edges D V (fun u v => (commonOut D V u v).card) := by
  let din := fun u => (inN D V u).card
  let c := fun u v => (endpoints D V u v).card
  let z := fun u v => (commonIn D V u v).card
  let t := fun u v => (commonOut D V u v).card
  let r := fun u v => (uncovered D V 1 u v).card
  have row := Finset.sum_congr (s₁:=V) rfl (fun u hu => Finset.sum_congr (s₁:=outN D V u) rfl
    (fun v hv => unit_exact hf hm hu (mem_outN.mp hv).1 (mem_outN.mp hv).2))
  change edges D V (fun u v => din u+din v+s+1+c u v+r u v)=edges D V (fun u v => V.card+z u v) at row
  obtain ⟨tails,_⟩ := indegree_contractions hm
  change edges D V (fun u _ => din u)=V.card*s*s at tails
  simp only [edges_add,edges_const hm,tails] at row
  have total : (∑ u∈V,din u)=V.card*s := (Compose.ThinRigid.sum_out_eq_sum_in D V).symm.trans (Finset.sum_const_nat hm)
  have squares := Finset.sum_congr (s₁:=V) rfl (fun v _ => degree_square (din v) s)
  change (∑ v∈V,(indegreeDeviation D V s v+2*s*din v))=_ at squares
  rw [Finset.sum_add_distrib,← Finset.mul_sum,total,Finset.sum_add_distrib,Finset.sum_const_nat (fun _ _ => rfl)] at squares
  have heads : edges D V (fun _ v => din v)=∑ v∈V,din v*din v := by
    rw [transpose]; simp only [Finset.sum_const_nat (fun _ _ => rfl)]; rfl
  have same : edges D V t=edges D V z := triple_balance D V
  change V.card*s*(3*s+1)+edges D V c+edges D V r+_ =V.card*s*V.card+edges D V t
  nlinarith only [row,heads,squares,same]

/-- CH at cutoff three when the common heads of each arc induce an acyclic graph. -/
theorem cycle_of_acyclic_banks {D : CH.Digraph} {n s : ℕ} (hn : 0<n) (hs : 0<s) (ord : n≤3*s)
    (hl : CH.Loopless D n) (hm : CH.MinOutdegreeAtLeast D n s)
    (acyclic : ∀ u∈Finset.range n,∀ v∈outN D (Finset.range n) u, let T := commonOut D (Finset.range n) u v
      QFree D T T.card) : CH.HasDirectedCycleAtMost D n 3 := by
  by_contra no
  obtain ⟨u,hu,v,hv,T,sub,_,_,_,cycle⟩ := cyclic_bank (qfree_of_noShort hl no)
    (fun x hx => Compose.FloorSix.out_card hm (Finset.mem_range.mp hx)) ⟨0,Finset.mem_range.mpr hn⟩ hs
    (by simpa using ord)
  exact cycle (((acyclic u hu v hv).mono_set sub).mono_bound (Finset.card_le_card sub))

#print axioms endpoint_exact
#print axioms exact_balance
#print axioms cycle_of_acyclic_banks

end LeanCH.BR.ShenSharedHead
