import checkpoints.shen_extension.ExclusiveRouteCapacity

namespace LeanCH.BR.LowShellCycleSelection
open Finset BRq2 BRq3 BR45 BRsGen ExteriorPacking PhysicalCycleStock

def fullRowFloor (q r : ℕ) := (q+1)-(r-(q+1))*(r-q)

structure StrongTerminal (D : CH.Digraph) (V : Finset ℕ) (r : ℕ) (T : Finset ℕ) : Prop where
  size : T.card=r-1
  rooted : ∀x∈T,Rooted D V x T
  nextSize : (exterior D V T).card=r-1
  nextRooted : ∀z∈exterior D V T,Rooted D V z (exterior D V T)
  strong : ∀x∈T,3*r+2≤(ball D V x 3).card

/-- Turn the very same routed deficit into an admitted arrival at a named
strong terminal. Its physical first bank has enough *complete* parents, and
each step (including the final landing) carries its own common-parent bound. -/
theorem routed_arrival {D V q r target g mid top C}
    (free : QFree D V q) (reg : OutEq r D V) (sel : Selection D V q r 3 (3*r))
    (ready : RoutingRoom q r V.card target) (cm : C∈booked sel)
    (bill : shortfall sel C (r-q)) (routed : RoutedClaim sel C)
    (positive : r-q+1<fullRowFloor q r)
    (score : ScoreRoom q r (r-1) g) (grow : GrowthRoom q r g mid) (again : GrowthRoom q r mid top) :
    ∃T,StrongTerminal D V r T ∧
      WeakArrival D V r (V.card-((r-1)+top)) (fullRowFloor q r) 1 C T := by
  classical
  obtain ⟨Y,only,dag,yc,om,v,vc,sends,high,k,kt,valid,strong⟩ := routed
  let Z := N3 D V (sel.rep Y)
  let B := bankIteration D V Z
  let δ := V.card-((r-1)+top)
  have hq := ready.cycle.1
  have hr := ready.growth.2.1
  have ym : Y∈claims sel C := only.symm ▸ mem_singleton_self Y
  have yk := (mem_filter.mp ym).1
  have supply := selected_stock free reg (by omega) sel yk ready.cycle dag
    (by have := ready.close; have := ready.space; omega) ready.distance ready.score
  dsimp only at supply
  rw [yc] at supply
  obtain ⟨cy,sz,nfull,paid⟩ := supply
  let G := C.filter (fun a=>Z⊆outN D V a)
  change C.card≤G.card+(r-C.card)*(r-q) at nfull
  have cc := sel.length _ (sel.assigned Y yk)
  rw [yc] at cc
  have delta := Nat.mul_le_mul_right (r-q) (show r-C.card≤r-(q+1) by omega)
  have count : fullRowFloor q r≤G.card := by dsimp [fullRowFloor]; omega
  have all W (wm : W∈claims sel C) : QFree D (outN D V (sel.rep W)) (outN D V (sel.rep W)).card := by
    rw [only,mem_singleton] at wm; exact wm ▸ dag
  obtain ⟨_,_,_,_,_,tiers⟩ := unpaid_acyclic free reg (by omega) sel cm bill all ready.cycle
    ready.close ready.space ready.distance ready.score ready.high
  have Ghigh : G ⊆ C.filter (fun a=>3*r<(ball D V a 3).card) :=
    fun a am=>mem_filter.mpr ⟨(mem_filter.mp am).1,ready.high.trans_le (paid a am)⟩
  have nz : 0<omissions D V C r := by
    by_contra! zero
    simp only [Nat.le_zero.mp zero,pow_zero,Nat.mul_one] at tiers
    have bound := count.trans (card_le_card Ghigh)
    omega
  have cv := sel.rooted _ (sel.assigned Y yk)
  rw [yc] at cv
  have sep : Disjoint C Z := disjoint_left.mpr (fun a am az=>(mem_N3.mp az).2
    (mem_N2.mp ((rep_key sel yk).symm ▸ cy am)).1)
  have capacity := along_chain (Z:=Z) free hq reg (by omega) ready.close score grow again valid
  have node j (jm : j≤k) : RouteBank D V r δ (B j) := by
    have p := capacity j jm
    change (allParents D V (B j)).card+(r-1)+top≤V.card at p
    exact ⟨(valid j (by omega)).1,(valid j (by omega)).2,by dsimp [δ]; omega⟩
  have path j (jm : j≤k) : Relation.ReflTransGen (RouteEdge D V r δ) Z (B j) := by
    induction j with
    | zero => exact .refl
    | succ j ih => exact .tail (ih (by omega)) ⟨node j (by omega),node _ jm,rfl⟩
  refine ⟨B k,⟨(valid k (by omega)).1,(valid k (by omega)).2,(valid (k+1) le_rfl).1,
    (valid (k+1) le_rfl).2,strong⟩,cv,⟨nz,om⟩,Z,node 0 (by omega),sep,count,path k le_rfl⟩

attribute [aesop safe forward (immediate := [free,hq,reg,hr,sparse,two,entry,arrive])
  (rule_sets := [CHGraphFamilies])] arrivals_bound

theorem exclusive_at {D V q r c C T v} (free : QFree D V q) (hq : 2≤q) (reg : OutEq r D V)
    (terminal : StrongTerminal D V r T) (rooted : ∀x∈C,Rooted D V x C)
    (om : omissions D V C r≤c) (room : c+1<r-1) (a : v∈T) (b : v∈C) : T=C :=
  complete_exclusive free hq terminal.rooted rooted reg terminal.nextSize
    (fun x xm=>((terminal.nextRooted x xm).one x xm).le) om room a b

/-- Adjoining every marked terminal simultaneously keeps the prices of *all*
previously booked rows fixed, including when a terminal was already booked. -/
theorem shares_unchanged {D V q r c} {F K : Finset (Finset ℕ)} (free : QFree D V q) (hq : 2≤q)
    (reg : OutEq r D V) (terminals : ∀T∈K,StrongTerminal D V r T)
    (rooted : ∀C∈F,∀x∈C,Rooted D V x C) (om : ∀C∈F,omissions D V C r≤c)
    (room : c+1<r-1) (stock : ℕ→ℚ) {C v} (cf : C∈F) (vc : v∈C) :
    share D V (F∪K) r stock C v=share D V F r stock C v := by
  have same : through (F∪K) v=through F v := by
    ext T
    constructor
    · intro cover
      obtain ⟨family,vt⟩ := mem_filter.mp cover
      rcases mem_union.mp family with tf|tk
      · exact mem_filter.mpr ⟨tf,vt⟩
      have id := exclusive_at free hq reg (terminals T tk) (rooted C cf) (om C cf) room vt vc
      exact mem_filter.mpr ⟨id ▸ cf,vt⟩
    · intro cover
      obtain ⟨tm,vm⟩ := mem_filter.mp cover
      exact mem_filter.mpr ⟨mem_union_left _ tm,vm⟩
  simp only [share,turns,same]

/-- Exact price on the terminal in any family of supports of bounded omission. -/
theorem terminal_stock {D V q r c T} {F : Finset (Finset ℕ)} (free : QFree D V q) (hq : 2≤q)
    (reg : OutEq r D V) (term : StrongTerminal D V r T) (used : T∈F)
    (rooted : ∀C∈F,∀x∈C,Rooted D V x C) (om : ∀C∈F,omissions D V C r≤c)
    (room : c+1<r-1) :
    (3*(r-1):ℕ) ≤ ∑x∈T,share D V F r (fun v=>surplus (3*r) (ball D V v 3).card) T x := by
  classical
  have row x (xm : x∈T) : (3:ℚ)≤share D V F r (fun v=>surplus (3*r) (ball D V v 3).card) T x := by
    have alone : through F x={T} := by
      apply eq_singleton_iff_unique_mem.mpr
      refine ⟨mem_filter.mpr ⟨used,xm⟩,?_⟩
      intro C cm
      obtain ⟨cf,xc⟩ := mem_filter.mp cm
      exact (exclusive_at free hq reg term (rooted C cf) (om C cf) room xm xc).symm
    have zero : omissions D V T r=0 := by simp [omissions,term.nextSize]
    have high := term.strong x xm
    have value : 3≤surplus (3*r) (ball D V x 3).card := by simp [surplus,show 3*r<(ball D V x 3).card by omega]; omega
    simpa [share,turns,alone,zero] using (show (3:ℚ)≤(surplus (3*r) (ball D V x 3).card:ℚ) by exact_mod_cast value)
  have paid := sum_le_sum row
  simpa [term.size,mul_comm] using paid

def TransferRoom (q r n g mid top : ℕ) : Prop :=
  r-q+1<fullRowFloor q r ∧ ScoreRoom q r (r-1) g ∧ GrowthRoom q r g mid ∧ GrowthRoom q r mid top ∧
  n-((r-1)+top)<2*(r-1) ∧ n-((r-1)+top)<r-1+fullRowFloor q r ∧ 2<r-1

instance {q r n g mid top} : Decidable (TransferRoom q r n g mid top) := by
  unfold TransferRoom; infer_instance

/-- Every financially short group on ONE common assignment has either a
first-layer claimant on that physical cycle or a labelled bounded-congestion route. -/
structure AssignmentLedger {D V q r} (sel : Selection D V q r 3 (3*r)) (δ : ℕ) : Prop where
  first : ∀Y∈classes D V 3 (3*r),¬QFree D (outN D V (sel.rep Y)) (outN D V (sel.rep Y)).card → sel.pay Y⊆outN D V (sel.rep Y)
  acyclic : ∀C,¬FirstClaim sel C → ∀Y∈claims sel C,QFree D (outN D V (sel.rep Y)) (outN D V (sel.rep Y)).card
  route : ∀C∈booked sel,shortfall sel C (r-q) → FirstClaim sel C ∨
    ((∑Y∈claims sel C,shellDebt D V 3 (3*r) Y)≤1 ∧ ∃T,StrongTerminal D V r T ∧ WeakArrival D V r δ (fullRowFloor q r) 1 C T)
  limit : ∀T,∀F : Finset (Finset ℕ),(∀C∈F,WeakArrival D V r δ (fullRowFloor q r) 1 C T) →
    F.card*fullRowFloor q r≤δ*2

theorem all_claims {D V q r target g mid top} (free : QFree D V q) (reg : OutEq r D V)
    (sel : Selection D V q r 3 (3*r)) (ready : RoutingRoom q r V.card target)
    (move : TransferRoom q r V.card g mid top) :
    ∃t : Selection D V q r 3 (3*r),t.rep=sel.rep ∧ AssignmentLedger t (V.card-((r-1)+top)) := by
  classical
  obtain ⟨t,eq,primary⟩ := primary_selection free reg sel ready.cycle
  obtain ⟨positive,score,grow,again,two,entry,sparse⟩ := move
  have hq := ready.cycle.1
  have hr := ready.growth.2.1
  refine ⟨t,eq,primary,?_,?_,?_⟩
  · intro C none Y ym
    by_contra cy
    obtain ⟨yk,id⟩ := mem_filter.mp ym
    exact none ⟨Y,ym,id ▸ primary Y yk cy,cy⟩
  · intro C cm bill
    by_cases cy : ∃Y∈claims t C,¬QFree D (outN D V (t.rep Y)) (outN D V (t.rep Y)).card
    · obtain ⟨Y,ym,no⟩ := cy
      obtain ⟨yk,mark⟩ := mem_filter.mp ym
      exact .inl ⟨Y,ym,mark ▸ primary Y yk no,no⟩
    push Not at cy
    obtain ⟨Y,only,yc,om,_,tiers⟩ := unpaid_acyclic free reg (by omega) t cm bill cy ready.cycle ready.close
      ready.space ready.distance ready.score ready.high
    have yk : Y∈claims t C := only.symm ▸ mem_singleton_self Y
    have dag := cy Y yk
    have mul := Nat.mul_le_mul_left (r-q+1) (Nat.pow_le_pow_right (n:=2) (by decide) om)
    have cap : (r-q+1)*2^(omissions D V C r)≤2*(r-q+1) := by simpa [Nat.mul_comm] using mul
    have bounds := tiers.trans cap
    rw [←yc] at bounds
    have result := weak_row_chain free reg (by omega) t (mem_filter.mp yk).1 dag ready.cycle ready.close
      ready.space ready.distance ready.score ready.high ready.squeeze ready.finite (2*(r-q+1)) bounds ready.margin
    rw [yc] at result
    have unit := (acyclic_class_debit free reg (by omega) t (mem_filter.mp yk).1 ready.cycle dag
      (by have := ready.close; have := ready.space; omega) ready.distance).2
    exact .inr ⟨by simpa [only] using unit,routed_arrival free reg t ready cm bill ⟨Y,only,dag,yc,om,result⟩ positive score grow again⟩
  · intro T F incoming
    simpa using arrivals_bound free (by omega) reg (by omega) sparse two entry incoming

#print axioms all_claims
#print axioms terminal_stock
#print axioms shares_unchanged

#print axioms routed_arrival
end LeanCH.BR.LowShellCycleSelection
