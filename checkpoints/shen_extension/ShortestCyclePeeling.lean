import checkpoints.shen_extension.ShortestCycleClasses

namespace LeanCH.BR.Closure.ShortestCyclePeeling
open Finset BRq2 BRq3 BR45 DeficitLevels CutoffDegreeRank ShortestCycleClasses

noncomputable def heads (D : CH.Digraph) (T : Finset ℕ) (q x : ℕ) : Finset ℕ := by
  classical exact (outN D T x).filter (fun y => Together D T q x y)

def Dense (D : CH.Digraph) (T : Finset ℕ) (q k : ℕ) : Prop :=
  T.Nonempty ∧ ∀x∈T, k<(heads D T q x).card

private def Masks (D : CH.Digraph) (U : Finset ℕ) (q k : ℕ) : Prop :=
  ∃Z : ℕ→Finset ℕ, (∀x∈U,(Z x).card≤k) ∧ ∀M⊆U,M.card=q+1 → OutEq 1 D M →
    ∃x∈M,∃y∈outN D M x,y∈Z x

/-- Each step either retains a nonempty set where all rows have many
shortest-cycle arcs or erases one vertex and charges its current arcs.
The order of the carrier strictly decreases, including on repeated types. -/
private theorem peel (D : CH.Digraph) (U : Finset ℕ) (q k : ℕ) :
    (∃T⊆U, Dense D T q k) ∨ Masks D U q k := by
  classical
  by_cases live : U.Nonempty
  · by_cases all : ∀x∈U,k<(heads D U q x).card
    · exact Or.inl ⟨U,Subset.rfl,live,all⟩
    · push Not at all
      obtain ⟨x,xu,low⟩ := all
      rcases peel D (U.erase x) q k with ⟨T,ts,good⟩|⟨Z,cap,cover⟩
      · exact Or.inl ⟨T,ts.trans (erase_subset _ _),good⟩
      · right
        let mark := fun v => if v=x then heads D U q x else Z v
        refine ⟨mark,?_,?_⟩
        · intro v vu
          by_cases vx : v=x
          · simpa [mark,vx] using low
          · simpa [mark,vx] using cap v (mem_erase.mpr ⟨vx,vu⟩)
        · intro M mu sz one
          by_cases xm : x∈M
          · obtain ⟨y,ym⟩ := card_pos.mp (show 0<(outN D M x).card by rw [one x xm]; decide)
            refine ⟨x,xm,y,ym,?_⟩
            have old := mem_outN.mp ym
            have h : y∈heads D U q x := mem_filter.mpr
              ⟨mem_outN.mpr ⟨mu old.1,old.2⟩,M,mu,sz,one,xm,old.1⟩
            simpa [mark] using h
          · have sub : M⊆U.erase x := fun v vm => mem_erase.mpr ⟨fun eq => xm (eq ▸ vm),mu vm⟩
            obtain ⟨v,vm,y,vy,yz⟩ := cover M sub sz one
            have vx : v≠x := fun eq => xm (eq ▸ vm)
            exact ⟨v,vm,y,vy,by simpa [mark,vx] using yz⟩
  · right
    refine ⟨fun _ => ∅,by simp,?_⟩
    intro M sub sz _
    obtain ⟨x,xm⟩ := card_pos.mp (show 0<M.card by omega)
    exact (live ⟨x,sub xm⟩).elim
termination_by U.card
decreasing_by exact card_erase_lt_of_mem xu

/-- An edge between graph families before imposing any minimality. Exhausting
the peeling process produces a subgraph on the same labels, raises the
short-cycle cutoff by one and preserves out-degree at least s-k. -/
theorem peel_or_raise {D V q s} (hq : 1≤q) (free : QFree D V q)
    (degree : ∀x∈V,s≤(outN D V x).card) (k : ℕ) :
    (∃T⊆V,Dense D T q k) ∨ ∃ E : CH.Digraph, (∀x y,E x y=true → D x y=true) ∧
      QFree E V (q+1) ∧ ∀x∈V,s-k≤(outN E V x).card := by
  classical
  rcases peel D V q k with win|⟨Z,cap,hit⟩
  · exact Or.inl win
  let E : CH.Digraph := fun x y => D x y && decide (y∉Z x)
  have inc (x y) (edge : E x y=true) : D x y=true := (Bool.and_eq_true_iff.mp edge).1
  have up {x y l} (p : Walk E V x y l) : Walk D V x y l := by
    induction p with
    | refl => exact .refl _
    | step vy e _ ih => exact .step vy (inc _ _ e) ih
  have safe : QFree E V q := fun x l pos le p => free x l pos le (up p)
  refine Or.inr ⟨E,inc,?_,?_⟩
  · intro x l pos le p
    have eq : l=q+1 := by
      have no : ¬l≤q := fun bound => safe x l pos bound p
      omega
    subst l
    obtain ⟨M,mv,sz,low⟩ := boundary_closed_walk_support safe p
    have headsSub (a) : outN E M a⊆outN D M a := fun z hz =>
      mem_outN.mpr ⟨(mem_outN.mp hz).1,inc _ _ (mem_outN.mp hz).2⟩
    have reg := dt_reg hq (ball_q_one q hq) (free.mono_set mv)
      (fun a am => (low a am).trans (card_le_card (headsSub a))) (by simpa using sz)
    obtain ⟨a,am,z,az,marked⟩ := hit M mv sz reg.1
    have same := eq_of_subset_of_card_le (headsSub a) ((reg.1 a am) ▸ low a am)
    have ze : z∈outN E M a := same.symm ▸ az
    have allowed := (Bool.and_eq_true_iff.mp (mem_outN.mp ze).2).2
    simp [marked] at allowed
  · intro x xv
    have sub : outN D V x⊆outN E V x∪Z x := by
      intro y hy
      by_cases zy : y∈Z x
      · exact mem_union_right _ zy
      · exact mem_union_left _ (mem_outN.mpr ⟨(mem_outN.mp hy).1,by simp [E,(mem_outN.mp hy).2,zy]⟩)
    have le := (card_le_card sub).trans (card_union_le _ _)
    have max := cap x xv
    have min := degree x xv
    omega

theorem dense_core {base q s} (O : Origin q s) (hb : 2≤base) (rank : Ranked base q s O.V.card)
    {k : ℕ} (budget : O.V.card≤(q+1)*(s-k)) :
    ∃T⊆O.V,Dense O.G T q k := by
  rcases peel O.G O.V q k with win|⟨Z,cap,hit⟩
  · exact win
  obtain ⟨M,mv,sz,one,clean⟩ := escapes_rows O hb rank Z cap budget
  obtain ⟨x,xm,y,ym,marked⟩ := hit M mv sz one
  exact (clean x xm y ym marked).elim

/-- A minimum carrier of this kind is a single overlap class *internally*.
Thus witnesses may be followed indefinitely inside the same carrier. -/
theorem recurrent_of_dense {D V q k} (existsDense : ∃T⊆V,Dense D T q k) :
    ∃T⊆V, Dense D T q k ∧ ∀x∈T,carrier D T q x=T := by
  classical
  let candidates := V.powerset.filter (fun T => Dense D T q k)
  obtain ⟨B,bv,bd⟩ := existsDense
  obtain ⟨T,ok,minimal⟩ := candidates.exists_min_image Finset.card
    ⟨B,mem_filter.mpr ⟨mem_powerset.mpr bv,bd⟩⟩
  obtain ⟨sub,dense⟩ := mem_filter.mp ok
  have tv := mem_powerset.mp sub
  refine ⟨T,tv,dense,?_⟩
  intro x xt
  let C := carrier D T q x
  have ct : C⊆T := filter_subset _ _
  have xc : x∈C := contains xt
  have closed (a) (ac : a∈C) : heads D T q a⊆heads D C q a := by
    intro y yh
    obtain ⟨ya,M,mt,sz,one,am,ym⟩ := mem_filter.mp yh
    have mc : M⊆C := by
      intro b bm
      refine mem_filter.mpr ⟨mt bm,.trans _ _ _ (mem_filter.mp ac).2 (.rel _ _ ?_)⟩
      exact ⟨M,mt,sz,one,am,bm⟩
    exact mem_filter.mpr ⟨mem_outN.mpr ⟨mc ym,(mem_outN.mp ya).2⟩,M,mc,sz,one,am,ym⟩
  have good : Dense D C q k := ⟨⟨x,xc⟩,fun a ac =>
    (dense.2 a (ct ac)).trans_le (card_le_card (closed a ac))⟩
  exact eq_of_subset_of_card_le ct (minimal C (mem_filter.mpr ⟨mem_powerset.mpr (ct.trans tv),good⟩))

theorem recurrent_core {base q s} (O : Origin q s) (hb : 2≤base) (rank : Ranked base q s O.V.card)
    {k : ℕ} (budget : O.V.card≤(q+1)*(s-k)) :
    ∃T⊆O.V, Dense O.G T q k ∧ ∀x∈T,carrier O.G T q x=T :=
  recurrent_of_dense (dense_core O hb rank budget)

/-- At every vertex of every shortest cycle in the core, at least k
distinct new first heads leave that cycle. Each starts a shortest cycle
still inside T, so this can be applied again at its next vertex. -/
theorem branches {D T q k} (dense : Dense D T q k) {M x} (mt : M⊆T) (xm : x∈M)
    (one : OutEq 1 D M) :
    ∃Y⊆outN D (T\M) x, k≤Y.card ∧ ∀a∈Y, Together D T q x a := by
  classical
  let A := heads D T q x
  refine ⟨A\M,?_,?_,fun a ha => (mem_filter.mp (mem_sdiff.mp ha).1).2⟩
  · intro a ha
    obtain ⟨aa,am⟩ := mem_sdiff.mp ha
    obtain ⟨at',xa⟩ := mem_outN.mp (mem_filter.mp aa).1
    exact mem_outN.mpr ⟨mem_sdiff.mpr ⟨at',am⟩,xa⟩
  · have internal : A∩M⊆outN D M x := fun a ha => mem_outN.mpr
      ⟨(mem_inter.mp ha).2,(mem_outN.mp (mem_filter.mp (mem_inter.mp ha).1).1).2⟩
    have count := card_le_card internal
    rw [one x xm] at count
    have eq := card_sdiff_add_card_inter A M
    have many : k<A.card := dense.2 x (mt xm)
    omega

/-- Two shortest circuits through the same root must assign the same
position to any other shared vertex. Positions are represented by their
forward and return walks, including position zero at the root. -/
theorem aligned {D V q h x i j} (safe : QFree D V q) (iMax : i≤q) (jMax : j≤q)
    (a : Walk D V h x i) (ar : Walk D V x h (q+1-i))
    (b : Walk D V h x j) (br : Walk D V x h (q+1-j)) : i=j := by
  apply le_antisymm
  · by_contra! less
    exact safe h _ (by omega) (by omega) (b.append ar)
  · by_contra! less
    exact safe h _ (by omega) (by omega) (a.append br)

/-- A cross arc cannot skip a forward position between two circuits
based at the same root. -/
theorem no_skip {D V q h x y i j} (safe : QFree D V q) (jMax : j≤q)
    (a : Walk D V h x i) (b : Walk D V y h (q+1-j)) (yv : y∈V) (edge : D x y=true) : j ≤ i+1 := by
  by_contra! missing
  exact safe h _ (by omega) (by omega) ((a.snoc yv edge).append b)

#print axioms aligned
#print axioms no_skip
#print axioms branches
#print axioms peel_or_raise
#print axioms dense_core
#print axioms recurrent_core
end LeanCH.BR.Closure.ShortestCyclePeeling
