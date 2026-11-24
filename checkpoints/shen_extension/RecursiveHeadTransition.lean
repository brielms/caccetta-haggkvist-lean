import checkpoints.shen_extension.ClosedHeadIntersection

namespace LeanCH.BR.Closure.RecursiveHeads
open BRq2 BRq3 Finset ClosedHeadIntersection

/-- A retained arc or a two-step path through a named parent vertex set. -/
def shortcut (D : CH.Digraph) (V : Finset ℕ) : CH.Digraph :=
  fun x y => D x y || decide (∃ t ∈ V, D x t=true ∧ D t y=true)

private theorem edge {D V x y} : shortcut D V x y=true ↔
    D x y=true ∨ ∃ t ∈ V, D x t=true ∧ D t y=true := by simp [shortcut]

theorem lift {D V W x y n} (sub : W ⊆ V) (w : Walk (shortcut D V) W x y n) :
    ∃ m, n ≤ m ∧ m ≤ 2*n ∧ Walk D V x y m := by
  induction w with
  | refl => exact ⟨0,by omega,by omega,.refl _⟩
  | step hb ab _ ih =>
    obtain ⟨m,lo,hi,tail⟩ := ih
    rcases edge.mp ab with ab | ⟨t,ht,at',tb⟩
    · exact ⟨m+1,by omega,by omega,.step (sub hb) ab tail⟩
    · exact ⟨m+2,by omega,by omega,.step ht at' (.step (sub hb) tb tail)⟩

structure State where
  D : CH.Digraph
  V : Finset ℕ
  q : ℕ
  safe : QFree D V q
  live : V.Nonempty
  heads : ∀ x ∈ V, (outN D V x).Nonempty
  pairs : Intersects D V

def Step (a b : State) : Prop :=
  (∃ u ∈ a.V, b.V = outN a.D a.V u) ∧ b.D = shortcut a.D a.V ∧
    b.q = a.q/2 ∧ b.V.card < a.V.card

theorem take_step (a : State) (cutoff : 3 ≤ a.q) {u} (hu : u ∈ a.V) :
    ∃ b, Step a b ∧ b.V = outN a.D a.V u := by
  let E := outN a.D a.V u
  let F := shortcut a.D a.V
  have sub : E ⊆ a.V := outN_subset
  have back {v h} (ve : v ∈ E) (hv : h ∈ a.V) (vh : a.D v h=true) :
      ∃ z ∈ E, z=h ∨ a.D h z=true := by
    obtain ⟨z,zv,uz,hz⟩ := a.pairs u hu h hv
    rcases uz with eq | uz
    · subst z
      rcases hz with rfl | hz
      · exact False.elim (digonfree a.safe (by omega) hu (sub ve) (mem_outN.mp ve).2 vh)
      · exact False.elim (a.safe u 3 (by omega) cutoff
          (.step (sub ve) (mem_outN.mp ve).2 (.step hv vh (.step hu hz (.refl u)))))
    · exact ⟨z,mem_outN.mpr ⟨zv,uz⟩,hz⟩
  have full (v) (ve : v ∈ E) : (outN F E v).Nonempty := by
    obtain ⟨h,hv,vh⟩ := show ∃ h ∈ a.V, a.D v h=true from
      (a.heads v (sub ve)).elim (fun h hh => ⟨h,mem_outN.mp hh⟩)
    obtain ⟨z,ze,hz⟩ := back ve hv vh
    refine ⟨z,mem_outN.mpr ⟨ze,edge.mpr ?_⟩⟩
    rcases hz with rfl | hz
    · exact Or.inl vh
    · exact Or.inr ⟨h,hv,vh,hz⟩
  have meet : Intersects F E := by
    intro v ve w we
    obtain ⟨h,hv,vh,wh⟩ := a.pairs v (sub ve) w (sub we)
    rcases vh with rfl | vh
    · exact ⟨h,ve,Or.inl rfl,wh.imp_right (fun e => edge.mpr (Or.inl e))⟩
    rcases wh with rfl | wh
    · exact ⟨h,we,Or.inr (edge.mpr (Or.inl vh)),Or.inl rfl⟩
    obtain ⟨z,ze,hz⟩ := back ve hv vh
    refine ⟨z,ze,Or.inr (edge.mpr ?_),Or.inr (edge.mpr ?_)⟩
    · rcases hz with rfl | hz
      · exact Or.inl vh
      · exact Or.inr ⟨h,hv,vh,hz⟩
    · rcases hz with rfl | hz
      · exact Or.inl wh
      · exact Or.inr ⟨h,hv,wh,hz⟩
  have safe : QFree F E (a.q/2) := by
    intro x k pos le walk
    obtain ⟨m,lo,hi,path⟩ := lift sub walk
    exact a.safe x m (by omega) (by omega) path
  let b : State := ⟨F,E,a.q/2,safe,a.heads u hu,full,meet⟩
  have strict : E ⊂ a.V :=
    ⟨sub,fun rev => loopfree a.safe (by omega) hu (mem_outN.mp (rev hu)).2⟩
  exact ⟨b,⟨⟨u,hu,rfl⟩,rfl,rfl,card_lt_card strict⟩,rfl⟩

/-- The transitions terminate even if different roots are chosen at different
levels. The terminal state retains the two structural properties in State. -/
theorem descend (a : State) : ∃ b, Reach Step a b ∧ b.q < 3 := by
  by_cases cap : a.q < 3
  · exact ⟨a,.refl,cap⟩
  obtain ⟨u,hu⟩ := a.live
  obtain ⟨b,step,_⟩ := take_step a (by omega) hu
  obtain ⟨c,path,done⟩ := descend b
  exact ⟨c,(Relation.ReflTransGen.single step).trans path,done⟩
termination_by a.V.card
decreasing_by exact step.2.2.2

theorem ten_heads (a : State) (cap : 6 ≤ a.q) {u} (hu : u ∈ a.V) : 10 ≤ (outN a.D a.V u).card := by
  obtain ⟨b,step,labels⟩ := take_step a (by omega) hu
  have half := step.2.2.1
  rw [← labels]
  exact order_ten (b.safe.mono_bound (by omega)) b.heads b.pairs b.live

theorem root_order (a : State) (cap : 6 ≤ a.q) {u} (hu : u ∈ a.V) :
    4*(a.q/2-1)+1 ≤ (outN a.D a.V u).card := by
  obtain ⟨b,step,labels⟩ := take_step a (by omega) hu
  rw [← step.2.2.1,← labels]
  exact order_at_girth (by have := step.2.2.1; omega) b.safe b.heads b.pairs b.live

/-- A digon in the child costs four old edges at the triangle cutoff. Both
intermediate vertices are actual labels and must be distinct. -/
theorem digon_lift {D V x y} (safe : QFree D V 3) (xv : x ∈ V) (yv : y ∈ V)
    (xy : shortcut D V x y=true) (yx : shortcut D V y x=true) :
    D x y≠true ∧ D y x≠true ∧ ∃ i ∈ V, ∃ j ∈ V, i≠j ∧
      D x i=true ∧ D i y=true ∧ D y j=true ∧ D j x=true := by
  have no {r t} (hr : r ∈ V) (ht : t ∈ V) (rt : D r t=true) (tr : shortcut D V t r=true) : False := by
    rcases edge.mp tr with old | ⟨i,hi,ti,ir⟩
    · exact digonfree safe (by decide) hr ht rt old
    · exact safe r 3 (by decide) (by decide) (.step ht rt (.step hi ti (.step hr ir (.refl r))))
  have nxy := fun old => no xv yv old yx
  have nyx := fun old => no yv xv old xy
  obtain ⟨i,iv,xi,iy⟩ := (edge.mp xy).resolve_left nxy
  obtain ⟨j,jv,yj,jx⟩ := (edge.mp yx).resolve_left nyx
  exact ⟨nxy,nyx,i,iv,j,jv,fun eq => digonfree safe (by decide) iv yv iy (eq ▸ yj),xi,iy,yj,jx⟩

/-- The actual order/degree inequality defining a counterexample at this cutoff. -/
def Bad (a : State) : Prop :=
  ∃ s, a.V.card ≤ a.q*s ∧ ∀ x ∈ a.V, s ≤ (outN a.D a.V x).card

def HeadRectangle (D : CH.Digraph) (V : Finset ℕ) (u : ℕ) : Prop :=
  let A := outN D V u
  ∃ x ∈ A, ∃ M ⊆ A, A.card < 2*M.card ∧ x ∈ M ∧
    (∀ z ∈ M, D x z≠true) ∧ ∀ h ∈ outN D V x, ∀ z ∈ M, D h z≠true

/-- At a root of a triangle-free graph, an opposite pair on a real four-cycle
or an old empty rectangle wider than half of the root's out-neighborhood. -/
def RootAlternative (D : CH.Digraph) (V : Finset ℕ) (u : ℕ) : Prop :=
  let A := outN D V u
  (∃ x ∈ A, ∃ y ∈ A, x≠y ∧ ∃ i ∈ V, ∃ j ∈ V, i≠j ∧
    D x i=true ∧ D i y=true ∧ D y j=true ∧ D j x=true) ∨ HeadRectangle D V u

theorem root_alternative {D V u} (safe : QFree D V 3) (live : (outN D V u).Nonempty) :
    RootAlternative D V u := by
  classical
  unfold RootAlternative
  intro A
  let F := shortcut D V
  have sub : A ⊆ V := outN_subset
  have noLoop (x) (hx : x ∈ A) (xx : F x x=true) : False := by
    rcases edge.mp xx with e | ⟨h,hv,xh,hx'⟩
    · exact loopfree safe (by decide) (sub hx) e
    · exact digonfree safe (by decide) (sub hx) hv xh hx'
  by_cases pair : ∃ x ∈ A, ∃ y ∈ A, F x y=true ∧ F y x=true
  · left
    obtain ⟨x,hx,y,hy,xy,yx⟩ := pair
    exact ⟨x,hx,y,hy,fun eq => noLoop y hy (eq ▸ xy),(digon_lift safe (sub hx) (sub hy) xy yx).2.2⟩
  right
  have oriented : QFree F A 2 := by
    intro x k lo hi walk
    rcases (show k=1 ∨ k=2 by omega) with rfl|rfl
    · cases walk with | step hb e tail => cases tail; exact noLoop x hb e
    · cases walk with
      | step hb xy tail =>
        cases tail with
        | step hx yx rest => cases rest; exact pair ⟨x,hx,_,hb,xy,yx⟩
  obtain ⟨x,hx,lo⟩ : ∃ x ∈ A, 2*(outN F A x).card < A.card := by
    by_contra! large
    let j := (A.card+1)/2
    have degrees (x) (hx : x ∈ A) : j ≤ (outN F A x).card := by
      have := large x hx; dsimp [j]; omega
    have balls : Ball 2 j := by
      intro G W free reg x hx
      change j*1+1 ≤ (ball G W x 1).card
      have eq : ball G W x 1 = insert x (outN G W x) := by ext z; rw [mem_ball_one hx,mem_insert]
      rw [eq,card_insert_of_notMem (fun h => loopfree free (by decide) hx (mem_outN.mp h).2),reg x hx]; omega
    have := BR45.dt_size (by decide) balls oriented degrees live
    dsimp [j] at this; omega
  let M := A \ outN F A x
  have split := card_sdiff_add_card_eq_card (outN_subset (D:=F) (W:=A) (y:=x))
  change M.card + _ = _ at split
  refine ⟨x,hx,M,sdiff_subset,by change A.card < 2*M.card; omega,
    mem_sdiff.mpr ⟨hx,fun h => noLoop x hx (mem_outN.mp h).2⟩,?_,?_⟩
  · exact fun z hz xz => (mem_sdiff.mp hz).2 (mem_outN.mpr ⟨(mem_sdiff.mp hz).1,edge.mpr (Or.inl xz)⟩)
  · intro h hh z hz hZ
    exact (mem_sdiff.mp hz).2 (mem_outN.mpr ⟨(mem_sdiff.mp hz).1,edge.mpr (Or.inr
      ⟨h,outN_subset hh,(mem_outN.mp hh).2,hZ⟩)⟩)

theorem rectangle_four {D V u} (safe : QFree D V 4) (live : (outN D V u).Nonempty) :
    HeadRectangle D V u := by
  rcases root_alternative (safe.mono_bound (by decide : 3≤4)) live with cycle | rect
  · obtain ⟨x,hx,y,hy,_,i,hi,j,hj,_,xi,iy,yj,jx⟩ := cycle
    exact False.elim (safe x 4 (by decide) (by decide) (.step hi xi (.step (outN_subset hy) iy
      (.step hj yj (.step (outN_subset hx) jx (.refl x))))))
  · exact rect

private theorem terminal_clear (a : State) (cap : a.q<3) : ¬ Bad a := by
  rintro ⟨s,ord,deg⟩
  have live := card_pos.mpr a.live
  by_cases zero : a.q=0
  · rw [zero,Nat.zero_mul] at ord; omega
  have balls : Ball a.q s := by
    intro D V safe reg u hu
    rcases (show a.q=1 ∨ a.q=2 by omega) with eq | eq
    · rw [eq]; simpa using (card_pos.mpr (show (ball D V u 0).Nonempty from ⟨u,self_mem_ball hu⟩))
    · rw [eq] at safe ⊢
      change s*1+1 ≤ (ball D V u 1).card
      have row : ball D V u 1 = insert u (outN D V u) := by
        ext z; rw [mem_ball_one hu,mem_insert]
      rw [row,card_insert_of_notMem (fun h => loopfree safe (by decide) hu (mem_outN.mp h).2),reg u hu]
      omega
  have := BR45.dt_size (by omega) balls a.safe deg a.live
  omega

/-- Every root of a last bad state has an explicitly underpaid compressed row. -/
def Underpaid (a : State) : Prop :=
  ∀ u ∈ a.V, ∀ j, (outN a.D a.V u).card ≤ (a.q/2)*j →
    ∃ x ∈ outN a.D a.V u, (outN (shortcut a.D a.V) (outN a.D a.V u) x).card < j

theorem last_bad (a : State) (bad : Bad a) :
    ∃ b, Reach Step a b ∧ Bad b ∧ 3≤b.q ∧ Underpaid b := by
  classical
  by_cases next : ∃ b, Step a b ∧ Bad b
  · obtain ⟨b,edge,bb⟩ := next
    obtain ⟨c,path,bc,cap,stuck⟩ := last_bad b bb
    exact ⟨c,(Relation.ReflTransGen.single edge).trans path,bc,cap,stuck⟩
  · have cap : 3≤a.q := by by_contra! small; exact terminal_clear a small bad
    refine ⟨a,.refl,bad,cap,?_⟩
    intro u hu j ord
    obtain ⟨b,edge,labels⟩ := take_step a cap hu
    by_contra! full
    apply next
    refine ⟨b,edge,j,?_,?_⟩
    · rw [labels,edge.2.2.1]; exact ord
    · rw [labels,edge.2.1]; exact full
termination_by a.V.card
decreasing_by exact edge.2.2.2

def Frontier (D : CH.Digraph) (V : Finset ℕ) (q : ℕ) : Prop :=
  (∃ u ∈ V, ∃ v ∈ V, Disjoint (insert u (outN D V u)) (insert v (outN D V v))) ∨
    ∃ a b : State, a.D=D ∧ a.V=V ∧ a.q=q ∧ Reach Step a b ∧ Bad b ∧ 3≤b.q ∧ Underpaid b

private theorem disjoint_rows {D V} (meet : ¬ Intersects D V) :
    ∃ u ∈ V, ∃ v ∈ V, Disjoint (insert u (outN D V u)) (insert v (outN D V v)) := by
  classical
  unfold Intersects at meet
  push Not at meet
  obtain ⟨u,ut,v,vt,no⟩ := meet
  refine ⟨u,ut,v,vt,disjoint_left.mpr ?_⟩
  intro w wu wv
  have wt := (insert_subset ut (outN_subset (D:=D) (y:=u))) wu
  have l := (mem_insert.mp wu).imp_right (fun h => (mem_outN.mp h).2)
  have r := (mem_insert.mp wv).imp_right (fun h => (mem_outN.mp h).2)
  specialize no w wt
  tauto

/-- At these cutoffs, every exact-degree thinning has a separated pair.
The original graph may have extra arcs. -/
theorem separated_exact {D V q s} (safe : QFree D V q) (live : V.Nonempty) (pos : 0<s)
    (degree : OutEq s D V) (cap : 6≤q) (small : s<10 ∨ s<4*(q/2-1)+1) :
    ∃ u ∈ V, ∃ v ∈ V, Disjoint (insert u (outN D V u)) (insert v (outN D V v)) := by
  apply disjoint_rows
  intro pairs
  let a : State := ⟨D,V,q,safe,live,fun x hx => card_pos.mp (pos.trans_le (degree x hx).ge),pairs⟩
  obtain ⟨u,hu⟩ := live
  have ten : 10 ≤ (outN D V u).card := ten_heads a cap hu
  have many : 4*(q/2-1)+1 ≤ (outN D V u).card := root_order a cap hu
  rw [degree u hu] at ten many
  omega

theorem separated_thinning {D V q s} (safe : QFree D V q) (live : V.Nonempty) (pos : 0<s)
    (degree : ∀ x ∈ V, s ≤ (outN D V x).card) (cap : 6≤q) (small : s<10 ∨ s<4*(q/2-1)+1) :
    ∃ F, (∀ x y, F x y=true → D x y=true) ∧ OutEq s F V ∧ QFree F V q ∧
      ∃ u ∈ V, ∃ v ∈ V, Disjoint (insert u (outN F V u)) (insert v (outN F V v)) := by
  obtain ⟨F,sub,rows⟩ := exists_outEq degree
  have free := qfree_sub sub safe
  exact ⟨F,sub,rows,free,separated_exact free live pos rows cap small⟩

/-- A live literal candidate at any cutoff either has disjoint closed rows or
reaches a smaller-order obstruction to paying for this recursive shortcut rule. -/
theorem from_candidate {D V q s} (safe : QFree D V q) (live : V.Nonempty) (pos : 0<s)
    (bound : V.card ≤ q*s) (degree : ∀ x ∈ V, s ≤ (outN D V x).card) : Frontier D V q := by
  classical
  by_cases meet : Intersects D V
  · right
    let a : State := ⟨D,V,q,safe,live,fun x hx => card_pos.mp (pos.trans_le (degree x hx)),meet⟩
    obtain ⟨b,path,bad,cap,stuck⟩ := last_bad a ⟨s,bound,degree⟩
    exact ⟨a,b,rfl,rfl,rfl,path,bad,cap,stuck⟩
  · exact Or.inl (disjoint_rows meet)

/-- Start the descent at the actual girth of this particular host. -/
def FromHost (D : CH.Digraph) (T : Finset ℕ) : Prop :=
  ∃ a : State, a.D=D ∧ a.V=T ∧ 3 ≤ a.q ∧ 4*(a.q-1)+1 ≤ T.card ∧
    (∃ M ⊆ T, M.card=a.q+1 ∧ OutEq 1 D M ∧
      ∀ u ∈ M, ∀ v ∈ outN D M u, ∀ w ∈ outN D M v,
        ∃ h ∈ T \ M, D u h=true ∧ D w h=true ∧ outN D M h=∅) ∧
    ∃ b, Reach Step a b ∧ b.q < 3

theorem from_host {D T} (safe : QFree D T 3) (heads : ∀ x ∈ T, (outN D T x).Nonempty)
    (pairs : Intersects D T) (live : T.Nonempty) : FromHost D T := by
  obtain ⟨q,M,hq,growth,free,sub,size,one,external⟩ := shortest_cycle_heads safe heads pairs live
  let a : State := ⟨D,T,q,free,live,heads,pairs⟩
  exact ⟨a,rfl,rfl,hq,growth,⟨M,sub,size,one,external⟩,descend a⟩

#print axioms lift
#print axioms take_step
#print axioms descend
#print axioms ten_heads
#print axioms root_order
#print axioms digon_lift
#print axioms root_alternative
#print axioms rectangle_four
#print axioms separated_exact
#print axioms separated_thinning
#print axioms last_bad
#print axioms from_candidate
#print axioms from_host
end LeanCH.BR.Closure.RecursiveHeads
