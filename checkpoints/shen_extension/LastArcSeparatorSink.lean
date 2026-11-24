import checkpoints.shen_extension.LastArcDistanceConflict

namespace LeanCH.BR.Closure.LastArcSeparatorSink
open Finset BRq2 BRq3 BR45 ShenPrimeTransition ShenParentIntersection ShortestCycleWeights
open WeightedSD FirstPacketBarrier SharedArcBarrier SharedArcComponentExchange
open MarkedCyclePeeling hiding Arc

/-- A nonempty set of at most q rows contains one row whose omitted targets
can all be charged, by cardinality, to the other menu labels. -/
theorem direct_targets {D V X B T q} (free : QFree D V q) (bx : B ⊆ X)
    (xv : X ⊆ V) (live : B.Nonempty) (few : B.card ≤ q)
    (quota : ∀ i ∈ B, T.card ≤ (outN D (X ∪ T) i).card) :
    ∃ i ∈ B, (T \ outN D T i).card ≤ (X \ B).card := by
  classical
  obtain ⟨i,ib,stop⟩ := exists_sink (free.mono_set (bx.trans xv)) live few
  have sub : outN D (X ∪ T) i ⊆ (X \ B) ∪ outN D T i := by
    intro z hz
    obtain ⟨menu,arc⟩ := mem_outN.mp hz
    rcases mem_union.mp menu with zx | zt
    · exact mem_union_left _ (mem_sdiff.mpr ⟨zx,fun zin => stop z zin arc⟩)
    · exact mem_union_right _ (mem_outN.mpr ⟨zt,arc⟩)
  have cap := (quota i ib).trans ((card_le_card sub).trans (card_union_le _ _))
  refine ⟨i,ib,?_⟩
  rw [card_sdiff_of_subset (fun z hz => (mem_outN.mp hz).1)]
  omega

/-- Select the two opposite distinguishing parents with their native
minimality bounds, keeping the weights and labels of the existing model. -/
private theorem priced {q n} (X : Model q n) {t r : ℕ} (tv : t ∈ X.V) (rv : r ∈ X.V) (diff : r ≠ t) :
    ∃ y∈X.V, X.D y t=true ∧ X.D y r=false ∧
      score q X.D X.V X.weights y + (if y=r then X.weights t else 0) ≤
        (∑ j∈X.V, X.weights j) + q*X.weights t := by
  let W : Witness q X.D X.V n :=
    ⟨X.V,Subset.rfl,X.live,X.prime,X.weights,X.positive,X.bounded,X.strict⟩
  have rigid : Rigid W := fun U sub nonempty w pos strong mass =>
    X.minimal X.D U w nonempty (X.free.mono_set sub) pos (mass.trans X.bounded) strong
  obtain ⟨y,yv,yes,no,bound⟩ := distinguishing_parent (X:=W) rigid tv rv diff
  exact ⟨y,mem_of_mem_erase yv,yes,no,bound⟩

/-- Observable facts about ONE row. Its outgoing menu contains exactly its
own target. Its excess exterior mass above the row threshold is controlled
by the weight of that target. The two target labels may overlap the two
distinguishing rows. -/
def Accounts {q n} (X : Model q n) (B : Finset ℕ) (t r s : ℕ) : Prop :=
  let T : Finset ℕ := {t,r}
  let E := X.V \ (B ∪ T)
  let L := ∑ j∈outN X.D E s, X.weights j
  let M := ∑ j∈X.V, X.weights j
  t ∉ B ∧ outN X.D (B ∪ T) s = {t} ∧ outN X.D X.V s = insert t (outN X.D E s) ∧
    M < X.weights s + q*(X.weights t + L) ∧
    X.weights s + q*L + (if s=r then X.weights t else 0) ≤ M

private theorem accounts {q n B s t r} (X : Model q n) (sv : s ∈ X.V) (tv : t ∈ X.V)
    (yes : X.D s t=true) (no : X.D s r=false) (sink : ∀ j ∈ B, ¬X.D s j=true)
    (price : score q X.D X.V X.weights s + (if s=r then X.weights t else 0) ≤
      (∑ j∈X.V, X.weights j) + q*X.weights t) : Accounts X B t r s := by
  classical
  let T : Finset ℕ := {t,r}
  let E := X.V \ (B ∪ T)
  have tin : t ∈ B ∪ T := mem_union_right _ (mem_insert_self _ _)
  have menu : outN X.D (B ∪ T) s={t} := by
    ext j
    constructor
    · intro hj
      obtain ⟨jm,arc⟩ := mem_outN.mp hj
      rcases mem_union.mp jm with jb | jt
      · exact (sink j jb arc).elim
      · rcases mem_insert.mp jt with eq | last
        · exact mem_singleton.mpr eq
        · have e : j=r := mem_singleton.mp last
          exact Bool.noConfusion (no.symm.trans (e ▸ arc))
    · intro single
      obtain rfl := mem_singleton.mp single
      exact mem_outN.mpr ⟨tin,yes⟩
  have partition : outN X.D X.V s = insert t (outN X.D E s) := by
    ext j
    constructor
    · intro hj
      obtain ⟨jv,arc⟩ := mem_outN.mp hj
      by_cases inside : j ∈ B ∪ T
      · have eq := mem_singleton.mp (menu ▸ mem_outN.mpr ⟨inside,arc⟩)
        exact mem_insert.mpr (Or.inl eq)
      · exact mem_insert_of_mem (mem_outN.mpr ⟨mem_sdiff.mpr ⟨jv,inside⟩,arc⟩)
    · intro hj
      rcases mem_insert.mp hj with rfl | tail
      · exact mem_outN.mpr ⟨tv,yes⟩
      · obtain ⟨je,arc⟩ := mem_outN.mp tail
        exact mem_outN.mpr ⟨(mem_sdiff.mp je).1,arc⟩
  have fresh : t ∉ outN X.D E s := fun hit => (mem_sdiff.mp (mem_outN.mp hit).1).2 tin
  have sumEq : score q X.D X.V X.weights s =
      X.weights s + q*(X.weights t + ∑ j∈outN X.D E s, X.weights j) := by
    change X.weights s + q*(∑ j∈X.V, if X.D s j=true then X.weights j else 0) = _
    rw [←sum_filter, show X.V.filter (fun j => X.D s j=true) = outN X.D X.V s from rfl,partition,sum_insert fresh]
  have strict := nat_strict.mp X.strict s sv
  rw [sumEq] at strict price
  rw [Nat.mul_add] at price
  refine ⟨fun h => sink t h yes,menu,partition,strict,?_⟩
  change X.weights s + q*(∑ j∈outN X.D E s, X.weights j) + _ ≤ _
  omega

/-- The same sink has an exact head shortfall and a two-sided exterior
weight bound, for any ordered pair of distinct native vertices. -/
theorem paired_sink {q n} (X : Model q n) (hq : 2≤q) (t r : X.V) (diff : t≠r) :
    ∃ y∈X.V, ∃ z∈X.V, y≠z ∧ X.D y t=true ∧ X.D y r=false ∧
      X.D z r=true ∧ X.D z t=false ∧
      (Accounts X {y,z} t r y ∨ Accounts X {y,z} r t z) := by
  classical
  have ne : t.val≠r.val := fun eq => diff (Subtype.ext eq)
  obtain ⟨y,yv,yt,yr,yp⟩ := priced X t.property r.property (Ne.symm ne)
  obtain ⟨z,zv,zr,zt,zp⟩ := priced X r.property t.property ne
  have distinct : y≠z := fun eq => Bool.noConfusion (yt.symm.trans (eq ▸ zt))
  let B : Finset ℕ := {y,z}
  have sub : B ⊆ X.V := insert_subset yv (singleton_subset_iff.mpr zv)
  have size : B.card ≤ q := by
    have : B.card=2 := by simp [B,distinct]
    omega
  obtain ⟨s,sb,stop⟩ := exists_sink (X.free.mono_set sub) ⟨y,mem_insert_self _ _⟩ size
  refine ⟨y,yv,z,zv,distinct,yt,yr,zr,zt,?_⟩
  rcases mem_insert.mp sb with eq | singled
  · subst s
    exact Or.inl (accounts X yv t.property yt yr stop yp)
  · obtain rfl := mem_singleton.mp singled
    exact Or.inr (accounts X zv r.property zr zt stop zp)

private theorem at_one {q n a b} (X : Model q n) (hq : 2≤q) (bv : b∈X.V) :
    X.D a b=true ↔ PuncturedDistance.depth X.D X.V a b=1 := by
  classical
  by_cases can : ∃ k, Walk X.D X.V a b k
  · rw [PuncturedDistance.depth,dite_eq_left can]
    constructor
    · intro arc
      have cap := Nat.find_min' can (show Walk X.D X.V a b 1 from .step bv arc (.refl b))
      have positive : Nat.find can ≠ 0 := by
        intro eq
        have path : Walk X.D X.V a b 0 := eq ▸ Nat.find_spec can
        cases path
        exact loopfree X.free (by omega) bv arc
      omega
    · intro eq
      have w : Walk X.D X.V a b 1 := eq ▸ Nat.find_spec can
      cases w with | step _ edge rest => cases rest; exact edge
  · have absent : X.D a b≠true := fun edge => can ⟨1,.step bv edge (.refl b)⟩
    simp [PuncturedDistance.depth,can,absent]

/-- At the actual return-position collision, the two selected native
separators avoid the heads of every other mark. One of THESE same rows
also satisfies the two-sided exterior account and has just one menu head. -/
theorem at_collision {q n F B} (X : Model q n) (hq : 2≤q)
    (small : SmallerSmallRow q X.V.card) (step : Boundary X F B)
    (least : LastArcDistanceConflict.Minimum X F B)
    (bad : ¬SmallRow q (graph X.D (insert B F)) X.V)
    (v u₁ u₂ : X.V) (ne : u₁≠u₂)
    (uv₁ : X.D u₁ v=true) (off₁ : graph X.D (insert B F) u₁ v=false)
    (uv₂ : X.D u₂ v=true) (off₂ : graph X.D (insert B F) u₂ v=false)
    {f g : Arc} (fm : f ∈ added X.D F B) (gm : g ∈ added X.D F B) (distinct : f≠g)
    (collision : PuncturedDistance.depth X.D X.V v.val f.1 = PuncturedDistance.depth X.D X.V v.val g.1) :
    ∃ y∈X.V, ∃ z∈X.V, y≠z ∧ X.D y u₁=true ∧ X.D y u₂=false ∧
      X.D z u₂=true ∧ X.D z u₁=false ∧
      (Accounts X {y,z} u₁ u₂ y ∨ Accounts X {y,z} u₂ u₁ z) ∧
      ∀ h∈added X.D F B, h≠f → h≠g → y≠h.2 ∧ z≠h.2 := by
  obtain ⟨y,yv,z,zv,yz,yt,yr,zr,zt,account⟩ := paired_sink X hq u₁ u₂ ne
  refine ⟨y,yv,z,zv,yz,yt,yr,zr,zt,account,?_⟩
  intro h hm hf hg
  have both := LastArcDistanceConflict.common_head_distances X hq small step least bad v fm gm hm distinct hf hg collision
  have equal := (both u₁ uv₁ off₁).trans (both u₂ uv₂ off₂).symm
  have uniform : X.D h.2 u₁=true ↔ X.D h.2 u₂=true := by
    rw [at_one X hq u₁.property, at_one X hq u₂.property, equal]
  constructor
  · rintro rfl
    exact Bool.noConfusion ((uniform.mp yt).symm.trans yr)
  · rintro rfl
    exact Bool.noConfusion ((uniform.mpr zr).symm.trans zt)


/-- The vertex immediately before v when a separator s hits the parent t.
Use the shortcut if present and otherwise keep both labelled arcs. -/
def predecessor (D : CH.Digraph) (s t v : ℕ) := if D s v=true then s else t

/-- The native return from v places the SAME selected separator in one of
two exact distance layers and supplies an induced shortest cycle. -/
theorem return_layer {q n s t v} (X : Model q n) (hq : 2≤q)
    (sv : s∈X.V) (tv : t∈X.V) (vv : v∈X.V) (st : X.D s t=true) (edge : X.D t v=true) :
    let p := predecessor X.D s t v
    ∃ C, ShenCycleSuccessor.Cycle X.D X.V q C ∧ s∈C ∧ v∈C ∧ p∈C ∧ X.D p v=true ∧
      PuncturedDistance.depth X.D X.V v s = (if X.D s v=true then q else q-1) := by
  classical
  intro p
  have last {C k} (cy : ShenCycleSuccessor.Cycle X.D X.V q C) (vc : v∈C) (kc : k∈C)
      (kv : X.D k v=true) : PuncturedDistance.depth X.D X.V v k=q := by
    have ne : v≠k := by rintro rfl; exact loopfree X.free (by omega) vv kv
    obtain ⟨_,cap,front,back⟩ := MandatoryExcursion.segments (by omega) X.free cy vc kc
    simp only [MandatoryExcursion.span,ite_eq_right ne] at cap front back
    have low : ¬ PuncturedDistance.depth X.D X.V v k<q := fun h =>
      X.free v _ (by omega) (by omega) ((front.mono cy.sub).snoc vv kv)
    have nonzero : q+1-PuncturedDistance.depth X.D X.V v k≠0 := by
      intro eq
      rw [eq] at back
      cases back
      exact ne rfl
    omega
  by_cases direct : X.D s v=true
  · obtain ⟨C,cy,sc,vc⟩ := ShortestCycleWeights.edge_cycle X hq sv vv direct
    simpa [p,predecessor,direct] using
      (show ∃ C, ShenCycleSuccessor.Cycle X.D X.V q C ∧ s∈C ∧ v∈C ∧ s∈C ∧ X.D s v=true ∧
        PuncturedDistance.depth X.D X.V v s=q from ⟨C,cy,sc,vc,sc,direct,last cy vc sc direct⟩)
  · obtain ⟨C,cy,sc,tc,vc⟩ := SaturatedCycleClasses.missing hq X.free X.sat sv tv vv st edge direct
    have tne : t≠v := by rintro rfl; exact loopfree X.free (by omega) vv edge
    have rise := PuncturedDistance.rise_on_cycle X.free cy vc sc tc tne st
    have cap := last cy vc tc edge
    have pos : PuncturedDistance.depth X.D X.V v s=q-1 := by omega
    simpa [p,predecessor,direct] using
      (show ∃ C, ShenCycleSuccessor.Cycle X.D X.V q C ∧ s∈C ∧ v∈C ∧ t∈C ∧ X.D t v=true ∧
        PuncturedDistance.depth X.D X.V v s=q-1 from ⟨C,cy,sc,vc,tc,edge,pos⟩)

/-- The two native returns can coincide only if a distinguishing row IS the
opposite original parent. Then the two parents have a labelled arc between
them. This is a sufficient distinctness test on the original parent pair. -/
theorem equal_returns_force_cross {q n v t r y z C} (X : Model q n)
    (cy : ShenCycleSuccessor.Cycle X.D X.V q C) (vc : v∈C)
    (tr : t≠r) (yz : y≠z) (yt : X.D y t=true) (zr : X.D z r=true)
    (pm : predecessor X.D y t v ∈ C) (am : X.D (predecessor X.D y t v) v=true)
    (pn : predecessor X.D z r v ∈ C) (an : X.D (predecessor X.D z r v) v=true) :
    (y=r ∧ X.D r t=true) ∨ (z=t ∧ X.D t r=true) := by
  have eq := card_le_one.mp (cy.incoming v vc).le _ (mem_inN.mpr ⟨pm,am⟩) _ (mem_inN.mpr ⟨pn,an⟩)
  by_cases sy : X.D y v=true <;> by_cases sz : X.D z v=true <;>
    simp [predecessor,sy,sz] at eq
  · exact (yz eq).elim
  · exact Or.inl ⟨eq,eq ▸ yt⟩
  · exact Or.inr ⟨eq.symm,eq.symm ▸ zr⟩
  · exact (tr eq).elim

/-- Both returns use the same v and the two given separator labels. Their
predecessors and distance layers are explicit, including a possible merge. -/
theorem paired_returns {q n v t r y z} (X : Model q n) (hq : 2≤q)
    (vv : v∈X.V) (tv : t∈X.V) (rv : r∈X.V) (yv : y∈X.V) (zv : z∈X.V)
    (tr : t≠r) (yz : y≠z) (yt : X.D y t=true) (zr : X.D z r=true)
    (tarc : X.D t v=true) (rarc : X.D r v=true) :
    ∃ A B, ShenCycleSuccessor.Cycle X.D X.V q A ∧ ShenCycleSuccessor.Cycle X.D X.V q B ∧
      y∈A ∧ v∈A ∧ predecessor X.D y t v∈A ∧ z∈B ∧ v∈B ∧ predecessor X.D z r v∈B ∧
      PuncturedDistance.depth X.D X.V v y=(if X.D y v=true then q else q-1) ∧
      PuncturedDistance.depth X.D X.V v z=(if X.D z v=true then q else q-1) ∧
      (A=B → (y=r ∧ X.D r t=true) ∨ (z=t ∧ X.D t r=true)) := by
  obtain ⟨A,ca,ya,va,pa,ae,dy⟩ := return_layer X hq yv tv vv yt tarc
  obtain ⟨B,cb,zb,vb,pb,be,dz⟩ := return_layer X hq zv rv vv zr rarc
  refine ⟨A,B,ca,cb,ya,va,pa,zb,vb,pb,dy,dz,?_⟩
  rintro rfl
  exact equal_returns_force_cross X ca va tr yz yt zr pa ae pb be


/-- A unit-weight target cannot have the opposite parent as its paid
sink when the native mass and the sink weight agree modulo q. -/
theorem unit_forbids_cross {q n B t r s} (X : Model q n)
    (acc : Accounts X B t r s) (unit : X.weights t=1)
    (residue : Nat.ModEq q (∑j∈X.V, X.weights j) (X.weights s)) : s≠r := by
  intro cross
  obtain ⟨_,_,_,floor,cap⟩ := acc
  let L := ∑j∈outN X.D (X.V \ (B ∪ {t,r})) s, X.weights j
  let M := ∑j∈X.V, X.weights j
  change M < X.weights s + q*(X.weights t+L) at floor
  change X.weights s + q*L + (if s=r then X.weights t else 0) ≤ M at cap
  rw [unit,Nat.mul_add,Nat.mul_one] at floor
  rw [ite_eq_left cross,unit] at cap
  let A := X.weights s + q*L
  let b := M-A
  have split : M=A+b := by dsimp only [A,b]; omega
  have lo : 0<b := by dsimp only [b,A]; omega
  have hi : b<q := by dsimp only [b,A]; omega
  change Nat.ModEq q M (X.weights s) at residue
  rw [split] at residue
  change Nat.ModEq q (X.weights s+q*L+b) (X.weights s) at residue
  rw [Nat.add_right_comm, Nat.add_modulus_mul_modEq_iff] at residue
  have zero := Nat.ModEq.add_left_cancel' (X.weights s)
    (show Nat.ModEq q (X.weights s+b) (X.weights s+0) by simpa using residue)
  change b%q=0%q at zero
  simp [Nat.mod_eq_of_lt hi] at zero
  omega

/-- At two unit-weight parents and native mass 1 modulo q, the paid pair
has distinct native shortest returns even when the parents are adjacent. -/
theorem unit_distinct_returns {q n v} (X : Model q n) (hq : 2≤q) (vv : v∈X.V)
    (t r : X.V) (tr : t≠r) (tarc : X.D t v=true) (rarc : X.D r v=true)
    (ut : X.weights t=1) (ur : X.weights r=1) (phase : Nat.ModEq q (∑j∈X.V, X.weights j) 1) :
    ∃ y∈X.V, ∃ z∈X.V, X.D y t=true ∧ X.D y r=false ∧ X.D z r=true ∧ X.D z t=false ∧
      (Accounts X {y,z} t r y ∨ Accounts X {y,z} r t z) ∧
      ∃ A B, ShenCycleSuccessor.Cycle X.D X.V q A ∧ ShenCycleSuccessor.Cycle X.D X.V q B ∧
        y∈A ∧ v∈A ∧ predecessor X.D y t v∈A ∧ z∈B ∧ v∈B ∧ predecessor X.D z r v∈B ∧ A≠B := by
  obtain ⟨y,yv,z,zv,yz,yt,yr,zr,zt,account⟩ := paired_sink X hq t r tr
  obtain ⟨A,B,ca,cb,ya,va,pa,zb,vb,pb,_,_,merge⟩ :=
    paired_returns X hq vv t.property r.property yv zv (fun e => tr (Subtype.ext e)) yz yt zr tarc rarc
  refine ⟨y,yv,z,zv,yt,yr,zr,zt,account,A,B,ca,cb,ya,va,pa,zb,vb,pb,?_⟩
  intro same
  rcases merge same with ⟨eq,_⟩ | ⟨eq,_⟩
  · rcases account with a | a
    · exact unit_forbids_cross X a ut (by simpa [eq,ur] using phase) eq
    · exact a.1 (eq ▸ mem_insert_self y {z})
  · rcases account with a | a
    · exact a.1 (eq ▸ mem_insert_of_mem (mem_singleton_self z))
    · exact unit_forbids_cross X a ur (by simpa [eq,ut] using phase) eq


/-- If the two returns merge on C, the missing shortcut at their OTHER
distinguishing row supplies a second native shortest cycle. It avoids v,
contains both original parents, and shares a named directed arc with C. -/
theorem merged_alternative {q n v t r y z C} (X : Model q n) (hq : 2≤q)
    (tv : t∈X.V) (rv : r∈X.V) (yv : y∈X.V) (zv : z∈X.V) (tr : t≠r)
    (yt : X.D y t=true) (yr : X.D y r=false) (zr : X.D z r=true) (zt : X.D z t=false)
    (tarc : X.D t v=true) (rarc : X.D r v=true) (yc : y∈C) (zc : z∈C) (vc : v∈C)
    (cross : (y=r ∧ X.D r t=true) ∨ (z=t ∧ X.D t r=true)) :
    ∃ L, ShenCycleSuccessor.Cycle X.D X.V q L ∧ v∉L ∧ L≠C ∧ t∈L ∧ r∈L ∧
      ((z∈C ∩ L ∧ r∈C ∩ L ∧ X.D z r=true) ∨ (y∈C ∩ L ∧ t∈C ∩ L ∧ X.D y t=true)) := by
  have exclude {L} (cy : ShenCycleSuccessor.Cycle X.D X.V q L) (tl : t∈L) (rl : r∈L) :
      v∉L := fun vl => tr (card_le_one.mp (cy.incoming v vl).le _
        (mem_inN.mpr ⟨tl,tarc⟩) _ (mem_inN.mpr ⟨rl,rarc⟩))
  rcases cross with ⟨eq,rt⟩ | ⟨eq,tt⟩
  · obtain ⟨L,cl,zl,rl,tl⟩ := SaturatedCycleClasses.missing hq X.free X.sat zv rv tv zr rt (by simp [zt])
    have nv := exclude cl tl rl
    exact ⟨L,cl,nv,fun same => nv (same ▸ vc),tl,rl,
      Or.inl ⟨mem_inter.mpr ⟨zc,zl⟩,mem_inter.mpr ⟨eq ▸ yc,rl⟩,zr⟩⟩
  · obtain ⟨L,cl,yl,tl,rl⟩ := SaturatedCycleClasses.missing hq X.free X.sat yv tv rv yt tt (by simp [yr])
    have nv := exclude cl tl rl
    exact ⟨L,cl,nv,fun same => nv (same ▸ vc),tl,rl,
      Or.inr ⟨mem_inter.mpr ⟨yc,yl⟩,mem_inter.mpr ⟨eq ▸ zc,tl⟩,yt⟩⟩

/-- At a merge, either the alternative is already in the old family and
certifies the merged cycle as a boundary there, or it is a boundary after
attaching the merged cycle. This uses a shared directed arc on actual labels. -/
theorem merged_boundary {q n v t r y z C F} (X : Model q n) (hq : 2≤q)
    (cy : ShenCycleSuccessor.Cycle X.D X.V q C)
    (tv : t∈X.V) (rv : r∈X.V) (yv : y∈X.V) (zv : z∈X.V) (tr : t≠r)
    (yt : X.D y t=true) (yr : X.D y r=false) (zr : X.D z r=true) (zt : X.D z t=false)
    (tarc : X.D t v=true) (rarc : X.D r v=true)
    (offT : graph X.D F t v=false) (offR : graph X.D F r v=false)
    (yc : y∈C) (zc : z∈C) (vc : v∈C)
    (cross : (y=r ∧ X.D r t=true) ∨ (z=t ∧ X.D t r=true)) :
    ∃ L, ShenCycleSuccessor.Cycle X.D X.V q L ∧ v∉L ∧ t∈L ∧ r∈L ∧
      SharedArcExpansion.Touch X.D C L ∧
      ((L∈F ∧ Boundary X F C) ∨ (L∉F ∧ Boundary X (insert C F) L)) := by
  classical
  obtain ⟨L,cl,vl,ne,tl,rl,arc⟩ := merged_alternative X hq tv rv yv zv tr yt yr zr zt tarc rarc yc zc vc cross
  have touch : SharedArcExpansion.Touch X.D C L := by
    rcases arc with ⟨za,ra,ed⟩ | ⟨ya,ta,ed⟩
    · exact ⟨z,za,r,ra,ed⟩
    · exact ⟨y,ya,t,ta,ed⟩
  have absent : C∉F := by
    intro member
    rcases cross with ⟨eq,_⟩ | ⟨eq,_⟩
    · exact Bool.noConfusion (offR.symm.trans (active.mpr ⟨C,mem_col.mpr ⟨member,eq ▸ yc,vc,rarc⟩⟩))
    · exact Bool.noConfusion (offT.symm.trans (active.mpr ⟨C,mem_col.mpr ⟨member,eq ▸ zc,vc,tarc⟩⟩))
  refine ⟨L,cl,vl,tl,rl,touch,?_⟩
  by_cases member : L∈F
  · exact Or.inl ⟨member,mem_filter.mpr ⟨mem_powerset.mpr cy.sub,cy⟩,absent,L,member,touch.symm⟩
  · exact Or.inr ⟨member,mem_filter.mpr ⟨mem_powerset.mpr cl.sub,cl⟩,
      fun h => (mem_insert.mp h).elim ne member,C,mem_insert_self _ _,touch⟩

#print axioms merged_boundary
#print axioms merged_alternative
#print axioms unit_distinct_returns
#print axioms unit_forbids_cross
#print axioms paired_returns
#print axioms return_layer
#print axioms direct_targets
#print axioms paired_sink
#print axioms at_collision
end LeanCH.BR.Closure.LastArcSeparatorSink

