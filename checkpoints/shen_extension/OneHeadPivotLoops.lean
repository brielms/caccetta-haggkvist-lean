import checkpoints.shen_extension.OneHeadHeavyRows
import checkpoints.shen_extension.UnitStateBoundary

namespace LeanCH.BR.Closure.PivotLoops
open BRq2 BRq3 Finset OneHeadHeavyRows DotOriginalStarReturn

def Normal {U d} (a : UnitRowState U d) :=
  ∀ x ∈ U, x ≠ a.root → (outN a.graph U x).card = d+1

def returns (D : CH.Digraph) (U : Finset ℕ) (y u : ℕ) :=
  (outN D U y).filter (fun z => D z u = true)

private theorem heavy_iff {U d} (a : UnitRowState U d) (norm : Normal a) {x : ℕ} :
    x ∈ heavy a.graph (U.erase a.root) (d+1) ↔
      x ∈ U ∧ x ≠ a.root ∧ a.graph x a.root ≠ true := by
  classical
  rw [heavy,mem_filter,mem_erase,UnitState.outN_erase]
  by_cases xu : x ∈ U
  · by_cases ne : x = a.root
    · simp [ne]
    have count := norm x xu ne
    by_cases edge : a.graph x a.root = true
    · rw [card_erase_of_mem (mem_outN.mpr ⟨a.live,edge⟩),count]
      simp [xu,ne,edge]
    · rw [erase_eq_of_notMem (fun h => edge (mem_outN.mp h).2),count]
      simp [xu,ne,edge]
  · simp [xu]

private theorem row_partition {U d} (a : UnitRowState U d) (norm : Normal a) {y : ℕ}
    (nonparent : a.graph y a.root ≠ true) :
    (outN a.graph (heavy a.graph (U.erase a.root) (d+1)) y).card +
      (returns a.graph U y a.root).card = (outN a.graph U y).card := by
  let L := heavy a.graph (U.erase a.root) (d+1)
  have sub : returns a.graph U y a.root ⊆ outN a.graph U y := filter_subset _ _
  have eq : outN a.graph L y = outN a.graph U y \ returns a.graph U y a.root := by
    ext z
    simp only [mem_outN,mem_sdiff,returns,mem_filter,L,heavy_iff a norm]
    grind
  rw [eq,card_sdiff_add_card_eq_card sub]

/-- y has no edge to the short row, and exactly one two-arc return to it, via t. -/
structure Site {U d} (a : UnitRowState U d) (y t : ℕ) : Prop where
  live : y ∈ U
  distinct : y ≠ a.root
  nonparent : a.graph y a.root ≠ true
  single : returns a.graph U y a.root = {t}

private theorem site_edges {U d} {a : UnitRowState U d} {y t} (site : Site a y t) :
    t ∈ U ∧ a.graph y t = true ∧ a.graph t a.root = true := by
  have hit : t ∈ returns a.graph U y a.root := site.single ▸ mem_singleton_self t
  obtain ⟨h,e⟩ := mem_filter.mp hit
  exact ⟨(mem_outN.mp h).1,(mem_outN.mp h).2,e⟩

theorem border_iff_site {U d} (a : UnitRowState U d) (norm : Normal a) (y : ℕ) :
    Border a y ↔ ∃ t, Site a y t := by
  constructor
  · rintro ⟨hy,degree⟩
    obtain ⟨hyU,ne,no⟩ := (heavy_iff a norm).mp hy
    have parts := row_partition a norm no
    rw [degree,norm y hyU ne] at parts
    obtain ⟨t,eq⟩ := card_eq_one.mp (show (returns a.graph U y a.root).card = 1 by omega)
    exact ⟨t,hyU,ne,no,eq⟩
  · rintro ⟨t,site⟩
    refine ⟨(heavy_iff a norm).mpr ⟨site.live,site.distinct,site.nonparent⟩,?_⟩
    have parts := row_partition a norm site.nonparent
    rw [site.single,card_singleton,norm y site.live site.distinct] at parts
    omega

/-- The actual pivot adds and deletes exactly these two arcs on the carrier. -/
def Turn {U d} (a b : UnitRowState U d) (y t : ℕ) : Prop :=
  b.root = y ∧ b.graph = pivotGraph a.graph U d a.root y ∧
  ∀ x ∈ U, ∀ z ∈ U, b.graph x z = true ↔
    (a.graph x z = true ∧ (x ≠ y ∨ z ≠ t)) ∨ (x = a.root ∧ z = y)

theorem rotate {U d} (O : Origin 3 (d+1)) (small : U.card < O.V.card)
    (a : UnitRowState U d) (norm : Normal a) {y t} (site : Site a y t) :
    ∃ b : UnitRowState U d, Turn a b y t ∧ Normal b ∧ Site b t a.root := by
  classical
  obtain ⟨tU,yt,tu⟩ := site_edges site
  have nt : t ≠ a.root := fun e => loopfree a.free (by decide) a.live (e ▸ tu)
  have ny : y ≠ t := fun e => loopfree a.free (by decide) tU (e ▸ yt)
  have rt : a.graph a.root t ≠ true := digonfree a.free (by decide) tU a.live tu
  have ry : a.graph a.root y ≠ true := fun e => a.free a.root 3 (by decide) (by decide)
    (.step site.live e (.step tU yt (.step a.live tu (.refl _))))
  have ty : a.graph t y ≠ true := digonfree a.free (by decide) site.live tU yt
  have path_unique {z} (hz : z ∈ U) (yz : a.graph y z = true) (zu : a.graph z a.root = true) : z = t := by
    have h : z ∈ returns a.graph U y a.root := mem_filter.mpr ⟨mem_outN.mpr ⟨hz,yz⟩,zu⟩
    rwa [site.single,mem_singleton] at h
  have border := (border_iff_site a norm y).mpr ⟨t,site⟩
  obtain ⟨E,edit,safe,uro,_,yro,full⟩ := move_short_row O a.free small a.live a.short
    a.full border.1 border.2
  let b : UnitRowState U d := ⟨E,y,site.live,safe,by rw [yro]; exact border.2,full⟩
  have bank := eligible_eq_short_heads O a.free small a.live a.short a.full
  have spec (x) (hx : x ∈ U) (z) (hz : z ∈ U) : E x z = true ↔
      (a.graph x z = true ∧ (x ≠ y ∨ z ≠ t)) ∨ (x = a.root ∧ z = y) := by
    have noCross (ux : a.graph a.root x = true) (xz : a.graph x z = true)
        (zu : a.graph z a.root = true) : False := a.free a.root 3 (by decide) (by decide)
      (.step hx ux (.step hz xz (.step a.live zu (.refl _))))
    have uniq := @path_unique z hz
    have noLoop := loopfree a.free (by decide : 1 ≤ 3) a.live
    have diff := site.distinct
    have np := site.nonparent
    rw [edit,pivotGraph,star_edge,bank]
    simp only [mem_erase,mem_sdiff,mem_insert,mem_outN,heavy_iff a norm,hx,hz,true_and,and_true]
    grind
  have nm : Normal b := by
    intro x hx ne
    change (outN E U x).card = d+1
    by_cases eq : x = a.root
    · subst x
      rw [uro,card_insert_of_notMem (fun h => ry (mem_outN.mp h).2),a.short]
    have same : outN E U x = outN a.graph U x := by
      ext z
      simp only [mem_outN]
      by_cases hz : z ∈ U
      · simp [hz,spec x hx z hz,eq,show x ≠ y from ne]
      · simp [hz]
    rw [same,norm x hx eq]
  refine ⟨b,⟨rfl,edit,spec⟩,nm,⟨tU,ny.symm,?_,?_⟩⟩
  · change E t y ≠ true
    intro hit
    rcases (spec t tU y site.live).mp hit with hit | hit
    · exact ty hit.1
    · exact nt hit.1
  · change returns E U t y = {a.root}
    ext z
    simp only [returns,mem_filter,mem_outN,mem_singleton]
    by_cases hz : z ∈ U
    · rw [spec t tU z hz,spec z hz y site.live]
      have no (tz : a.graph t z = true) (zy : a.graph z y = true) : False :=
        a.free y 3 (by decide) (by decide) (.step tU yt (.step hz tz (.step site.live zy (.refl _))))
      grind
    · have ne : z ≠ a.root := fun eq => hz (eq ▸ a.live)
      simp [hz,ne]

#print axioms border_iff_site
#print axioms rotate

/-- States record graphs on U. Values at labels outside U do not define new
vertices of this transition graph. Every edge uses the existing pivot edit. -/
def Pivot {U d} (a b : UnitRowState U d) : Prop :=
  Border a b.root ∧ ∀ x ∈ U, ∀ z ∈ U, b.graph x z = true ↔
    pivotGraph a.graph U d a.root b.root x z = true

private theorem turn_pivot {U d} {a b : UnitRowState U d} {y t}
    (norm : Normal a) (site : Site a y t) (turn : Turn a b y t) : Pivot a b := by
  rw [Pivot,turn.1]
  exact ⟨(border_iff_site a norm y).mpr ⟨t,site⟩,by rw [turn.2.1]; simp⟩

/-- Each allowed normalized border lies on a directed triangle of real pivots.
The third edge restores every arc on U as well as the initial root. -/
theorem three_pivots {U d} (O : Origin 3 (d+1)) (small : U.card < O.V.card)
    (a : UnitRowState U d) (norm : Normal a) {y t} (site : Site a y t) :
    ∃ b c : UnitRowState U d, b.root = y ∧ c.root = t ∧
      Normal b ∧ Normal c ∧ Pivot a b ∧ Pivot b c ∧ Pivot c a ∧
      BR45.inN b.graph U y = insert a.root (BR45.inN a.graph U y) ∧
      BR45.inN c.graph U t = BR45.inN a.graph U t := by
  obtain ⟨b,ab,nb,sb⟩ := rotate O small a norm site
  obtain ⟨c,bc,nc,sc⟩ := rotate O small b nb sb
  obtain ⟨f,cf,_,_⟩ := rotate O small c nc sc
  obtain ⟨tU,yt,tu⟩ := site_edges site
  have ry : a.graph a.root y ≠ true := fun e => a.free a.root 3 (by decide) (by decide)
    (.step site.live e (.step tU yt (.step a.live tu (.refl _))))
  have ne := site.distinct
  have ny : y ≠ t := fun eq => loopfree a.free (by decide) tU (eq ▸ yt)
  have nt : t ≠ a.root := fun eq => loopfree a.free (by decide) a.live (eq ▸ tu)
  have byRoot := ab.1
  have ct := bc.1
  have restore (x) (hx : x ∈ U) (z) (hz : z ∈ U) :
      f.graph x z = true ↔ a.graph x z = true := by
    rw [cf.2.2 x hx z hz,bc.2.2 x hx z hz,ab.2.2 x hx z hz,byRoot,ct]
    grind
  have back : Pivot c a := by
    refine ⟨(border_iff_site c nc a.root).mpr ⟨b.root,sc⟩,?_⟩
    intro x hx z hz
    rw [← cf.2.1]
    exact (restore x hx z hz).symm
  refine ⟨b,c,byRoot,ct,nb,nc,turn_pivot norm site ab,turn_pivot nb sb bc,back,?_,?_⟩
  · ext x
    by_cases hx : x ∈ U
    · simp only [BR45.mem_inN,hx,true_and,mem_insert,ab.2.2 x hx y site.live]
      grind
    · have neq : x ≠ a.root := fun e => hx (e ▸ a.live)
      simp [BR45.mem_inN,hx,neq]
  · ext x
    by_cases hx : x ∈ U
    · simp only [BR45.mem_inN,hx,true_and,bc.2.2 x hx t tU,ab.2.2 x hx t tU,byRoot]
      grind
    · simp [BR45.mem_inN,hx]

/-- Thin each full row independently. The puncture's short row keeps its
degree, and edge deletion preserves the cutoff. -/
theorem normalize {U d} (a : UnitRowState U d) :
    ∃ b : UnitRowState U d, b.root = a.root ∧ Normal b ∧
      ∀ x z, b.graph x z = true → a.graph x z = true := by
  classical
  let n (x : ℕ) := if x = a.root then d else d+1
  have avail (x) (hx : x ∈ U) : n x ≤ (outN a.graph U x).card := by
    by_cases eq : x = a.root
    · simp [n,eq,a.short]
    · simpa [n,eq] using a.full x hx eq
  have choices (x : ℕ) : ∃ S : Finset ℕ, S ⊆ outN a.graph U x ∧ (x ∈ U → S.card = n x) := by
    by_cases hx : x ∈ U
    · obtain ⟨S,sub,count⟩ := exists_subset_card_eq (avail x hx)
      exact ⟨S,sub,fun _ => count⟩
    · exact ⟨∅,empty_subset _,fun h => (hx h).elim⟩
  choose row sub count using choices
  let E : CH.Digraph := fun x z => decide (z ∈ row x)
  have kept (x z) (e : E x z = true) : a.graph x z = true :=
    (mem_outN.mp (sub x (of_decide_eq_true e))).2
  have rows (x) : outN E U x = row x := by
    ext z
    simp only [mem_outN,E,decide_eq_true_eq,and_iff_right_iff_imp]
    exact fun h => outN_subset (sub x h)
  have sr : (outN E U a.root).card = d := by rw [rows,count _ a.live]; simp [n]
  have ns (x) (hx : x ∈ U) (ne : x ≠ a.root) : (outN E U x).card = d+1 := by
    rw [rows,count _ hx]; simp [n,ne]
  exact ⟨⟨E,a.root,a.live,qfree_sub kept a.free,sr,fun x hx ne => (ns x hx ne).ge⟩,
    rfl,ns,kept⟩

/-- Edges of the triples, on normalized graphs. The three-pivot theorem
supplies a triple at every border of every proper normalized unit state. -/
def Rotation {U d} (a b : UnitRowState U d) : Prop :=
  Normal a ∧ Normal b ∧ Pivot a b ∧
    ∃ c, Normal c ∧ Pivot b c ∧ Pivot c a

private theorem triple_edges {U d} {a b c : UnitRowState U d}
    (na : Normal a) (nb : Normal b) (nc : Normal c)
    (ab : Pivot a b) (bc : Pivot b c) (ca : Pivot c a) :
    Rotation a b ∧ Rotation b c ∧ Rotation c a :=
  ⟨⟨na,nb,ab,c,nc,bc,ca⟩,⟨nb,nc,bc,a,na,ca,ab⟩,⟨nc,na,ca,b,nb,ab,bc⟩⟩

theorem symmetric_reach {U d} {a b : UnitRowState U d} (path : Reach Rotation a b) :
    Reach Rotation b a := by
  induction path with
  | refl => exact .refl
  | tail _ edge back =>
    obtain ⟨na,nb,ab,c,nc,bc,ca⟩ := edge
    obtain ⟨_,next,last⟩ := triple_edges na nb nc ab bc ca
    exact (Relation.ReflTransGen.single next).trans ((Relation.ReflTransGen.single last).trans back)

/-- At a maximum over the entire communicating class, the candidate head has
strictly fewer parents and its unique intervening parent has at most as many.
The second comparison uses the second, possibly non-improving, rotation. -/
theorem component_maximum {U d} (O : Origin 3 (d+1)) (small : U.card < O.V.card)
    (start : UnitRowState U d) (ns : Normal start) :
    ∃ a, Reach Rotation start a ∧ Normal a ∧
      (∀ b, Reach Rotation a b →
        (BR45.inN b.graph U b.root).card ≤ (BR45.inN a.graph U a.root).card) ∧
      ∀ y t, Site a y t →
        (BR45.inN a.graph U y).card < (BR45.inN a.graph U a.root).card ∧
        (BR45.inN a.graph U t).card ≤ (BR45.inN a.graph U a.root).card := by
  classical
  let P (k : ℕ) := ∃ a, Reach Rotation start a ∧ Normal a ∧ (BR45.inN a.graph U a.root).card = k
  have bound (a : UnitRowState U d) : (BR45.inN a.graph U a.root).card ≤ U.card :=
    card_le_card (filter_subset _ _)
  have p0 : P (BR45.inN start.graph U start.root).card := ⟨start,.refl,ns,rfl⟩
  obtain ⟨a,pa,na,maximum⟩ := Nat.findGreatest_spec (bound start) p0
  have maxAt (b) (pb : Reach Rotation a b) :
      (BR45.inN b.graph U b.root).card ≤ (BR45.inN a.graph U a.root).card := by
    have nb := invariant_of_reach (inv:=Normal) (fun _ _ _ edge => edge.2.1) na pb
    have hit : P (BR45.inN b.graph U b.root).card := ⟨b,pa.trans pb,nb,rfl⟩
    rw [maximum]
    exact Nat.le_findGreatest (bound b) hit
  refine ⟨a,pa,na,maxAt,?_⟩
  intro y t site
  obtain ⟨b,c,byRoot,ct,nb,nc,ab,bc,ca,gain,same⟩ := three_pivots O small a na site
  obtain ⟨r1,r2,_⟩ := triple_edges na nb nc ab bc ca
  have mb := maxAt b (.single r1)
  have mc := maxAt c ((Relation.ReflTransGen.single r1).tail r2)
  obtain ⟨tU,yt,tu⟩ := site_edges site
  have fresh : a.root ∉ BR45.inN a.graph U y := fun h => a.free a.root 3 (by decide) (by decide)
    (.step site.live (BR45.mem_inN.mp h).2 (.step tU yt (.step a.live tu (.refl _))))
  rw [byRoot,gain,card_insert_of_notMem fresh] at mb
  rw [ct,same] at mc
  exact ⟨by omega,mc⟩

/-- A direct output of the one-head case. First choose a degree-exact subgraph,
then maximize only among states reached by its reversible edits. -/
theorem unit_component {d} (O : Origin 3 (d+1)) {st : State} (valid : Valid O st)
    (proper : st.U.card < O.V.card) (unit : DeficitLevels.total (d+1) st.H st.U = 1) :
    ∃ a b : UnitRowState st.U d, Normal a ∧ (∀ x z, a.graph x z = true → st.H x z = true) ∧
      Reach Rotation a b ∧ Normal b ∧
      (∀ c, Reach Rotation b c →
        (BR45.inN c.graph st.U c.root).card ≤ (BR45.inN b.graph st.U b.root).card) ∧
      ∀ y t, Site b y t →
        (BR45.inN b.graph st.U y).card < (BR45.inN b.graph st.U b.root).card ∧
        (BR45.inN b.graph st.U t).card ≤ (BR45.inN b.graph st.U b.root).card := by
  obtain ⟨u,hu,short,full⟩ := PrivateCompletion.unit_profile unit
  let raw : UnitRowState st.U d := ⟨st.H,u,hu,valid.2.2,by omega,full⟩
  obtain ⟨a,_,na,sub⟩ := normalize raw
  obtain ⟨b,path,nb,maxAt,bounds⟩ := component_maximum O proper a na
  exact ⟨a,b,na,sub,path,nb,maxAt,bounds⟩

#print axioms three_pivots
#print axioms normalize
#print axioms symmetric_reach
#print axioms component_maximum
#print axioms unit_component
end LeanCH.BR.Closure.PivotLoops
