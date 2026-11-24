import checkpoints.shen_extension.PunctureReceiverFrontier

namespace LeanCH.BR.Closure.MandatoryTwoStep
open Finset BRq2 BRq3 BR45 ShenCycleSuccessor ShortestCycleWeights RootedSplice

/-- Inclusion of two columns in the cycle-versus-vertex incidence matrix. -/
def Forces (D : CH.Digraph) (V : Finset ℕ) (q u v : ℕ) :=
  ∀ C, Cycle D V q C → u∈C → v∈C

theorem forces_iff {D V q u v} : Forces D V q u v ↔ ¬Covered D V q v u := by
  classical
  constructor
  · rintro f ⟨C,c,uc⟩
    have big : Cycle D V q C := ⟨c.sub.trans (erase_subset _ _),c.size,c.heads,c.incoming⟩
    exact (mem_erase.mp (c.sub (f C big uc))).1 rfl
  · intro no C c uc
    by_contra miss
    exact no ⟨C,⟨fun z zc => mem_erase.mpr ⟨fun e => miss (e ▸ zc),c.sub zc⟩,
      c.size,c.heads,c.incoming⟩,uc⟩

private theorem next_head {q D V} (hq : 2≤q) (free : QFree D V q)
    (witness : ∀ {x y},x∈V → y∈V → D x y=true → ∃C,Cycle D V q C ∧ x∈C ∧ y∈C) {u a v x}
    (uv : u∈V) (av : a∈V) (vv : v∈V) (xv : x∈V)
    (ua : D u a=true) (atv : D a v=true) (ux : D u x=true)
    (forced : Forces D V q u v) : D x v=true := by
  have distinct : u≠v := by
    rintro rfl
    exact free u 2 (by decide) hq (.step av ua (.step uv atv (.refl _)))
  have short : ¬D u v=true := by
    intro direct
    obtain ⟨C,c,uc,ac⟩ := witness uv av ua
    have vc := forced C c uc
    have same := card_le_one.mp (c.heads u uc).le _ (mem_outN.mpr ⟨ac,ua⟩) _ (mem_outN.mpr ⟨vc,direct⟩)
    exact loopfree free (by omega) vv (same ▸ atv)
  obtain ⟨C,c,uc,xc⟩ := witness uv xv ux
  have vc := forced C c uc
  have heads (z) (zc : z∈C) : ∃y∈C,D z y=true := by
    obtain ⟨y,yh⟩ := card_pos.mp (show 0<(outN D C z).card by rw [c.heads z zc]; decide)
    exact ⟨y,mem_outN.mp yh⟩
  obtain ⟨d,lo,hi,path,back⟩ := WeightedSD.tight_cycle_complementary_walks
    (free.mono_set c.sub) c.size heads uc vc distinct
  have bound : d≤2 := by
    by_contra! greater
    exact free u ((q+1-d)+2) (by omega) (by omega)
      (.step av ua (.step vv atv (back.mono c.sub)))
  have two : d=2 := by
    by_contra ne
    have one : d=1 := by omega
    subst d
    cases path with
    | step _ first tail => cases tail; exact short first
  subst d
  cases path with
  | step zm first tail =>
    obtain rfl := card_le_one.mp (c.heads u uc).le _ (mem_outN.mpr ⟨zm,first⟩) _ (mem_outN.mpr ⟨xc,ux⟩)
    cases tail with
    | step _ second last => cases last; exact second

/-- The entire first layer is a module and primeness makes it a singleton.
The unique intermediate vertex also has a unique head. Only the forward
inclusion of cycle columns is required. -/
theorem graph_corridor {q D V} (hq : 2≤q) (free : QFree D V q)
    (sat : BRsub.Sat q D V) (prime : ShenPrimeTransition.Prime D V)
    (witness : ∀ {x y},x∈V → y∈V → D x y=true → ∃C,Cycle D V q C ∧ x∈C ∧ y∈C) {u a v}
    (uv : u∈V) (av : a∈V) (vv : v∈V)
    (ua : D u a=true) (atv : D a v=true) (forced : Forces D V q u v) :
    outN D V u={a} ∧ outN D V a={v} := by
  classical
  let A := outN D V u
  have sub : A⊆V := fun _ zA => (mem_outN.mp zA).1
  have all (x) (xA : x∈A) := next_head hq free witness uv av vv (sub xA) ua atv (mem_outN.mp xA).2 forced
  have target (x) (xA : x∈A) (z) (zv : z∈V) (away : z∉A) (xz : D x z=true) : z=v := by
    have miss : ¬D u z=true := fun uz => away (mem_outN.mpr ⟨zv,uz⟩)
    obtain ⟨C,c,uc,xc,zc⟩ := SaturatedCycleClasses.missing hq free sat uv (sub xA) zv
      (mem_outN.mp xA).2 xz miss
    exact card_le_one.mp (c.heads x xc).le _ (mem_outN.mpr ⟨zc,xz⟩) _
      (mem_outN.mpr ⟨forced C c uc,all x xA⟩)
  have uniform : BRsub.OutUniform D V A := by
    intro x xA y yA z zv away
    apply Bool.eq_iff_iff.mpr
    exact ⟨fun edge => (target x xA z zv away edge).symm ▸ all y yA,
      fun edge => (target y yA z zv away edge).symm ▸ all x xA⟩
  have noSelf : u∉A := fun hu => loopfree free (by omega) uv (mem_outN.mp hu).2
  have proper : A≠V := fun eq => noSelf (eq ▸ uv)
  have small : A.card≤1 := by
    by_contra! many
    exact prime A sub many proper ⟨uniform,BRsub.outUniform_inUniform free sat sub uniform⟩
  have aA : a∈A := mem_outN.mpr ⟨av,ua⟩
  have singleton : A={a} := by
    ext z
    exact ⟨fun hz => mem_singleton.mpr (card_le_one.mp small _ hz _ aA),fun hz => mem_singleton.mp hz ▸ aA⟩
  refine ⟨singleton,?_⟩
  ext z
  constructor
  · intro za
    have az := (mem_outN.mp za).2
    have away : z∉A := by
      rw [singleton]
      intro eq
      exact loopfree free (by omega) av (mem_singleton.mp eq ▸ az)
    exact mem_singleton.mpr (target a aA z (mem_outN.mp za).1 away az)
  · intro eq
    exact mem_singleton.mp eq ▸ mem_outN.mpr ⟨vv,atv⟩

theorem unique_corridor {q n} (X : Model q n) (hq : 2≤q) {u a v}
    (uv : u∈X.V) (av : a∈X.V) (vv : v∈X.V)
    (ua : X.D u a=true) (atv : X.D a v=true) (forced : Forces X.D X.V q u v) :
    outN X.D X.V u={a} ∧ outN X.D X.V a={v} :=
  graph_corridor hq X.free X.sat X.prime (edge_cycle X hq) uv av vv ua atv forced

private theorem reverse_cycle {D : CH.Digraph} {V q C} (c : Cycle D V q C) : Cycle (fun u v => D v u) V q C :=
  ⟨c.sub,c.size,c.incoming,c.heads⟩

/-- The dual geometric corridor uses the same support and the same cycle columns.
Only the unweighted hypotheses are reversed. -/
theorem unique_incoming {q n} (X : Model q n) (hq : 2≤q) {u a v}
    (uv : u∈X.V) (av : a∈X.V) (vv : v∈X.V)
    (ua : X.D u a=true) (atv : X.D a v=true) (forced : Forces X.D X.V q v u) :
    inN X.D X.V v={a} ∧ outN X.D X.V a={v} := by
  let E : CH.Digraph := fun x y => X.D y x
  have prime : ShenPrimeTransition.Prime E X.V := fun K sub sz ne both => X.prime K sub sz ne ⟨both.2,both.1⟩
  have wit {x y} (xv : x∈X.V) (yv : y∈X.V) (arc : E x y=true) : ∃C,Cycle E X.V q C ∧ x∈C ∧ y∈C := by
    obtain ⟨C,c,yc,xc⟩ := edge_cycle X hq yv xv arc
    exact ⟨C,reverse_cycle c,xc,yc⟩
  have revf : Forces E X.V q v u := fun C c hit => forced C (reverse_cycle c) hit
  obtain ⟨first,_⟩ := graph_corridor hq X.free.reverse (WeightedSD.SerialChain.sat_reverse X.sat) prime wit vv av uv atv ua revf
  change inN X.D X.V v={a} at first
  refine ⟨first,?_⟩
  ext y
  constructor
  · intro ay
    by_contra miss
    have ne : y≠v := fun e => miss (mem_singleton.mpr e)
    obtain ⟨p,pv,pt,py⟩ := X.separated v vv y (mem_outN.mp ay).1 ne
    have pa : p∈inN X.D X.V v := mem_inN.mpr ⟨pv,pt⟩
    rw [first] at pa
    obtain rfl := mem_singleton.mp pa
    have yes := (mem_outN.mp ay).2
    rw [py] at yes
    contradiction
  · intro e
    exact mem_singleton.mp e ▸ mem_outN.mpr ⟨vv,atv⟩

/-- Every vertex two arcs upstream of a minimum root has a retained
shortest-cycle witness after deleting the root. No size threshold. -/
theorem upstream_covered {q n} (X : Model q n) (hq : 2≤q) {u a h}
    (uv : u∈X.V) (av : a∈X.V) (hv : h∈X.V)
    (minimum : ∀z∈X.V,X.weights h≤X.weights z)
    (ua : X.D u a=true) (ah : X.D a h=true) : Covered X.D X.V q h u := by
  by_contra absent
  obtain ⟨_,one⟩ := unique_corridor X hq uv av hv ua ah (forces_iff.mpr absent)
  have aw : a∈X.V.erase h := mem_erase.mpr ⟨by rintro rfl; exact loopfree X.free (by omega) av ah,av⟩
  obtain ⟨C,c,_,_⟩ := edge_cycle X hq av hv ah
  have size := c.size ▸ card_le_card c.sub
  obtain ⟨B,b,aB⟩ := PunctureWeightCoverage.parent_covered X hq aw minimum size ah
  obtain ⟨z,zh⟩ := card_pos.mp (show 0<(outN X.D B a).card by rw [b.heads a aB]; decide)
  obtain ⟨zm,az⟩ := mem_outN.mp zh
  have zv := mem_erase.mp (b.sub zm)
  have zfull : z∈outN X.D X.V a := mem_outN.mpr ⟨zv.2,az⟩
  rw [one] at zfull
  exact zv.1 (mem_singleton.mp zfull)

/-- The whole backward ball of radius two, with the deleted root removed,
is covered. The statement has no order, degree or support-size split. -/
theorem ball_covered {q n} (X : Model q n) (hq : 2≤q) {u h}
    (uv : u∈X.V) (hv : h∈X.V) (uh : u≠h)
    (minimum : ∀z∈X.V,X.weights h≤X.weights z) (reach : h∈ball X.D X.V u 2) :
    Covered X.D X.V q h u := by
  obtain ⟨_,k,bound,path⟩ := mem_ball.mp reach
  cases path with
  | refl => exact (uh rfl).elim
  | step av ua tail =>
    cases tail with
    | refl =>
      obtain ⟨C,c,_,_⟩ := edge_cycle X hq uv hv ua
      exact PunctureWeightCoverage.parent_covered X hq (mem_erase.mpr ⟨uh,uv⟩) minimum
        (c.size ▸ card_le_card c.sub) ua
    | step _ ah last =>
      cases last with
      | refl => exact upstream_covered X hq uv av hv minimum ua ah
      | step => omega

theorem from_input {n r q D} (hn : 0<n) (hq : 2≤q) (order : n≤q*r)
    (loop : CH.Loopless D n) (degree : CH.MinOutdegreeAtLeast D n r)
    (no : ¬CH.HasDirectedCycleAtMost D n q) :
    ∃X : Model q n, ∀h∈X.V,(∀z∈X.V,X.weights h≤X.weights z) →
      ∀u∈X.V,u≠h → h∈ball X.D X.V u 2 → Covered X.D X.V q h u := by
  obtain ⟨X⟩ := normalize hq hn order loop degree no
  exact ⟨X,fun _ hv min _ uv ne reach => ball_covered X hq uv hv ne min reach⟩

#print axioms unique_incoming
#print axioms ball_covered
#print axioms from_input
#print axioms unique_corridor
#print axioms upstream_covered
end LeanCH.BR.Closure.MandatoryTwoStep
