import checkpoints.shen_extension.CrossValueOmissions
import checkpoints.shen_extension.ReturnTargetCycles
import checkpoints.shen_extension.FiniteHorizonHall

namespace LeanCH.BR.Closure.ReturnCycleOmissions
open Finset BRq2 BRq3 BR45 FirstPacketBarrier MarkedCyclePeeling ShenCycleSuccessor
open CrossValueOmissions

/-- Completeness detects any selected return to the root after the two marked arcs. -/
theorem no_selected_return {q D V F p t z} (hq : 2≤q) (free : QFree D V q)
    (complete : ∀M,M∈F ↔ Cycle (graph D F) V q M)
    (pv : p∈V) (tv : t∈V) (zv : z∈V) (pt : graph D F p t=true) (tz : graph D F t z=true)
    (uncovered : z∉(col D F (p,t)).biUnion (fun M=>outN D M t)) :
    p∉ball (graph D F) V z (q-1) := by
  intro hit
  obtain ⟨M,cm,pm,tm,zm⟩ := FiniteHorizonHall.marked_of_port hq
    (qfree_sub (fun _ _=>selected_sub) free) tv (mem_outN.mpr ⟨zv,tz⟩) (mem_inN.mpr ⟨pv,pt⟩) hit
  exact uncovered (mem_biUnion.mpr ⟨M,mem_col.mpr ⟨(complete M).mpr cm,pm,tm,selected_sub pt⟩,
    mem_outN.mpr ⟨zm,selected_sub tz⟩⟩)

/-- On a native return confined to W, cross from a vertex that misses its
remaining time limit to a vertex that can meet it in the selected graph on V. -/
theorem crossing {D G : CH.Digraph} {W V : Finset ℕ} (sub : W⊆V) {p z k}
    (pw : p∈W) (zw : z∈W) (path : Walk D W z p k) (bad : p∉ball G V z k) :
    ∃u∈W,∃v∈W,∃l m, l+m+1=k ∧ Walk D W z u l ∧ D u v=true ∧ Walk D W v p m ∧
      p∉ball G V u (m+1) ∧ p∈ball G V v m ∧ G u v=false := by
  match k, path with
  | 0, .refl _ => exact False.elim (bad (mem_ball.mpr ⟨sub pw,0,le_rfl,.refl _⟩))
  | k+1, .step hw edge tail =>
    rename_i h
    by_cases hit : p∈ball G V h k
    · refine ⟨z,zw,h,hw,0,k,by omega,.refl _,edge,tail,bad,hit,?_⟩
      apply Bool.eq_false_iff.mpr
      intro kept
      obtain ⟨pv,j,le,ret⟩ := mem_ball.mp hit
      exact bad (mem_ball.mpr ⟨pv,j+1,by omega,.step (sub hw) kept ret⟩)
    · obtain ⟨u,uw,v,vw,l,m,eq,pre,uv,suf,miss,reach,off⟩ := crossing sub pw hw tail hit
      exact ⟨u,uw,v,vw,l+1,m,by omega,.step hw edge pre,uv,suf,miss,reach,off⟩
termination_by k

/-- Arcs omitted where a native shortest cycle first has a selected suffix
of the required length. The index counts native steps after the crossing arc. -/
noncomputable def layer (q : ℕ) (D G : CH.Digraph) (V : Finset ℕ) (p k : ℕ) := by
  classical
  exact (lost D G V).filter (fun e=>Walk D V p e.1 (q-k) ∧ Walk D V e.2 p k ∧
    p∉ball G V e.1 (k+1) ∧ p∈ball G V e.2 k)

/-- The first two arcs have tail at the root or at one of its native heads. -/
def initial (D G : CH.Digraph) (V : Finset ℕ) (p : ℕ) :=
  (lost D G V).filter (fun e=>e.1∈insert p (outN D V p))

/-- Applies to each particular carrier W bearing the specified native return. -/
theorem on_carrier {q D V F p t z} (hq : 2≤q) (free : QFree D V q)
    (complete : ∀M,M∈F ↔ Cycle (graph D F) V q M)
    {W : Finset ℕ} (sub : W⊆V) (pw : p∈W) (tw : t∈W) (zw : z∈W)
    (pt : D p t=true) (tz : D t z=true) (path : Walk D W z p (q-1))
    (uncovered : z∉(col D F (p,t)).biUnion (fun M=>outN D M t)) :
    let G := graph D F
    (p,t)∈initial D G V p ∨ (t,z)∈initial D G V p ∨
      ∃k∈range (q-1),∃u∈W,∃v∈W,(u,v)∈layer q D G V p k := by
  classical
  intro G
  cases a : G p t with
  | false => exact Or.inl (mem_filter.mpr ⟨mem_filter.mpr ⟨mem_product.mpr ⟨sub pw,sub tw⟩,pt,a⟩,mem_insert_self ..⟩)
  | true =>
    cases b : G t z with
    | false => exact Or.inr (Or.inl (mem_filter.mpr ⟨mem_filter.mpr ⟨mem_product.mpr ⟨sub tw,sub zw⟩,tz,b⟩,
        mem_insert_of_mem (mem_outN.mpr ⟨sub tw,pt⟩)⟩))
    | true =>
      have bad := no_selected_return hq free complete (sub pw) (sub tw) (sub zw) a b uncovered
      obtain ⟨u,uw,v,vw,l,k,eq,pre,uv,suf,miss,reach,off⟩ := crossing sub pw zw path bad
      refine Or.inr (Or.inr ⟨k,mem_range.mpr (by omega),u,uw,v,vw,?_⟩)
      apply mem_filter.mpr
      refine ⟨mem_filter.mpr ⟨mem_product.mpr ⟨sub uw,sub vw⟩,uv,off⟩,?_,suf.mono sub,miss,reach⟩
      rw [show q-k=l+1+1 by omega]
      exact .step (sub tw) pt (.step (sub zw) tz (pre.mono sub))

/-- The path hypothesis is automatic on every particular native marked cycle. -/
theorem on_cycle {q D V F p t z M} (hq : 2≤q) (free : QFree D V q)
    (complete : ∀N,N∈F ↔ Cycle (graph D F) V q N)
    (cycle : Cycle D V q M) (pm : p∈M) (tm : t∈M) (zm : z∈M)
    (pt : D p t=true) (tz : D t z=true)
    (uncovered : z∉(col D F (p,t)).biUnion (fun N=>outN D N t)) :
    let G := graph D F
    (p,t)∈initial D G V p ∨ (t,z)∈initial D G V p ∨
      ∃k∈range (q-1),∃u∈M,∃v∈M,(u,v)∈layer q D G V p k := by
  have mf := free.mono_set cycle.sub
  have heads (i) (im : i∈M) : ∃h∈M,D i h=true := by
    obtain ⟨h,hh⟩ := card_pos.mp (show 0<(outN D M i).card by rw [cycle.heads i im]; decide)
    exact ⟨h,mem_outN.mp hh⟩
  have ne : p≠z := by
    rintro rfl
    exact mf p 2 (by omega) hq (.step tm pt (.step pm tz (.refl _)))
  obtain ⟨j,pos,room,front,back⟩ := WeightedSD.tight_cycle_complementary_walks mf cycle.size heads pm zm ne
  have short : j≤2 := by
    by_contra! many
    exact mf p (q+1-j+1+1) (by omega) (by omega) (.step tm pt (.step zm tz back))
  have one : j≠1 := by
    rintro rfl
    have hit := (mem_ball_one pm).mp (mem_ball_of_walk front (by rfl) zm)
    have zh := hit.resolve_left ne.symm
    have eq := card_le_one.mp (cycle.heads p pm).le _ zh _ (mem_outN.mpr ⟨tm,pt⟩)
    exact loopfree mf (by omega) tm (eq ▸ tz)
  have ret : Walk D M z p (q-1) := (show q+1-j=q-1 by omega) ▸ back
  exact on_carrier hq free complete cycle.sub pm tm zm pt tz ret uncovered

theorem layers_disjoint {q D G V p i j} (free : QFree D V q) (hi : i<q-1) (hj : j<q-1)
    (ne : i≠j) : Disjoint (layer q D G V p i) (layer q D G V p j) := by
  classical
  have ordered {a b : ℕ} (lt : a<b) (room : b<q-1) :
      Disjoint (layer q D G V p a) (layer q D G V p b) := by
    apply disjoint_left.mpr
    rintro ⟨u,v⟩ ea eb
    obtain ⟨lostArc,_,suf,_,_⟩ := mem_filter.mp ea
    obtain ⟨_,pre,_,_,_⟩ := mem_filter.mp eb
    obtain ⟨inside,uv,_⟩ := mem_filter.mp lostArc
    have loop := pre.append (.step (mem_product.mp inside).2 uv suf)
    exact free p _ (by omega) (by omega) loop
  rcases lt_or_gt_of_ne ne with lt|gt
  · exact ordered lt hj
  · exact (ordered gt hi).symm

theorem initial_disjoint {q D G V p k} (free : QFree D V q) (room : k<q-1) :
    Disjoint (initial D G V p) (layer q D G V p k) := by
  classical
  apply disjoint_left.mpr
  rintro ⟨u,v⟩ first later
  obtain ⟨_,tail⟩ := mem_filter.mp first
  obtain ⟨lostArc,_,suf,_,_⟩ := mem_filter.mp later
  obtain ⟨inside,uv,_⟩ := mem_filter.mp lostArc
  obtain ⟨um,vm⟩ := mem_product.mp inside
  rcases mem_insert.mp tail with eq|head
  · change u=p at eq
    subst u
    exact free p (k+1) (by omega) (by omega) (.step vm uv suf)
  · exact free p (k+1+1) (by omega) (by omega) (.step um (mem_outN.mp head).2 (.step vm uv suf))

/-- All first-arc omissions and all suffix layers share a single budget.
Distinct cycles using the same arc at the same depth are charged only once. -/
theorem total_budget {q D G V p a b c d} (free : QFree D V q)
    (an : ∀i∈V,0≤a i) (bn : ∀j∈V,0≤b j) (gap : cost q a b (lost D G V)=c-d) :
    cost q a b (initial D G V p) + ∑k∈range (q-1),cost q a b (layer q D G V p k) ≤ c-d := by
  classical
  let K := range (q-1)
  let L := layer q D G V p
  have pairs : (K:Set ℕ).PairwiseDisjoint L :=
    fun _ hi _ hj ne=>layers_disjoint free (mem_range.mp hi) (mem_range.mp hj) ne
  have sep : Disjoint (initial D G V p) (K.biUnion L) := by
    apply disjoint_left.mpr
    intro e first later
    obtain ⟨k,hk,inside⟩ := mem_biUnion.mp later
    exact disjoint_left.mp (initial_disjoint free (mem_range.mp hk)) first inside
  have sub : initial D G V p ∪ K.biUnion L ⊆ lost D G V := by
    intro e he
    rcases mem_union.mp he with first|later
    · exact (mem_filter.mp first).1
    · obtain ⟨k,_,hk⟩ := mem_biUnion.mp later
      exact (mem_filter.mp hk).1
  have bound := subset_budget an bn gap sub
  unfold cost at bound ⊢
  rwa [sum_union sep,sum_biUnion pairs] at bound

#print axioms on_carrier
#print axioms on_cycle
#print axioms total_budget
end LeanCH.BR.Closure.ReturnCycleOmissions
