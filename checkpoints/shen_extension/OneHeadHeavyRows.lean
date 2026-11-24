import checkpoints.shen_extension.RecursivePrivateCompletion
import checkpoints.shen_extension.dot_tensor_research.DotOriginalStarReturn_20261118

namespace LeanCH.BR.Closure.OneHeadHeavyRows
open BRq2 BRq3 Finset DotOriginalStarReturn

/-- Rows that meet the new degree already inside the heavy part of the puncture. -/
def heavy (D : CH.Digraph) (W : Finset ℕ) (s : ℕ) :=
  W.filter (fun x => s ≤ (outN D W x).card)

def eligible (D : CH.Digraph) (W : Finset ℕ) (s : ℕ) :=
  (heavy D W s).filter (fun x => s ≤ (outN D (heavy D W s) x).card)

/-- Restore a vertex with all light rows as parents and all eligible rows as heads.
The complete return cut still leaves every eligible row paid. -/
theorem eligible_lt (O : Origin 3 (d+1)) {D : CH.Digraph} {W : Finset ℕ} {v : ℕ}
    (free : QFree D W 3) (fresh : v ∉ W) (small : W.card+1 < O.V.card)
    (deg : ∀ x ∈ W, d ≤ (outN D W x).card) :
    (eligible D W (d+1)).card < d+1 := by
  classical
  let L := heavy D W (d+1)
  let T := W \ L
  let Y := eligible D W (d+1)
  let E := star D W T Y v
  have lw : L ⊆ W := filter_subset _ _
  have tw : T ⊆ W := sdiff_subset
  have yl : Y ⊆ L := filter_subset _ _
  have dis : Disjoint T Y := disjoint_left.mpr (fun _ xt xy => (mem_sdiff.mp xt).2 (yl xy))
  have safe : QFree E (insert v W) 3 := star_qfree free fresh tw (yl.trans lw) dis
  by_contra! enough
  have degree (x) (hx : x ∈ insert v W) : d+1 ≤ (outN E (insert v W) x).card := by
    rcases mem_insert.mp hx with rfl | xw
    · have sub : Y ⊆ outN E (insert x W) x := fun y hy =>
        mem_outN.mpr ⟨mem_insert_of_mem (lw (yl hy)), (star_outgoing fresh tw).mpr hy⟩
      exact enough.trans (card_le_card sub)
    by_cases xy : x ∈ Y
    · have sub : outN D L x ⊆ outN E (insert v W) x := by
        intro z hz
        obtain ⟨zl, edge⟩ := mem_outN.mp hz
        exact mem_outN.mpr ⟨mem_insert_of_mem (lw zl), (star_old_edge fresh xw (lw zl)).mpr
          ⟨edge, Or.inr (fun zt => (mem_sdiff.mp zt).2 zl)⟩⟩
      exact (mem_filter.mp xy).2.trans (card_le_card sub)
    have keep : outN D W x ⊆ outN E (insert v W) x := by
      intro z hz
      obtain ⟨zw, edge⟩ := mem_outN.mp hz
      exact mem_outN.mpr ⟨mem_insert_of_mem zw, (star_old_edge fresh xw zw).mpr ⟨edge, Or.inl xy⟩⟩
    by_cases xl : x ∈ L
    · exact (mem_filter.mp xl).2.trans (card_le_card keep)
    have gain : v ∈ outN E (insert v W) x := mem_outN.mpr
      ⟨mem_insert_self _ _, (star_incoming fresh (yl.trans lw)).mpr (mem_sdiff.mpr ⟨xw,xl⟩)⟩
    have count := card_le_card (insert_subset gain keep)
    rw [card_insert_of_notMem (fun hz => fresh (outN_subset hz))] at count
    have := deg x xw
    omega
  have minimal := O.least E (insert v W) safe degree (insert_nonempty _ _)
  rw [card_insert_of_notMem fresh] at minimal
  omega

/-- In a proper unit state the entire eligible set equals the original short
row's head set. In particular its cardinality is exactly d, in every degree. -/
theorem eligible_eq_short_heads (O : Origin 3 (d+1)) {D : CH.Digraph} {U : Finset ℕ} {u : ℕ}
    (free : QFree D U 3) (small : U.card < O.V.card) (hu : u ∈ U)
    (short : (outN D U u).card = d)
    (full : ∀ x ∈ U, x ≠ u → d+1 ≤ (outN D U x).card) :
    eligible D (U.erase u) (d+1) = outN D U u := by
  classical
  let W := U.erase u
  have eraseRow (x) : outN D W x = (outN D U x).erase u := by
    ext z
    simp only [W, mem_outN, mem_erase]
    tauto
  have after (x) (hx : x ∈ W) (no : D x u ≠ true) : d+1 ≤ (outN D W x).card := by
    rw [eraseRow, erase_eq_of_notMem (fun hit => no (mem_outN.mp hit).2)]
    exact full x (mem_erase.mp hx).2 (mem_erase.mp hx).1
  have deg (x) (hx : x ∈ W) : d ≤ (outN D W x).card := by
    rw [eraseRow]
    have := pred_card_le_card_erase (s := outN D U x) (a := u)
    have := full x (mem_erase.mp hx).2 (mem_erase.mp hx).1
    omega
  have cap := eligible_lt O (free.mono_set (erase_subset u U)) (notMem_erase u U)
    (by rw [card_erase_of_mem hu]; have := card_pos.mpr ⟨u,hu⟩; omega) deg
  have sub : outN D U u ⊆ eligible D W (d+1) := by
    intro b hb
    obtain ⟨bu, ub⟩ := mem_outN.mp hb
    have bw : b ∈ W := mem_erase.mpr ⟨fun e => loopfree free (by omega) hu (e ▸ ub),bu⟩
    have no := digonfree free (by omega) hu bu ub
    have bh := after b bw no
    have kept : outN D W b ⊆ outN D (heavy D W (d+1)) b := by
      intro z hz
      obtain ⟨zw, bz⟩ := mem_outN.mp hz
      have noReturn : D z u ≠ true := fun zu => free u 3 (by omega) (by omega)
        (.step bu ub (.step (mem_erase.mp zw).2 bz (.step hu zu (.refl u))))
      exact mem_outN.mpr ⟨mem_filter.mpr ⟨zw,after z zw noReturn⟩, bz⟩
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨bw,bh⟩,bh.trans (card_le_card kept)⟩
  exact (eq_of_subset_of_card_le sub (by rw [short]; exact Nat.le_of_lt_succ cap)).symm

/-- The input interface of the one-head alternative of the recursive capstone. -/
theorem unit_state_heads (O : Origin 3 (d+1)) {st : State}
    (valid : Valid O st) (proper : st.U.card < O.V.card)
    (unit : DeficitLevels.total (d+1) st.H st.U = 1) :
    ∃ u ∈ st.U, (outN st.H st.U u).card = d ∧
      eligible st.H (st.U.erase u) (d+1) = outN st.H st.U u := by
  obtain ⟨u,hu,short,full⟩ := PrivateCompletion.unit_profile unit
  have count : (outN st.H st.U u).card = d := by omega
  exact ⟨u,hu,count,eligible_eq_short_heads O valid.2.2 proper hu count full⟩

#print axioms eligible_lt
#print axioms eligible_eq_short_heads
#print axioms unit_state_heads

/-- The graph edit used when moving the shortfall from u to y. -/
noncomputable def pivotGraph (D : CH.Digraph) (U : Finset ℕ) (d u y : ℕ) : CH.Digraph :=
  let W := U.erase u
  star D W (W \ heavy D W (d+1)) (insert y (eligible D W (d+1))) u

/-- A heavy row with exactly d heavy heads can take over the unique shortfall
on the same carrier. The former short row gains a head. -/
theorem move_short_row (O : Origin 3 (d+1)) {D : CH.Digraph} {U : Finset ℕ} {u y : ℕ}
    (free : QFree D U 3) (small : U.card < O.V.card) (hu : u ∈ U)
    (short : (outN D U u).card = d)
    (full : ∀ x ∈ U, x ≠ u → d+1 ≤ (outN D U x).card)
    (hy : y ∈ heavy D (U.erase u) (d+1))
    (border : (outN D (heavy D (U.erase u) (d+1)) y).card = d) :
    ∃ E : CH.Digraph, E = pivotGraph D U d u y ∧ QFree E U 3 ∧
      outN E U u = insert y (outN D U u) ∧
      BR45.inN E U y = insert u (BR45.inN D U y) ∧
      outN E U y = outN D (heavy D (U.erase u) (d+1)) y ∧
      ∀ x ∈ U, x ≠ y → d+1 ≤ (outN E U x).card := by
  classical
  let W := U.erase u
  let L := heavy D W (d+1)
  let T := W \ L
  let B := eligible D W (d+1)
  let Y := insert y B
  let E := star D W T Y u
  have lw : L ⊆ W := filter_subset _ _
  have bl : B ⊆ L := filter_subset _ _
  have tw : T ⊆ W := sdiff_subset
  have yl : Y ⊆ L := insert_subset hy bl
  have yw := yl.trans lw
  have fresh : u ∉ W := notMem_erase _ _
  have carrier : insert u W = U := insert_erase hu
  have bank : B = outN D U u := eligible_eq_short_heads O free small hu short full
  have outside : y ∉ B := by
    intro h
    have le : d+1 ≤ (outN D L y).card := (mem_filter.mp h).2
    change (outN D L y).card = d at border
    omega
  have safe : QFree E U 3 := carrier ▸ star_qfree (free.mono_set (erase_subset u U)) fresh tw yw
    (disjoint_left.mpr (fun _ xt xy => (mem_sdiff.mp xt).2 (yl xy)))
  have urow : outN E U u = Y := by
    ext z
    exact ⟨fun h => (star_outgoing fresh tw).mp (mem_outN.mp h).2,
      fun h => mem_outN.mpr ⟨(mem_erase.mp (yw h)).2,(star_outgoing fresh tw).mpr h⟩⟩
  have target (x) (xy : x ∈ Y) : outN E U x = outN D L x := by
    ext z
    have xw := yw xy
    constructor
    · intro h
      obtain ⟨zu,xz⟩ := mem_outN.mp h
      have zw : z ∈ W := mem_erase.mpr ⟨by
        rintro rfl
        exact (mem_sdiff.mp ((star_incoming fresh yw).mp xz)).2 (yl xy),zu⟩
      obtain ⟨old,cut⟩ := (star_old_edge fresh xw zw).mp xz
      have zl : z ∈ L := by
        by_contra no
        exact (cut.resolve_left (not_not.mpr xy)) (mem_sdiff.mpr ⟨zw,no⟩)
      exact mem_outN.mpr ⟨zl,old⟩
    · intro h
      obtain ⟨zl,xz⟩ := mem_outN.mp h
      exact mem_outN.mpr ⟨(mem_erase.mp (lw zl)).2,(star_old_edge fresh xw (lw zl)).mpr
        ⟨xz,Or.inr (fun zt => (mem_sdiff.mp zt).2 zl)⟩⟩
  have parents : BR45.inN E U y = insert u (BR45.inN D U y) := by
    ext x
    by_cases eq : x = u
    · subst x
      have hit : E u y = true := (star_outgoing fresh tw).mpr (mem_insert_self y B)
      simp [BR45.mem_inN, hu, hit]
    · have old (hx : x ∈ U) : E x y = true ↔ D x y = true := by
        rw [star_old_edge fresh (mem_erase.mpr ⟨eq,hx⟩ : x ∈ W) (lw hy)]
        exact ⟨And.left, fun a => ⟨a,Or.inr (fun yt => (mem_sdiff.mp yt).2 hy)⟩⟩
      simp only [BR45.mem_inN,mem_insert,eq,false_or]
      exact ⟨fun h => ⟨h.1,(old h.1).mp h.2⟩,fun h => ⟨h.1,(old h.1).mpr h.2⟩⟩
  refine ⟨E,rfl,safe,by simpa only [Y, bank] using urow,parents,target y (mem_insert_self _ _),?_⟩
  intro x xu ne
  by_cases eq : x = u
  · subst x
    rw [urow,show Y = insert y B from rfl,card_insert_of_notMem outside,bank,short]
  have xw : x ∈ W := mem_erase.mpr ⟨eq,xu⟩
  by_cases xb : x ∈ B
  · rw [target x (mem_insert_of_mem xb)]
    exact (mem_filter.mp xb).2
  have notY : x ∉ Y := fun hit => xb ((mem_insert.mp hit).resolve_left ne)
  have keep : outN D W x ⊆ outN E U x := by
    intro z hz
    obtain ⟨zw,xz⟩ := mem_outN.mp hz
    exact mem_outN.mpr ⟨(mem_erase.mp zw).2,(star_old_edge fresh xw zw).mpr ⟨xz,Or.inl notY⟩⟩
  by_cases xl : x ∈ L
  · exact (mem_filter.mp xl).2.trans (card_le_card keep)
  have gain : u ∈ outN E U x := mem_outN.mpr
    ⟨hu,(star_incoming fresh yw).mpr (mem_sdiff.mpr ⟨xw,xl⟩)⟩
  have count := card_le_card (insert_subset gain keep)
  rw [card_insert_of_notMem (fun hz => fresh (outN_subset hz))] at count
  have old : outN D W x = (outN D U x).erase u := by
    ext z
    simp only [W, mem_outN, mem_erase]
    tauto
  rw [old] at count
  have := pred_card_le_card_erase (s := outN D U x) (a := u)
  have := full x xu eq
  omega

#print axioms move_short_row

/-- States and edges on one carrier for the recursive triangle branch. -/
structure UnitRowState (U : Finset ℕ) (d : ℕ) where
  graph : CH.Digraph
  root : ℕ
  live : root ∈ U
  free : QFree graph U 3
  short : (outN graph U root).card = d
  full : ∀ x ∈ U, x ≠ root → d+1 ≤ (outN graph U x).card

def Border {U d} (a : UnitRowState U d) (y : ℕ) : Prop :=
  let L := heavy a.graph (U.erase a.root) (d+1)
  y ∈ L ∧ (outN a.graph L y).card = d

def ImprovingPivot {U d} (a b : UnitRowState U d) : Prop :=
  Border a b.root ∧ b.graph = pivotGraph a.graph U d a.root b.root ∧
    (BR45.inN a.graph U a.root).card < (BR45.inN b.graph U b.root).card

/-- From every unit state there is a finite sequence of the actual star edits
to a state where every potential replacement has strictly fewer parents than
the short row. The maximizing set is restricted to reachable states. -/
theorem reachable_parent_maximum (O : Origin 3 (d+1)) {U : Finset ℕ}
    (small : U.card < O.V.card) (start : UnitRowState U d) :
    ∃ a, Reach ImprovingPivot start a ∧ ∀ y, Border a y →
      (BR45.inN a.graph U y).card < (BR45.inN a.graph U a.root).card := by
  classical
  let P (k : ℕ) := ∃ a, Reach ImprovingPivot start a ∧ (BR45.inN a.graph U a.root).card = k
  have bound (D : CH.Digraph) (x) : (BR45.inN D U x).card ≤ U.card :=
    card_le_card (filter_subset _ _)
  have initial : P (BR45.inN start.graph U start.root).card := ⟨start,.refl,rfl⟩
  obtain ⟨a,path,maximal⟩ := Nat.findGreatest_spec (bound _ _) initial
  refine ⟨a,path,?_⟩
  intro y border
  by_contra! larger
  obtain ⟨E,edit,safe,_,parents,row,full⟩ :=
    move_short_row O a.free small a.live a.short a.full border.1 border.2
  have yU : y ∈ U := (mem_erase.mp (mem_filter.mp border.1).1).2
  let b : UnitRowState U d := ⟨E,y,yU,safe,by rw [row]; exact border.2,full⟩
  have outside : a.root ∉ BR45.inN a.graph U y := by
    intro hit
    have head := mem_outN.mpr ⟨yU,(BR45.mem_inN.mp hit).2⟩
    rw [← eligible_eq_short_heads O a.free small a.live a.short a.full] at head
    have hi : d+1 ≤ (outN a.graph (heavy a.graph (U.erase a.root) (d+1)) y).card :=
      (mem_filter.mp head).2
    have lo := border.2
    omega
  have gain : (BR45.inN b.graph U b.root).card = (BR45.inN a.graph U y).card + 1 := by
    change (BR45.inN E U y).card = _
    rw [parents,card_insert_of_notMem outside]
  have step : ImprovingPivot a b := ⟨border,edit,by omega⟩
  have next : P (BR45.inN b.graph U b.root).card := ⟨b,path.tail step,rfl⟩
  have := Nat.le_findGreatest (bound _ _) next
  omega

#print axioms reachable_parent_maximum

/-- At a reachable stop, every heavy nonhead with at least the root's indegree
points to two distinct light rows in the puncture. -/
theorem reachable_double_cover (O : Origin 3 (d+1)) {U : Finset ℕ}
    (small : U.card < O.V.card) (start : UnitRowState U d) :
    ∃ a, Reach ImprovingPivot start a ∧
      let W := U.erase a.root
      let L := heavy a.graph W (d+1)
      ∀ y ∈ L, y ∉ outN a.graph U a.root →
        (BR45.inN a.graph U a.root).card ≤ (BR45.inN a.graph U y).card →
        2 ≤ (outN a.graph (W \ L) y).card := by
  classical
  obtain ⟨a,path,stop⟩ := reachable_parent_maximum O small start
  refine ⟨a,path,?_⟩
  intro W L y yl nonhead high
  have bank := eligible_eq_short_heads O a.free small a.live a.short a.full
  have below : (outN a.graph L y).card < d+1 := by
    by_contra! le
    apply nonhead
    rw [← bank]
    exact mem_filter.mpr ⟨yl,le⟩
  have ne : (outN a.graph L y).card ≠ d := fun eq =>
    (Nat.not_lt_of_ge high) (stop y ⟨yl,eq⟩)
  have full : d+1 ≤ (outN a.graph W y).card := (mem_filter.mp yl).2
  have sub : outN a.graph L y ⊆ outN a.graph W y := by
    intro z hz
    exact mem_outN.mpr ⟨(mem_filter.mp (mem_outN.mp hz).1).1,(mem_outN.mp hz).2⟩
  have diff : outN a.graph (W \ L) y = outN a.graph W y \ outN a.graph L y := by
    ext z
    simp only [mem_sdiff,mem_outN]
    tauto
  rw [diff,card_sdiff_of_subset sub]
  omega

#print axioms reachable_double_cover
end LeanCH.BR.Closure.OneHeadHeavyRows
