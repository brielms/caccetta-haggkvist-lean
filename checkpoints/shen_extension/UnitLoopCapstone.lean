import checkpoints.shen_extension.UnitBatchComponents
import checkpoints.shen_extension.PivotLoopNativeOrder
import checkpoints.shen_extension.FourLabelRecursiveHost
import checkpoints.shen_extension.SponsoredHeadPool
import checkpoints.shen_extension.FreeSecondHeadGap

namespace LeanCH.BR.Closure.UnitLoopCapstone
open BRq2 BRq3 DeficitLevels PackingFrontier PrivateCompletion OneHeadHeavyRows PivotLoops

/-- Deleting any one marked vertex is enough. Even sets containing only one
triangle label trigger the contraction test. -/
def MarkedTests (U : Finset ℕ) (d : ℕ) (H : CH.Digraph) (A : Finset ℕ) : Prop :=
  ∀ v ∈ A,
    (∃ x ∈ U.erase v, (BR45.inN H U x).card < d+1 ∧
      (d+1 ≤ (BR45.inN H U x).card+1 → H x v = true)) ∧
    (∀ w ∈ U, w ≠ v → ∃ x ∈ (U.erase v).erase w, H x v = true ∧ H x w = true) ∧
    ∀ S ⊆ U, v ∈ S → 3 ≤ S.card → (∀ x ∈ U \ S, (outN H S x).card < S.card) →
      2*d+3 ≤ (PivotContraction.grow H U (PivotContraction.grow H U S)).card

/-- Specializing the contraction to a marked vertex and all its parents
forces two multiple-return targets behind a single non-triangle head. -/
theorem marked_return_fan {U A d} {H : CH.Digraph} {v y t : ℕ}
    (tests : MarkedTests U d H A) (mark : v ∈ A) (size : U.card = 3*d+2)
    (oriented : QFree H U 2) (puncture : QFree H (U.erase y) 3)
    (vU : v ∈ U) (yU : y ∈ U) (tU : t ∈ U) (vy : H v y = true) (tv : H t v = true)
    (degree : (outN H U v).card = d+1) :
    let S := insert v (BR45.inN H U v)
    ∃ h ∈ outN H U v, h ≠ y ∧ 2 ≤ (outN H (PivotContraction.grow H U S \ S) h).card := by
  classical
  intro S
  let I := BR45.inN H U v
  let F := PivotContraction.grow H U S
  let FF := PivotContraction.grow H U F
  have isub : I ⊆ U := Finset.filter_subset _ _
  have sub : S ⊆ U := Finset.insert_subset vU isub
  have vI : v ∉ I := fun hit => loopfree oriented (by decide) vU (BR45.mem_inN.mp hit).2
  have ne : t ≠ v := fun eq => loopfree oriented (by decide) vU (eq ▸ tv)
  have vyne : v ≠ y := fun eq => loopfree oriented (by decide) yU (eq ▸ vy)
  obtain ⟨x,hx,xv,_⟩ := (tests v mark).2.1 t tU ne
  have two : ({x,t} : Finset ℕ) ⊆ I := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl|hz
    · exact BR45.mem_inN.mpr ⟨(Finset.mem_erase.mp (Finset.mem_erase.mp hx).2).2,xv⟩
    · rw [Finset.mem_singleton.mp hz]
      exact BR45.mem_inN.mpr ⟨tU,tv⟩
  have twoI := Finset.card_le_card two
  rw [Finset.card_pair (Finset.mem_erase.mp hx).1] at twoI
  have three : 3 ≤ S.card := by change 3 ≤ (insert v I).card; rw [Finset.card_insert_of_notMem vI]; omega
  have misses (z) (hz : z ∈ U \ S) : (outN H S z).card < S.card := by
    have notIn := (Finset.mem_sdiff.mp hz).2
    have zv : H z v ≠ true := fun edge => notIn
      (Finset.mem_insert_of_mem (BR45.mem_inN.mpr ⟨(Finset.mem_sdiff.mp hz).1,edge⟩))
    apply Finset.card_lt_card
    exact ⟨outN_subset,fun cover => zv (mem_outN.mp (cover (Finset.mem_insert_self v I))).2⟩
  have growth : 2*d+3 ≤ FF.card := (tests v mark).2.2 S sub (Finset.mem_insert_self v I) three misses
  have ffsub : FF ⊆ U := Finset.filter_subset _ _
  have rest := Finset.card_sdiff_add_card_eq_card ffsub
  obtain ⟨h,head,ny,high⟩ : ∃ h ∈ outN H U v, h ≠ y ∧ h ∈ FF := by
    by_contra! none
    have hs : outN H U v ⊆ insert y (U \ FF) := by
      intro z hz
      by_cases eq : z = y
      · exact eq ▸ Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Finset.mem_sdiff.mpr ⟨outN_subset hz,none z hz eq⟩)
    have le := (Finset.card_le_card hs).trans (Finset.card_insert_le _ _)
    omega
  obtain ⟨hU,vh⟩ := mem_outN.mp head
  have hv := digonfree oriented (by decide) vU hU vh
  have hnot : h ∉ S := by
    intro mem
    rcases Finset.mem_insert.mp mem with rfl|hi
    · exact loopfree oriented (by decide) vU vh
    · exact hv (BR45.mem_inN.mp hi).2
  have sf : S ⊆ F := fun z hz => Finset.mem_filter.mpr ⟨sub hz,Or.inl hz⟩
  have paid : 2 ≤ (outN H F h).card := by
    rcases (Finset.mem_filter.mp high).2 with earlier | later
    · have low := (Finset.mem_filter.mp earlier).2.resolve_left hnot
      exact low.trans (Finset.card_le_card (fun z hz => mem_outN.mpr ⟨sf (mem_outN.mp hz).1,(mem_outN.mp hz).2⟩))
    · exact later
  have kept : outN H F h ⊆ outN H (F \ S) h := by
    intro z hz
    obtain ⟨zf,hzEdge⟩ := mem_outN.mp hz
    refine mem_outN.mpr ⟨Finset.mem_sdiff.mpr ⟨zf,?_⟩,hzEdge⟩
    intro hit
    rcases Finset.mem_insert.mp hit with rfl|zi
    · exact hv hzEdge
    obtain ⟨zU,zv⟩ := BR45.mem_inN.mp zi
    have nz : z ≠ y := fun eq => digonfree oriented (by decide) vU yU vy (eq ▸ zv)
    exact puncture v 3 (by decide) (by decide)
      (.step (Finset.mem_erase.mpr ⟨ny,hU⟩) vh (.step (Finset.mem_erase.mpr ⟨nz,zU⟩) hzEdge
        (.step (Finset.mem_erase.mpr ⟨vyne,vU⟩) zv (.refl _))))
  exact ⟨h,mem_outN.mpr ⟨hU,vh⟩,ny,paid.trans (Finset.card_le_card kept)⟩

#print axioms marked_return_fan

/-- A four-label deletion hitting a marked vertex cannot pass the two-copy test. -/
def FourLabelTests (U : Finset ℕ) (d : ℕ) (H : CH.Digraph) (A : Finset ℕ) : Prop :=
  ∀ S ⊆ U, S.card = 4 → (∃ v ∈ A, v ∈ S) →
    (∀ P ⊆ U \ S, ∀ Q ⊆ U \ S, ¬ TwoReplacement.Feasible H (U \ S) P Q d) ∧
    (2 ≤ d → (∀ x ∈ U \ S, (outN H S x).card ≤ 2) →
      (TwoReplacement.NearMiss.commonBank H (U \ S) (TwoReplacement.NearMiss.doubleRows H U S) ∅ d).card+1=d →
      FourLabelHost.Child H U S d) ∧
    let W := U \ S
    let R := TwoReplacement.NearMiss.doubleRows H U S
    let T := TwoReplacement.NearMiss.tripleRows H U S
    ((∀ x ∈ W, (outN H S x).card ≤ 3) → ∀ z ∈ W, d ≤ (outN H W z).card →
      let J := SponsoredHeadPool.parents H W z
      let P := T ∪ (R \ J)
      T ⊆ J → (TwoReplacement.pool H W P J P d).card < d ∧
        TwoReplacement.NearMiss.commonBank H W R T d ⊆ TwoReplacement.pool H W P J P d) ∧
    ((∀ x ∈ W, (outN H S x).card ≤ 2) → d ≤ (TwoReplacement.NearMiss.commonBank H W R ∅ d).card+1 →
      ∀ y ∈ W \ R, d ≤ (outN H (W \ R) y).card ∨ (outN H (W \ R) y).card+3 ≤ d) ∧
    ((∀ x ∈ W, (outN H S x).card ≤ 2) → (TwoReplacement.NearMiss.commonBank H W R ∅ d).card+1=d →
      (∀ z ∈ W \ R, ∀ r ∈ R, H r z=true → ∃ t ∈ outN H R r, H t z≠true) ∧
      ∀ y ∈ (W \ R) \ TwoReplacement.NearMiss.commonBank H W R ∅ d, ∀ z ∈ W \ R,
        (outN H (W \ R) y).card + (outN H R y ∩ BR45.inN H W z).card +
          (if y=z ∨ H y z=true then 1 else 0) < d)

private theorem four_label_tests {U A : Finset ℕ} {d : ℕ} {H : CH.Digraph}
    (laws : ∀ k<d+1, OrderLaw 3 k (3*k+1)) (size : U.card=3*d+2)
    (puncture : ∀ v ∈ A, QFree H (U.erase v) 3)
    (full : ∀ v ∈ A, ∀ x ∈ U, x ≠ v → (outN H U x).card=d+1) :
    FourLabelTests U d H A := by
  rintro S subS four ⟨v,hv,hit⟩
  have kept : U \ S ⊆ U.erase v := by
    intro x hx
    obtain ⟨xu,xs⟩ := Finset.mem_sdiff.mp hx
    exact Finset.mem_erase.mpr ⟨fun eq => xs (eq ▸ hit),xu⟩
  have safe := (puncture v hv).mono_set kept
  have rows (x) (hx : x ∈ U \ S) := full v hv x (Finset.mem_sdiff.mp hx).1
      (fun eq => (Finset.mem_sdiff.mp hx).2 (eq ▸ hit))
  have lower := laws d (by omega)
  exact ⟨TwoReplacement.critical_obstruction lower size subS four safe,
    fun hd' => FourLabelHost.native_host laws size subS four safe hd' rows,
    fun three z zw degz cov => SponsoredHeadPool.native_cap lower size subS four safe rows three zw degz cov,
    FreeSecondHead.native_gap lower size subS four safe rows,
    fun two near => ⟨SponsoredHeadPool.native_missed_head lower size subS four safe rows two near,
      SponsoredHeadPool.two_step_cap lower size subS four safe rows two near⟩⟩

/-- Even a normalized state with no border obeys the four-label tests.
The deleted set contains its short row, so all surviving native rows are full. -/
theorem unit_tests {U : Finset ℕ} {d : ℕ}
    (laws : ∀ k<d+1, OrderLaw 3 k (3*k+1)) (size : U.card=3*d+2)
    (a : UnitRowState U d) (normal : Normal a) : FourLabelTests U d a.graph {a.root} := by
  apply four_label_tests laws size
  · intro v _
    exact a.free.mono_set (Finset.erase_subset _ _)
  · intro v hv
    rw [Finset.mem_singleton.mp hv]
    exact normal

#print axioms unit_tests

/-- Any missing head gives a full graph whose cycles are destroyed by either
endpoint. This lets the deletion range beyond sets containing the short row. -/
theorem filled_tests {U : Finset ℕ} {d : ℕ}
    (laws : ∀ k<d+1, OrderLaw 3 k (3*k+1)) (size : U.card=3*d+2)
    (a : UnitRowState U d) (normal : Normal a) {y} (hy : y ∈ U) (missing : a.graph a.root y ≠ true) :
    FourLabelTests U d (DeleteRepair.repair a.graph {a.root} (fun _ => {y})) {a.root,y} := by
  obtain ⟨rows,safe⟩ := filled_punctures a normal hy missing
  exact four_label_tests laws size safe (fun _ _ x hx _ => rows x hx)

#print axioms filled_tests

/-- Inspect a normalized subgraph of one particular actual plateau state.
The possible loss of surplus during normalization is explicit. -/
def TriangleObserver (U : Finset ℕ) (d : ℕ) (D : CH.Digraph) : Prop :=
  ∃ a b : UnitRowState U d, Normal a ∧ (∀ x z, a.graph x z = true → D x z = true) ∧
    Reach Rotation a b ∧ Normal b ∧
    (∀ c, Reach Rotation b c → (BR45.inN c.graph U c.root).card ≤ (BR45.inN b.graph U b.root).card) ∧
    (∀ c : UnitRowState U d, Normal c → FourLabelTests U d c.graph {c.root}) ∧
    (∀ (c : UnitRowState U d), Normal c → ∀ y ∈ U, c.graph c.root y ≠ true →
      FourLabelTests U d (DeleteRepair.repair c.graph {c.root} (fun _ => {y})) {c.root,y}) ∧
    ∀ y t, Site b y t →
      (BR45.inN b.graph U y).card < (BR45.inN b.graph U b.root).card ∧
      (BR45.inN b.graph U t).card ≤ (BR45.inN b.graph U b.root).card ∧
      let H := DeleteRepair.repair b.graph {b.root} (fun _ => {y})
      MarkedTests U d H {b.root,y,t} ∧ FourLabelTests U d H {b.root,y,t}

private theorem observe {U d} (O : Origin 3 (d+1)) (proper : U.card < O.V.card)
    (size : U.card = 3*d+2) (laws : ∀ k<d+1, OrderLaw 3 k (3*k+1)) (src : UnitBatch.Unit 3 d U) :
    TriangleObserver U d src.graph := by
  have lower := laws d (by omega)
  let raw : UnitRowState U d := ⟨src.graph,src.root,src.live,src.free,src.short,src.full⟩
  obtain ⟨a,_,na,sub⟩ := normalize raw
  obtain ⟨b,path,nb,maxAt,both⟩ := component_maximum O proper a na
  refine ⟨a,b,na,sub,path,nb,maxAt,unit_tests laws size,fun c nc _ => filled_tests laws size c nc,?_⟩
  intro y t site
  refine ⟨(both y t site).1,(both y t site).2,?_⟩
  obtain ⟨degree,oriented,punctures⟩ := loop_punctures O proper b nb site
  have hd := UnitState.origin_degree_pos O
  intro H
  constructor
  · intro v hv
    obtain ⟨vU,live,safe⟩ := punctures v hv
    refine ⟨puncture_low_indegree oriented vU live safe (fun x hx => (degree x hx).ge) (by omega),
      fun w hw ne => native_pair_parent lower size (by omega) (fun x hx => (degree x hx).ge) safe vU hw ne,?_⟩
    intro S subS hit three misses
    have kept : U \ S ⊆ U.erase v := by
      intro x hx
      obtain ⟨xu,xs⟩ := Finset.mem_sdiff.mp hx
      exact Finset.mem_erase.mpr ⟨fun eq => xs (eq ▸ hit),xu⟩
    exact PivotContraction.growth_obstruction lower size subS three (safe.mono_set kept)
      (fun x hx => (degree x (Finset.mem_sdiff.mp hx).1).ge) misses
  · exact four_label_tests laws size (fun v hv => (punctures v hv).2.2)
      (fun _ _ x hx _ => degree x hx)

/-- All observations after further nondecreasing paths refer to the very same
carrier and degree. Only the triangle observer changes to a specified subgraph. -/
def Stops (q d : ℕ) (st : State) : Prop :=
  ∃ start a : UnitBatch.Unit q d st.U, start.graph = st.H ∧ Reach UnitBatch.Ascent start a ∧
    BRsub.Sat q a.graph st.U ∧ ∀ b, Reach UnitBatch.Ascent a b →
      UnitBatch.arcs b.graph st.U = UnitBatch.arcs a.graph st.U ∧ UnitBatch.CutBound b ∧
      (q = 3 → TriangleObserver st.U d b.graph)

theorem stops {q d} (P : Origin q (d+1)) {st : State} (valid : Valid P st)
    (proper : st.U.card < P.V.card) (hq : 2 ≤ q) (unit : total (d+1) st.H st.U = 1)
    (laws : ∀ k<d+1, OrderLaw q k (q*k+1)) :
    Stops q d st := by
  obtain ⟨start,a,eq,path,sat,stop⟩ := UnitBatch.native_saturated_plateau P valid proper hq unit
  refine ⟨start,a,eq,path,sat,?_⟩
  intro b pb
  refine ⟨(stop b pb).1,(stop b pb).2,?_⟩
  rintro rfl
  exact observe P proper (UnitState.unit_state_three P valid proper unit (laws d (by omega))).1 laws b

/-- The same three-way split as the recursive capstone. The extra data is
attached to the actual middle witness, and the prior overshoot bound stays
attached to the actual positive overshoot. -/
def AlternativesWithLoops {q d} (O : Origin q (d+1)) (st : State) : Prop :=
  (total (d+1) st.H st.U = d+1 ∧
    ∀ v ∈ O.V, (outN O.G O.V v).card = d+1 ∧ (BR45.inN O.G O.V v).card = d+1) ∨
  (∃ (P : Origin q (d+1)) (v : ℕ) (t : State), P.V.card = O.V.card ∧
    MaximalReturns q P.G P.V ∧ v ∈ P.V ∧ t.U = P.V.erase v ∧
    Reach (RStep q (d+1)) P.init t ∧ total (d+1) t.H t.U = 1 ∧ Stops q d t) ∨
  (total (d+1) st.H st.U < d+1 ∧ ∃ g e, 0 < g ∧
    O.V.card+e = q*(d+1) ∧ O.V.card+g = st.U.card+total (d+1) st.H st.U ∧
    (q=3 → e=1 → 3≤g) ∧
    let t := (st.U.filter (fun u => 0 < cost (d+1) st.H st.U u)).card
    total (d+1) st.H st.U+t*t+t*e ≤ t*(q+2*g))

theorem from_candidate {D : CH.Digraph} {V : Finset ℕ} {q s : ℕ}
    (hq : 2 ≤ q) (free : QFree D V q) (live : V.Nonempty) (bound : V.card ≤ q*s)
    (degree : ∀ u ∈ V, s ≤ (outN D V u).card) :
    ∃ d, d+1 ≤ s ∧ ∃ (O : Origin q (d+1)) (st : State), Frontier O st ∧ AlternativesWithLoops O st := by
  obtain ⟨d,le,O,st,fr,alt,limit⟩ := PrivateCompletionOrder.candidate_alternatives_with_orders
    (by omega) free live bound degree
  refine ⟨d,le,O,st,fr,?_⟩
  rcases alt with high | ⟨P,v,t,same,sat,hv,labels,path,unit⟩ | ⟨low,g,e,pos,order,cost,box⟩
  · exact Or.inl high
  · have proper : t.U.card < P.V.card := by rw [labels]; exact Finset.card_lt_card (Finset.erase_ssubset hv)
    exact Or.inr (Or.inl ⟨P,v,t,same,sat,hv,labels,path,unit,stops P (rreach_valid P path) proper hq unit fr.lower_degrees⟩)
  · exact Or.inr (Or.inr ⟨low,g,e,pos,order,cost,fun three one => limit three (one ▸ order) low g pos cost,box⟩)

#print axioms stops
#print axioms from_candidate
end LeanCH.BR.Closure.UnitLoopCapstone
