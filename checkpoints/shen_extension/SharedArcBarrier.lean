import checkpoints.shen_extension.NativeCycleConnectivity

namespace LeanCH.BR.Closure.SharedArcBarrier
open Finset BRq2 BRq3 BR45 WeightedSD ShenCycleSuccessor ShortestCycleWeights FirstPacketBarrier
open MarkedCyclePeeling SharedArcExpansion

def Boundary {q n} (X : Model q n) (F : Family) (B : Finset ℕ) : Prop :=
  B∈family X ∧ B∉F ∧ ∃A∈F,Touch X.D A B

private theorem no_bad_private {q n} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    {F} (sub : F⊆family X) (bad : ¬SmallRow q (graph X.D F) X.V) {B z} (bf : B∈F) (zb : z∈B) :
    ∃M∈F,M≠B ∧ z∈M := by
  obtain ⟨x,xn,_,strict⟩ := strict_witness_of_not_smallRow bad
  have pos := strict_positive_of_proper_smallRow (small.induced (PrivateArcEndpoints.graph_free X F)) x xn strict
  obtain ⟨w,wp,ws⟩ := GlobalFamilyDual.integral_strict pos strict
  let X' : Model q (n+∑i∈X.V,w i) := { X with
    bounded := X.bounded.trans (Nat.le_add_right ..)
    minimal := by
      intro E U v live safe vp _ high
      by_contra! less
      exact (small E U less safe).no_strict live _ (fun _ _ => Nat.cast_nonneg _) high }
  have feas : Feasible q (n+∑i∈X.V,w i) X'.D X'.V F := ⟨w,wp,Nat.le_add_left ..,ws⟩
  exact PrivateArcEndpoints.other_witness X' hq sub feas bf zb

/-- Exactly which columns change when this single cycle is attached. -/
noncomputable def targets (D : CH.Digraph) (V : Finset ℕ) (F : Family) (B : Finset ℕ) : Finset ℕ := by
  classical exact V.filter (fun v => v∈B ∧ ∃u∈B,D u v=true ∧ graph D F u v=false)

theorem column {D V q F B} (cb : Cycle D V q B) (p : ℕ→ℝ) {v} (vv : v∈V) :
    let E := graph D F
    let G := graph D (insert B F)
    (v∉targets D V F B → realCol q G V p v=realCol q E V p v) ∧
    (v∈targets D V F B → ∃u∈B,v∈B ∧ D u v=true ∧ E u v=false ∧
      realCol q G V p v=realCol q E V p v+q*p u) := by
  intro E G
  classical
  have mono {u v} (e : E u v=true) : G u v=true := by
    obtain ⟨A,a⟩ := active.mp e
    obtain ⟨af,ua,va,uv⟩ := mem_col.mp a
    exact active.mpr ⟨A,mem_col.mpr ⟨mem_insert_of_mem af,ua,va,uv⟩⟩
  have extra {u v} (a : G u v=true) (miss : ¬E u v=true) : u∈B ∧ v∈B ∧ D u v=true := by
    obtain ⟨A,af⟩ := active.mp a
    obtain ⟨ag,ua,va,uv⟩ := mem_col.mp af
    rcases mem_insert.mp ag with rfl|old
    · exact ⟨ua,va,uv⟩
    · exact (miss (active.mpr ⟨A,mem_col.mpr ⟨old,ua,va,uv⟩⟩)).elim
  have sub : inN E V v⊆inN G V v := fun u hu => mem_inN.mpr ⟨(mem_inN.mp hu).1,mono (mem_inN.mp hu).2⟩
  constructor
  · intro outside
    have eq : inN G V v=inN E V v := by
      apply Subset.antisymm _ sub
      intro i ic
      obtain ⟨iv,edge⟩ := mem_inN.mp ic
      by_contra off
      have miss : ¬E i v=true := fun e => off (mem_inN.mpr ⟨iv,e⟩)
      have data := extra edge miss
      exact outside (mem_filter.mpr ⟨vv,data.2.1,i,data.1,data.2.2,Bool.eq_false_iff.mpr miss⟩)
    simp only [realCol,realInW_eq_mass_inN,eq]
  intro inT
  obtain ⟨_,vb,u,ub,ed,miss⟩ := mem_filter.mp inT
  have has : u∈inN G V v := mem_inN.mpr ⟨cb.sub ub,active.mpr ⟨B,mem_col.mpr ⟨mem_insert_self B F,ub,vb,ed⟩⟩⟩
  have no : u∉inN E V v := fun h => Bool.noConfusion (miss.symm.trans (mem_inN.mp h).2)
  have one : (inN D B v).card≤1 := (cb.incoming v vb).le
  have eq : inN G V v=insert u (inN E V v) := by
    ext i
    constructor
    · intro mark
      by_cases old : i∈inN E V v
      · exact mem_insert_of_mem old
      obtain ⟨iv,ig⟩ := mem_inN.mp mark
      have raw := extra ig (fun ie => old (mem_inN.mpr ⟨iv,ie⟩))
      exact mem_insert.mpr (Or.inl (card_le_one.mp one _ (mem_inN.mpr ⟨raw.1,raw.2.2⟩) u (mem_inN.mpr ⟨ub,ed⟩)))
    · intro mark
      rcases mem_insert.mp mark with rfl|old
      · exact has
      · exact sub old
  refine ⟨u,ub,vb,ed,miss,?_⟩
  simp only [realCol,realInW_eq_mass_inN,eq,realMass,sum_insert no]
  ring

theorem price {D V q F B} (cb : Cycle D V q B) {p} (hp : RealDual q (graph D F) V 1 p)
    (bad : ¬SmallRow q (graph D (insert B F)) V) :
    ∃u∈B,∃v∈B,D u v=true ∧ graph D F u v=false ∧
      1 < realCol q (graph D F) V p v + q*p u := by
  classical
  obtain ⟨v,vv,high⟩ : ∃v∈V,1<realCol q (graph D (insert B F)) V p v := by
    by_contra! low
    exact bad (smallRow_of_realDual ⟨hp.nonneg,hp.normalized,low⟩)
  have account := column (F:=F) cb p vv
  by_cases inT : v∈targets D V F B
  · obtain ⟨u,ub,vb,uv,off,eq⟩ := account.2 inT
    exact ⟨u,ub,v,vb,uv,off,eq ▸ high⟩
  · exact (high.not_ge ((account.1 inT).symm ▸ hp.columns v vv)).elim

/-- From every starting cycle a counterexample supplies a maximal connected
family with a valid dual. It already spans. Each adjacent outside cycle
defeats every old dual on one of its genuinely new arcs. -/
theorem on_source {q n} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    {C} (cf : C∈family X) :
    ∃F : Family,Built X.D C F ∧ F⊆family X ∧ C∈F ∧ support F=X.V ∧
      SmallRow q (graph X.D F) X.V ∧ (∃p,RealDual q (graph X.D F) X.V 1 p) ∧
      (∃B,Boundary X F B) ∧
      ∀B,Boundary X F B → ¬SmallRow q (graph X.D (insert B F)) X.V ∧
        ∀p,RealDual q (graph X.D F) X.V 1 p →
          ∃u∈B,∃v∈B,X.D u v=true ∧ graph X.D F u v=false ∧
            1<realCol q (graph X.D F) X.V p v+q*p u := by
  classical
  let Good := fun F : Family => Built X.D C F ∧ SmallRow q (graph X.D F) X.V
  let pool := (family X).powerset.filter Good
  have mem (F) : F∈pool ↔ F⊆family X ∧ Good F := by simp [pool]
  have first : Good {C} := by
    refine ⟨.seed,?_⟩
    by_contra bad
    have cc : Cycle X.D X.V q C := (mem_filter.mp cf).2
    obtain ⟨z,zc⟩ := card_pos.mp (show 0<C.card by rw [cc.size]; omega)
    obtain ⟨M,mm,ne,_⟩ := no_bad_private X hq small (singleton_subset_iff.mpr cf) bad (mem_singleton_self C) zc
    exact ne (mem_singleton.mp mm)
  obtain ⟨F,fp,top⟩ := pool.exists_max_image Finset.card ⟨{C},(mem _).mpr ⟨singleton_subset_iff.mpr cf,first⟩⟩
  obtain ⟨sub,built,good⟩ := (mem F).mp fp
  have seedIn : C∈F := by
    clear top fp sub good
    induction built with
    | seed => simp
    | add _ _ _ _ ih => exact mem_insert_of_mem ih
  have fails {B} (b : Boundary X F B) : ¬SmallRow q (graph X.D (insert B F)) X.V := by
    rintro win
    obtain ⟨bf,off,A,af,hit⟩ := b
    have limit := top (insert B F) ((mem _).mpr ⟨insert_subset bf sub,built.add af hit off,win⟩)
    rw [card_insert_of_notMem off] at limit
    omega
  have spans : support F=X.V := by
    by_contra no
    obtain ⟨A,af,B,bf,hit,z,zb,fresh⟩ := enlarge X hq built sub no
    have off : B∉F := fun memB => fresh (mem_biUnion.mpr ⟨B,memB,zb⟩)
    obtain ⟨M,mg,ne,zm⟩ := no_bad_private X hq small (insert_subset bf sub) (fails ⟨bf,off,A,af,hit⟩) (mem_insert_self B F) zb
    exact fresh (mem_biUnion.mpr ⟨M,(mem_insert.mp mg).resolve_left ne,zm⟩)
  have next : ∃B,Boundary X F B := by
    by_contra no
    have invariant {L M} (way : Linked X L M) : L∈F ↔ M∈F := by
      induction way with
      | refl => rfl
      | rel A B e =>
        exact ⟨fun af => by by_contra nb; exact no ⟨B,e.2.1,nb,A,af,e.2.2⟩,
          fun bf => by by_contra na; exact no ⟨A,e.1,na,B,bf,e.2.2.symm⟩⟩
      | symm _ _ _ ih => exact ih.symm
      | trans _ _ _ _ _ ab bc => exact ab.trans bc
    have eq := Subset.antisymm sub (fun B bf => (invariant (NativeCycleConnectivity.connected X hq cf bf)).mp seedIn)
    obtain ⟨w,_,_,hi⟩ := full_feasible X hq
    rw [eq] at good
    exact good.no_strict X.live _ (fun _ _ => Nat.cast_nonneg _) hi
  exact ⟨F,built,sub,seedIn,spans,good,realDual_of_smallRow good X.live,next,fun B b =>
    ⟨fails b,fun _ hp => price (show Cycle X.D X.V q B from (mem_filter.mp b.1).2) hp (fails b)⟩⟩

#print axioms price
#print axioms on_source
end LeanCH.BR.Closure.SharedArcBarrier
