import checkpoints.shen_extension.ReturnTargetCycles
import checkpoints.shen_extension.CrossValueOmissions
import checkpoints.shen_extension.FlatCycleFamilyCompletion
import LeanCH.BR.BRWeightedStrictAtomFloor

namespace LeanCH.BR.Closure.OmittedCycleProgress
open Finset BRq2 BRq3 BR45 WeightedSD FirstPacketBarrier MarkedCyclePeeling CrossValueOmissions

/-- A strict normalized allocation and its native column partner at the same value. -/
def Flat (q : ℕ) (D : CH.Digraph) (V : Finset ℕ) (x π : ℕ→ℚ) (c : ℚ) : Prop :=
  1<c ∧ (∀i∈V,0<x i) ∧ (∀i∈V,0<π i) ∧ mass V x=1 ∧ mass V π=1 ∧
  (∀i∈V,WeightedSD.row q D V x i=c) ∧ (∀i∈V,WeightedSD.col q D V π i=c)

def height (q : ℕ) (c : ℚ) : ℚ := ((q:ℚ)-1)^2 / ((q:ℚ)*(c-1))
noncomputable def rank (q : ℕ) (c : ℚ) : ℕ := ⌊height q c⌋₊

/-- Each distinct restored arc spends at least one unit of height. The strict
inequality comes from the atom floors on the two actual graphs. -/
theorem descent {q V D G w π x ρ c d} (hq : 2≤q) (free : QFree D V q)
    (fg : QFree G V q) (small : SmallerSmallRow q V.card) (sub : ∀i∈V,∀j∈V,G i j=true → D i j=true)
    (parent : Flat q G V x ρ d) (child : Flat q D V w π c)
    (added : (lost D G V).Nonempty) :
    let m := (lost D G V).card
    (m:ℚ) < height q d-height q c ∧ rank q c+m≤rank q d := by
  intro m
  obtain ⟨dh,xp,rp,xm,rm,xr,rc⟩ := parent
  obtain ⟨ch,wp,pp,wm,pm,wr,pc⟩ := child
  have floorX (v) (vv : v∈V) : d-1<((q:ℚ)-1)*x v := by
    simpa [xm] using strict_atom_floor_of_proper hq fg (small.induced fg) x
      (fun j jv=>(xp j jv).le) d (xm ▸ dh) (fun j jv=>(xr j jv).ge) v vv
  have floorP (v) (vv : v∈V) : c-1<((q:ℚ)-1)*π v := by
    simpa [pm] using strict_atom_floor_of_proper hq free.reverse (small.induced free.reverse) π
      (fun j jv=>(pp j jv).le) c (pm ▸ ch) (fun j jv=>(pc j jv).ge) v vv
  have qt : (2:ℚ)≤q := by exact_mod_cast hq
  have qpos : (0:ℚ)<q := by linarith
  have cq : 0<c-1 := by linarith
  have dq : 0<d-1 := by linarith
  have budget := (exact_gap sub wm pm xm rm wr pc xr rc).2
  let L := lost D G V
  have strict (e : ℕ×ℕ) (he : e∈L) :
      (q:ℚ)*(c-1)*(d-1)<((q:ℚ)-1)^2*((q:ℚ)*π e.1*x e.2) := by
    obtain ⟨iv,jv⟩ := mem_product.mp (mem_filter.mp he).1
    have cmp := mul_lt_mul_of_pos_right (floorP _ iv) dq
    have cmp' := mul_lt_mul_of_pos_left (floorX _ jv) (mul_pos (show (0:ℚ)<q-1 by linarith) (pp _ iv))
    nlinarith only [mul_lt_mul_of_pos_left (cmp.trans cmp') qpos]
  have total := sum_lt_sum_of_nonempty added strict
  have amount : (m:ℚ)*(q:ℚ)*(c-1)*(d-1)<((q:ℚ)-1)^2*(c-d) := by
    rw [←budget,cost,mul_sum]
    simpa [m,L,nsmul_eq_mul,mul_assoc] using total
  have eq : height q d-height q c=((q:ℚ)-1)^2*(c-d)/((q:ℚ)*(c-1)*(d-1)) := by
    unfold height
    field_simp [qpos.ne',cq.ne',dq.ne']
    ring
  have drop : (m:ℚ)<height q d-height q c := by
    rw [eq,lt_div_iff₀ (mul_pos (mul_pos qpos cq) dq)]
    linarith only [amount]
  have hc : 0≤height q c := div_nonneg (sq_nonneg _) (mul_nonneg qpos.le cq.le)
  have low : (rank q c:ℚ)≤height q c := Nat.floor_le hc
  have summed : ((rank q c+m:ℕ):ℚ)≤height q d := by
    push_cast
    linarith only [low,drop]
  exact ⟨drop,Nat.le_floor summed⟩

/-- Insert one actual missing shortest cycle into a selected family. Its old
strict allocation is feasible on the enlarged graph, which has its own flat
state and a strictly smaller natural rank. -/
theorem restore {q n F M x ρ d} (X : ShortestCycleWeights.Model q n) (hq : 2≤q)
    (small : SmallerSmallRow q X.V.card) (old : Flat q (graph X.D F) X.V x ρ d)
    (mf : M∈family X) {u v} (um : u∈M) (vm : v∈M) (uv : X.D u v=true)
    (gone : graph X.D F u v=false) :
    let G := graph X.D F
    let D := graph X.D (insert M F)
    let L := lost D G X.V
    (u,v)∈L ∧ ∃w π c,Flat q D X.V w π c ∧ (L.card:ℚ)<height q d-height q c ∧
      rank q c+L.card≤rank q d ∧ rank q c<rank q d := by
  classical
  intro G D L
  have cm := (mem_filter.mp mf).2
  have iv := cm.sub um
  have jv := cm.sub vm
  have mono (i) (_ : i∈X.V) (j) (_ : j∈X.V) (edge : G i j=true) : D i j=true := by
    obtain ⟨C,ci⟩ := active.mp edge
    obtain ⟨cf,cc⟩ := mem_col.mp ci
    exact active.mpr ⟨C,mem_col.mpr ⟨mem_insert_of_mem cf,cc⟩⟩
  have hit : D u v=true := active.mpr ⟨M,mem_col.mpr ⟨mem_insert_self _ _,um,vm,uv⟩⟩
  have la : (u,v)∈L := mem_filter.mpr ⟨mem_product.mpr ⟨iv,jv⟩,hit,gone⟩
  have free := PrivateArcEndpoints.graph_free X (insert M F)
  have ⟨dh,xp,_,xm,_,xr,_⟩ := old
  have strict (i) (hi : i∈X.V) : mass X.V x<WeightedSD.row q D X.V x i := by
    rw [xm]
    apply dh.trans_le
    rw [←xr i hi,WeightedSD.row,WeightedSD.row]
    exact add_le_add_right (mul_le_mul_of_nonneg_left (outW_mono_graph mono (fun i iv=>(xp i iv).le) hi)
      (Nat.cast_nonneg q)) _
  obtain ⟨w,π,c,high,wp,pp,wm,pm,wr,pc⟩ := strict_pair_of_proper_smallRow (small.induced free)
    X.live x (fun i iv=>(xp i iv).le) strict
  have child : Flat q D X.V w π c := ⟨high,wp,pp,wm,pm,wr,pc⟩
  have ⟨drop,ranked⟩ := descent hq free (PrivateArcEndpoints.graph_free X F) small mono old child ⟨(u,v),la⟩
  change rank q c+L.card≤rank q d at ranked
  have many : 0<L.card := card_pos.mpr ⟨_,la⟩
  exact ⟨la,w,π,c,child,drop,ranked,by omega⟩

structure Stage {q n} (X : ShortestCycleWeights.Model q n) where
  cycles : Family
  x : ℕ→ℚ
  π : ℕ→ℚ
  value : ℚ
  valid : cycles⊆family X
  complete : ∀M,M∈cycles ↔ ShenCycleSuccessor.Cycle (graph X.D cycles) X.V q M
  flat : Flat q (graph X.D cycles) X.V x π value

/-- One allowed edit. Recompletion adds every shortest cycle of the enlarged
selected graph and adds no further arcs. -/
def Edge {q n} (X : ShortestCycleWeights.Model q n) (wanted : Family) (A B : Stage X) : Prop :=
  ∃M∈wanted,M∉A.cycles ∧ insert M A.cycles⊆B.cycles ∧
    graph X.D B.cycles=graph X.D (insert M A.cycles) ∧
    let L := lost (graph X.D B.cycles) (graph X.D A.cycles) X.V
    (∃u∈M,∃v∈M,(u,v)∈L) ∧ (L.card:ℚ)<height q A.value-height q B.value ∧
    rank q B.value+L.card≤rank q A.value ∧ rank q B.value<rank q A.value

theorem advance {q n} (X : ShortestCycleWeights.Model q n) (hq : 2≤q)
    (small : SmallerSmallRow q X.V.card) {wanted : Family} (ws : wanted⊆family X)
    (A : Stage X) {M} (mw : M∈wanted) (off : M∉A.cycles) :
    ∃B : Stage X,M∈B.cycles ∧ Edge X wanted A B := by
  classical
  have cm := (mem_filter.mp (ws mw)).2
  obtain ⟨u,um,v,vm,uv,absent⟩ := ReturnTargetCycles.missing_arc X A.complete cm off
  obtain ⟨add,w,π,c,strict,drop,amount,less⟩ := restore X hq small A.flat (ws mw) um vm uv absent
  let F := insert M A.cycles
  have valid : F⊆family X := insert_subset (ws mw) A.valid
  have actual (N) (nf : N∈F) : ShenCycleSuccessor.Cycle (graph X.D F) X.V q N :=
    retain_cycle (mem_filter.mp (valid nf)).2 nf
  obtain ⟨G,fg,same,complete,native⟩ := FlatCycleFamilyCompletion.complete (by omega : 1≤q) X.free actual
  let B : Stage X := ⟨G,w,π,c,fun N ng=>mem_filter.mpr ⟨mem_powerset.mpr (native N ng).sub,native N ng⟩,
    fun N => by rw [same]; exact complete N,by rw [same]; exact strict⟩
  refine ⟨B,fg (mem_insert_self _ _),M,mw,off,fg,same,?_⟩
  change (∃u∈M,∃v∈M,(u,v)∈lost (graph X.D G) (graph X.D A.cycles) X.V) ∧ _
  dsimp only [B]
  rw [same]
  exact ⟨⟨u,um,v,vm,add⟩,drop,amount,less⟩

theorem lowers {q n} {X : ShortestCycleWeights.Model q n} {wanted A B}
    (edge : Edge X wanted A B) : rank q B.value<rank q A.value := by
  obtain ⟨_,_,_,_,_,_,_,_,h⟩ := edge
  exact h

theorem well_founded {q n} (X : ShortestCycleWeights.Model q n) (wanted : Family) :
    WellFounded (fun B A : Stage X => Edge X wanted A B) :=
  Subrelation.wf (fun {_ _} h=>lowers h) (measure (fun A : Stage X=>rank q A.value)).wf

/-- Continue applying the same edit to new states until every requested
native shortest cycle belongs to the completed selected family. -/
theorem saturate {q n} (X : ShortestCycleWeights.Model q n) (hq : 2≤q)
    (small : SmallerSmallRow q X.V.card) (wanted : Family) (ws : wanted⊆family X)
    (A : Stage X) : ∃B,Relation.ReflTransGen (Edge X wanted) A B ∧ wanted⊆B.cycles := by
  classical
  apply (well_founded X wanted).induction A
  intro S ih
  by_cases done : wanted⊆S.cycles
  · exact ⟨S,.refl,done⟩
  obtain ⟨M,mw,off⟩ := not_subset.mp done
  obtain ⟨N,_,edit⟩ := advance X hq small ws S mw off
  obtain ⟨B,tail,incl⟩ := ih N edit
  exact ⟨B,(Relation.ReflTransGen.single edit).trans tail,incl⟩

/-- Close all prescribed arc-columns jointly on a single descendant. Every
marked native cycle in each column is present with its original labels. -/
theorem cover_arcs {q n} (X : ShortestCycleWeights.Model q n) (hq : 2≤q)
    (small : SmallerSmallRow q X.V.card) (A : Stage X) (marked : Finset (ℕ×ℕ)) :
    let wanted := marked.biUnion (fun e=>col X.D (family X) e)
    ∃B,Relation.ReflTransGen (Edge X wanted) A B ∧
      ∀e∈marked,col X.D B.cycles e=col X.D (family X) e := by
  classical
  intro wanted
  have sub : wanted⊆family X := by
    intro M hm
    obtain ⟨e,_,me⟩ := mem_biUnion.mp hm
    exact (mem_col.mp me).1
  obtain ⟨B,path,covered⟩ := saturate X hq small wanted sub A
  refine ⟨B,path,?_⟩
  intro e em
  ext M
  constructor
  · intro mc
    obtain ⟨mb,use⟩ := mem_col.mp mc
    exact mem_col.mpr ⟨B.valid mb,use⟩
  · intro mc
    exact mem_col.mpr ⟨covered (mem_biUnion.mpr ⟨e,em,mc⟩),(mem_col.mp mc).2⟩

/-- The very same missing arc on a prescribed native cycle is paid into
both global omission budgets and is restored by a lower-rank edit. -/
theorem priced_cycle {q n w π c} (X : ShortestCycleWeights.Model q n) (hq : 2≤q)
    (small : SmallerSmallRow q X.V.card) (native : Flat q X.D X.V w π c) (A : Stage X)
    {M} (cm : ShenCycleSuccessor.Cycle X.D X.V q M) (miss : M∉A.cycles) :
    ∃u∈M,∃v∈M,X.D u v=true ∧ graph X.D A.cycles u v=false ∧
      (q:ℚ)*A.π u*w v≤c-A.value ∧ (q:ℚ)*π u*A.x v≤c-A.value ∧ c-A.value<c-1 ∧
      ∃B,Edge X {M} A B ∧ M∈B.cycles ∧ graph X.D B.cycles u v=true := by
  classical
  obtain ⟨u,um,v,vm,uv,absent⟩ := ReturnTargetCycles.missing_arc X A.complete cm miss
  have mf : M∈family X := mem_filter.mpr ⟨mem_powerset.mpr cm.sub,cm⟩
  obtain ⟨B,mb,edge⟩ := advance X hq small (singleton_subset_iff.mpr mf) A (mem_singleton_self M) miss
  obtain ⟨_,wp,pp,wm,pm,wr,pc⟩ := native
  obtain ⟨high,xp,rp,xm,rm,xr,rc⟩ := A.flat
  have all := on_family wm pm xm rm wp pp xp rp wr pc xr rc high
  have singleton : ({v}:Finset ℕ)⊆outN X.D X.V u := singleton_subset_iff.mpr (mem_outN.mpr ⟨cm.sub vm,uv⟩)
  have old := all.2.2.2 u (cm.sub um) {v} singleton (by intro j hj; obtain rfl:=mem_singleton.mp hj; exact absent)
  have pay1 : (q:ℚ)*A.π u*w v≤c-A.value := by simpa [mass] using old.2.1
  have pay2 : (q:ℚ)*π u*A.x v≤c-A.value := by simpa [mass] using old.1
  exact ⟨u,um,v,vm,uv,absent,pay1,pay2,all.2.2.1,B,edge,mb,active.mpr ⟨M,mem_col.mpr ⟨mb,um,vm,uv⟩⟩⟩

def OnModel {q n} (X : ShortestCycleWeights.Model q n) : Prop :=
  ∀(A : Stage X) (marked : Finset (ℕ×ℕ)),
    ∃B,Relation.ReflTransGen (Edge X (marked.biUnion (fun e=>col X.D (family X) e))) A B ∧
      ∀e∈marked,col X.D B.cycles e=col X.D (family X) e

theorem on_model {q n} (X : ShortestCycleWeights.Model q n) (hq : 2≤q)
    (small : SmallerSmallRow q X.V.card) : OnModel X := fun A marked=>cover_arcs X hq small A marked

#print axioms on_model
#print axioms cover_arcs
#print axioms priced_cycle

#print axioms advance
#print axioms well_founded
#print axioms saturate

#print axioms descent
#print axioms restore
end LeanCH.BR.Closure.OmittedCycleProgress
