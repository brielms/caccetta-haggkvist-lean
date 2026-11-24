import checkpoints.shen_extension.SharedArcPivotFold
import checkpoints.shen_extension.CyclePhaseFork
import Mathlib.SetTheory.Ordinal.Rank

namespace LeanCH.BR.Closure.SharedArcCleanRecurrence
open Finset BRq2 BRq3 BR45 ShortestCycleWeights ShenCycleSuccessor

/-- Transport an exterior incidence along a walk whose steps preserve it. -/
private theorem carry {D : CH.Digraph} {M : Finset ℕ} {P : ℕ → Prop}
    (pass : ∀ u ∈ M, ∀ v ∈ M, D u v = true → P u → P v)
    {u v k} (walk : Walk D M u v k) (um : u ∈ M) (start : P u) : P v := by
  induction walk with
  | refl => exact start
  | step hv ed rest ih => exact ih hv (pass _ um _ hv ed start)

/-- Any strongly connected family of actual transitions on a proper carrier
in a prime saturated source must lose an exterior head on at least one step.
The transitions may use a subgraph of the native graph. -/
theorem exterior_loss {q n} (X : Model q n) {M : Finset ℕ} (sub : M ⊆ X.V)
    (large : 2 ≤ M.card) (proper : M ≠ X.V) (E : CH.Digraph)
    (connected : ∀ u ∈ M, ∀ v ∈ M, ∃ k, Walk E M u v k) :
    ∃ u ∈ M, ∃ v ∈ M, E u v = true ∧
      ∃ z ∈ X.V \ M, X.D u z = true ∧ X.D v z = false := by
  classical
  by_contra fail
  have pass (z) (zv : z ∈ X.V \ M) (u) (um : u ∈ M) (v) (vm : v ∈ M)
      (ed : E u v = true) (hit : X.D u z = true) : X.D v z = true := by
    cases e : X.D v z
    · exact (fail ⟨u,um,v,vm,ed,z,zv,hit,e⟩).elim
    · rfl
  have uniform : BRsub.OutUniform X.D X.V M := by
    intro u um v vm z zv outside
    obtain ⟨_,go⟩ := connected u um v vm
    obtain ⟨_,back⟩ := connected v vm u um
    exact Bool.eq_iff_iff.mpr
      ⟨carry (pass z (mem_sdiff.mpr ⟨zv,outside⟩)) go um,
       carry (pass z (mem_sdiff.mpr ⟨zv,outside⟩)) back vm⟩
  exact X.prime M sub large proper ⟨uniform,BRsub.outUniform_inUniform X.free X.sat sub uniform⟩

/-- The same outside vertex is gained on one arc and lost on another.
Both arcs lie on the specified induced shortest cycle. -/
theorem cycle_switches {q n} (X : Model q n) (hq : 2 ≤ q) {M : Finset ℕ}
    (cycle : Cycle X.D X.V q M) :
    ∃ z ∈ X.V \ M, ∃ u ∈ M, ∃ v ∈ M, X.D u v = true ∧ X.D u z = true ∧ X.D v z = false ∧
      ∃ i ∈ M, ∃ j ∈ M, X.D i j = true ∧ X.D i z = false ∧ X.D j z = true := by
  have size := cycle.size
  have room := CyclePhaseFork.support_bound X hq
  have paths (i) (im : i ∈ M) (j) (jm : j ∈ M) : ∃ k, Walk X.D M i j k :=
    ⟨_,(MandatoryExcursion.segments (by omega : 1≤q) X.free cycle im jm).2.2.1⟩
  obtain ⟨u,um,v,vm,uv,z,zm,uz,vz⟩ :=
    exterior_loss X cycle.sub (by omega) (fun eq => by rw [eq] at size; omega) X.D paths
  refine ⟨z,zm,u,um,v,vm,uv,uz,vz,?_⟩
  by_contra missing
  have pass (i) (im : i ∈ M) (j) (jm : j ∈ M) (ij : X.D i j = true)
      (off : X.D i z = false) : X.D j z = false := by
    cases e : X.D j z
    · rfl
    · exact (missing ⟨i,im,j,jm,ij,off,e⟩).elim
  obtain ⟨_,back⟩ := paths v vm u um
  exact Bool.noConfusion (uz.symm.trans (carry pass back vm vz))

#print axioms exterior_loss
#print axioms cycle_switches

/-- Saturation on the full carrier suffices. If the short return starts
at the deleted vertex, its remaining suffix already closes a forbidden walk. -/
theorem parent_transfer {q n} (X : Model q n) (hq : 2≤q) {t a u : ℕ}
    (tv : t∈X.V) (av : a∈X.V) (uv : u∈X.V) (diff : t≠u) (ua : X.D u a=true)
    (clean : ∀z∈X.V.erase a,X.D t z=true → X.D a z=true) : X.D u t=true := by
  by_contra missing
  obtain ⟨_,_,bound,walk⟩ := mem_ball.mp (X.sat t tv u uv missing)
  cases walk with
  | refl => exact diff rfl
  | @step _ x _ k xv tx tail =>
    by_cases eq : x=a
    · subst x
      exact X.free a (k+1) (by omega) (by omega) (tail.snoc av ua)
    · exact X.free a (k+1+1) (by omega) (by omega)
        (.step xv (clean x (mem_erase.mpr ⟨eq,xv⟩) tx) (tail.snoc av ua))

/-- Along a clean arc the indegree cannot increase. Separation supplies
a parent at the tail to replace the tail itself. -/
theorem indegree_step {q n} (X : Model q n) (hq : 2 ≤ q) {t a : ℕ}
    (tv : t∈X.V) (av : a∈X.V) (ta : X.D t a=true)
    (clean : ∀z∈X.V.erase a,X.D t z=true → X.D a z=true) :
    (inN X.D X.V a).card ≤ (inN X.D X.V t).card := by
  classical
  have diff : t≠a := fun eq => loopfree X.free (by omega) av (eq ▸ ta)
  obtain ⟨y,yv,yt,ya⟩ := X.separated t tv a av diff.symm
  let A := inN X.D X.V a
  have sub : insert y (A.erase t) ⊆ inN X.D X.V t := by
    intro x hx
    rcases mem_insert.mp hx with rfl|old
    · exact mem_inN.mpr ⟨yv,yt⟩
    obtain ⟨xt,xm⟩ := mem_erase.mp old
    obtain ⟨xv,xa⟩ := mem_inN.mp xm
    exact mem_inN.mpr ⟨xv,parent_transfer X hq tv av xv xt.symm xa clean⟩
  have exclude : y∉A.erase t := fun hit => Bool.noConfusion (ya.symm.trans (mem_inN.mp (mem_of_mem_erase hit)).2)
  have bound := card_le_card sub
  rw [card_insert_of_notMem exclude,card_erase_add_one (s:=A) (mem_inN.mpr ⟨tv,ta⟩)] at bound
  exact bound

private theorem order_bound {q n k} (X : Model q n)
    (reg : ∀v∈X.V,(inN X.D X.V v).card=k) : X.V.card ≤ q*k := by
  classical
  let w (v : ℕ) : ℚ := X.weights v
  let m := WeightedSD.mass X.V w
  have positive : 0<m := sum_pos (fun v hv => by dsimp [w]; exact_mod_cast X.positive v hv) X.live
  have h := sum_lt_sum_of_nonempty X.live (fun i hi => X.strict i hi)
  change (∑ _i∈X.V,m) < ∑ i∈X.V,WeightedSD.row q X.D X.V w i at h
  simp only [WeightedSD.row,sum_add_distrib,←mul_sum,WeightedSD.sum_outW_cycle_incidence,
    sum_const,nsmul_eq_mul] at h
  have total : (∑z∈X.V,((inN X.D X.V z).card:ℚ)*w z)=(k:ℚ)*m := by
    rw [show m=∑z∈X.V,w z from rfl,mul_sum]
    exact sum_congr rfl (fun z hz => by rw [reg z hz])
  rw [total] at h
  change (X.V.card:ℚ)*m < m+q*((k:ℚ)*m) at h
  have bound : (X.V.card:ℚ)<1+q*(k:ℚ) :=
    lt_of_mul_lt_mul_right (by nlinarith only [h] : (X.V.card:ℚ)*m < (1+q*(k:ℚ))*m) positive.le
  have : X.V.card < 1+q*k := by exact_mod_cast bound
  omega

/-- If a column has k parents and incidence propagates along a simple
spanning cyclic order, it receives every one of the previous k vertices. -/
private theorem jump {D : CH.Digraph} {V : Finset ℕ} {f : ℕ → ℕ} {N k : ℕ}
    (period : ∀i,f (i+N)=f i) (inside : ∀i,f i∈V)
    (window : ∀i,(range N).image (fun j => f (i+j)) = V)
    (inj : ∀i u v,u<N → v<N → f (i+u)=f (i+v) → u=v)
    (clean : ∀i z,z∈V → z≠f (i+1) → D (f i) z=true → D (f (i+1)) z=true)
    (degree : ∀i,(inN D V (f i)).card=k) (kN : k<N) {i d} (lo : 0<d) (hi : d≤k) :
    D (f i) (f (i+d))=true := by
  classical
  by_contra missing
  let j := i+d
  have id' : f (j+(N-d))=f i := by rw [show j+(N-d)=i+N by dsimp [j]; omega,period]
  have carryTo (r l : ℕ) (bound : r+l<N) (hit : D (f (j+r)) (f j)=true) :
      D (f (j+(r+l))) (f j)=true := by
    induction l with
    | zero => simpa using hit
    | succ l ih =>
      have ne : f j≠f (j+(r+l)+1) := by
        intro eq
        have := inj j 0 (r+l+1) (by omega) (by omega) (by simpa [Nat.add_assoc] using eq)
        omega
      simpa [Nat.add_assoc] using clean (j+(r+l)) _ (inside j) ne (ih (by omega))
  have sub : inN D V (f j) ⊆ (Ico (N-d+1) N).image (fun r => f (j+r)) := by
    intro x hx
    obtain ⟨xv,hit⟩ := mem_inN.mp hx
    rw [←window j] at xv
    obtain ⟨r,rm,rfl⟩ := mem_image.mp xv
    have lt := mem_range.mp rm
    apply mem_image.mpr
    refine ⟨r,mem_Ico.mpr ⟨?_,lt⟩,rfl⟩
    by_contra! early
    have endHit := carryTo r (N-d-r) (by omega) hit
    rw [show r+(N-d-r)=N-d by omega,id'] at endHit
    exact missing endHit
  have count := (card_le_card sub).trans card_image_le
  rw [degree,Nat.card_Ico] at count
  omega

private theorem jump_walk {D : CH.Digraph} {V : Finset ℕ} {f : ℕ→ℕ} {k : ℕ}
    (live : ∀i,f i∈V) (arcs : ∀i d,0<d → d≤k → D (f i) (f (i+d))=true)
    (b i d : ℕ) (budget : d≤b*k) : ∃ m≤b,Walk D V (f i) (f (i+d)) m ∧ (0<d → 0<m) := by
  induction b generalizing i d with
  | zero =>
    have : d=0 := by simpa using budget
    subst d
    exact ⟨0,le_rfl,by simp [Walk.refl],by omega⟩
  | succ b ih =>
    by_cases zero : d=0
    · subst d; exact ⟨0,by omega,by simp [Walk.refl],by omega⟩
    let e := min d k
    have ek : e≤k := min_le_right _ _
    have ed : e≤d := min_le_left _ _
    have remain : d-e≤b*k := by rw [Nat.succ_mul] at budget; dsimp [e]; omega
    have ep : 0<e := by
      have : k≠0 := fun h => by simp_all
      dsimp [e]; omega
    obtain ⟨m,mb,w,_⟩ := ih (i+e) (d-e) remain
    rw [show i+e+(d-e)=i+d by omega] at w
    exact ⟨m+1,by omega,.step (live _) (arcs _ _ ep ek) w,by omega⟩

#print axioms indegree_step

/-- Every periodic sequence of native arcs loses an actual retained head
at some step. This includes spanning orbits, independently of order and degree. -/
theorem periodic_escape {q n} (X : Model q n) (hq : 2≤q) (go : X.V → X.V)
    (root : X.V) (recurs : root ∈ Function.periodicPts go)
    (native : ∀i : ℕ,X.D (go^[i] root) (go^[i+1] root)=true) :
    ∃i : ℕ, let t := go^[i] root; let a := go^[i+1] root
            ∃z∈X.V.erase a.val,X.D t z=true ∧ X.D a z=false := by
  classical
  let f (i : ℕ) : ℕ := (go^[i] root).val
  let N := Function.minimalPeriod go root
  let M := (range N).image f
  have Npos : 0<N := Function.minimalPeriod_pos_of_mem_periodicPts recurs
  have per (i) : f (i+N)=f i := congrArg Subtype.val (Function.iterate_add_minimalPeriod_eq (n:=i))
  have inside (i) : f i∈X.V := (go^[i] root).property
  have mem (i) : f i∈M := mem_image.mpr ⟨i%N,mem_range.mpr (Nat.mod_lt _ Npos),
    congrArg Subtype.val Function.iterate_mod_minimalPeriod_eq⟩
  have inj (i u v : ℕ) (hu : u<N) (hv : v<N) (eq : f (i+u)=f (i+v)) : u=v := by
    have h : go^[i+u] root=go^[i+v] root := Subtype.ext eq
    rw [Nat.add_comm i u,Nat.add_comm i v,Function.iterate_add_apply,Function.iterate_add_apply] at h
    apply Function.iterate_injOn_Iio_minimalPeriod _ _ h <;>
      simpa only [Set.mem_Iio,Function.minimalPeriod_apply_iterate recurs] using ‹_›
  have size : M.card=N := by
    rw [show M=(range N).image f from rfl,card_image_of_injOn,card_range]
    exact fun u hu v hv h => inj 0 u v (mem_range.mp hu) (mem_range.mp hv) (by simpa using h)
  have sub : M⊆X.V := by
    intro x hx
    obtain ⟨i,_,rfl⟩ := mem_image.mp hx
    exact inside i
  by_contra failed
  have clean (i z) (zv : z∈X.V) (diff : z≠f (i+1)) (hit : X.D (f i) z=true) : X.D (f (i+1)) z=true := by
    cases e : X.D (f (i+1)) z
    · exact (failed ⟨i,z,mem_erase.mpr ⟨diff,zv⟩,hit,e⟩).elim
    · rfl
  let E : CH.Digraph := fun x y => decide (∃i,x=f i ∧ y=f (i+1))
  have run (i d) : Walk E M (f i) (f (i+d)) d := by
    induction d with
    | zero => simpa using (Walk.refl (D:=E) (W:=M) (f i))
    | succ d ih =>
      apply ih.snoc (mem _)
      exact decide_eq_true ⟨i+d,rfl,rfl⟩
  have paths (x) (xm : x∈M) (y) (ym : y∈M) : ∃d, Walk E M x y d := by
    obtain ⟨i,im,rfl⟩ := mem_image.mp xm
    obtain ⟨j,jm,rfl⟩ := mem_image.mp ym
    have back := run i (j+N-i)
    rw [show i+(j+N-i)=j+N by have := mem_range.mp im; omega,per] at back
    exact ⟨_,back⟩
  have span : M=X.V := by
    by_contra proper
    have two : 2≤M.card := by
      by_contra! tiny
      have eq := card_le_one.mp (show M.card≤1 by omega) _ (mem 0) _ (mem 1)
      have ed : X.D (f 0) (f 1)=true := native 0
      rw [eq] at ed
      exact loopfree X.free (by omega) (inside 1) ed
    obtain ⟨u,_,v,_,uv,z,zm,uz,vz⟩ := exterior_loss X sub two proper E paths
    obtain ⟨i,rfl,rfl⟩ := of_decide_eq_true uv
    exact Bool.noConfusion (vz.symm.trans (clean i z (mem_sdiff.mp zm).1
      (fun eq => (mem_sdiff.mp zm).2 (eq ▸ mem _)) uz))
  have win (i) : (range N).image (fun j => f (i+j))=X.V := by
    apply eq_of_subset_of_card_le
    · intro x hx; obtain ⟨j,_,rfl⟩ := mem_image.mp hx; exact inside _
    · rw [←span,size,card_image_of_injOn,card_range]
      exact fun u hu v hv h => inj i u v (mem_range.mp hu) (mem_range.mp hv) h
  let deg (i : ℕ) := (inN X.D X.V (f i)).card
  have down (i) : deg (i+1) ≤ deg i := indegree_step X hq (inside i) (inside (i+1))
    (native i) (fun z hz => clean i z (mem_of_mem_erase hz) (mem_erase.mp hz).1)
  have mono := antitone_nat_of_succ_le down
  have reg (v) (vv : v∈X.V) : (inN X.D X.V v).card=deg 0 := by
    rw [←span] at vv
    obtain ⟨i,im,rfl⟩ := mem_image.mp vv
    change deg i=deg 0
    have eqN : deg N=deg 0 := by simp only [deg,show f N=f 0 by simpa using per 0]
    exact le_antisymm (mono (Nat.zero_le i)) (eqN ▸ mono (mem_range.mp im).le)
  have kN : deg 0<N := by
    have ss : inN X.D X.V (f 0) ⊆ X.V.erase (f 0) := by
      intro y hy
      obtain ⟨yv,yf⟩ := mem_inN.mp hy
      exact mem_erase.mpr ⟨fun eq => loopfree X.free (by omega) (inside 0) (eq ▸ yf),yv⟩
    have lt := (card_le_card ss).trans_lt (card_erase_lt_of_mem (inside 0))
    exact lt.trans_eq (congrArg Finset.card span.symm |>.trans size)
  have budget := order_bound X reg
  rw [←span,size] at budget
  obtain ⟨m,bound,walk,pos⟩ := jump_walk inside
    (fun i d pd kd => jump per inside win inj clean (fun j => reg _ (inside j)) kN pd kd) q 0 N budget
  rw [per] at walk
  exact X.free _ m (pos Npos) bound walk

#print axioms periodic_escape

/-- The arguments are in the order expected by well-founded induction:
`Clean X a t` allows a transition from the current vertex t to a. -/
def Clean {q n} (X : Model q n) (a t : X.V) : Prop :=
  X.D t a = true ∧ ∀ z ∈ X.V.erase a.val, X.D t z = true → X.D a z = true

theorem wellFounded {q n} (X : Model q n) (hq : 2≤q) : WellFounded (Clean X) := by
  classical
  apply WellFounded.wellFounded_iff_has_min.mpr
  intro S live
  by_contra! next
  let go (u : X.V) := if hu : u∈S then (next u hu).choose else u
  have moves (u) (hu : u∈S) : go u∈S ∧ Clean X (go u) u := by
    simpa [go,hu] using (next u hu).choose_spec
  obtain ⟨start,hs⟩ := live
  have inside (i : ℕ) : go^[i] start∈S := by
    induction i with
    | zero => exact hs
    | succ i ih => simpa only [Function.iterate_succ_apply'] using (moves _ ih).1
  obtain ⟨i,j,eq,ne⟩ : ∃i j : ℕ,go^[i] start=go^[j] start ∧ i≠j := by
    simpa [Function.Injective] using not_injective_infinite_finite (go^[·] start)
  have closed {i j : ℕ} (lt : i<j) (eq : go^[i] start=go^[j] start) : False := by
    let r := go^[i] start
    have recurs : r∈Function.periodicPts go := by
      apply Function.mk_mem_periodicPts (show 0<j-i by omega)
      change go^[j-i] (go^[i] start)=go^[i] start
      rw [←Function.iterate_add_apply,show j-i+i=j by omega]
      exact eq.symm
    have step (m : ℕ) : Clean X (go^[m+1] r) (go^[m] r) := by
      have hm : go^[m] r∈S := by simpa only [r,←Function.iterate_add_apply] using inside (m+i)
      simpa only [Function.iterate_succ_apply'] using (moves _ hm).2
    obtain ⟨m,z,zm,hit,off⟩ := periodic_escape X hq go r recurs (fun m => (step m).1)
    exact Bool.noConfusion (off.symm.trans ((step m).2 z zm hit))
  exact (lt_or_gt_of_ne ne).elim (fun lt => closed lt eq) (fun lt => closed lt eq.symm)

/-- A recursive state may contain arbitrary extra data. Its clean steps
inherit the strict decrease whenever they project to clean native arcs. -/
theorem transition_induction {q n} (X : Model q n) (hq : 2≤q)
    {State : Type*} (pivot : State → X.V) (edge : State → State → Prop)
    (projects : ∀ ⦃next current⦄, edge next current → Clean X (pivot next) (pivot current)) :
    WellFounded edge :=
  Subrelation.wf (fun h => projects h) ((wellFounded X hq).onFun (f:=pivot))

/-- In any chosen nonempty family of possible pivots, one pivot has an
actual loss witness for every native step staying in that family. -/
theorem terminal {q n} (X : Model q n) (hq : 2≤q) (S : Set X.V) (live : S.Nonempty) :
    ∃t∈S,∀a∈S,X.D t a=true → ∃z∈X.V.erase a.val,X.D t z=true ∧ X.D a z=false := by
  classical
  obtain ⟨t,ts,last⟩ := (wellFounded X hq).has_min S live
  refine ⟨t,ts,?_⟩
  intro a h ed
  by_contra fail
  apply last a h
  refine ⟨ed,?_⟩
  intro z hz tz
  cases az : X.D a z
  · exact (fail ⟨z,hz,tz,az⟩).elim
  · rfl

#print axioms wellFounded
#print axioms transition_induction
#print axioms terminal

/-- From each prescribed pivot clean moves reach a vertex where every
native head has a different head that returns to it in the deletion. -/
theorem terminal_from {q n} (X : Model q n) (hq : 2≤q) (start : X.V) :
    ∃ t : X.V, Relation.ReflTransGen (fun u v => Clean X v u) start t ∧
      ∀ a : X.V,X.D t a=true → ∃ z∈X.V.erase a.val,X.D t z=true ∧ X.D a z=false ∧
        ∃l,0<l ∧ l<q ∧ Walk X.D (X.V.erase t.val) z a.val l := by
  let S : Set X.V := {u | Relation.ReflTransGen (fun i j => Clean X j i) start u}
  obtain ⟨t,reach,last⟩ := (wellFounded X hq).has_min S ⟨start,.refl⟩
  refine ⟨t,reach,?_⟩
  intro a ta
  have dirty : ¬Clean X a t := fun h => last a (Relation.ReflTransGen.tail reach h) h
  obtain ⟨z,zm,tz,az⟩ : ∃z∈X.V.erase a.val,X.D t z=true ∧ X.D a z=false := by
    by_contra miss
    apply dirty
    refine ⟨ta,?_⟩
    intro z zm tz
    cases az : X.D a z
    · exact (miss ⟨z,zm,tz,az⟩).elim
    · rfl
  have zv := mem_of_mem_erase zm
  obtain ⟨_,l,bound,w⟩ := mem_ball.mp (X.sat z zv a.val a.property (by simp [az]))
  have positive : 0<l := by
    cases w with
    | refl => exact ((mem_erase.mp zm).1 rfl).elim
    | step => omega
  refine ⟨z,zm,tz,az,l,positive,by omega,?_⟩
  rcases w.lastVisit t.val with clear|⟨k,j,_,len,back,_⟩
  · exact clear
  · exact (X.free t.val (k+1) (by omega) (by omega) (.step zv tz back)).elim

#print axioms terminal_from

private theorem inside_ball {q n} (X : Model q n) (hq : 2≤q) {t u v l}
    (w : Walk X.D (X.V.erase t) u v l) (vv : v∈X.V) (tv : X.D t v=true)
    {k} (front : Walk X.D X.V t u k) (bound : k+l≤q) :
    Walk X.D ((ball X.D X.V t (q-1)).erase t) u v l := by
  induction w generalizing k with
  | refl => exact .refl _
  | @step a b c j bu ab tail ih =>
    have bv := mem_of_mem_erase bu
    have extended := front.snoc bv ab
    have accessible : b∈ball X.D X.V t (q-1) := by
      cases j with
      | zero =>
        cases tail
        exact mem_ball.mpr ⟨bv,1,by omega,.step bv tv (.refl _)⟩
      | succ j => exact mem_ball.mpr ⟨bv,k+1,by omega,extended⟩
    exact .step (mem_erase.mpr ⟨(mem_erase.mp bu).1,accessible⟩) ab (ih vv tv extended (by omega))

/-- A terminal pivot at cutoff at least three has two incomparable heads.
Both paths between them stay in its punctured (q-1)-ball. -/
theorem terminal_pair {q n} (X : Model q n) (hq : 3≤q) (t : X.V)
    (dirty : ∀a : X.V,X.D t a=true → ∃z∈X.V.erase a.val,X.D t z=true ∧ X.D a z=false) :
    ∃a∈X.V,∃b∈X.V,a≠b ∧ X.D t a=true ∧ X.D t b=true ∧ X.D a b=false ∧ X.D b a=false ∧
      ∃ (i j : ℕ), 2 ≤ i ∧ i < q ∧ 2 ≤ j ∧ j < q ∧ q < i+j ∧
        Walk X.D ((ball X.D X.V t.val (q-1)).erase t.val) a b i ∧
        Walk X.D ((ball X.D X.V t.val (q-1)).erase t.val) b a j := by
  classical
  let H := outN X.D X.V t
  obtain ⟨C,_,cycle,tc,_⟩ := ShortestReturnCertificate.on_model X (by omega) t.property
  obtain ⟨h,hh⟩ := card_pos.mp (show 0<(outN X.D C t).card by rw [cycle.heads t tc]; decide)
  have live : H.Nonempty := ⟨h,mem_outN.mpr ⟨cycle.sub (mem_outN.mp hh).1,(mem_outN.mp hh).2⟩⟩
  have pair : ∃a∈H,∃b∈H,a≠b ∧ X.D a b=false ∧ X.D b a=false := by
    by_contra missing
    have reverse {a b} (ah : a∈H) (bh : b∈H) (diff : a≠b) (ab : X.D a b=false) : X.D b a=true := by
      cases ba : X.D b a
      · exact (missing ⟨a,ah,b,bh,diff,ab,ba⟩).elim
      · rfl
    obtain ⟨a,ah,maximal⟩ := exists_max_image H (fun v => (outN X.D H v).card) live
    obtain ⟨av,ta⟩ := mem_outN.mp ah
    obtain ⟨z,zm,tz,az⟩ := dirty ⟨a,av⟩ ta
    have zv := mem_of_mem_erase zm
    have zh : z∈H := mem_outN.mpr ⟨zv,tz⟩
    have za := reverse ah zh (mem_erase.mp zm).1.symm az
    have sub : insert a (outN X.D H a) ⊆ outN X.D H z := by
      intro v hv
      rcases mem_insert.mp hv with rfl|hv
      · exact mem_outN.mpr ⟨ah,za⟩
      obtain ⟨vh,av'⟩ := mem_outN.mp hv
      refine mem_outN.mpr ⟨vh,?_⟩
      cases zv' : X.D z v
      · have diff : z≠v := by rintro rfl; exact Bool.noConfusion (az.symm.trans av')
        have vz := reverse zh vh diff zv'
        exact (X.free z 3 (by decide) hq (.step av za (.step (mem_outN.mp vh).1 av' (.step zv vz (.refl _))))).elim
      · rfl
    have bound := (card_le_card sub).trans (maximal z zh)
    rw [card_insert_of_notMem (fun h => loopfree X.free (by omega) av (mem_outN.mp h).2)] at bound
    omega
  obtain ⟨a,ah,b,bh,diff,ab,ba⟩ := pair
  have path {u v} (uh : u∈H) (vh : v∈H) (uv : u≠v) (off : X.D u v=false) (back : X.D v u=false) :
      ∃ l : ℕ, 2 ≤ l ∧ l < q ∧ Walk X.D (X.V.erase t.val) u v l := by
    obtain ⟨_,l,le,w⟩ := mem_ball.mp (X.sat u (mem_outN.mp uh).1 v (mem_outN.mp vh).1 (by simp [back]))
    have lower : 2≤l := by
      cases w with
      | refl => exact (uv rfl).elim
      | step _ edge tail =>
        cases tail with
        | refl => exact Bool.noConfusion (off.symm.trans edge)
        | step => omega
    refine ⟨l,lower,by omega,?_⟩
    rcases w.lastVisit t.val with clear|⟨k,j,_,len,hit,_⟩
    · exact clear
    · exact (X.free t.val (k+1) (by omega) (by omega) (.step (mem_outN.mp uh).1 (mem_outN.mp uh).2 hit)).elim
  obtain ⟨i,il,iq,forward⟩ := path ah bh diff ab ba
  obtain ⟨j,jl,jq,reverse⟩ := path bh ah diff.symm ba ab
  exact ⟨a,(mem_outN.mp ah).1,b,(mem_outN.mp bh).1,diff,(mem_outN.mp ah).2,(mem_outN.mp bh).2,
    ab,ba,i,j,il,iq,jl,jq,by
      by_contra! le
      exact X.free a (i+j) (by omega) le ((forward.append reverse).mono (erase_subset _ _)),
    inside_ball X (by omega) forward (mem_outN.mp bh).1 (mem_outN.mp bh).2
      (.step (mem_outN.mp ah).1 (mem_outN.mp ah).2 (.refl _)) (by omega),
    inside_ball X (by omega) reverse (mem_outN.mp ah).1 (mem_outN.mp ah).2
      (.step (mem_outN.mp bh).1 (mem_outN.mp bh).2 (.refl _)) (by omega)⟩

#print axioms terminal_pair

open MarkedCyclePeeling FirstPacketBarrier SharedArcComponentExchange WeightedSD

/-- Re-select a genuinely failed one-arc test. The caller specifies all
eligibility conditions and may allow different attachments on the same source.
Every eligible test based at a clean parent of the selected pivot has a
strict column certificate. -/
theorem first_failure {q n} (X : Model q n) (hq : 2≤q)
    (eligible : Family → X.V → X.V → Prop) {G u v}
    (seed : eligible G u v)
    (failed : ¬SharedArcReachMargin.StrictColumns q (insertArc (graph X.D G) u v) X.V) :
    ∃ F a b, eligible F a b ∧
      ¬SharedArcReachMargin.StrictColumns q (insertArc (graph X.D F) a b) X.V ∧
      ∀ t : X.V, Clean X a t → ∀ K h, eligible K t h →
        SharedArcReachMargin.StrictColumns q (insertArc (graph X.D K) t h) X.V := by
  classical
  let _ : WellFounded (Clean X) := wellFounded X hq
  let bad (a : X.V) := ∃F b,eligible F a b ∧
    ¬SharedArcReachMargin.StrictColumns q (insertArc (graph X.D F) a b) X.V
  let S := univ.filter bad
  have live : S.Nonempty := ⟨u,mem_filter.mpr ⟨mem_univ _,G,v,seed,failed⟩⟩
  obtain ⟨a,am,bound⟩ := exists_max_image S (WellFounded.rank (Clean X)) live
  obtain ⟨F,b,ok,fail⟩ := (mem_filter.mp am).2
  refine ⟨F,a,b,ok,fail,?_⟩
  intro t clean K h test
  by_contra no
  exact (WellFounded.rank_lt_of_rel clean).not_ge
    (bound t (mem_filter.mpr ⟨mem_univ _,K,h,test,no⟩))

#print axioms first_failure

open SharedArcExpansion SharedArcBarrier

/-- Keep the same starting cycle and all the graph and stopping conditions
when choosing across different attachments. -/
structure TestFamily {q n} (X : Model q n) (C : Finset ℕ) (F : Family) : Prop where
  built : Built X.D C F
  native : F ⊆ family X
  seed : C ∈ F
  spans : support F = X.V
  feasible : SmallRow q (graph X.D F) X.V
  stopped : ∀M,Boundary X F M → ¬SmallRow q (graph X.D (insert M F)) X.V
  minimum : ∃B,Boundary X F B ∧ 1<(targets X.D X.V F B).card ∧
    ∀M,Boundary X F M → (targets X.D X.V F B).card ≤ (targets X.D X.V F M).card

theorem stopped_frontier {q n} (X : Model q n) (hq : 2≤q) {C F B}
    (built : Built X.D C F) (within : F⊆family X) (seed : C∈F) (spans : support F=X.V)
    (good : SmallRow q (graph X.D F) X.V) (step : Boundary X F B)
    (least : ∀M,Boundary X F M → (targets X.D X.V F B).card ≤ (targets X.D X.V F M).card)
    (stop : ∀M,Boundary X F M → ¬SmallRow q (graph X.D (insert M F)) X.V)
    (many : 1<(targets X.D X.V F B).card) {a b : X.V} (edge : Fresh X F (a,b))
    (no : ¬SharedArcReachMargin.StrictColumns q (insertArc (graph X.D F) a b) X.V) :
    ∃ (K : Family) (c h : X.V), TestFamily X C K ∧ Fresh X K (c,h) ∧
      ¬SharedArcReachMargin.StrictColumns q (insertArc (graph X.D K) c h) X.V ∧
      ∀t : X.V,Clean X c t → ∀L,TestFamily X C L → ∀w : X.V,Fresh X L (t,w) →
        SharedArcReachMargin.StrictColumns q (insertArc (graph X.D L) t w) X.V := by
  let eligible (K : Family) (u v : X.V) := TestFamily X C K ∧ Fresh X K (u,v)
  have start : eligible F a b := ⟨⟨built,within,seed,spans,good,stop,B,step,many,least⟩,edge⟩
  obtain ⟨K,c,h,⟨familyK,ch⟩,failed,parents⟩ := first_failure X hq eligible start no
  exact ⟨K,c,h,familyK,ch,failed,fun t clean L familyL w tw => parents t clean L w ⟨familyL,tw⟩⟩

#print axioms stopped_frontier

open Matrix
open scoped Matrix

/-- The same strict certificate for the incoming single arc overdraws the
changed column at every fresh head when that head is added. -/
theorem parent_prices {q n} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    {C K} (candidate : TestFamily X C K) {a b t : X.V} (edge : Fresh X K (a,b))
    (no : ¬SharedArcReachMargin.StrictColumns q (insertArc (graph X.D K) a b) X.V)
    (parent : Fresh X K (t,a)) (p : X.V→ℝ) (pn : ∀i,0≤p i) (pm : ∑i,p i=1)
    (strict : ∀i,(p ᵥ* realMatrix q (insertArc (graph X.D K) t a) X.V) i<1) :
    ∀ h : X.V,Fresh X K (a,h) →
      1 < (p ᵥ* realMatrix q (insertArc (graph X.D K) t a) X.V) h + q*p a := by
  classical
  obtain ⟨B,step,many,least⟩ := candidate.minimum
  intro h fresh
  obtain ⟨M,bm,shape⟩ := SharedArcPivotChoice.joint_pair X hq small step least candidate.stopped many edge no parent fresh
  let E := insertArc (graph X.D K) t a
  have ne : t.val≠a.val := fun eq => loopfree X.free (by omega) a.property (by simpa [eq] using parent.2.2.1)
  have off : ¬E a h=true := by simp [E,insertArc,ne.symm,fresh.2.2.2]
  have graphEq : graph X.D (insert M K)=insertArc E a h := by
    funext i j
    apply Bool.eq_iff_iff.mpr
    rw [union_arc,shape]
    by_cases p₁ : i=t.val ∧ j=a.val <;> by_cases p₂ : i=a.val ∧ j=h.val <;>
      simp [SharedArcPivotChoice.pair,E,insertArc,p₁,p₂]
  have diff (j : X.V) :
      (p ᵥ* realMatrix q (insertArc E a h) X.V) j - (p ᵥ* realMatrix q E X.V) j =
        if j=h then (q:ℝ)*p a else 0 := by
    simp only [vecMul,dotProduct,←sum_sub_distrib,←mul_sub,realMatrix_insert_difference a h off]
    by_cases eq : j=h <;> simp [eq,mul_ite,mul_comm]
  by_contra! low
  apply candidate.stopped M bm
  rw [graphEq]
  apply smallRow_of_realDual (p:=realExtendWeight X.V p)
  constructor
  · intro i hi; rw [realExtendWeight_on X.V p ⟨i,hi⟩]; exact pn _
  · rw [realMass_extendWeight]; exact pm
  · intro j hj
    let v : X.V := ⟨j,hj⟩
    rw [←realMatrix_col q (insertArc E a h) X.V _ v,show (fun i : X.V => realExtendWeight X.V p i)=p from
      funext (realExtendWeight_on X.V p)]
    have d := diff v
    by_cases eq : v=h
    · simp only [eq,ite_true] at d
      change (p ᵥ* realMatrix q (insertArc E a h) X.V) v≤1
      rw [eq]; change (p ᵥ* realMatrix q E X.V) h+q*p a≤1 at low
      linarith only [d,low]
    · simp only [eq,ite_false,sub_eq_zero] at d
      exact d.trans_le (strict v).le

#print axioms parent_prices

theorem priced_frontier {q n} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    {C F B} (built : Built X.D C F) (within : F⊆family X) (seed : C∈F) (spans : support F=X.V)
    (good : SmallRow q (graph X.D F) X.V) (step : Boundary X F B)
    (least : ∀M,Boundary X F M → (targets X.D X.V F B).card ≤ (targets X.D X.V F M).card)
    (stop : ∀M,Boundary X F M → ¬SmallRow q (graph X.D (insert M F)) X.V)
    (many : 1<(targets X.D X.V F B).card) {a b : X.V} (edge : Fresh X F (a,b))
    (no : ¬SharedArcReachMargin.StrictColumns q (insertArc (graph X.D F) a b) X.V) :
    ∃ (K : Family) (c h : X.V), TestFamily X C K ∧ Fresh X K (c,h) ∧
      ¬SharedArcReachMargin.StrictColumns q (insertArc (graph X.D K) c h) X.V ∧
      ∀t : X.V,Clean X c t → Fresh X K (t,c) →
        ∃p : X.V→ℝ,(∀i,0≤p i) ∧ (∑i,p i)=1 ∧
          (∀j,(p ᵥ* realMatrix q (insertArc (graph X.D K) t c) X.V) j<1) ∧
          ∀w : X.V,Fresh X K (c,w) →
            1<(p ᵥ* realMatrix q (insertArc (graph X.D K) t c) X.V) w+q*p c := by
  obtain ⟨K,c,h,test,ch,fail,parents⟩ :=
    stopped_frontier X hq built within seed spans good step least stop many edge no
  refine ⟨K,c,h,test,ch,fail,?_⟩
  intro t clean tc
  obtain ⟨p,pn,pm,strict⟩ := parents t clean K test c tc
  exact ⟨p,pn,pm,strict,parent_prices X hq small test ch fail tc p pn pm strict⟩

#print axioms priced_frontier
end LeanCH.BR.Closure.SharedArcCleanRecurrence
