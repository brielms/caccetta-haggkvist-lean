import checkpoints.shen_extension.CoupledSegmentPorts

namespace LeanCH.BR.Closure.SharedArcExpansion
open Finset BRq2 BRq3 BR45 BRsub ShenCycleSuccessor ShortestCycleWeights FirstPacketBarrier MarkedCyclePeeling

def Touch (D : CH.Digraph) (A B : Finset ℕ) : Prop :=
  ∃i∈A∩B,∃j∈A∩B,D i j=true

theorem Touch.symm {D A B} : Touch D A B → Touch D B A := by
  unfold Touch
  rw [inter_comm]
  exact id

def support (F : Family) := F.biUnion id

/-- The recorded family starts at C. Each addition keeps the directed arc
through which it was attached and adds a previously unvisited cycle. -/
inductive Built (D : CH.Digraph) (C : Finset ℕ) : Family → Prop
  | seed : Built D C {C}
  | add {F A B} : Built D C F → A∈F → Touch D A B → B∉F → Built D C (insert B F)

private theorem in_support {F : Family} {A} (af : A∈F) : A⊆support F :=
  fun _ mem => mem_biUnion.mpr ⟨A,af,mem⟩

private theorem supported {q n} {X : Model q n} {F} (sub : F⊆family X) :
    support F⊆X.V := by
  classical
  intro x mem
  obtain ⟨A,af,hx⟩ := mem_biUnion.mp mem
  exact ((mem_filter.mp (sub af)).2 : Cycle X.D X.V q A).sub hx

private theorem seed_mem {D C F} (chain : Built D C F) : C∈F := by
  induction chain with
  | seed => simp
  | add _ _ _ _ ih => exact mem_insert_of_mem ih

private theorem propagate {D C F} (chain : Built D C F) (f : ℕ→Bool)
    (localLaw : ∀A∈F,∀u∈A,∀v∈A,f u=f v) :
    ∀u∈support F,∀v∈support F,f u=f v := by
  induction chain with
  | seed => simpa [support] using localLaw C (by simp)
  | @add F A B _ af touch _ ih =>
    obtain ⟨p,pm,_⟩ := touch
    have pB := (mem_inter.mp pm).2
    have pF := in_support af (mem_inter.mp pm).1
    have old := ih (fun M mf => localLaw M (mem_insert_of_mem mf))
    have same (u) (hu : u∈support (insert B F)) : f u=f p := by
      obtain ⟨M,mg,um⟩ := mem_biUnion.mp hu
      rcases mem_insert.mp mg with rfl|mf
      · exact localLaw _ (mem_insert_self _ _) u um _ pB
      · exact old u (in_support mf um) _ pF
    exact fun u hu v hv => (same u hu).trans (same v hv).symm

private theorem backwards {D A z} (closed : ∀i∈A,∀j∈A,D i j=true → D j z=true → D i z=true)
    {a b len} (path : Walk D A a b len) (ac : a∈A) (ed : D b z=true) : D a z=true := by
  induction path with
  | refl => exact ed
  | step j e _ ih => exact closed _ ac _ j e (ih j ed)

/-- An arc-connected patch on a proper part of the support can always add
a native shortest cycle meeting a previously uncovered vertex. -/
theorem enlarge {q n} (X : Model q n) (hq : 2≤q) {C F} (chain : Built X.D C F)
    (sub : F⊆family X) (proper : support F≠X.V) :
    ∃A∈F,∃B∈family X,Touch X.D A B ∧ ∃z∈B,z∉support F := by
  classical
  by_contra no
  have sc := supported sub
  have const : OutUniform X.D X.V (support F) := by
    intro x xx y yy z zv out
    apply propagate chain (fun i => X.D i z) _ x xx y yy
    intro A af a aa b ba
    have ca : Cycle X.D X.V q A := (mem_filter.mp (sub af)).2
    have closed (i) (ic : i∈A) (j) (jc : j∈A) (ij : X.D i j=true) (jz : X.D j z=true) : X.D i z=true := by
      by_contra missing
      obtain ⟨B,cb,ib,jb,zb⟩ := SaturatedCycleClasses.missing hq X.free X.sat
        (ca.sub ic) (ca.sub jc) zv ij jz missing
      exact no ⟨A,af,B,mem_filter.mpr ⟨mem_powerset.mpr cb.sub,cb⟩,
        ⟨i,mem_inter.mpr ⟨ic,ib⟩,j,mem_inter.mpr ⟨jc,jb⟩,ij⟩,z,zb,out⟩
    obtain ⟨_,_,ab,back⟩ := MandatoryExcursion.segments (by omega : 1≤q) X.free ca aa ba
    exact Bool.eq_iff_iff.mpr ⟨backwards closed back ba,backwards closed ab aa⟩
  have cf := seed_mem chain
  have cy : Cycle X.D X.V q C := (mem_filter.mp (sub cf)).2
  have size := (cy.size ▸ card_le_card (in_support cf) : q+1≤(support F).card)
  exact X.prime _ sc (by omega) proper ⟨const,outUniform_inUniform X.free X.sat sc const⟩

/-- Two common vertices force an intermediate shortest cycle sharing one
actual arc with each original cycle. Both arcs meet at the named vertex j. -/
theorem splice {q n} (X : Model q n) (hq : 2≤q) {A B} (ca : Cycle X.D X.V q A)
    (cb : Cycle X.D X.V q B) {i j} (ii : i∈A∩B) (jj : j∈A∩B) (ne : i≠j) :
    ∃M∈family X,Touch X.D A M ∧ Touch X.D M B := by
  classical
  have ia := (mem_inter.mp ii).1
  have ib := (mem_inter.mp ii).2
  have ja := (mem_inter.mp jj).1
  have jb := (mem_inter.mp jj).2
  obtain ⟨lo,hi,front,_⟩ := MandatoryExcursion.segments (by omega : 1≤q) X.free ca ia ja
  obtain ⟨_,_,_,back⟩ := MandatoryExcursion.segments (by omega : 1≤q) X.free cb ib jb
  let d := MandatoryExcursion.span X.D X.V q i j
  change Walk X.D A i j d at front
  change Walk X.D B j i (q+1-d) at back
  change 1≤d at lo
  change d≤q+1 at hi
  have bp : 0<q+1-d := by
    by_contra! zero
    rw [show q+1-d=0 by omega] at back
    cases back
    exact ne rfl
  obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero (show d≠0 by omega)
  obtain ⟨l,hl⟩ := Nat.exists_eq_succ_of_ne_zero (show q+1-d≠0 by omega)
  rw [hk] at front
  rw [hl] at back
  obtain ⟨p,prefixPath,_,pj⟩ := front.unsnoc
  have pa : p∈A := prefixPath.end_mem_or.elim (fun eq => eq ▸ ia) id
  cases back with
  | step hb jh tail =>
    have miss : ¬X.D p _=true := fun ph =>
      X.free i (k+1+l) (by omega) (by omega) (((prefixPath.mono ca.sub).snoc (cb.sub hb) ph).append (tail.mono cb.sub))
    obtain ⟨M,cm,pm,jm,hm⟩ := SaturatedCycleClasses.missing hq X.free X.sat (ca.sub pa) (ca.sub ja) (cb.sub hb) pj jh miss
    exact ⟨M,mem_filter.mpr ⟨mem_powerset.mpr cm.sub,cm⟩,
      ⟨p,mem_inter.mpr ⟨pa,pm⟩,j,mem_inter.mpr ⟨ja,jm⟩,pj⟩,
      ⟨j,mem_inter.mpr ⟨jm,jb⟩,_,mem_inter.mpr ⟨hm,hb⟩,jh⟩⟩

/-- A spanning patch of at most q cycles is within two arc-sharing steps
of *each* prescribed native shortest cycle. -/
theorem two_steps {q n} (X : Model q n) (hq : 2≤q) {F}
    (sub : F⊆family X) (cover : support F=X.V) (few : F.card≤q) {B} (cb : Cycle X.D X.V q B) :
    ∃A∈F,∃M∈family X,Touch X.D A M ∧ Touch X.D M B := by
  classical
  have hit : ∃A∈F,1<(A∩B).card := by
    by_contra! thin
    have into : B⊆F.biUnion (fun A => A∩B) := by
      intro z zb
      obtain ⟨A,af,za⟩ := mem_biUnion.mp (cover ▸ cb.sub zb : z∈support F)
      exact mem_biUnion.mpr ⟨A,af,mem_inter.mpr ⟨za,zb⟩⟩
    have b := (card_le_card into).trans card_biUnion_le
    have lim := sum_le_sum thin
    rw [sum_const,nsmul_eq_mul,Nat.mul_one] at lim
    change (∑a∈F,(a∩B).card)≤F.card at lim
    exact (by have := cb.size; omega)
  obtain ⟨A,af,rich⟩ := hit
  obtain ⟨i,ii,j,jj,ne⟩ := one_lt_card.mp rich
  exact ⟨A,af,splice X hq (mem_filter.mp (sub af)).2 cb ii jj ne⟩

#print axioms enlarge
#print axioms splice
#print axioms two_steps
/-- From any assembled patch, add at most one cycle per missing vertex
to cover the entire native support, with a strictly increasing carrier. -/
theorem span_all {q n} (X : Model q n) (hq : 2≤q) {C F} (chain : Built X.D C F)
    (sub : F⊆family X) : ∃G : Family,F⊆G ∧ Built X.D C G ∧ G⊆family X ∧
      support G=X.V ∧ G.card+(support F).card≤F.card+X.V.card := by
  classical
  by_cases full : support F=X.V
  · exact ⟨F,Subset.rfl,chain,sub,full,by rw [full]⟩
  obtain ⟨A,af,B,bf,touch,z,zb,fresh⟩ := enlarge X hq chain sub full
  have newB : B∉F := fun bad => fresh (in_support bad zb)
  have more : support F⊂support (insert B F) := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨biUnion_subset.mpr (fun T tf => in_support (mem_insert_of_mem tf)),?_⟩
    exact fun eq => fresh (eq.symm ▸ in_support (mem_insert_self B F) zb)
  have newsub := insert_subset bf sub
  have gt := card_lt_card more
  have _ := card_le_card (supported newsub)
  obtain ⟨G,fg,cg,sg,all,size⟩ := span_all X hq (chain.add af touch newB) newsub
  rw [card_insert_of_notMem newB] at size
  exact ⟨G,(subset_insert B F).trans fg,cg,sg,all,by omega⟩
termination_by X.V.card-(support F).card

def Linked {q n} (X : Model q n) : Finset ℕ → Finset ℕ → Prop :=
  Relation.EqvGen (fun A B => A∈family X ∧ B∈family X ∧ Touch X.D A B)

private theorem linked_of_built {q n} {X : Model q n} {C F} (chain : Built X.D C F)
    (sub : F⊆family X) : ∀A∈F,Linked X C A := by
  induction chain with
  | seed =>
    intro A af
    obtain rfl := mem_singleton.mp af
    exact .refl _
  | @add F A B prev af touch _ ih =>
    have small := (subset_insert B F).trans sub
    intro M mf
    rcases mem_insert.mp mf with rfl|old
    · exact .trans _ _ _ (ih small A af) (.rel _ _ ⟨small af,sub (mem_insert_self _ _),touch⟩)
    · exact ih small _ old

/-- Any given native vertex lies on a cycle reachable from the prescribed
seed by shared directed arcs. A finite witness family is built by span_all. -/
theorem reaches_vertex {q n} (X : Model q n) (hq : 2≤q) {C} (cf : C∈family X)
    {v} (vv : v∈X.V) : ∃A∈family X,Linked X C A ∧ v∈A := by
  have initial : Built X.D C {C} := .seed
  obtain ⟨G,_,cg,sg,all,_⟩ := span_all X hq initial (singleton_subset_iff.mpr cf)
  obtain ⟨A,ag,va⟩ := mem_biUnion.mp (all.symm ▸ vv : v∈support G)
  exact ⟨A,sg ag,linked_of_built cg sg A ag,va⟩

/-- A cycle outside the arc component meets every member in at most one vertex. -/
theorem overlap_bound {q n} (X : Model q n) (hq : 2≤q) {C B} (cf : C∈family X) (bf : B∈family X)
    (apart : ¬Linked X C B) : (C∩B).card≤1 := by
  classical
  by_contra! rich
  obtain ⟨i,ii,j,jj,ne⟩ := one_lt_card.mp rich
  obtain ⟨M,mf,cm,mb⟩ := splice X hq (mem_filter.mp cf).2 (mem_filter.mp bf).2 ii jj ne
  exact apart (.trans _ _ _ (.rel _ _ ⟨cf,mf,cm⟩) (.rel _ _ ⟨mf,bf,mb⟩))

/-- Every native arc-sharing component has empty common intersection.
This uses strictness to obtain an unrestricted cycle avoiding the mark,
then primeness and saturation to transfer avoidance to the chosen component. -/
theorem avoids_vertex {q n} (X : Model q n) (hq : 2≤q) {C} (cf : C∈family X)
    (h : ℕ) : ∃B∈family X,Linked X C B ∧ h∉B := by
  classical
  by_contra! stuck
  have cy : Cycle X.D X.V q C := (mem_filter.mp cf).2
  have hc := stuck C cf (.refl _)
  have all : ∀B∈family X,Linked X C B := by
    intro B bf
    obtain ⟨T,tf,bt,ht⟩ := reaches_vertex X hq bf (cy.sub hc)
    have ct : Cycle X.D X.V q T := (mem_filter.mp tf).2
    obtain ⟨z,zt,ne⟩ := exists_mem_ne (a:=h) (show 1<T.card by rw [ct.size]; omega)
    obtain ⟨A,af,ca,za⟩ := reaches_vertex X hq cf (ct.sub zt)
    have ha := stuck A af ca
    have fat : 1<(A∩T).card := one_lt_card.mpr
      ⟨z,mem_inter.mpr ⟨za,zt⟩,h,mem_inter.mpr ⟨ha,ht⟩,ne⟩
    have atLink : Linked X A T := by
      by_contra no
      exact fat.not_ge (overlap_bound X hq af tf no)
    exact .trans _ _ _ (.trans _ _ _ ca atLink) (.symm _ _ bt)
  apply CycleCoverWeights.common_false hq X.free cy (x:=fun i => (X.weights i : ℚ))
    (fun _ _ => Nat.cast_nonneg _) X.strict
  intro u uv v vv edge
  obtain ⟨M,cm,um,vm⟩ := edge_cycle X hq uv vv edge
  have mf : M∈family X := mem_filter.mpr ⟨mem_powerset.mpr cm.sub,cm⟩
  exact ⟨M,cm,stuck M mf (all M mf),um,vm⟩

/-- A family retaining even one common label admits an outgoing step to
a genuinely new cycle. No size bound or spanning assumption is needed. -/
theorem escape {q n} (X : Model q n) (hq : 2≤q) {F : Family} {C h}
    (cf : C∈F) (sub : F⊆family X) (mark : ∀A∈F,h∈A) :
    ∃A∈F,∃B∈family X,B∉F ∧ Touch X.D A B := by
  classical
  by_contra no
  have lift {A B} (reach : Linked X A B) : A∈F ↔ B∈F := by
    induction reach with
    | refl => rfl
    | rel A B e =>
      exact ⟨fun af => by by_contra nb; exact no ⟨A,af,B,e.2.1,nb,e.2.2⟩,
        fun bf => by by_contra na; exact no ⟨B,bf,A,e.1,na,e.2.2.symm⟩⟩
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ab bc => exact ab.trans bc
  obtain ⟨B,_,way,miss⟩ := avoids_vertex X hq (sub cf) h
  exact miss (mark B ((lift way).mp cf))

#print axioms span_all
#print axioms reaches_vertex
#print axioms overlap_bound
#print axioms avoids_vertex
#print axioms escape
end LeanCH.BR.Closure.SharedArcExpansion
