import checkpoints.shen_extension.LastArcCompetitor

namespace LeanCH.BR.Closure.LastArcDistanceConflict
open Finset BRq2 BRq3 BR45 WeightedSD FiniteCutInverse ShenCycleSuccessor FirstPacketBarrier
open ShortestCycleWeights SharedArcBarrier SharedArcComponentExchange
open MarkedCyclePeeling hiding Arc

/-- Necessary distance and matching conditions for two arcs to lie on one
shortest cycle. A repeated arc is eligible as its own representative. -/
def Fits {q n} (X : Model q n) (e f : Arc) : Prop :=
  e = f ∨ (e.1 ≠ f.1 ∧ e.2 ≠ f.2 ∧
    PuncturedDistance.depth X.D X.V e.2 f.1 +
    PuncturedDistance.depth X.D X.V f.2 e.1 = q-1)

theorem fits_on_cycle {q n F M} (X : Model q n) (hq : 2 ≤ q)
    (cm : Cycle X.D X.V q M) {e f : Arc}
    (em : e ∈ added X.D F M) (fm : f ∈ added X.D F M) : Fits X e f := by
  classical
  by_cases eq : e=f
  · exact Or.inl eq
  have tails : e.1 ≠ f.1 := fun h => eq (matching cm em fm (Or.inl h))
  have heads : e.2 ≠ f.2 := fun h => eq (matching cm em fm (Or.inr h))
  obtain ⟨et,eh,ed,_⟩ := mem_added.mp em
  obtain ⟨ft,fh,fd,_⟩ := mem_added.mp fm
  let d := PuncturedDistance.depth X.D X.V
  have riseF : d e.2 f.2 = d e.2 f.1 + 1 :=
    PuncturedDistance.rise_on_cycle X.free cm eh ft fh heads.symm fd
  have riseE : d f.2 e.2 = d f.2 e.1 + 1 :=
    PuncturedDistance.rise_on_cycle X.free cm fh et eh heads ed
  have seg := MandatoryExcursion.segments (by omega : 1 ≤ q) X.free cm eh fh
  have rev := MandatoryExcursion.segments (by omega : 1 ≤ q) X.free cm fh eh
  simp only [MandatoryExcursion.span, ite_eq_right heads, ite_eq_right heads.symm] at seg rev
  obtain ⟨pos,cap,go,back⟩ := seg
  have upper := PuncturedDistance.depth_le_walk (back.mono cm.sub)
  have lower : q < d e.2 f.2 + d f.2 e.2 := by
    by_contra! short
    exact X.free e.2 _ (Nat.add_pos_left pos _) short ((go.mono cm.sub).append (rev.2.2.1.mono cm.sub))
  refine Or.inr ⟨tails,heads,?_⟩
  change d e.2 f.1 + d f.2 e.1 = q-1
  change 1 ≤ d e.2 f.2 at pos
  change d e.2 f.2 ≤ q+1 at cap
  change d f.2 e.2 ≤ q+1-d e.2 f.2 at upper
  omega

abbrev Minimum {q n} (X : Model q n) (F : Family) (B : Finset ℕ) :=
  ∀ M, Boundary X F M → (targets X.D X.V F B).card ≤ (targets X.D X.V F M).card

/-- For each fresh arc, the labels that fail its distance or endpoint test
can occupy at most one slot of an original minimum packet. -/
theorem at_most_one {q n F B} (X : Model q n) (hq : 2 ≤ q)
    (small : SmallerSmallRow q X.V.card) (step : Boundary X F B) (least : Minimum X F B)
    (bad : ¬SmallRow q (graph X.D (insert B F)) X.V) {e f g : Arc} (fresh : Fresh X F e)
    (fm : f ∈ added X.D F B) (gm : g ∈ added X.D F B)
    (failF : ¬ Fits X e f) (failG : ¬ Fits X e g) : f = g := by
  classical
  let u : X.V := ⟨e.1,fresh.1⟩
  let v : X.V := ⟨e.2,fresh.2.1⟩
  have absent : graph X.D (insert B F) u v = false := by
    apply Bool.eq_false_iff.mpr
    intro hit
    rcases union_arc.mp hit with old | marked
    · exact Bool.noConfusion (fresh.2.2.2.symm.trans old)
    · exact failF (fits_on_cycle X hq (mem_filter.mp step.1).2 marked fm)
  obtain ⟨M, bm, em, full | ⟨h,_,swap⟩⟩ :=
    LastArcCompetitor.packet X hq small step least bad u v fresh.2.2.1 absent
  · exact (failF (fits_on_cycle X hq (mem_filter.mp bm.1).2 em (full.1 ▸ mem_insert_of_mem fm))).elim
  · have forces (z : Arc) (zm : z ∈ added X.D F B) (hz : ¬ Fits X e z) : z = h := by
      by_contra ne
      apply hz
      exact fits_on_cycle X hq (mem_filter.mp bm.1).2 em
        (swap ▸ mem_insert_of_mem (mem_erase.mpr ⟨ne,zm⟩))
    exact (forces f fm failF).trans (forces g gm failG).symm

private theorem move_minimum {q n F B} (X : Model q n) (hq : 2 ≤ q)
    (small : SmallerSmallRow q X.V.card) (step : Boundary X F B) (least : Minimum X F B)
    (stop : ∀ M, Boundary X F M → ¬SmallRow q (graph X.D (insert M F)) X.V)
    {f g} (fm : f ∈ added X.D F B) (way : Relation.ReflTransGen (neighbor X F) f g) :
    g ∉ (added X.D F B).erase f ∧ ∃ M, Boundary X F M ∧ Minimum X F M ∧
      added X.D F M = insert g ((added X.D F B).erase f) := by
  classical
  obtain ⟨out,M,bm,swap⟩ := transport X hq small step least stop fm way
  have equal : (targets X.D X.V F M).card = (targets X.D X.V F B).card := by
    rw [←count (mem_filter.mp bm.1).2, ←count (mem_filter.mp step.1).2, swap, card_insert_of_notMem out]
    exact card_erase_add_one fm
  exact ⟨out,M,bm,fun K bk => equal.trans_le (least K bk),swap⟩

/-- Reapply the single-packet test after two independent sequences of
endpoint exchanges. At most one represented incidence component contains
any arc conflicting with a given fresh arc. -/
theorem one_exceptional_component {q n F B} (X : Model q n) (hq : 2 ≤ q)
    (small : SmallerSmallRow q X.V.card) (step : Boundary X F B) (least : Minimum X F B)
    (stop : ∀ M, Boundary X F M → ¬SmallRow q (graph X.D (insert M F)) X.V)
    {e f g f' g' : Arc} (fresh : Fresh X F e)
    (fm : f ∈ added X.D F B) (gm : g ∈ added X.D F B)
    (wf : Relation.ReflTransGen (neighbor X F) f f')
    (wg : Relation.ReflTransGen (neighbor X F) g g')
    (failF : ¬ Fits X e f') (failG : ¬ Fits X e g') : f = g := by
  classical
  by_contra ne
  obtain ⟨out,M,bm,lm,swap⟩ := move_minimum X hq small step least stop fm wf
  have frozen : g ∈ (added X.D F B).erase f := mem_erase.mpr ⟨Ne.symm ne,gm⟩
  have gm' : g ∈ added X.D F M := swap ▸ mem_insert_of_mem frozen
  have fm' : f' ∈ added X.D F M := swap ▸ mem_insert_self _ _
  have kept : f' ∈ (added X.D F M).erase g :=
    mem_erase.mpr ⟨fun eq => out (eq ▸ frozen),fm'⟩
  obtain ⟨out',N,bn,ln,final⟩ := move_minimum X hq small bm lm stop gm' wg
  have first : f' ∈ added X.D F N := final ▸ mem_insert_of_mem kept
  have second : g' ∈ added X.D F N := final ▸ mem_insert_self _ _
  have eq := at_most_one X hq small bn ln (stop N bn) fresh first second failF failG
  exact out' (eq ▸ kept)

/-- A failing distance test pins the debit to the specified original label.
The mixed prices are measured on the same single-arc insertion. -/
theorem named_price {q n F B} (X : Model q n) (hq : 2 ≤ q)
    (small : SmallerSmallRow q X.V.card) (step : Boundary X F B) (least : Minimum X F B)
    (stop : ∀ M, Boundary X F M → ¬SmallRow q (graph X.D (insert M F)) X.V)
    {x ρ d} {H : Matrix X.V X.V ℝ}
    (old : OmittedCycleProgress.Flat q (graph X.D (insert B F)) X.V x ρ d)
    (inv : CommonInverse (realMatrix q (graph X.D (insert B F)) X.V) H)
    (u v a b : X.V) (uv : X.D u v = true) (off : graph X.D (insert B F) u v = false)
    (mark : (a.val,b.val) ∈ added X.D F B) (conflict : ¬ Fits X (u.val,v.val) (a.val,b.val)) :
    ∃ w π c, OmittedCycleProgress.Flat q (insertArc (graph X.D (insert B F)) u v) X.V w π c ∧
      (q:ℚ)*ρ u*w v = c-d ∧ (q:ℚ)*π u*x v = c-d ∧ 0 < c-d ∧
      ∃ M, Boundary X F M ∧
        added X.D F M = insert (u.val,v.val) ((added X.D F B).erase (a.val,b.val)) ∧
        let debit := (q:ℝ)*((c:ℝ)-d)*H b u*H v a
        let credit := ((q:ℝ)*H b a-1)*(((d:ℝ)-1)*((c:ℝ)-1)*(∑i,H i u)*(∑j,H v j))
        credit < debit ∧ (debit ≤ credit → SharedArcPivotGate.ProgressAt X F B H ρ d) := by
  classical
  obtain ⟨w,π,c,flat,p₁,p₂,gain,M,bm,em,full | ⟨i,j,_,swap,price,_,exitGate⟩⟩ :=
    LastArcCompetitor.fork X hq small step least stop old inv u v uv off
  · exact (conflict (fits_on_cycle X hq (mem_filter.mp bm.1).2 em (full.1 ▸ mem_insert_of_mem mark))).elim
  · have same : (a.val,b.val) = (i.val,j.val) := by
      by_contra ne
      exact conflict (fits_on_cycle X hq (mem_filter.mp bm.1).2 em
        (swap ▸ mem_insert_of_mem (mem_erase.mpr ⟨ne,mark⟩)))
    have ai : a=i := Subtype.ext (congrArg Prod.fst same)
    have bj : b=j := Subtype.ext (congrArg Prod.snd same)
    subst i
    subst j
    exact ⟨w,π,c,flat,p₁,p₂,gain,M,bm,swap,price,exitGate⟩

/-- Both endpoints are actual boundary cycles over the same original family.
A step adds just one native arc and preserves every prior added arc. -/
def Keep {q n} (X : Model q n) (F : Family) (A C : Finset ℕ) : Prop :=
  Boundary X F A ∧ Boundary X F C ∧ ∃ e : Arc,
    e ∉ added X.D F A ∧ added X.D F C = insert e (added X.D F A)

inductive KeepTrace {q n} (X : Model q n) (F : Family) (A : Finset ℕ) : ℕ → Finset ℕ → Prop where
  | start : KeepTrace X F A 0 A
  | next {k B C} : KeepTrace X F A k B → Keep X F B C → KeepTrace X F A (k+1) C

theorem trace_size {q n F A k C} {X : Model q n} (path : KeepTrace X F A k C) :
    (added X.D F A).card + k = (added X.D F C).card := by
  induction path with
  | start => simp
  | next _ step ih =>
    obtain ⟨_,_,e,fresh,addedEq⟩ := step
    rw [addedEq,card_insert_of_notMem fresh,←ih]
    omega

private theorem packet_bound {q n F C} (X : Model q n) (bc : Boundary X F C) :
    (added X.D F C).card ≤ q := by
  classical
  have cc : Cycle X.D X.V q C := (mem_filter.mp bc.1).2
  obtain ⟨A,af,i,im,j,jm,ij⟩ := bc.2.2
  obtain ⟨ia,ic⟩ := mem_inter.mp im
  obtain ⟨ja,jc⟩ := mem_inter.mp jm
  have kept : graph X.D F i j = true := active.mpr ⟨A,mem_col.mpr ⟨af,ia,ja,ij⟩⟩
  have misses : j ∉ targets X.D X.V F C := by
    intro h
    obtain ⟨_,_,v,vc,vj,off⟩ := mem_filter.mp h
    have same := card_le_one.mp (cc.incoming j jc).le _ (mem_inN.mpr ⟨vc,vj⟩) _ (mem_inN.mpr ⟨ic,ij⟩)
    exact Bool.noConfusion (off.symm.trans (same ▸ kept))
  have strict : targets X.D X.V F C ⊂ C := Finset.ssubset_iff_subset_ne.mpr
    ⟨fun _ h => (mem_filter.mp h).2.1, fun eq => misses (by rw [eq]; exact jc)⟩
  have bound := card_lt_card strict
  rw [←count cc,cc.size] at bound
  omega

/-- The saturation uses reachable packets only. At its terminal cycle, replay
any still-missing arc back at the original attachment. The resulting genuine
boundary competitor must discard some currently installed arc. -/
theorem saturate {q n F B} (X : Model q n) (hq : 2 ≤ q)
    (small : SmallerSmallRow q X.V.card) (step : Boundary X F B) (least : Minimum X F B)
    (bad : ¬SmallRow q (graph X.D (insert B F)) X.V) :
    ∃ k C, KeepTrace X F B k C ∧ Boundary X F C ∧
      (added X.D F B).card + k ≤ q ∧ (∀ L, ¬Keep X F C L) ∧
      ∀ u v : X.V, X.D u v = true → graph X.D (insert C F) u v = false →
        ∃ M, Boundary X F M ∧ (u.val,v.val) ∈ added X.D F M ∧
          added X.D F M ⊆ insert (u.val,v.val) (added X.D F B) ∧
          ∃ f ∈ added X.D F C, f ∉ added X.D F M := by
  classical
  let pool := (family X).filter (fun L => ∃ k, KeepTrace X F B k L)
  have initial : B ∈ pool := mem_filter.mpr ⟨step.1,0,.start⟩
  obtain ⟨C,cm,maxC⟩ := exists_max_image pool (fun L => (added X.D F L).card) ⟨B,initial⟩
  obtain ⟨k,path⟩ := (mem_filter.mp cm).2
  have bc : Boundary X F C := by cases path with | start => exact step | next _ edge => exact edge.2.1
  have sub {j L} (walk : KeepTrace X F B j L) : added X.D F B ⊆ added X.D F L := by
    induction walk with
    | start => exact Subset.rfl
    | next _ edge ih =>
      obtain ⟨_,_,e,_,eq⟩ := edge
      exact eq ▸ ih.trans (subset_insert e _)
  have terminal (L) : ¬Keep X F C L := by
    intro link
    have nextPath := KeepTrace.next path link
    obtain ⟨_,bl,e,off,eq⟩ := link
    have inPool : L ∈ pool := mem_filter.mpr ⟨bl.1,k+1,nextPath⟩
    have cap := maxC L inPool
    rw [eq,card_insert_of_notMem off] at cap
    omega
  refine ⟨k,C,path,bc,(trace_size path).trans_le (packet_bound X bc),terminal,?_⟩
  intro u v uv off
  have offC : (u.val,v.val) ∉ added X.D F C := fun hit =>
    Bool.noConfusion (off.symm.trans (union_arc.mpr (Or.inr hit)))
  have offB : graph X.D (insert B F) u v = false := by
    apply Bool.eq_false_iff.mpr
    intro hit
    rcases union_arc.mp hit with old | mark
    · exact Bool.noConfusion (off.symm.trans (union_arc.mpr (Or.inl old)))
    · exact offC (sub path mark)
  obtain ⟨M,bm,em,alt⟩ := LastArcCompetitor.packet X hq small step least bad u v uv offB
  have upper : added X.D F M ⊆ insert (u.val,v.val) (added X.D F B) := by
    rcases alt with ⟨eq,_⟩ | ⟨f,_,eq⟩
    · exact eq ▸ Subset.rfl
    · exact eq ▸ insert_subset_insert _ (erase_subset _ _)
  refine ⟨M,bm,em,upper,?_⟩
  apply not_subset.mp
  intro retain
  have eq := Subset.antisymm (upper.trans (insert_subset_insert _ (sub path))) (insert_subset em retain)
  exact terminal M ⟨bc,bm,_,offC,eq⟩

private theorem endpoint_unique {D V q M} (cm : Cycle D V q M)
    {k p a b} (pm : p ∈ M) (wa : Walk D M p a k) (wb : Walk D M p b k) : a=b := by
  induction k generalizing p a b with
  | zero => cases wa; cases wb; rfl
  | succ k ih =>
    cases wa with
    | @step _ y _ _ ym py tail =>
      cases wb with
      | @step _ z _ _ zm pz rest =>
        have eq : y=z := card_le_one.mp (cm.heads p pm).le _ (mem_outN.mpr ⟨ym,py⟩) _ (mem_outN.mpr ⟨zm,pz⟩)
        subst z
        exact ih ym tail rest

private theorem walk_at_depth {q n M h a} (X : Model q n) (hq : 2 ≤ q) (cm : Cycle X.D X.V q M)
    (hm : h∈M) (am : a∈M) : Walk X.D M h a (PuncturedDistance.depth X.D X.V h a) := by
  by_cases sameVertex : h=a
  · subst a
    have zero := Nat.eq_zero_of_le_zero (PuncturedDistance.depth_le_walk (Walk.refl (D:=X.D) (W:=X.V) h))
    exact zero ▸ Walk.refl h
  · have path := (MandatoryExcursion.segments (by omega : 1 ≤ q) X.free cm hm am).2.2.1
    simpa only [MandatoryExcursion.span,ite_eq_right sameVertex] using path


/-- Assign positions 0 through q-1 from both ends of the return. -/
def Positions {q n} (X : Model q n) (u v : ℕ) (S : Finset Arc) : Prop :=
  let outPos := fun f : Arc => PuncturedDistance.depth X.D X.V v f.1
  let backPos := fun f : Arc => PuncturedDistance.depth X.D X.V f.2 u
  (∀ f ∈ S, outPos f + backPos f = q-1) ∧
    Set.InjOn outPos (S : Set Arc) ∧ Set.InjOn backPos (S : Set Arc)

private theorem positions_of_carried {q n F M S u v} (X : Model q n) (hq : 2 ≤ q)
    (cm : Cycle X.D X.V q M) (em : (u,v) ∈ added X.D F M)
    (no : (u,v) ∉ S) (kept : S ⊆ added X.D F M) : Positions X u v S := by
  classical
  let outPos := fun f : Arc => PuncturedDistance.depth X.D X.V v f.1
  let backPos := fun f : Arc => PuncturedDistance.depth X.D X.V f.2 u
  have sumPos (f) (hf : f∈S) : outPos f + backPos f = q-1 := by
    rcases fits_on_cycle X hq cm em (kept hf) with eq | compatible
    · exact (no (eq ▸ hf)).elim
    · exact compatible.2.2
  have inj : Set.InjOn outPos (S : Set Arc) := by
    intro f hf g hg same
    have vm := (mem_added.mp em).2.1
    have wf := walk_at_depth X hq cm vm (mem_added.mp (kept hf)).1
    have wg := walk_at_depth X hq cm vm (mem_added.mp (kept hg)).1
    change PuncturedDistance.depth X.D X.V v f.1 = PuncturedDistance.depth X.D X.V v g.1 at same
    exact matching cm (kept hf) (kept hg) (Or.inl (endpoint_unique cm vm wf (same ▸ wg)))
  refine ⟨sumPos,inj,?_⟩
  intro f hf g hg eq
  have first := sumPos f hf
  have second := sumPos g hg
  change backPos f = backPos g at eq
  apply inj hf hg
  omega

/-- With at most one common deletion, both lists have distinct positions. -/
theorem return_positions {q n F B} (X : Model q n) (hq : 2 ≤ q)
    (small : SmallerSmallRow q X.V.card) (step : Boundary X F B) (least : Minimum X F B)
    (bad : ¬SmallRow q (graph X.D (insert B F)) X.V)
    (u v : X.V) (uv : X.D u v=true) (off : graph X.D (insert B F) u v=false) :
    let P := added X.D F B
    ∃ S ⊆ P, P.card ≤ S.card+1 ∧ Positions X u v S := by
  classical
  intro P
  obtain ⟨M,bm,em,alt⟩ := LastArcCompetitor.packet X hq small step least bad u v uv off
  have select : ∃ S ⊆ P, P.card ≤ S.card+1 ∧ S ⊆ added X.D F M := by
    rcases alt with ⟨full,_⟩ | ⟨f,mark,swap⟩
    · exact ⟨P,Subset.rfl,by omega,full ▸ subset_insert _ _⟩
    · exact ⟨P.erase f,erase_subset _ _,(card_erase_add_one mark).symm.le,swap ▸ subset_insert _ _⟩
  obtain ⟨S,sub,size,kept⟩ := select
  have no : (u.val,v.val) ∉ S := fun h => Bool.noConfusion (off.symm.trans (union_arc.mpr (Or.inr (sub h))))
  exact ⟨S,sub,size,positions_of_carried X hq (mem_filter.mp bm.1).2 em no kept⟩

/-- Count distinct usable levels. A wrong sum and a time-slot collision
among other arcs count against the same one available deletion. -/
theorem position_count {q n F B} (X : Model q n) (hq : 2 ≤ q)
    (small : SmallerSmallRow q X.V.card) (step : Boundary X F B) (least : Minimum X F B)
    (bad : ¬SmallRow q (graph X.D (insert B F)) X.V)
    (u v : X.V) (uv : X.D u v=true) (off : graph X.D (insert B F) u v=false) :
    let P := added X.D F B
    let pos := fun f : Arc => PuncturedDistance.depth X.D X.V v.val f.1
    let eligible := P.filter (fun f => pos f + PuncturedDistance.depth X.D X.V f.2 u.val = q-1)
    P.card ≤ (eligible.image pos).card + 1 := by
  classical
  intro P pos eligible
  obtain ⟨S,sub,room,sums,inj,_⟩ := return_positions X hq small step least bad u v uv off
  have kept : S ⊆ eligible := fun f hf => mem_filter.mpr ⟨sub hf,sums f hf⟩
  have cap := card_le_card (image_subset_image (f:=pos) kept)
  rw [card_image_of_injOn inj] at cap
  exact room.trans (Nat.add_le_add_right cap 1)

/-- A position failure forces a genuine competitor that omits one arc.
Its deletion repairs all position constraints, and its payment margin at a
stuck attachment is strictly negative on that very arc. -/
theorem price_on_position_failure {q n F B} (X : Model q n) (hq : 2 ≤ q)
    (small : SmallerSmallRow q X.V.card) (step : Boundary X F B) (least : Minimum X F B)
    (stop : ∀ M, Boundary X F M → ¬SmallRow q (graph X.D (insert M F)) X.V)
    {x ρ d} {H : Matrix X.V X.V ℝ} (old : OmittedCycleProgress.Flat q (graph X.D (insert B F)) X.V x ρ d)
    (inv : CommonInverse (realMatrix q (graph X.D (insert B F)) X.V) H)
    (u v : X.V) (uv : X.D u v=true) (off : graph X.D (insert B F) u v=false)
    (fail : ¬Positions X u v (added X.D F B)) :
    ∃ w π c, OmittedCycleProgress.Flat q (insertArc (graph X.D (insert B F)) u v) X.V w π c ∧
      (q:ℚ)*ρ u*w v=c-d ∧ (q:ℚ)*π u*x v=c-d ∧
      ∃ a b : X.V, (a.val,b.val) ∈ added X.D F B ∧
        Positions X u v ((added X.D F B).erase (a.val,b.val)) ∧
        ∃ M, Boundary X F M ∧ added X.D F M = insert (u.val,v.val) ((added X.D F B).erase (a.val,b.val)) ∧
        ((q:ℝ)*H b a-1)*(((d:ℝ)-1)*((c:ℝ)-1)*(∑i,H i u)*(∑j,H v j)) <
          (q:ℝ)*((c:ℝ)-d)*H b u*H v a := by
  classical
  have absent : (u.val,v.val) ∉ added X.D F B := fun hit => Bool.noConfusion (off.symm.trans (union_arc.mpr (Or.inr hit)))
  obtain ⟨w,π,c,flat,p₁,p₂,_,M,bm,em,full | ⟨a,b,mark,swap,price,_,_⟩⟩ :=
    LastArcCompetitor.fork X hq small step least stop old inv u v uv off
  · exact (fail (positions_of_carried X hq (mem_filter.mp bm.1).2 em absent
      (full.1 ▸ subset_insert _ _))).elim
  · have layout := positions_of_carried X hq (mem_filter.mp bm.1).2 em
        (fun hit => absent (mem_of_mem_erase hit)) (swap ▸ subset_insert _ _)
    exact ⟨w,π,c,flat,p₁,p₂,a,b,mark,layout,M,bm,swap,price⟩

/-- Once two original marks collide at a head v, they exhaust the deletion
budget at every missing parent u of v. Every other mark has one prescribed
backward distance to ALL those parents, even across different repairs. -/
theorem common_head_distances {q n F B} (X : Model q n) (hq : 2 ≤ q)
    (small : SmallerSmallRow q X.V.card) (step : Boundary X F B) (least : Minimum X F B)
    (bad : ¬SmallRow q (graph X.D (insert B F)) X.V)
    (v : X.V) {f g h : Arc} (fm : f ∈ added X.D F B) (gm : g ∈ added X.D F B)
    (hm : h ∈ added X.D F B) (distinct : f ≠ g) (hf : h ≠ f) (hg : h ≠ g)
    (collision : PuncturedDistance.depth X.D X.V v.val f.1 = PuncturedDistance.depth X.D X.V v.val g.1) :
    ∀ u : X.V, X.D u v=true → graph X.D (insert B F) u v=false →
      PuncturedDistance.depth X.D X.V h.2 u.val = q-1-PuncturedDistance.depth X.D X.V v.val h.1 := by
  classical
  intro u uv off
  obtain ⟨M,bm,em,alt⟩ := LastArcCompetitor.packet X hq small step least bad u v uv off
  have no : (u.val,v.val) ∉ added X.D F B := fun hit => Bool.noConfusion (off.symm.trans (union_arc.mpr (Or.inr hit)))
  have cm : Cycle X.D X.V q M := (mem_filter.mp bm.1).2
  rcases alt with ⟨full,_⟩ | ⟨z,_,swap⟩
  · have layout := positions_of_carried X hq cm em no (full ▸ subset_insert _ _)
    exact (distinct (layout.2.1 fm gm collision)).elim
  · have no' : (u.val,v.val) ∉ (added X.D F B).erase z := fun hit => no (mem_of_mem_erase hit)
    have layout := positions_of_carried X hq cm em no' (swap ▸ subset_insert _ _)
    have which : f=z ∨ g=z := by
      by_contra! neither
      exact distinct (layout.2.1 (mem_erase.mpr ⟨neither.1,fm⟩) (mem_erase.mpr ⟨neither.2,gm⟩) collision)
    have kept : h ∈ (added X.D F B).erase z := mem_erase.mpr ⟨which.elim (fun e => e ▸ hf) (fun e => e ▸ hg),hm⟩
    have eq := layout.1 h kept
    dsimp only at eq
    omega

private theorem depth_one_iff {q n} (X : Model q n) (hq : 2 ≤ q) {a b : ℕ}
    (bv : b∈X.V) : PuncturedDistance.depth X.D X.V a b = 1 ↔ X.D a b=true := by
  classical
  constructor
  · intro eq
    by_cases can : ∃ k, Walk X.D X.V a b k
    · rw [PuncturedDistance.depth,dite_eq_left can] at eq
      have path : Walk X.D X.V a b 1 := eq ▸ Nat.find_spec can
      cases path with
      | step _ arc rest => cases rest; exact arc
    · simp [PuncturedDistance.depth,can] at eq
  · intro ab
    have walk : Walk X.D X.V a b 1 := .step bv ab (.refl b)
    have can : ∃ k, Walk X.D X.V a b k := ⟨1,walk⟩
    have short := PuncturedDistance.depth_le_walk walk
    by_contra wrong
    have zero : PuncturedDistance.depth X.D X.V a b=0 := by omega
    rw [PuncturedDistance.depth,dite_eq_left can] at zero
    have empty : Walk X.D X.V a b 0 := zero ▸ Nat.find_spec can
    cases empty
    exact loopfree X.free (by omega) bv ab

/-- Native column separation supplies two distinct actual rows, one in
each direction. Neither can be the head of a third marked arc. -/
theorem separating_rows {q n F B} (X : Model q n) (hq : 2 ≤ q)
    (small : SmallerSmallRow q X.V.card) (step : Boundary X F B) (least : Minimum X F B)
    (bad : ¬SmallRow q (graph X.D (insert B F)) X.V)
    (v u₁ u₂ : X.V) (ne : u₁ ≠ u₂)
    (uv₁ : X.D u₁ v=true) (off₁ : graph X.D (insert B F) u₁ v=false)
    (uv₂ : X.D u₂ v=true) (off₂ : graph X.D (insert B F) u₂ v=false)
    {f g : Arc} (fm : f ∈ added X.D F B) (gm : g ∈ added X.D F B) (distinct : f ≠ g)
    (collision : PuncturedDistance.depth X.D X.V v.val f.1 = PuncturedDistance.depth X.D X.V v.val g.1) :
    ∃ y∈X.V, ∃ z∈X.V, y≠z ∧ X.D y u₁=true ∧ X.D y u₂=false ∧
      X.D z u₂=true ∧ X.D z u₁=false ∧
      ∀ h∈added X.D F B, h≠f → h≠g → y≠h.2 ∧ z≠h.2 := by
  classical
  have diff : u₁.val≠u₂.val := fun eq => ne (Subtype.ext eq)
  obtain ⟨y,yv,y1,y2⟩ := X.separated u₁ u₁.property u₂ u₂.property (Ne.symm diff)
  obtain ⟨z,zv,z2,z1⟩ := X.separated u₂ u₂.property u₁ u₁.property diff
  refine ⟨y,yv,z,zv,(fun eq => Bool.noConfusion (y1.symm.trans (eq ▸ z1))),y1,y2,z2,z1,?_⟩
  intro h hm hf hg
  have both := common_head_distances X hq small step least bad v fm gm hm distinct hf hg collision
  have equal := (both u₁ uv₁ off₁).trans (both u₂ uv₂ off₂).symm
  have adjacent : X.D h.2 u₁=true ↔ X.D h.2 u₂=true :=
    (depth_one_iff X hq u₁.property).symm.trans
      ((show PuncturedDistance.depth X.D X.V h.2 u₁.val=1 ↔ PuncturedDistance.depth X.D X.V h.2 u₂.val=1 by rw [equal]).trans
        (depth_one_iff X hq u₂.property))
  constructor
  · rintro rfl
    exact Bool.noConfusion ((adjacent.mp y1).symm.trans y2)
  · rintro rfl
    exact Bool.noConfusion ((adjacent.mpr z2).symm.trans z1)

#print axioms separating_rows
#print axioms common_head_distances
#print axioms price_on_position_failure
#print axioms position_count
#print axioms return_positions
#print axioms saturate
#print axioms fits_on_cycle
#print axioms at_most_one
#print axioms one_exceptional_component
#print axioms named_price
end LeanCH.BR.Closure.LastArcDistanceConflict

