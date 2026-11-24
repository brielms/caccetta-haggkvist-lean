import checkpoints.shen_extension.SharedArcTailExchange

namespace LeanCH.BR.Closure.SharedArcComponentExchange
open Finset BRq2 BRq3 BR45 WeightedSD ShenCycleSuccessor ShortestCycleWeights FirstPacketBarrier
open MarkedCyclePeeling SharedArcExpansion SharedArcBarrier SharedArcPacketDescent

abbrev Arc := ℕ × ℕ

noncomputable def added (D : CH.Digraph) (F : Family) (B : Finset ℕ) : Finset Arc :=
  (B ×ˢ B).filter (fun e => D e.1 e.2=true ∧ graph D F e.1 e.2=false)

theorem mem_added {D F B} {e : Arc} : e∈added D F B ↔
    e.1∈B ∧ e.2∈B ∧ D e.1 e.2=true ∧ graph D F e.1 e.2=false := by
  simp only [added,mem_filter,mem_product]; tauto

theorem union_arc {D F B i j} : graph D (insert B F) i j=true ↔
    graph D F i j=true ∨ (i,j)∈added D F B := by
  classical
  constructor
  · intro ed
    by_cases old : graph D F i j=true
    · exact Or.inl old
    obtain ⟨A,hit⟩ := active.mp ed
    obtain ⟨mem,ia,ja,ij⟩ := mem_col.mp hit
    rcases mem_insert.mp mem with rfl|af
    · exact Or.inr (mem_added.mpr ⟨ia,ja,ij,Bool.eq_false_iff.mpr old⟩)
    · exact (old (active.mpr ⟨A,mem_col.mpr ⟨af,ia,ja,ij⟩⟩)).elim
  · rintro (ed|mark)
    · obtain ⟨A,m⟩ := active.mp ed
      obtain ⟨af,ia,ja,ij⟩ := mem_col.mp m
      exact active.mpr ⟨A,mem_col.mpr ⟨mem_insert_of_mem af,ia,ja,ij⟩⟩
    · obtain ⟨ib,jb,ij,_⟩ := mem_added.mp mark
      exact active.mpr ⟨B,mem_col.mpr ⟨mem_insert_self B F,ib,jb,ij⟩⟩

/-- The added arcs are a matching between the tail copy and the head copy. -/
theorem matching {D F B V q} (cb : Cycle D V q B) {e f : Arc}
    (em : e∈added D F B) (fm : f∈added D F B) (share : e.1=f.1 ∨ e.2=f.2) : e=f := by
  obtain ⟨ea,eb,ed,_⟩ := mem_added.mp em
  obtain ⟨fa,fb,fd,_⟩ := mem_added.mp fm
  rcases share with head|tail
  · exact Prod.ext head (card_le_one.mp (cb.heads f.1 fa).le _ (mem_outN.mpr ⟨eb,head ▸ ed⟩) _ (mem_outN.mpr ⟨fb,fd⟩))
  · exact Prod.ext (card_le_one.mp (cb.incoming f.2 fb).le _ (mem_inN.mpr ⟨ea,tail ▸ ed⟩) _ (mem_inN.mpr ⟨fa,fd⟩)) tail

theorem count {D F B V q} (cb : Cycle D V q B) : (added D F B).card=(targets D V F B).card := by
  classical
  have image : (added D F B).image Prod.snd=targets D V F B := by
    ext j
    constructor
    · intro h
      obtain ⟨⟨i,v⟩,pair,rfl⟩ := mem_image.mp h
      obtain ⟨ib,vb,iv,miss⟩ := mem_added.mp pair
      exact mem_filter.mpr ⟨cb.sub vb,vb,i,ib,iv,miss⟩
    · intro h
      obtain ⟨_,jb,i,ib,ij,no⟩ := mem_filter.mp h
      exact mem_image.mpr ⟨(i,j),mem_added.mpr ⟨ib,jb,ij,no⟩,rfl⟩
  rw [←image,card_image_of_injOn]
  intro e em f fm eq
  exact matching cb em fm (Or.inr eq)

def Fresh {q n} (X : Model q n) (F : Family) (f : Arc) : Prop :=
  f.1∈X.V ∧ f.2∈X.V ∧ X.D f.1 f.2=true ∧ graph X.D F f.1 f.2=false

/-- Either endpoint may be held fixed. All actual fresh native alternatives
are realized while all the other selected arcs remain exactly the same. -/
theorem exchange {q n} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    {F B} (step : Boundary X F B)
    (least : ∀M,Boundary X F M → (targets X.D X.V F B).card≤(targets X.D X.V F M).card)
    (bad : ¬SmallRow q (graph X.D (insert B F)) X.V) {e f : Arc}
    (en : e∈added X.D F B) (fresh : Fresh X F f) (share : e.1=f.1 ∨ e.2=f.2) :
    ∃M,Boundary X F M ∧ added X.D F M=insert f ((added X.D F B).erase e) := by
  classical
  by_cases same : e=f
  · exact ⟨B,step,same ▸ (insert_erase en).symm⟩
  let G := graph X.D (insert B F)
  let J := insertArc G f.1 f.2
  let P := added X.D F B
  let Q := insert f (P.erase e)
  obtain ⟨fv,fw,fd,off⟩ := fresh
  have cb : Cycle X.D X.V q B := (mem_filter.mp step.1).2
  have fn : f∉P := fun h => same (matching cb en h share)
  have sz : Q.card=P.card := by
    change (insert f (P.erase e)).card=_
    rw [card_insert_of_notMem (fun h => fn (mem_of_mem_erase h)),card_erase_add_one en]
  have short : P.card<q+1 := by
    obtain ⟨A,af,i,im,j,jm,ij⟩ := step.2.2
    have jb := (mem_inter.mp jm).2
    have keep : graph X.D F i j=true := active.mpr ⟨A,mem_col.mpr ⟨af,(mem_inter.mp im).1,(mem_inter.mp jm).1,ij⟩⟩
    have jt : j∉targets X.D X.V F B := by
      intro hit
      obtain ⟨_,_,v,vb,vj,miss⟩ := mem_filter.mp hit
      have eq : v=i := card_le_one.mp (cb.incoming j jb).le _ (mem_inN.mpr ⟨vb,vj⟩) _ (mem_inN.mpr ⟨(mem_inter.mp im).2,ij⟩)
      exact Bool.noConfusion (miss.symm.trans (eq ▸ keep))
    have sub : targets X.D X.V F B⊂B := Finset.ssubset_iff_subset_ne.mpr ⟨fun _ h => (mem_filter.mp h).2.1,
      fun eq => jt (by rw [eq]; exact jb)⟩
    exact (count (F:=F) cb).trans_lt ((card_lt_card sub).trans_eq cb.size)
  have raw {u v} (ed : J u v=true) : X.D u v=true := by
    by_cases eq : u=f.1 ∧ v=f.2
    · exact eq.1 ▸ eq.2 ▸ fd
    have old : G u v=true := by simpa [J,insertArc,eq] using ed
    obtain ⟨A,hit⟩ := active.mp old
    exact (mem_col.mp hit).2.2.2
  have safe := qfree_sub (fun _ _ h => raw h) X.free
  have strong : ¬SmallRow q J X.V := by
    obtain ⟨w,wn,_,hi⟩ := strict_witness_of_not_smallRow bad
    intro weak
    apply weak.no_strict X.live w wn
    intro v vv
    apply (hi v vv).trans_le
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
      (outW_mono_graph (fun i _ j _ h => insertArc_mono G f.1 f.2 i j h) wn vv) (Nat.cast_nonneg q))
  obtain ⟨M,cm,im,jm⟩ := SharedArcMinimalPacket.cycle_at_arc hq small safe strong fv fw
    (show J f.1 f.2=true by simp [J,insertArc])
  obtain ⟨cd,kept⟩ := SharedArcMinimalPacket.lift_cycle (by omega : 1≤q) X.free (fun ed => raw ed) cm
  have fm : f∈added X.D F M := mem_added.mpr ⟨im,jm,fd,off⟩
  have subset : added X.D F M⊆Q := by
    intro g gm
    by_cases eq : g=f
    · exact eq ▸ mem_insert_self _ _
    have diff : ¬(g.1=f.1 ∧ g.2=f.2) := fun h => eq (Prod.ext h.1 h.2)
    obtain ⟨gu,gv,gd,miss⟩ := mem_added.mp gm
    have orig : G g.1 g.2=true := by simpa [J,insertArc,diff] using kept g.1 gu g.2 gv gd
    have marked : g∈P := (union_arc.mp orig).resolve_left (fun h => Bool.noConfusion (miss.symm.trans h))
    have other : g≠e := fun eqe => same (matching cd (eqe ▸ gm) fm share)
    exact mem_insert_of_mem (mem_erase.mpr ⟨other,marked⟩)
  have has : ∃v∈M,v∉targets X.D X.V F M := by
    by_contra! incl
    have m := card_le_card incl
    rw [←count cd,cd.size] at m
    have k := card_le_card subset
    rw [sz] at k
    omega
  obtain ⟨v,vm,no⟩ := has
  obtain ⟨u,uh⟩ := card_pos.mp (show 0<(inN X.D M v).card by have := cd.incoming v vm; change (inN X.D M v).card=1 at this; omega)
  obtain ⟨um,uv⟩ := mem_inN.mp uh
  have old : graph X.D F u v=true := by
    by_contra miss
    exact no (mem_filter.mpr ⟨cd.sub vm,vm,u,um,uv,Bool.eq_false_iff.mpr miss⟩)
  obtain ⟨A,hit⟩ := active.mp old
  obtain ⟨af,ua,va,arc⟩ := mem_col.mp hit
  have outside : M∉F := fun h => Bool.noConfusion (off.symm.trans (active.mpr ⟨M,mem_col.mpr ⟨h,im,jm,fd⟩⟩))
  have bm : Boundary X F M := ⟨mem_filter.mpr ⟨mem_powerset.mpr cd.sub,cd⟩,outside,A,af,
    u,mem_inter.mpr ⟨ua,um⟩,v,mem_inter.mpr ⟨va,vm⟩,arc⟩
  refine ⟨M,bm,eq_of_subset_of_card_le subset ?_⟩
  rw [sz,count cb,count cd]
  exact least M bm

/-- A step in the bipartite incidence graph of fresh native arcs. -/
def neighbor {q n} (X : Model q n) (F : Family) (e f : Arc) : Prop :=
  Fresh X F f ∧ (e.1=f.1 ∨ e.2=f.2)

/-- An entire sequence of endpoint changes carries just the marked arc.
Every other original new arc is retained. No other original marked arc
lies in this fresh incidence component. -/
theorem transport {q n} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    {F B} (step : Boundary X F B)
    (least : ∀M,Boundary X F M → (targets X.D X.V F B).card≤(targets X.D X.V F M).card)
    (stop : ∀M,Boundary X F M → ¬SmallRow q (graph X.D (insert M F)) X.V) {e f : Arc}
    (en : e∈added X.D F B) (way : Relation.ReflTransGen (neighbor X F) e f) :
    f∉(added X.D F B).erase e ∧
      ∃M,Boundary X F M ∧ added X.D F M=insert f ((added X.D F B).erase e) := by
  classical
  let P := added X.D F B
  let R := P.erase e
  have cb : Cycle X.D X.V q B := (mem_filter.mp step.1).2
  induction way with
  | refl => exact ⟨notMem_erase _ _,B,step,(insert_erase en).symm⟩
  | @tail g f _ move ih =>
    obtain ⟨gn,M,bm,old⟩ := ih
    change added X.D F M=insert g R at old
    have cm : Cycle X.D X.V q M := (mem_filter.mp bm.1).2
    have gm : g∈added X.D F M := old ▸ mem_insert_self _ _
    have out : f∉R := by
      intro fr
      have fm : f∈added X.D F M := old ▸ mem_insert_of_mem fr
      exact gn (matching cm gm fm move.2 ▸ fr)
    have eq : (targets X.D X.V F M).card=(targets X.D X.V F B).card := by
      rw [←count cm,←count cb,old,card_insert_of_notMem gn]
      exact card_erase_add_one en
    obtain ⟨L,bl,replace⟩ := exchange X hq small bm (fun K bk => eq.trans_le (least K bk)) (stop M bm) gm move.1 move.2
    refine ⟨out,L,bl,?_⟩
    rw [replace,old,erase_insert gn]

theorem separate {q n} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    {F B} (step : Boundary X F B)
    (least : ∀M,Boundary X F M → (targets X.D X.V F B).card≤(targets X.D X.V F M).card)
    (stop : ∀M,Boundary X F M → ¬SmallRow q (graph X.D (insert M F)) X.V) {e f : Arc}
    (en : e∈added X.D F B) (fn : f∈added X.D F B) (way : Relation.ReflTransGen (neighbor X F) e f) : e=f := by
  by_contra ne
  exact (transport X hq small step least stop en way).1 (mem_erase.mpr ⟨Ne.symm ne,fn⟩)

/-- On a connected fresh incidence graph, at most one new arc is needed. -/
theorem one_of_connected {q n} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    {F B} (step : Boundary X F B)
    (least : ∀M,Boundary X F M → (targets X.D X.V F B).card≤(targets X.D X.V F M).card)
    (stop : ∀M,Boundary X F M → ¬SmallRow q (graph X.D (insert M F)) X.V)
    (connected : ∀e,Fresh X F e → ∀f,Fresh X F f → Relation.ReflTransGen (neighbor X F) e f) :
    (targets X.D X.V F B).card≤1 := by
  classical
  have cb : Cycle X.D X.V q B := (mem_filter.mp step.1).2
  have fresh {g} (mem : g∈added X.D F B) : Fresh X F g := by
    obtain ⟨gu,gv,gd,no⟩ := mem_added.mp mem
    exact ⟨cb.sub gu,cb.sub gv,gd,no⟩
  rw [←count cb]
  exact card_le_one.mpr (fun e he f hf => separate X hq small step least stop he hf (connected e (fresh he) f (fresh hf)))

theorem graph_swap {D F B M} {e f : Arc} (en : e∈added D F B) (_diff : e≠f)
    (swap : added D F M=insert f ((added D F B).erase e)) :
    graph D (insert M F)=insertArc (eraseArc (graph D (insert B F)) e.1 e.2) f.1 f.2 := by
  classical
  funext i j
  by_cases atF : i=f.1 ∧ j=f.2
  · have eq : (i,j)=f := Prod.ext atF.1 atF.2
    rw [insertArc,ite_eq_left atF]
    exact union_arc.mpr (Or.inr (swap ▸ mem_insert.mpr (Or.inl eq)))
  have nf : (i,j)≠f := fun eq => atF ⟨congrArg Prod.fst eq,congrArg Prod.snd eq⟩
  by_cases atE : i=e.1 ∧ j=e.2
  · have eq : (i,j)=e := Prod.ext atE.1 atE.2
    rw [insertArc,ite_eq_right atF,eraseArc,ite_eq_left atE]
    apply Bool.eq_false_iff.mpr
    intro h
    rcases union_arc.mp h with old|mark
    · have no := (mem_added.mp en).2.2.2
      rw [atE.1,atE.2] at old
      exact Bool.noConfusion (no.symm.trans old)
    · rw [swap] at mark
      exact (mem_erase.mp ((mem_insert.mp mark).resolve_left nf)).1 eq
  have ne : (i,j)≠e := fun eq => atE ⟨congrArg Prod.fst eq,congrArg Prod.snd eq⟩
  rw [insertArc,ite_eq_right atF,eraseArc,ite_eq_right atE]
  apply Bool.eq_iff_iff.mpr
  rw [union_arc,union_arc,swap]
  simp [nf,ne]

/-- No missing native parent of a changed head is cheaper at the terminal
prices. No common parent, square, or assumed return path is required. -/
theorem all_parents {q n} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    {F B} (step : Boundary X F B)
    (least : ∀M,Boundary X F M → (targets X.D X.V F B).card≤(targets X.D X.V F M).card)
    (stop : ∀M,Boundary X F M → ¬SmallRow q (graph X.D (insert M F)) X.V)
    {p : ℕ→ℚ} {c : ℚ} (cols : ∀v∈X.V,WeightedSD.col q (graph X.D (insert B F)) X.V p v=c)
    (stuck : ¬Cheaper X F B p c) {a b z} (en : (a,b)∈added X.D F B) (fresh : Fresh X F (z,b)) :
    p a≤p z := by
  classical
  by_contra! disc
  have diff : (a,b)≠(z,b) := fun eq => disc.ne (congrArg p (congrArg Prod.fst eq)).symm
  have cb : Cycle X.D X.V q B := (mem_filter.mp step.1).2
  have fn : (z,b)∉added X.D F B := fun hit => diff (matching cb en hit (Or.inr rfl))
  obtain ⟨M,bm,swap⟩ := exchange X hq small step least (stop B step) en fresh (Or.inr rfl)
  have cm : Cycle X.D X.V q M := (mem_filter.mp bm.1).2
  have countEq : (targets X.D X.V F M).card=(targets X.D X.V F B).card := by
    rw [←count cm,←count cb,swap,card_insert_of_notMem (fun h => fn (mem_of_mem_erase h)),card_erase_add_one en]
  exact stuck (cheaper_of_swap X (by omega) bm countEq cols (cb.sub (mem_added.mp en).1) fresh.2.1 fresh.1
    (union_arc.mpr (Or.inr en)) (fun h => by
      rcases union_arc.mp h with old|marked
      · exact Bool.noConfusion (fresh.2.2.2.symm.trans old)
      · exact fn marked) (graph_swap en diff swap) disc)

/-- Representatives of two different marked components may be chosen
independently and occur on one and the same shortest cycle. -/
theorem pair {q n} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    {F B} (step : Boundary X F B)
    (least : ∀M,Boundary X F M → (targets X.D X.V F B).card≤(targets X.D X.V F M).card)
    (stop : ∀M,Boundary X F M → ¬SmallRow q (graph X.D (insert M F)) X.V) {e g f h : Arc}
    (en : e∈added X.D F B) (gn : g∈added X.D F B) (ne : e≠g)
    (ef : Relation.ReflTransGen (neighbor X F) e f) (gh : Relation.ReflTransGen (neighbor X F) g h) :
    f≠h ∧ ∃N,Boundary X F N ∧ f∈added X.D F N ∧ h∈added X.D F N := by
  classical
  obtain ⟨out,M,bm,moved⟩ := transport X hq small step least stop en ef
  have cm : Cycle X.D X.V q M := (mem_filter.mp bm.1).2
  have cb : Cycle X.D X.V q B := (mem_filter.mp step.1).2
  have eq : (targets X.D X.V F M).card=(targets X.D X.V F B).card := by
    rw [←count cm,←count cb,moved,card_insert_of_notMem out,card_erase_add_one en]
  have frozen : g∈(added X.D F B).erase e := mem_erase.mpr ⟨Ne.symm ne,gn⟩
  have fm : f∈added X.D F M := moved ▸ mem_insert_self _ _
  have gm : g∈added X.D F M := moved ▸ mem_insert_of_mem frozen
  have keep : f∈(added X.D F M).erase g := mem_erase.mpr ⟨fun same => out (same ▸ frozen),fm⟩
  obtain ⟨off,N,bn,final⟩ := transport X hq small bm (fun K bk => eq.trans_le (least K bk)) stop gm gh
  exact ⟨fun same => off (same ▸ keep),N,bn,final ▸ mem_insert_of_mem keep,final ▸ mem_insert_self _ _⟩

private theorem distance_sum {q D V F B} (hq : 2≤q) (free : QFree D V q) (cb : Cycle D V q B)
    {e f : Arc} (en : e∈added D F B) (fn : f∈added D F B) (ne : e≠f) :
    PuncturedDistance.depth D V e.2 f.1+PuncturedDistance.depth D V f.2 e.1=q-1 := by
  obtain ⟨ea,eb,arc,_⟩ := mem_added.mp en
  obtain ⟨fa,fb,far,_⟩ := mem_added.mp fn
  have diff : e.1≠f.1 := fun same => ne (matching cb en fn (Or.inl same))
  obtain ⟨lo,hi,go,back⟩ := MandatoryExcursion.segments (by omega : 1≤q) free cb ea fa
  let k := MandatoryExcursion.span D V q e.1 f.1
  change Walk D B e.1 f.1 k at go
  change Walk D B f.1 e.1 (q+1-k) at back
  change 1≤k at lo
  change k≤q+1 at hi
  have pos : 0<q+1-k := by
    by_contra! zero
    rw [show q+1-k=0 by omega] at back
    have equal {u v} (path : Walk D B u v 0) : u=v := by cases path; rfl
    exact diff (equal back).symm
  obtain ⟨r,rr⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k≠0)
  obtain ⟨s,ss⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q+1-k≠0)
  rw [rr] at go
  rw [ss] at back
  have split {i j l} (path : Walk D B i j (l+1)) : ∃v∈B,D i v=true ∧ Walk D B v j l := by
    cases path with
    | step hv ed tail => exact ⟨_,hv,ed,tail⟩
  obtain ⟨_,vv,ed,rest⟩ := split go
  obtain ⟨_,ww,fd,tail⟩ := split back
  have atDepth {i j} (reach : ∃k,Walk D V i j k) : Walk D V i j (PuncturedDistance.depth D V i j) := by
    classical
    rw [PuncturedDistance.depth,dite_eq_left reach]
    exact Nat.find_spec reach
  have v := card_le_one.mp (cb.heads e.1 ea).le _ (mem_outN.mpr ⟨vv,ed⟩) _ (mem_outN.mpr ⟨eb,arc⟩)
  have w := card_le_one.mp (cb.heads f.1 fa).le _ (mem_outN.mpr ⟨ww,fd⟩) _ (mem_outN.mpr ⟨fb,far⟩)
  have forward : Walk D V e.2 f.1 r := v ▸ rest.mono cb.sub
  have reverse : Walk D V f.2 e.1 s := w ▸ tail.mono cb.sub
  have l := PuncturedDistance.depth_le_walk forward
  have h := PuncturedDistance.depth_le_walk reverse
  have a := atDepth ⟨r,forward⟩
  have b := atDepth ⟨s,reverse⟩
  apply le_antisymm (by omega)
  by_contra! tooShort
  exact free e.1 _ (by omega) (by omega) ((Walk.step (cb.sub eb) arc a).append (Walk.step (cb.sub fb) far b))

/-- The native distance tensor is constant on each ordered pair of
distinct selected incidence components. Opposite distances add to q-1. -/
theorem distance_rectangle {q n} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    {F B} (step : Boundary X F B)
    (least : ∀M,Boundary X F M → (targets X.D X.V F B).card≤(targets X.D X.V F M).card)
    (stop : ∀M,Boundary X F M → ¬SmallRow q (graph X.D (insert M F)) X.V) {e g f h : Arc}
    (en : e∈added X.D F B) (gn : g∈added X.D F B) (ne : e≠g)
    (ef : Relation.ReflTransGen (neighbor X F) e f) (gh : Relation.ReflTransGen (neighbor X F) g h) :
    let d := PuncturedDistance.depth X.D X.V
    d f.2 h.1=d e.2 g.1 ∧ d h.2 f.1=d g.2 e.1 ∧ d f.2 h.1+d h.2 f.1=q-1 := by
  classical
  intro d
  have total {a b : Arc} (wa : Relation.ReflTransGen (neighbor X F) e a) (wb : Relation.ReflTransGen (neighbor X F) g b) :
      d a.2 b.1+d b.2 a.1=q-1 := by
    obtain ⟨diff,M,bm,am,bm'⟩ := pair X hq small step least stop en gn ne wa wb
    exact distance_sum hq X.free (show Cycle X.D X.V q M from (mem_filter.mp bm.1).2) am bm' diff
  have r0 : Relation.ReflTransGen (neighbor X F) e e := .refl
  have s0 : Relation.ReflTransGen (neighbor X F) g g := .refl
  have right {b} (path : Relation.ReflTransGen (neighbor X F) g b) : d e.2 b.1=d e.2 g.1 := by
    induction path with
    | refl => rfl
    | @tail i j wi edge prev =>
      rcases edge.2 with eq|eq
      · simpa only [←eq] using prev
      · have h1 := total r0 wi
        have h2 := total r0 (wi.tail edge)
        rw [←eq] at h2
        omega
  have left {a} (path : Relation.ReflTransGen (neighbor X F) e a) : d a.2 h.1=d e.2 h.1 := by
    induction path with
    | refl => rfl
    | @tail i j wi edge prev =>
      rcases edge.2 with eq|eq
      · have h1 := total wi gh
        have h2 := total (wi.tail edge) gh
        rw [←eq] at h2
        omega
      · simpa only [←eq] using prev
  have first := (left ef).trans (right gh)
  have t0 := total r0 s0
  have t1 := total ef gh
  exact ⟨first,by omega,t1⟩

/-- Each distance entry is attained by a native walk on the full support.
In particular a zero entry is an actual equality of vertex labels. -/
theorem phase_walk {q n} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    {F B} (step : Boundary X F B)
    (least : ∀M,Boundary X F M → (targets X.D X.V F B).card≤(targets X.D X.V F M).card)
    (stop : ∀M,Boundary X F M → ¬SmallRow q (graph X.D (insert M F)) X.V) {e g f h : Arc}
    (en : e∈added X.D F B) (gn : g∈added X.D F B) (ne : e≠g)
    (ef : Relation.ReflTransGen (neighbor X F) e f) (gh : Relation.ReflTransGen (neighbor X F) g h) :
    Walk X.D X.V f.2 h.1 (PuncturedDistance.depth X.D X.V e.2 g.1) := by
  classical
  obtain ⟨_,M,bm,fm,hm⟩ := pair X hq small step least stop en gn ne ef gh
  have cm : Cycle X.D X.V q M := (mem_filter.mp bm.1).2
  obtain ⟨_,_,go,_⟩ := MandatoryExcursion.segments (by omega : 1≤q) X.free cm (mem_added.mp fm).2.1 (mem_added.mp hm).1
  have reach : ∃k,Walk X.D X.V f.2 h.1 k := ⟨_,go.mono cm.sub⟩
  rw [←(distance_rectangle X hq small step least stop en gn ne ef gh).1,PuncturedDistance.depth,dite_eq_left reach]
  exact Nat.find_spec reach

theorem contact {q n} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    {F B} (step : Boundary X F B)
    (least : ∀M,Boundary X F M → (targets X.D X.V F B).card≤(targets X.D X.V F M).card)
    (stop : ∀M,Boundary X F M → ¬SmallRow q (graph X.D (insert M F)) X.V) {e g f h : Arc}
    (en : e∈added X.D F B) (gn : g∈added X.D F B) (ne : e≠g)
    (ef : Relation.ReflTransGen (neighbor X F) e f) (gh : Relation.ReflTransGen (neighbor X F) g h)
    (meet : e.2=g.1) : f.2=e.2 ∧ h.1=g.1 := by
  have zero : PuncturedDistance.depth X.D X.V e.2 g.1=0 := by
    rw [meet]; exact Nat.eq_zero_of_le_zero (PuncturedDistance.depth_le_walk (.refl g.1))
  have eq0 {i j : ℕ} (w : Walk X.D X.V i j 0) : i=j := by cases w; rfl
  have first := phase_walk X hq small step least stop en gn ne ef Relation.ReflTransGen.refl
  have next := phase_walk X hq small step least stop en gn ne Relation.ReflTransGen.refl gh
  rw [zero] at first next
  exact ⟨(eq0 first).trans meet.symm,(eq0 next).symm.trans meet⟩

#print axioms phase_walk
#print axioms contact

#print axioms pair
#print axioms distance_rectangle

#print axioms all_parents

#print axioms transport
#print axioms separate
#print axioms one_of_connected

#print axioms exchange
end LeanCH.BR.Closure.SharedArcComponentExchange
