import checkpoints.shen_extension.ReservedReachDebt
import checkpoints.shen_extension.BoundaryReceiverWitness

namespace LeanCH.BR.OldCorridorCapacity

open Finset BRq2 BRq3 BR45 BRsub WeightedSD ShenCycleSuccessor
open Closure.ShortestCycleWeights Closure.FirstPacketBarrier Closure.MarkedCyclePeeling
open Closure.SharedArcComponentExchange Classical

private theorem path_labels {E V a b k} (path : Walk E V a b k) :
    ∃ W ⊆ V, W.card ≤ k ∧ Walk E W a b k := by
  induction path with
  | refl => exact ⟨∅, empty_subset _, by simp, .refl _⟩
  | @step a b c k bv ab _ ih =>
    obtain ⟨S, sv, size, segment⟩ := ih
    exact ⟨insert b S, insert_subset bv sv, (card_insert_le ..).trans (by omega),
      .step (mem_insert_self ..) ab (segment.mono (subset_insert ..))⟩

/-- Any old-to-new edit confined to L can be reversed along a common return.
The same physical corridor and support work for every middle in C. -/
theorem common_return {D E O : CH.Digraph} {V L C : Finset ℕ} {q h y : ℕ}
    (hq : 2 ≤ q) (free : QFree D V q) (cycle : Cycle D V q L)
    (inside : ∀i j, E i j=true → D i j=true)
    (unchanged : ∀i∉L, ∀j, E i j=true → O i j=true)
    (large : 2 ≤ C.card) (cl : C ⊆ L) (hv : h∈V)
    (feeder : ∀c∈C, D c h=true) (parent : ∀c∈C, E y c=true)
    (back : Walk E V h y (q-1)) :
    ∃W ⊆ V, W.card=q ∧ Disjoint W L ∧ h∈W ∧ y∈W ∧
      Walk O W h y (q-1) ∧ ∀c∈C, O y c=true ∧ Cycle D V q (insert c W) := by
  obtain ⟨T,tv,size,seg⟩ := path_labels back
  let W := insert h T
  have hw : h∈W := mem_insert_self ..
  have wv : W⊆V := insert_subset hv tv
  have ew : Walk E W h y (q-1) := seg.mono (subset_insert ..)
  have yw : y∈W := by
    rcases ew.end_mem_or with eq|hit
    · simpa only [eq] using hw
    · exact hit
  have small : W.card ≤ q := by
    have bound := card_insert_le h T
    dsimp [W]
    omega
  have make (c) (cm : c∈C) : Cycle D V q (insert c W) := by
    let M := insert c W
    have mv : M ⊆ V := insert_subset (cycle.sub (cl cm)) wv
    have cmem : c∈M := mem_insert_self ..
    have hm : h∈M := mem_insert_of_mem hw
    have path := (walk_back (fun i _ j _ ij => inside i j ij) hw ew).mono (subset_insert c W)
    have closed := Walk.step hm (feeder c cm) (path.snoc cmem (inside _ _ (parent c cm)))
    rw [show q-1+1+1=q+1 by omega] at closed
    obtain ⟨N,nm,count,degree⟩ := boundary_closed_walk_support (free.mono_set mv) closed
    have eq : N=M := eq_of_subset_of_card_le nm (by
      have bound := card_insert_le c W
      dsimp [M]; omega)
    subst N
    have reg := dt_reg (by omega : 1≤q) (ball_q_one q (by omega))
      (free.mono_set mv) degree (by simpa using count)
    exact ⟨mv,count,reg.1,reg.2⟩
  obtain ⟨p,pc,t,tc,diff⟩ := one_lt_card.mp large
  have sep := Closure.BoundaryReceiverWitness.separate hq free cycle (make p pc) (make t tc)
    (cl pc) (cl tc) diff (feeder p pc) (feeder t tc)
    (mem_insert_self ..) (mem_insert_of_mem hw) (mem_insert_self ..) (mem_insert_of_mem hw)
  have outside : Disjoint W L := by
    apply disjoint_left.mpr
    intro i iw il
    exact disjoint_left.mp sep (mem_inter.mpr ⟨il,mem_insert_of_mem iw⟩)
      (mem_inter.mpr ⟨il,mem_insert_of_mem iw⟩)
  have exactSize : W.card=q := by
    have bound := card_insert_le p W
    have eq := (make p pc).size
    omega
  exact ⟨W,wv,exactSize,outside,hw,yw,
    walk_back (fun i iw j _ ij=>unchanged i (disjoint_left.mp outside iw) j ij) hw ew,
    fun c cm=>⟨unchanged y (disjoint_left.mp outside yw) c (parent c cm),make c cm⟩⟩
/-- The same-count identity, before assuming a particular graph or distance. -/
theorem incidence (E : CH.Digraph) (V C B : Finset ℕ) (w : ℕ→ℚ) (bv : B⊆V) :
    ∑c∈C, mass (inN E V c ∩ B) w = ∑y∈B,w y * ((outN E C y).card:ℚ) := by
  classical
  have at_col (c) : inN E V c ∩ B = B.filter (fun y=>E y c=true) := by
    ext y
    simp only [mem_inter,mem_inN,mem_filter]
    exact ⟨fun ⟨⟨_,arc⟩,yb⟩=>⟨yb,arc⟩,fun ⟨yb,arc⟩=>⟨⟨bv yb,arc⟩,yb⟩⟩
  simp_rw [at_col,mass,sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro y _
  rw [←sum_filter]
  simp [outN,mul_comm]

/-- At the fixed prices of a stuck subgraph, reached parent mass is counted
with its actual number of incidences. Each measured bank can have any size. -/
theorem return_volume {q E V w C S}
    (law : ReverseReachPayment.Expansion q E V w) (positive : ∀i∈V,0<w i)
    (free : QFree E V q) (hq : 1≤q) (cv : C⊆V) (sv : S⊆V)
    (cn : C.Nonempty) (sn : S.Nonempty) (cs : Disjoint C S)
    (room : ∀c∈C,(V\insert c S).Nonempty) :
    ∑c∈C,(mass S w+(WeightedSD.col q E V w c-mass V w)) <
      (q:ℚ)*∑y∈ballSet E V S (q-1), w y * ((outN E C y).card:ℚ) := by
  have each (c) (cm : c∈C) := ParentReachCapacity.parent_mass law positive free hq
    (cv cm) sv sn (disjoint_left.mp cs cm) (room c cm)
  have strict := sum_lt_sum_of_nonempty cn each
  rw [←mul_sum,incidence] at strict
  · exact strict
  · intro y ym
    obtain ⟨_,_,hit⟩ := mem_ballSet.mp ym
    exact (mem_ball.mp hit).1

/-- A price bound can force an actual parent to serve more than its individual
allowance, for an arbitrary requested profile m on the reachable labels. -/
theorem exceeds_allowance {q E V w C S} (law : ReverseReachPayment.Expansion q E V w)
    (positive : ∀i∈V,0<w i) (free : QFree E V q) (hq : 1≤q)
    (cv : C⊆V) (sv : S⊆V) (cn : C.Nonempty) (sn : S.Nonempty) (cs : Disjoint C S)
    (room : ∀c∈C,(V\insert c S).Nonempty) (m : ℕ→ℕ)
    (budget : (q:ℚ)*(∑y∈ballSet E V S (q-1), w y*(m y:ℚ)) ≤
        ∑c∈C,(mass S w + (WeightedSD.col q E V w c - mass V w))) :
    ∃ y∈ballSet E V S (q-1), m y < (outN E C y).card := by
  by_contra! all_fit
  have ub := return_volume law positive free hq cv sv cn sn cs room
  refine (not_lt_of_ge budget) (ub.trans_le (mul_le_mul_of_nonneg_left ?_ (by positivity)))
  apply sum_le_sum
  intro y ym
  obtain ⟨_,_,hit⟩ := mem_ballSet.mp ym
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast all_fit y ym) (positive y (mem_ball.mp hit).1).le

/-- Old labels reached without touching the set of edited rows. -/
noncomputable def exteriorReach (O : CH.Digraph) (V L S : Finset ℕ) (k : ℕ) :=
  ballSet O (V \ L) (S \ L) k

/-- A label reached by the selected heads can feed more than one boundary
row only along an old exterior return. Every one of its arcs to C is then old. -/
theorem old_multiple {q D E O V L C S y}
    (hq : 2≤q) (free : QFree D V q) (cycle : Cycle D V q L)
    (inside : ∀i j,E i j=true → D i j=true)
    (old : ∀i∉L,∀j,E i j=true → O i j=true)
    (cl : C⊆L) (sv : S⊆V) (feeds : ∀c∈C,∀h∈S,D c h=true)
    (reached : y∈ballSet E V S (q-1)) (multiple : 2≤(outN E C y).card) :
    y∈exteriorReach O V L S (q-1) ∧ outN E C y ⊆ outN O C y := by
  obtain ⟨h,hs,hit⟩ := mem_ballSet.mp reached
  obtain ⟨_,k,time,path⟩ := mem_ball.mp hit
  let T := outN E C y
  have tc : T⊆C := outN_subset
  have all (c) (ct : c∈T) := feeds c (tc ct) h hs
  obtain ⟨c,ct⟩ := card_pos.mp (by change 0<(outN E C y).card; omega : 0<T.card)
  have reg : k=q-1 := by
    by_contra diff
    have closed := Walk.step (sv hs) (all c ct)
      ((walk_back (fun i _ j _ ij=>inside i j ij) (sv hs) path).snoc
        (cycle.sub (cl (tc ct))) (inside y c (mem_outN.mp ct).2))
    exact free c (k+2) (by omega) (by omega) closed
  obtain ⟨W,wv,_,apart,hw,yw,oldpath,turns⟩ := common_return hq free cycle inside old multiple
    (tc.trans cl) (sv hs) all (fun _ cm=>(mem_outN.mp cm).2) (reg ▸ path)
  have wout : W⊆V \ L := fun i im=>mem_sdiff.mpr ⟨wv im,disjoint_left.mp apart im⟩
  exact ⟨mem_ballSet.mpr ⟨h,mem_sdiff.mpr ⟨hs,disjoint_left.mp apart hw⟩,
    mem_ball.mpr ⟨wout yw,q-1,le_rfl,oldpath.mono wout⟩⟩,
    fun c cm=>mem_outN.mpr ⟨tc cm,(turns c cm).1⟩⟩

/-- At an actual old exterior label every retained head is old, even when the
multiplicity is zero. Elsewhere at most one incidence can be billed. -/
noncomputable def oldAllowance (O : CH.Digraph) (V L C S : Finset ℕ) (k y : ℕ) : ℕ :=
  if y∈exteriorReach O V L S k then (outN O C y).card else 1

theorem covered_allowance {q D E O V L C S y}
    (hq : 2≤q) (free : QFree D V q) (cycle : Cycle D V q L)
    (inside : ∀i j,E i j=true → D i j=true)
    (old : ∀i∉L,∀j,E i j=true → O i j=true)
    (cl : C⊆L) (sv : S⊆V) (feeds : ∀c∈C,∀h∈S,D c h=true)
    (hit : y∈ballSet E V S (q-1)) :
    (outN E C y).card≤oldAllowance O V L C S (q-1) y := by
  unfold oldAllowance
  split_ifs with holds
  · obtain ⟨_,_,reach⟩ := mem_ballSet.mp holds
    have off := (mem_sdiff.mp (mem_ball.mp reach).1).2
    exact card_le_card (fun c cm=>mem_outN.mpr ⟨(mem_outN.mp cm).1,old y off c (mem_outN.mp cm).2⟩)
  · by_contra! large
    exact holds (old_multiple hq free cycle inside old cl sv feeds hit large).1

/-- Literal original-carrier reverse merge. The right side can use a single
shared native head. The budget on the left reads old arcs at the terminal
prices and allows one incidence for every reached row outside old reach. -/
theorem old_capacity_pays {q D E O V L C S w}
    (hq : 2≤q) (free : QFree D V q) (cycle : Cycle D V q L)
    (inside : ∀i j,E i j=true → D i j=true)
    (old : ∀i∉L,∀j,E i j=true → O i j=true)
    (cl : C⊆L) (sv : S⊆V) (feeds : ∀c∈C,∀h∈S,D c h=true)
    (positive : ∀i∈V,0<w i) (strict : ∀i∈V,mass V w<WeightedSD.col q E V w i)
    (cn : C.Nonempty) (sn : S.Nonempty) (cs : Disjoint C S)
    (room : ∀c∈C,(V\insert c S).Nonempty)
    (budget : (q:ℚ)*(∑y∈ballSet E V S (q-1), w y*(oldAllowance O V L C S (q-1) y:ℚ)) ≤
        ∑c∈C,(mass S w + (WeightedSD.col q E V w c - mass V w))) :
    Closure.ForwardMerge.NativeMergePays q D V := by
  by_contra stuck
  have law := ReverseReachPayment.expansion inside positive strict stuck
  obtain ⟨y,hit,excess⟩ := exceeds_allowance law positive (qfree_sub inside free) (by omega)
    (cl.trans cycle.sub) sv cn sn cs room _ budget
  exact (not_lt_of_ge (covered_allowance hq free cycle inside old cl sv feeds hit)) excess
/-- Strict capacity law, with every native parent incidence replaced by its
old bound whenever several feeders use the same reached vertex. -/
def Inequality (q : ℕ) (E O : CH.Digraph) (V L C S : Finset ℕ) (w : ℕ→ℚ) : Prop :=
  ∑c∈C,(mass S w + (WeightedSD.col q E V w c - mass V w)) <
    (q:ℚ)*∑y∈ballSet E V S (q-1),w y*(oldAllowance O V L C S (q-1) y:ℚ)

theorem necessary {q D E O V L C S w}
    (hq : 2≤q) (free : QFree D V q) (cycle : Cycle D V q L)
    (inside : ∀i j,E i j=true → D i j=true)
    (old : ∀i∉L,∀j,E i j=true → O i j=true)
    (cl : C⊆L) (sv : S⊆V) (feeds : ∀c∈C,∀h∈S,D c h=true)
    (positive : ∀i∈V,0<w i) (law : ReverseReachPayment.Expansion q E V w)
    (cn : C.Nonempty) (sn : S.Nonempty) (cs : Disjoint C S)
    (room : ∀c∈C,(V\insert c S).Nonempty) : Inequality q E O V L C S w := by
  apply (return_volume law positive (qfree_sub inside free) (by omega)
    (cl.trans cycle.sub) sv cn sn cs room).trans_le
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply sum_le_sum
  intro y hit
  obtain ⟨_,_,reach⟩ := mem_ballSet.mp hit
  apply mul_le_mul_of_nonneg_left _ (positive y (mem_ball.mp reach).1).le
  exact_mod_cast covered_allowance hq free cycle inside old cl sv feeds hit

/-- The marked head can start alone. All labelled nonempty subsets of the
common-head pool are also allowed. The minimum two feeders supplies a
remaining physical label for each single-receiver calculation. -/
structure HeadCapacity (q : ℕ) (D E O : CH.Digraph) (V L C : Finset ℕ) (z : ℕ)
    (w : ℕ→ℚ) : Prop where
  single : Inequality q E O V L C {z} w
  pools : ∀S⊆ReachSlotMatching.commonHeads D V C,S.Nonempty → Inequality q E O V L C S w

theorem marked_capacity {q n} (X : Model q n) {F : Family} {L C : Finset ℕ} {z w}
    (hq : 2≤q) (boundary : Closure.SharedArcBarrier.Boundary X F L)
    (marked : ReachSlotMatching.Marked X C z) (cl : C⊆L) (many : 2≤C.card)
    (positive : ∀i∈X.V,0<w i) (law : ReverseReachPayment.Expansion q (graph X.D (insert L F)) X.V w) :
    HeadCapacity q X.D (graph X.D (insert L F)) (graph X.D F) X.V L C z w := by
  have cy := (mem_filter.mp boundary.1).2
  have cv := cl.trans cy.sub
  have cn := card_pos.mp (by omega : 0<C.card)
  have every (S : Finset ℕ) (sh : S⊆ReachSlotMatching.commonHeads X.D X.V C) (live : S.Nonempty) :
      Inequality q (graph X.D (insert L F)) (graph X.D F) X.V L C S w := by
    have sv : S⊆X.V := sh.trans (filter_subset ..)
    have joins (c) (cm : c∈C) (h) (hm : h∈S) := (mem_filter.mp (sh hm)).2 c cm
    have apart : Disjoint C S := by
      apply disjoint_left.mpr
      intro v cm sm
      exact loopfree X.free (by omega) (cv cm) (joins v cm v sm)
    have room (c) (cm : c∈C) : (X.V\insert c S).Nonempty := by
      obtain ⟨d,dc,diff⟩ := exists_mem_ne (by omega : 1<C.card) c
      exact ⟨d,mem_sdiff.mpr ⟨cv dc,fun dm=> (mem_insert.mp dm).elim diff (disjoint_left.mp apart dc)⟩⟩
    apply necessary hq X.free cy _ _ cl sv joins positive law cn live apart room
    · intro i j ij
      obtain ⟨A,al⟩ := active.mp ij
      exact (mem_col.mp al).2.2.2
    · intro i il j ij
      exact (union_arc.mp ij).elim id (fun added=>False.elim (il (mem_added.mp added).1))
  exact ⟨every {z} (singleton_subset_iff.mpr marked.receiver) (singleton_nonempty _),every⟩

theorem marked_pair {q n} (X : Model q n) {F : Family} {L : Finset ℕ} {p t z w}
    (hq : 2≤q) (boundary : Closure.SharedArcBarrier.Boundary X F L)
    (marked : ReachSlotMatching.Marked X {p,t} z) (pl : p∈L) (tl : t∈L) (diff : p≠t)
    (positive : ∀i∈X.V,0<w i) (law : ReverseReachPayment.Expansion q (graph X.D (insert L F)) X.V w) :
    HeadCapacity q X.D (graph X.D (insert L F)) (graph X.D F) X.V L {p,t} z w :=
  marked_capacity X hq boundary marked (insert_subset pl (singleton_subset_iff.mpr tl)) (by simp [diff]) positive law

attribute [aesop safe forward (immediate := [X,hq,boundary,marked,cl,many,positive,law]) (rule_sets := [CHGraphFamilies])] marked_capacity
attribute [aesop safe forward (immediate := [X,hq,boundary,marked,pl,tl,diff,positive,law]) (rule_sets := [CHGraphFamilies])] marked_pair
attribute [aesop safe forward (immediate := [hq,free,cycle,inside,old,cl,sv,feeds,positive,strict,cn,sn,cs,room,budget]) (rule_sets := [CHGraphFamilies])] old_capacity_pays
#print axioms necessary
#print axioms marked_capacity
#print axioms marked_pair

#print axioms old_multiple
#print axioms covered_allowance
#print axioms old_capacity_pays

#print axioms incidence
#print axioms return_volume
#print axioms exceeds_allowance

#print axioms common_return
end LeanCH.BR.OldCorridorCapacity

