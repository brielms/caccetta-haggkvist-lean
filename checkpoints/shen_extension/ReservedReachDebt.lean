import checkpoints.shen_extension.ParentReachCapacity

namespace LeanCH.BR.ReservedReachDebt
open Finset BRq2 BRq3 BR45 BRsub WeightedSD ReverseReachPayment ReachSlotMatching
open ParentReachCapacity PricedReachAssignments Closure.ShortestCycleWeights
open Closure.FirstPacketBarrier Closure.MarkedCyclePeeling Classical

/-- Demand is additive on disjoint labels. Supply can be shared. If every
set with at least k labels is funded, all remaining deficits meet one
physical set of fewer than k labels. The complement satisfies every cut. -/
theorem trim_deficit {α : Type*} [DecidableEq α] {T : Finset α}
    {demand : α→ℕ} {supply : Finset α→ℕ} {k : ℕ} (pos : 0<k)
    (subadd : ∀A⊆T,∀B⊆T,Disjoint A B → supply (A∪B)≤supply A+supply B)
    (large : ∀S⊆T,k≤S.card → (∑x∈S,demand x)≤supply S) :
    ∃B⊆T,B.card<k ∧ (B.Nonempty → supply B<(∑x∈B,demand x)) ∧
      ∀S⊆T\B,(∑x∈S,demand x)≤supply S := by
  classical
  let bad := T.powerset.filter (fun S=>supply S<∑x∈S,demand x)
  by_cases live : bad.Nonempty
  · obtain ⟨B,bm,best⟩ := bad.exists_max_image Finset.card live
    obtain ⟨bt,deficit⟩ := mem_filter.mp bm
    have sub := mem_powerset.mp bt
    refine ⟨B,sub,lt_of_not_ge (fun enough=>deficit.not_ge (large B sub enough)),fun _=>deficit,?_⟩
    intro S ss
    by_contra! short
    have st := ss.trans sdiff_subset
    have apart : Disjoint B S := disjoint_left.mpr (fun _ bm sm=>(mem_sdiff.mp (ss sm)).2 bm)
    have sum := sum_union (f:=demand) apart
    have size := card_union_of_disjoint apart
    have combined : B∪S∈bad := mem_filter.mpr ⟨mem_powerset.mpr (union_subset sub st),by
      have limit := subadd B sub S st apart
      omega⟩
    have bound := best _ combined
    have nonempty : S.Nonempty := by
      by_contra! empty
      simp [empty] at short
    have := card_pos.mpr nonempty
    omega
  · refine ⟨∅,empty_subset _,by simpa using pos,fun h=>h.elim (fun x m=>False.elim (notMem_empty x m)),?_⟩
    intro S ss
    by_contra! short
    exact live ⟨S,mem_filter.mpr ⟨mem_powerset.mpr (ss.trans sdiff_subset),short⟩⟩

/-- For multiple native heads the receiver can stay in the graph. No head
reaches the receiver before the last forbidden step; the receiver's full
price contributes to the available margin. -/
theorem retained_receiver {q D E V w z H} (law : Expansion q E V w)
    (positive : ∀i∈V,0<w i) (free : QFree D V q) (hq : 1≤q)
    (sub : ∀i j,E i j=true→D i j=true) (zv : z∈V)
    (heads : H⊆outN D V z) (wide : 2≤H.card) :
    mass H w+(WeightedSD.col q E V w z-mass V w)+((q:ℚ)-1)*w z <
      (q:ℚ)*mass (inN E V z∩ballSet E V H (q-1)) w := by
  let P := inN E V z
  have hv := heads.trans outN_subset
  have nz : z∉H := fun zm=>loopfree free hq zv (mem_outN.mp (heads zm)).2
  have zp : z∉P := fun zm=>loopfree free hq zv (sub _ _ (mem_inN.mp zm).2)
  have off : z∉ballSet E V H (q-1) := by
    intro hit
    obtain ⟨a,ah,az⟩ := mem_ballSet.mp hit
    obtain ⟨_,l,le,path⟩ := mem_ball.mp az
    exact free z (l+1) (by omega) (by omega) (.step (hv ah) (mem_outN.mp (heads ah)).2 (walk_sub sub path))
  have limit := card_sdiff_add_card_eq_card hv
  have bill := reached_mass law positive hv (insert_subset zv (filter_subset _ _) : insert z P ⊆ V)
    (by omega) ⟨z,mem_sdiff.mpr ⟨zv,nz⟩⟩
  have same : insert z P∩ballSet E V H (q-1)=P∩ballSet E V H (q-1) := by
    ext x
    simp only [mem_inter,mem_insert]
    constructor
    · rintro ⟨rfl|m,witness⟩
      · exact (off witness).elim
      · exact ⟨m,witness⟩
    · rintro ⟨m,witness⟩
      exact ⟨Or.inr m,witness⟩
  have plus : mass (insert z P) w=w z+mass P w := sum_insert zp
  rw [same,plus] at bill
  have split : mass (V\H) w+mass H w=mass V w := sum_sdiff hv
  change mass H w+(w z+q*inW E V w z-mass V w)+((q:ℚ)-1)*w z<q*mass _ w
  rw [in_mass]
  dsimp only [P] at bill
  linarith

/-- Every label in C is missed by every selected head. It can therefore
be credited once, as long as it is outside the parents already counted. -/
theorem missed_credit {q E V w z H C} (law : Expansion q E V w)
    (positive : ∀i∈V,0<w i) (hv : H⊆V) (cv : C⊆V) (wide : 2≤H.card)
    (live : (V\H).Nonempty) (apart : Disjoint C (inN E V z))
    (miss : Disjoint C (ballSet E V H (q-1))) :
    mass H w + (WeightedSD.col q E V w z-mass V w) - w z + q*mass C w <
      (q:ℚ)*mass (inN E V z∩ballSet E V H (q-1)) w := by
  let P := inN E V z
  have total := card_sdiff_add_card_eq_card hv
  have bill := reached_mass law positive hv (union_subset cv (filter_subset _ _) : C∪P⊆V) (by omega) live
  have same : (C∪P)∩ballSet E V H (q-1)=P∩ballSet E V H (q-1) := by
    rw [union_inter_distrib_right,Finset.disjoint_iff_inter_eq_empty.mp miss,empty_union]
  have parts : mass (C∪P) w=mass C w+mass P w := sum_union apart
  rw [same,parts] at bill
  have split : mass (V\H) w+mass H w=mass V w := sum_sdiff hv
  change mass H w+(w z+q*inW E V w z-mass V w)-w z+q*mass C w<q*mass _ w
  rw [in_mass]
  dsimp only [P] at bill
  linarith

theorem common_missed {q D E V H C} (free : QFree D V q) (hq : 1≤q)
    (sub : ∀i j,E i j=true→D i j=true) (hv : H⊆V) (feeds : ∀c∈C,∀a∈H,D c a=true) :
    Disjoint C (ballSet E V H (q-1)) := by
  apply disjoint_left.mpr
  intro c cm hit
  obtain ⟨a,ah,r⟩ := mem_ballSet.mp hit
  obtain ⟨_,l,le,path⟩ := mem_ball.mp r
  exact free c (l+1) (by omega) (by omega) (.step (hv ah) (feeds c cm a ah) (walk_sub sub path))

/-- Unavailable parents Y are charged in their entire original price.
Whenever C covers their bill, every subset of at least two heads retains
enough supply in its own reachable parent labels outside Y. -/
theorem funded_group {q E V w z H C Y} (law : Expansion q E V w)
    (positive : ∀i∈V,0<w i) (hv : H⊆V) (cv : C⊆V) (yv : Y⊆V)
    (wide : 2≤H.card) (live : (V\H).Nonempty) (apart : Disjoint C (inN E V z))
    (miss : Disjoint C (ballSet E V H (q-1)))
    (budget : (q:ℚ)*mass Y w ≤ WeightedSD.col q E V w z-mass V w-w z+q*mass C w) :
    mass H w < (q:ℚ)*mass ((inN E V z\Y)∩ballSet E V H (q-1)) w := by
  let A := inN E V z∩ballSet E V H (q-1)
  have paid := missed_credit law positive hv cv wide live apart miss
  have used : mass (A∩Y) w≤mass Y w := mass_mono inter_subset_right (fun i im=>(positive i (yv im)).le)
  have split := sum_inter_add_sum_sdiff A Y w
  have rest : A\Y=(inN E V z\Y)∩ballSet E V H (q-1) := by ext i; simp [A]; tauto
  rw [←rest]
  change mass H w+_ - w z+q*mass C w<(q:ℚ)*mass A w at paid
  change mass (A∩Y) w+mass (A\Y) w=mass A w at split
  have weight := congrArg (fun v:ℚ=>(q:ℚ)*v) split
  have bound := mul_le_mul_of_nonneg_left used (Nat.cast_nonneg q : (0:ℚ)≤q)
  nlinarith only [paid,weight,bound,budget]

private theorem scaled {V w} {d : ℕ} {cap : ℕ→ℕ} (scale : ∀v∈V,(cap v:ℚ)=d*w v)
    {S : Finset ℕ} (sv : S⊆V) : (↑(∑x∈S,cap x):ℚ)=d*mass S w := by
  rw [Nat.cast_sum,mass,mul_sum]
  exact sum_congr rfl (fun i im=>scale i (sv im))

private theorem count_supplies {q E V z Y} {cap : ℕ→ℕ} {S : Finset ℕ} (sv : S⊆V) :
    (slots (starts (fun i j=>E j i) V S (q-1))
      (fun u=>if u∈inN E V z\Y then q*cap u else 0)).card =
        q*(∑u∈(inN E V z\Y)∩ballSet E V S (q-1),cap u) := by
  rw [card_slots,reversed_starts sv,←sum_filter,Finset.mul_sum]
  apply sum_congr _ (fun _ _=>rfl)
  ext i
  simp [and_comm]

/-- After removing the whole priced parent set Y, all but at most one
physical starting label can still be routed simultaneously. The exceptional
set, when present, is itself deficient and is kept in the output. -/
theorem remaining_assignment {q D E V w z H C Y} (law : Expansion q E V w)
    (positive : ∀i∈V,0<w i) (free : QFree D V q) (hq : 1≤q)
    (sub : ∀i j,E i j=true→D i j=true) (hv : H⊆V) (cv : C⊆V) (yv : Y⊆V)
    (live : (V\H).Nonempty) (apart : Disjoint C (inN E V z)) (feeds : ∀c∈C,∀a∈H,D c a=true)
    (budget : (q:ℚ)*mass Y w≤WeightedSD.col q E V w z-mass V w-w z+q*mass C w)
    {d : ℕ} {cap : ℕ→ℕ} (scale : ∀i∈V,(cap i:ℚ)=d*w i) :
    let offer := fun u=>if u∈inN E V z\Y then q*cap u else 0
    ∃B⊆H,B.card<2 ∧ (B.Nonempty → (slots (ballSet E V B (q-1)) offer).card<∑u∈B,cap u) ∧
      Assignment (fun i j=>E j i) V (H\B) (q-1) cap offer ∅ := by
  classical
  intro offer
  let options (S : Finset ℕ) := slots (ballSet E V S (q-1)) offer
  have subadd (A : Finset ℕ) (_ : A⊆H) (B : Finset ℕ) (_ : B⊆H) (_ : Disjoint A B) :
      (options (A∪B)).card≤(options A).card+(options B).card := by
    apply (card_le_card (t:=options A∪options B) _).trans (card_union_le ..)
    intro v vm
    obtain ⟨vhit,ix⟩ := mem_slots.mp vm
    obtain ⟨a,am,path⟩ := mem_ballSet.mp vhit
    rcases mem_union.mp am with ma|mb
    · exact mem_union_left _ (mem_slots.mpr ⟨mem_ballSet.mpr ⟨a,ma,path⟩,ix⟩)
    · exact mem_union_right _ (mem_slots.mpr ⟨mem_ballSet.mpr ⟨a,mb,path⟩,ix⟩)
  have large (S : Finset ℕ) (sh : S⊆H) (wide : 2≤S.card) : (∑u∈S,cap u)≤(options S).card := by
    have sv := sh.trans hv
    have survives := live.mono (show V\H⊆V\S from fun _ m=>mem_sdiff.mpr
      ⟨(mem_sdiff.mp m).1,fun sm=>(mem_sdiff.mp m).2 (sh sm)⟩)
    have missed := common_missed free hq sub sv (fun c cm a am=>feeds c cm a (sh am))
    have bill := funded_group law positive sv cv yv wide survives apart missed budget
    have size := count_supplies (q:=q) (E:=E) (z:=z) (Y:=Y) (cap:=cap) sv
    rw [reversed_starts sv] at size
    change _≤(slots (ballSet E V S (q-1)) offer).card
    rw [size]
    have fit : (inN E V z\Y)∩ballSet E V S (q-1)⊆V :=
      inter_subset_left.trans (sdiff_subset.trans (filter_subset _ _))
    have scaledBill := mul_le_mul_of_nonneg_left bill.le (Nat.cast_nonneg d : (0:ℚ)≤d)
    have rat : (↑(∑u∈S,cap u):ℚ) ≤ (q:ℚ)*↑(∑u∈(inN E V z\Y)∩ballSet E V S (q-1),cap u) := by
      rw [scaled scale sv,scaled scale fit]
      nlinarith only [scaledBill]
    exact_mod_cast rat
  obtain ⟨B,bh,small,short,rest⟩ := trim_deficit (demand:=cap) (supply:=fun S=>(options S).card)
    (by decide : 0<2) subadd large
  refine ⟨B,bh,small,short,?_⟩
  apply assign
  intro S ss _
  rw [sdiff_empty,card_slots,reversed_starts (ss.trans (sdiff_subset.trans hv))]
  exact rest S ss

/-- Apply the smaller-host law to these same feeders at these same prices.
One physical feeder works for every subsequent choice of unavailable parents. -/
def ReceiverChoice (q : ℕ) (E : CH.Digraph) (V C H : Finset ℕ) (w : ℕ→ℚ) : Prop :=
  ∃z∈C,w z+q*mass (C∩inN E V z) w≤mass C w ∧
    ∃d : ℕ,0<d ∧ ∃cap : ℕ→ℕ,(∀i∈V,(cap i:ℚ)=d*w i) ∧
    ∀Y⊆V,(q:ℚ)*mass Y w≤WeightedSD.col q E V w z-mass V w+((q:ℚ)-1)*mass C w →
      let offer := fun u=>if u∈inN E V z\Y then q*cap u else 0
      ∃B⊆H,B.card<2 ∧ (B.Nonempty → (slots (ballSet E V B (q-1)) offer).card<∑u∈B,cap u) ∧
        Assignment (fun i j=>E j i) V (H\B) (q-1) cap offer ∅

theorem receiver_choice {q D E V C H w} (law : Expansion q E V w) (positive : ∀i∈V,0<w i)
    (free : QFree D V q) (hq : 1≤q) (sub : ∀i j,E i j=true→D i j=true)
    (light : SmallRow q (fun i j=>E j i) C) (cv : C⊆V) (hv : H⊆V)
    (live : C.Nonempty) (room : (V\H).Nonempty) (feeds : ∀c∈C,∀a∈H,D c a=true) :
    ReceiverChoice q E V C H w := by
  obtain ⟨z,zc,low⟩ := light w (fun u um=>(positive u (cv um)).le) live
  change w z+q*inW E C w z≤mass C w at low
  rw [in_mass] at low
  have same : inN E C z=C∩inN E V z := by
    ext u
    simp only [mem_inN,mem_inter]
    exact ⟨fun ⟨uc,e⟩=>⟨uc,cv uc,e⟩,fun ⟨uc,_,e⟩=>⟨uc,e⟩⟩
  rw [same] at low
  obtain ⟨d,dp,cap,scale⟩ := integer_units w V (fun i im=>(positive i im).le)
  refine ⟨z,zc,low,d,dp,cap,scale,?_⟩
  intro Y yv paid
  have split : mass (C∩inN E V z) w+mass (C\inN E V z) w=mass C w := sum_inter_add_sum_sdiff .. 
  have budget : (q:ℚ)*mass Y w≤WeightedSD.col q E V w z-mass V w-w z+q*mass (C\inN E V z) w := by
    nlinarith only [paid,low,congrArg (fun v:ℚ=>(q:ℚ)*v) split]
  exact remaining_assignment law positive free hq sub hv (sdiff_subset.trans cv) yv
    room sdiff_disjoint (fun c cm=>feeds c (mem_sdiff.mp cm).1) budget scale

theorem common_receivers {q D E V C w} (law : Expansion q E V w) (positive : ∀i∈V,0<w i)
    (free : QFree D V q) (hq : 1≤q) (sub : ∀i j,E i j=true→D i j=true)
    (small : SmallerSmallRow q V.card) (cv : C⊆V) (live : C.Nonempty)
    (off : (commonHeads D V C).Nonempty) :
    ReceiverChoice q E V C (commonHeads D V C) w := by
  let H := commonHeads D V C
  have emptyMeet : Disjoint C H := by
    apply disjoint_left.mpr
    intro x xc xh
    exact loopfree free hq (cv xc) ((mem_filter.mp xh).2 x xc)
  have proper : C≠V := by
    obtain ⟨a,ah⟩ := off
    intro eq
    exact disjoint_left.mp emptyMeet (eq ▸ (mem_filter.mp ah).1) ah
  have room : (V\H).Nonempty := by
    obtain ⟨x,xc⟩ := live
    exact ⟨x,mem_sdiff.mpr ⟨cv xc,fun xh=>disjoint_left.mp emptyMeet xc xh⟩⟩
  exact receiver_choice law positive free hq sub (small.reverse_induced (qfree_sub sub free) C cv proper)
    cv (filter_subset _ _) live room (fun c cm _ ah=>(mem_filter.mp ah).2 c cm)

theorem family_choice {q n} (X : Model q n) {G : Family} {w : ℕ→ℚ}
    (law : Expansion q (graph X.D G) X.V w) (positive : ∀i∈X.V,0<w i)
    (small : SmallerSmallRow q X.V.card) (hq : 2≤q) {C z}
    (marked : Marked X C z) (live : C.Nonempty) (cv : C⊆X.V) :
    ReceiverChoice q (graph X.D G) X.V C (commonHeads X.D X.V C) w := by
  apply common_receivers law positive X.free (by omega) _ small cv live ⟨z,marked.1⟩
  intro i j ed
  obtain ⟨A,am⟩ := active.mp ed
  exact (mem_col.mp am).2.2.2

/-- Two distinct native feeders are already labelled in the failed attachment.
The general common-feeder law chooses one of them and remembers every shared head. -/
theorem pair_choice {q n} (X : Model q n) {G : Family} {w : ℕ→ℚ}
    (law : Expansion q (graph X.D G) X.V w) (positive : ∀i∈X.V,0<w i)
    (small : SmallerSmallRow q X.V.card) (hq : 2≤q) {L F p t z}
    (boundary : Closure.SharedArcBarrier.Boundary X F L) (pl : p∈L) (tl : t∈L)
    (marked : Marked X {p,t} z) :
    ReceiverChoice q (graph X.D G) X.V {p,t} (commonHeads X.D X.V {p,t}) w := by
  have cy := (mem_filter.mp boundary.1).2
  exact family_choice X law positive small hq marked (insert_nonempty ..)
    (insert_subset (cy.sub pl) (singleton_subset_iff.mpr (cy.sub tl)))

attribute [aesop safe forward (immediate := [law,positive,free,hq,sub,small,cv,live,off]) (rule_sets := [CHGraphFamilies])] common_receivers
attribute [aesop safe forward (immediate := [X,law,positive,small,hq,marked,live,cv]) (rule_sets := [CHGraphFamilies])] family_choice
attribute [aesop safe forward (immediate := [X,law,positive,small,hq,boundary,pl,tl,marked]) (rule_sets := [CHGraphFamilies])] pair_choice
/-- If several actual heads together can reach only the affordable parents
Y, the reverse merge pays on this very carrier. The cardinality guard is
the number of labels that the smaller-host merge must erase. -/
theorem confined_exit {q D E V w z H C Y}
    (free : QFree D V q) (hq : 1≤q) (sub : ∀i j,E i j=true→D i j=true)
    (positive : ∀i∈V,0<w i) (strict : ∀i∈V,mass V w<WeightedSD.col q E V w i)
    (cv : C⊆V) (hv : H⊆V) (yv : Y⊆V) (wide : 2≤H.card) (live : (V\H).Nonempty)
    (feeds : ∀c∈C,∀h∈H,D c h=true) (light : w z+q*mass (C∩inN E V z) w≤mass C w)
    (cheap : (q:ℚ)*mass Y w≤WeightedSD.col q E V w z-mass V w+((q:ℚ)-1)*mass C w)
    (trapped : inN E V z∩ballSet E V H (q-1)⊆Y) : Closure.ForwardMerge.NativeMergePays q D V := by
  by_contra stuck
  have law := expansion sub positive strict stuck
  have split : mass (C∩inN E V z) w+mass (C\inN E V z) w=mass C w := sum_inter_add_sum_sdiff ..
  have budget : (q:ℚ)*mass Y w≤WeightedSD.col q E V w z-mass V w-w z+q*mass (C\inN E V z) w := by
    nlinarith only [cheap,light,congrArg (fun v:ℚ=>(q:ℚ)*v) split]
  have force := funded_group law positive hv (sdiff_subset.trans cv) yv wide live sdiff_disjoint
    (common_missed free hq sub hv (fun c cm h hm=>feeds c (mem_sdiff.mp cm).1 h hm)) budget
  have none : (inN E V z\Y)∩ballSet E V H (q-1)=∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro y ym
    obtain ⟨inside,path⟩ := mem_inter.mp ym
    obtain ⟨parent,off⟩ := mem_sdiff.mp inside
    exact off (trapped (mem_inter.mpr ⟨parent,path⟩))
  rw [none] at force
  simp only [mass,sum_empty,mul_zero] at force
  exact (not_lt_of_ge (sum_nonneg (fun v vm=>(positive v (hv vm)).le))) force

attribute [aesop safe forward (immediate := [free,hq,sub,positive,strict,cv,hv,yv,wide,live,feeds,light,cheap,trapped]) (rule_sets := [CHGraphFamilies])] confined_exit
#print axioms confined_exit
#print axioms common_receivers
#print axioms pair_choice
#print axioms remaining_assignment
#print axioms trim_deficit
#print axioms retained_receiver
end LeanCH.BR.ReservedReachDebt
