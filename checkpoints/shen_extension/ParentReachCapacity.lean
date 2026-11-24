import checkpoints.shen_extension.PricedReachAssignments
namespace LeanCH.BR.ParentReachCapacity
open Finset BRq2 BRq3 BR45 BRsub WeightedSD ReverseReachPayment ReachSlotMatching PricedReachAssignments
open Closure.ShortestCycleWeights Closure.FirstPacketBarrier Closure.MarkedCyclePeeling Classical

theorem in_mass (E V w z) : inW E V w z = mass (inN E V z) w := by
  simp only [inW,mass,inN,sum_filter]

/-- All sources in S compete for the SAME actual parent set of z at the
original column prices. The column's own surplus is an additive margin. -/
theorem parent_mass {q E V w} (law : Expansion q E V w) (positive : ∀i∈V,0<w i)
    (free : QFree E V q) (hq : 1≤q) {z S} (zv : z∈V) (sv : S⊆V)
    (ne : S.Nonempty) (zs : z∉S) (room : (V\insert z S).Nonempty) :
    mass S w+(WeightedSD.col q E V w z-mass V w) <
      (q:ℚ)*mass (inN E V z ∩ ballSet E V S (q-1)) w := by
  classical
  let P := inN E V z
  have pv : P⊆V := filter_subset _ _
  have hv := insert_subset zv sv
  have size := card_sdiff_add_card_eq_card hv
  rw [card_insert_of_notMem zs] at size
  have bill := reached_mass law positive hv pv (by have := card_pos.mpr ne; omega) room
  have same : P∩ballSet E V (insert z S) (q-1)=P∩ballSet E V S (q-1) := by
    ext u
    constructor
    · rintro h
      obtain ⟨pu,hit⟩ := mem_inter.mp h
      obtain ⟨x,xh,walk⟩ := mem_ballSet.mp hit
      rcases mem_insert.mp xh with rfl|xs
      · obtain ⟨uv,k,dist,path⟩ := mem_ball.mp walk
        exact (free u (k+1) (by omega) (by omega) (.step zv (mem_inN.mp pu).2 path)).elim
      · exact mem_inter.mpr ⟨pu,mem_ballSet.mpr ⟨x,xs,walk⟩⟩
    · intro h
      obtain ⟨pu,hit⟩ := mem_inter.mp h
      obtain ⟨x,xs,walk⟩ := mem_ballSet.mp hit
      exact mem_inter.mpr ⟨pu,mem_ballSet.mpr ⟨x,mem_insert_of_mem xs,walk⟩⟩
  rw [same] at bill
  have split : mass (V\insert z S) w+(w z+mass S w)=mass V w := by
    simpa only [mass,sum_insert zs] using (sum_sdiff hv (f:=w))
  change mass S w + (w z+q*inW E V w z-mass V w)<(q:ℚ)*mass _ w
  rw [in_mass]
  linarith

theorem reversed_starts {E V S k} (sv : S⊆V) :
    starts (fun i j=>E j i) V S k=ballSet E V S k := by
  ext u
  constructor
  · intro m
    obtain ⟨uv,s,sm,hit⟩ := mem_filter.mp m
    obtain ⟨_,l,time,walk⟩ := mem_ball.mp hit
    exact mem_ballSet.mpr ⟨s,sm,mem_ball.mpr ⟨uv,l,time,walk.reverse_of_mem uv⟩⟩
  · intro m
    obtain ⟨s,sm,hit⟩ := mem_ballSet.mp m
    obtain ⟨uv,l,time,walk⟩ := mem_ball.mp hit
    exact mem_filter.mpr ⟨uv,s,sm,mem_ball.mpr ⟨sv sm,l,time,walk.reverse_of_mem (sv sm)⟩⟩

/-- At a fixed receiver only its actual retained parents can supply a slot. -/
noncomputable def parentCapacity (q : ℕ) (E : CH.Digraph) (V : Finset ℕ) (cap : ℕ→ℕ) (z u : ℕ) : ℕ :=
  if u∈inN E V z then q*cap u else 0

private theorem total_scaled {V w} {d : ℕ} {cap : ℕ→ℕ} (scale : ∀v∈V,(cap v:ℚ)=d*w v)
    {S : Finset ℕ} (sv : S⊆V) : (↑(∑v∈S,cap v):ℚ)=d*mass S w := by
  rw [Nat.cast_sum,mass,mul_sum]
  exact sum_congr rfl (fun v vm=>scale v (sv vm))

/-- At prices measured in one common unit, Hall's hypotheses hold even after
reserving arbitrary last-parent slots up to one beyond the indicated surplus. -/
theorem parent_assignment {q E V w z H} (law : Expansion q E V w) (positive : ∀i∈V,0<w i)
    (free : QFree E V q) (hq : 1≤q) (zv : z∈V) (hv : H⊆V) (zh : z∉H)
    (room : (V\insert z H).Nonempty) {d : ℕ} (dp : 0<d) {cap : ℕ→ℕ}
    (scale : ∀v∈V,(cap v:ℚ)=d*w v) {margin : ℕ}
    (paid : (margin:ℚ) ≤ d*(WeightedSD.col q E V w z-mass V w))
    {reserve : Finset Slot} (spent : reserve.card≤margin+1) :
    Assignment (fun i j=>E j i) V H (q-1) cap (parentCapacity q E V cap z) reserve := by
  apply assign_margin (margin:=margin+1) _ spent
  intro S sh live
  have sv := sh.trans hv
  have remains : (V\insert z S).Nonempty := room.mono (fun _ m=>mem_sdiff.mpr
    ⟨(mem_sdiff.mp m).1,fun bad=>(mem_sdiff.mp m).2 ((insert_subset_insert z sh) bad)⟩)
  have bill := parent_mass law positive free hq zv sv live (fun m=>zh (sh m)) remains
  let P := inN E V z ∩ ballSet E V S (q-1)
  have pv : P⊆V := inter_subset_left.trans (filter_subset _ _)
  change mass S w+(WeightedSD.col q E V w z-mass V w)<q*mass P w at bill
  have scaled := mul_lt_mul_of_pos_left bill (show (0:ℚ)<d by exact_mod_cast dp)
  have comparison : ((↑(∑u∈S,cap u):ℚ)+margin) < (q:ℚ)*↑(∑v∈P,cap v) := by
    rw [total_scaled scale sv,total_scaled scale pv]
    nlinarith only [scaled,paid]
  have nat : (∑u∈S,cap u)+margin<q*(∑v∈P,cap v) := by exact_mod_cast comparison
  rw [reversed_starts sv]
  have count : (∑u∈ballSet E V S (q-1),parentCapacity q E V cap z u)=q*(∑v∈P,cap v) := by
    unfold parentCapacity
    rw [←sum_filter,Finset.mul_sum]
    apply sum_congr _ (fun _ _=>rfl)
    ext u
    simp [P,and_comm]
  rw [count]
  omega

/-- A matched slot records the exact return on the retained graph. The two
closing arcs can come from different graphs on the same labels. -/
def Returns (q : ℕ) (D E : CH.Digraph) (V : Finset ℕ) (z : ℕ)
    (cap : ℕ→ℕ) (reserve : Finset Slot) : Prop :=
  ∃f : ↥(slots (outN D V z) cap)→Slot, Function.Injective f ∧ ∀u,
    f u∈slots (inN E V z) (fun v=>q*cap v) ∧ f u∉reserve ∧
    Walk E V u.val.1 (f u).1 (q-1)

theorem exact_returns {q D E V z cap reserve} (free : QFree D V q)
    (sub : ∀i j,E i j=true→D i j=true) (zv : z∈V)
    (matchSlots : Assignment (fun i j=>E j i) V (outN D V z) (q-1) cap
      (parentCapacity q E V cap z) reserve) : Returns q D E V z cap reserve := by
  classical
  obtain ⟨f,inj,fit⟩ := matchSlots
  refine ⟨f,inj,?_⟩
  intro u
  obtain ⟨slot,clear,hit⟩ := fit u
  obtain ⟨av,ix⟩ := mem_slots.mp slot
  have az : (f u).1∈inN E V z := by
    by_contra off
    simp [parentCapacity,off] at ix
  obtain ⟨hv,zh⟩ := mem_outN.mp (mem_slots.mp u.property).1
  obtain ⟨_,l,ub,reversed⟩ := mem_ball.mp hit
  have path : Walk E V u.val.1 (f u).1 l := reversed.reverse_of_mem av
  have depth : l=q-1 := by
    by_contra diff
    have closed : Walk D V z z (l+2) :=
      .step hv zh ((walk_sub sub path).snoc zv (sub _ _ (mem_inN.mp az).2))
    exact free z (l+2) (by omega) (by omega) closed
  exact ⟨mem_slots.mpr ⟨az,by simpa only [parentCapacity,ite_eq_left az] using ix⟩,clear,depth ▸ path⟩

/-- Measure prices once, before the receiver and the unavailable slots
are chosen. Each receiver retaining a native parent has a spare label outside
itself and its heads, as required by the underlying reverse merge. -/
def OnCarrier (q : ℕ) (D E : CH.Digraph) (V : Finset ℕ) (w : ℕ→ℚ) : Prop :=
  ∃d : ℕ,0<d ∧ ∃cap : ℕ→ℕ,(∀i∈V,(cap i:ℚ)=d*w i) ∧
    ∀z∈V,(inN D V z).Nonempty → ∀m : ℕ,
      (m:ℚ)≤d*(WeightedSD.col q E V w z-mass V w) →
      ∀R : Finset Slot,R.card≤m+1 → Returns q D E V z cap R

theorem all_receivers {q D E V w} (free : QFree D V q) (hq : 2≤q)
    (sub : ∀i j,E i j=true→D i j=true) (law : Expansion q E V w)
    (positive : ∀i∈V,0<w i) : OnCarrier q D E V w := by
  obtain ⟨d,dp,cap,scale⟩ := integer_units w V (fun i im=>(positive i im).le)
  refine ⟨d,dp,cap,scale,?_⟩
  intro z zv parent m budget R spent
  obtain ⟨p,pm⟩ := parent
  obtain ⟨pv,pz⟩ := mem_inN.mp pm
  have notHead : z∉outN D V z := fun bad=>loopfree free (by omega) zv (mem_outN.mp bad).2
  have room : (V\insert z (outN D V z)).Nonempty := by
    refine ⟨p,mem_sdiff.mpr ⟨pv,?_⟩⟩
    intro inside
    rcases mem_insert.mp inside with eq|head
    · exact loopfree free (by omega) zv (eq ▸ pz)
    · exact digonfree free hq pv zv pz (mem_outN.mp head).2
  exact exact_returns free sub zv (parent_assignment law positive (qfree_sub sub free)
    (by omega) zv outN_subset notHead room dp scale budget spent)

theorem family_receivers {q n} (X : Model q n) {G : Family} {w : ℕ→ℚ}
    (hq : 2≤q) (law : Expansion q (graph X.D G) X.V w) (positive : ∀i∈X.V,0<w i) :
    OnCarrier q X.D (graph X.D G) X.V w := by
  apply all_receivers X.free hq _ law positive
  intro i j edge
  obtain ⟨A,am⟩ := active.mp edge
  exact (mem_col.mp am).2.2.2

/-- A structural upper bound on the reachable parents closes the original
payment goal, even at equality. Neither normalization nor column flatness is required. -/
theorem pays_of_parent_bound {q D E V w z S} (free : QFree E V q) (hq : 1≤q)
    (sub : ∀i j,E i j=true→D i j=true) (positive : ∀i∈V,0<w i)
    (strict : ∀i∈V,mass V w<WeightedSD.col q E V w i)
    (zv : z∈V) (sv : S⊆V) (live : S.Nonempty) (outside : z∉S) (room : (V\insert z S).Nonempty)
    (bound : (q:ℚ)*mass (inN E V z∩ballSet E V S (q-1)) w≤
      mass S w+(WeightedSD.col q E V w z-mass V w)) : Closure.ForwardMerge.NativeMergePays q D V := by
  by_contra stuck
  exact (not_lt_of_ge bound) (parent_mass (expansion sub positive strict stuck) positive free hq zv sv live outside room)

attribute [aesop safe forward (immediate := [X,hq,law,positive]) (rule_sets := [CHGraphFamilies])] family_receivers
attribute [aesop safe forward (immediate := [free,hq,sub,law,positive]) (rule_sets := [CHGraphFamilies])] all_receivers
attribute [aesop safe forward (immediate := [free,hq,sub,positive,strict,zv,sv,live,outside,room,bound]) (rule_sets := [CHGraphFamilies])] pays_of_parent_bound
#print axioms pays_of_parent_bound
#print axioms all_receivers
#print axioms family_receivers

#print axioms parent_mass
#print axioms parent_assignment
end LeanCH.BR.ParentReachCapacity
