import checkpoints.shen_extension.RootFamilyEntry
import checkpoints.shen_extension.MissedFreshCut
import checkpoints.shen_extension.FlatPeelReach
import checkpoints.shen_extension.EndpointBills
import checkpoints.shen_extension.SharedArcPivotGate

namespace LeanCH.BR.FreshMenuExitRules
open Finset BRq2 BRq3 BR45 BRsub WeightedSD RootFamilyEntry
open Closure Closure.ShortestCycleWeights Closure.FirstPacketBarrier

/-- On a saturated native source, test every erased label at the original
row prices. The direction is from the erased label to the survivor. -/
theorem native_survivors {q n} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    {w c} (pos : ∀i∈X.V,0≤w i) (hi : mass X.V w<c) (flat : ∀i∈X.V,row q X.D X.V w i=c)
    {W : Finset ℕ} (within : W⊆X.V) :
    ForwardMerge.rounds q X.D X.V w (X.V\W) (q-1) =
      X.V.filter (fun i=>∀z∈W,X.D z i=true) := by
  classical
  rw [FlatPeelReach.exact_rounds hq X.free small sdiff_subset pos hi flat]
  ext i
  change i∈X.V.filter _ ↔ _
  simp only [mem_filter]
  refine and_congr_right fun iv=>?_
  constructor
  · intro inside z zw
    by_contra off
    have back := (DepositTrace.returns_iff_not_head X (by omega) (within zw) iv).2 off
    exact (mem_sdiff.mp (inside back)).2 zw
  · intro all z back
    exact mem_sdiff.mpr ⟨ball_subset back,fun zw=>
      (DepositTrace.returns_iff_not_head X (by omega) (within zw) iv).1 back (all z zw)⟩

/-- An exact account for an arbitrary bank of erased heads of d. The
last term retains each uncounted head on its original vertex. -/
theorem star_deficit {q D V d W S w c}
    (inside : insert d W ⊆ V) (outside : d∉W) (heads : W⊆outN D V d)
    (common : S⊆outN D V d) (separate : Disjoint W S) (flat : row q D V w d=c) :
    mass (V\insert d W) w - q*mass S w =
      ((q:ℚ)-1)*mass W w - (c-mass V w) + q*mass (outN D V d\(W∪S)) w := by
  classical
  have deleted := sum_sdiff inside (f:=w)
  have remainder := sum_sdiff (union_subset heads common) (f:=w)
  simp only [sum_insert outside] at deleted
  rw [sum_union separate] at remainder
  rw [WeightedSD.row,outW_eq_mass] at flat
  unfold mass at *
  linear_combination deleted - flat - (q:ℚ) * remainder

/-- A retained row loses exactly the native price on the removed labels
it points to, for any graph and any deletion. -/
theorem restricted_row {q D V W w i c} (sub : W⊆V) (flat : row q D V w i=c) :
    row q D (V\W) w i = c-(q:ℚ)*outW D W w i := by
  have split := sum_sdiff sub (f:=fun j=>if D i j=true then w j else 0)
  unfold WeightedSD.row outW at *
  linear_combination flat + (q:ℚ)*split

/-- Exact inner and outer ranked tests for two marked rows. The lost
outgoing masses may come from any erased set on the same graph. -/
theorem ranked_costs {q : ℕ} {D V W w i j c} (pos : 0<q) (sub : W⊆V)
    (fi : row q D V w i=c) (fj : row q D V w j=c) :
    let U := V\W
    let m := mass U w
    let loss := outW D W w
    (m<row q D U w i ↔ (q:ℚ)*loss i<c-m) ∧
    (m≤((q:ℚ)-1)*(row q D U w i-m)+row q D U w j ↔
      ((q:ℚ)-1)*loss i+loss j≤c-m) := by
  intro U m loss
  rw [show row q D U w i=_ from restricted_row sub fi,show row q D U w j=_ from restricted_row sub fj]
  change (m<c-q*loss i ↔ (q:ℚ)*loss i<c-m) ∧ _
  constructor
  · constructor <;> intro h <;> linarith
  · have eq : ((q:ℚ)-1)*(c-q*loss i-m)+(c-q*loss j)-m =
        (q:ℚ)*((c-m)-(((q:ℚ)-1)*loss i+loss j)) := by ring
    rw [←sub_nonneg,eq,mul_nonneg_iff_of_pos_left (show (0:ℚ)<q by exact_mod_cast pos),sub_nonneg]

theorem arc_gap {q D V w c d a} (hq : 2≤q) (free : QFree D V q)
    (dv : d∈V) (hit : a∈outN D V d) (unit : mass V w=1)
    (flat : row q D V w d=c) (floor : c-1<((q:ℚ)-1)*w a) :
    let S := outN D V a ∩ outN D V d
    mass (V\{a,d}) w - q*mass S w =
      ((q:ℚ)-1)*w a-(c-1)+q*mass (outN D V d\(insert a S)) w ∧
    0<((q:ℚ)-1)*w a-(c-1) := by
  classical
  intro S
  have av := outN_subset hit
  have e := (mem_outN.mp hit).2
  have ne : d≠a := fun eq=>loopfree free (by omega) av (eq ▸ e)
  have apart : Disjoint ({a}:Finset ℕ) S := by
    apply disjoint_left.mpr
    intro j hj js
    have eq := mem_singleton.mp hj
    exact loopfree free (by omega) av (eq ▸ (mem_outN.mp (mem_inter.mp js).1).2)
  have id := star_deficit (d:=d) (W:={a}) (S:=S)
    (insert_subset dv (singleton_subset_iff.mpr av)) (by simpa using ne)
    (singleton_subset_iff.mpr hit) inter_subset_right apart flat
  rw [unit] at id
  exact ⟨by simpa only [Finset.pair_comm d a, singleton_union, mass, sum_singleton] using id,sub_pos.mpr floor⟩

/-- Add the contributions of the actual surviving labels, for any menu,
atom floor and cap; no graph assumptions enter this step. -/
theorem menu_mass {S M : Finset ℕ} {w : ℕ→ℚ} {l k d h : ℚ}
    (floor : ∀i∈S∩M,l<k*w i) (cap : ∀i∈S∩M,d*w i≤h) :
    ((S∩M).Nonempty → ((S∩M).card:ℚ)*l < k*mass (S∩M) w) ∧
    d*mass (S∩M) w ≤ ((S∩M).card:ℚ)*h := by
  constructor
  · intro live
    simpa [mass,mul_sum] using sum_lt_sum_of_nonempty live floor
  · simpa [mass,mul_sum] using sum_le_sum cap

/-- A bank of size m in the live pool can supply at most m/q² on the
diffuse branch. Preserve the entire off-menu remainder in the inequality. -/
theorem off_menu_needed {q : ℕ} {U S M : Finset ℕ} {w : ℕ→ℚ} {a d : ℕ}
    (massU : mass U w + (w a+w d)=1)
    (ea : (q:ℚ)^2*w a≤1) (ed : (q:ℚ)^2*w d≤1)
    (cap : (q:ℚ)^2*mass (S∩M) w≤(S∩M).card)
    (bill : mass U w ≤ q*mass S w) :
    (q:ℚ)*((q:ℚ)-(S∩M).card)-2 ≤ (q:ℚ)^3*mass (S\M) w := by
  have split : mass (S∩M) w + mass (S\M) w = mass S w := sum_inter_add_sum_sdiff S M w
  have cost := mul_le_mul_of_nonneg_left bill (sq_nonneg (q:ℚ))
  rw [←split] at cost
  nlinarith only [cost,congrArg (fun t:ℚ=>(q:ℚ)^2*t) massU,ea,ed,
    mul_le_mul_of_nonneg_left cap (Nat.cast_nonneg (α:=ℚ) q)]

/-- Enlarge a paid ranked head bank by ANY set of retained labels. All
these labels are now in the tested inner ball; positivity preserves the
strict bank budget. The returned obstruction keeps its actual row(s). -/
theorem enlarge_ranked {q n D U H M} (hq : 2≤q) (free : QFree D U q)
    (small : SmallerSmallRow q n) (room : U.card+1<n) (hs : H⊆U) (ms : M⊆U)
    (live : H.Nonempty) {w : ℕ→ℚ} (pos : ∀i∈U,0<w i) (heavy : mass U w<q*mass H w) :
    let B := H∪M
    let R := ballSet D U B (q-2)
    mass U w<q*mass B w ∧ M⊆R ∧ ∃i∈R,
      (∀j∈R,row q D U w i≤row q D U w j) ∧
      (row q D U w i≤mass U w ∨ ∃j∈U\R,
        (q-1:ℚ)*(row q D U w i-mass U w)+row q D U w j<mass U w) := by
  intro B R
  have bs : B⊆U := union_subset hs ms
  have mono : mass H w≤mass B w := sum_le_sum_of_subset_of_nonneg
    (subset_union_left (s₂:=M)) (fun i im _=>(pos i (bs im)).le)
  have paid := heavy.trans_le (mul_le_mul_of_nonneg_left mono (Nat.cast_nonneg q))
  exact ⟨paid,(subset_union_right (s₁:=H)).trans (subset_ballSet bs),
    RankedMerge.pair_obstruction hq free small room bs (live.mono subset_union_left) w pos paid⟩

/-- Localize the minimum row by comparing its exact loss with that of
the kept label. Preserve a physical starting vertex when a menu path is forced. -/
theorem minimum_turn {q D V U M a d keep b w c}
    (hq : 2≤q) (free : QFree D V q) (av : a∈V) (ne : a≠d)
    (us : U⊆V) (km : keep∈M) (ka : D keep a=true)
    (wa : 0<w a) (wd : 0≤w d) (ms : M⊆U)
    (rows : ∀i∈V,row q D U w i=c-(q:ℚ)*outW D {a,d} w i)
    (bb : b∈ballSet D U (outN D V a ∪ M) (q-2))
    (least : ∀i∈ballSet D U (outN D V a ∪ M) (q-2),row q D U w b≤row q D U w i) :
    (D b a=true ∧ ∃m∈M\outN D V a,b∈ball D U m (q-2)) ∨
    (D b a=false ∧ D b d=true ∧ w a≤w d) := by
  classical
  by_cases ba : D b a=true
  · left
    obtain ⟨m,hm,walk⟩ := mem_ballSet.mp bb
    have off : m∉outN D V a := by
      intro head
      obtain ⟨_,k,hk,path⟩ := mem_ball.mp walk
      exact free a (k+1+1) (by omega) (by omega)
        (.step (outN_subset head) (mem_outN.mp head).2 ((path.mono us).snoc av ba))
    exact ⟨ba,m,mem_sdiff.mpr ⟨(mem_union.mp hm).resolve_left off,off⟩,walk⟩
  · have kb := least keep (mem_ballSet.mpr ⟨keep,mem_union_right _ km,self_mem_ball (ms km)⟩)
    rw [rows b (us (ballSet_subset bb)),rows keep (us (ms km))] at kb
    have qp : (0:ℚ)<q := by exact_mod_cast (show 0<q by omega)
    have cost : outW D {a,d} w keep ≤ outW D {a,d} w b :=
      (mul_le_mul_iff_right₀ qp).mp (by linarith only [kb])
    by_cases bd : D b d=true
    · right
      refine ⟨Bool.eq_false_iff.mpr ba,bd,?_⟩
      by_cases kd : D keep d=true <;> simp [outW,sum_pair ne,ka,ba,bd,kd] at cost <;> linarith
    · by_cases kd : D keep d=true <;> simp [outW,sum_pair ne,ka,ba,bd,kd] at cost <;> linarith

/-- All three exit tests refer to the same missed row and fresh head. -/
structure Report (q : ℕ) (D : CH.Digraph) (V R : Finset ℕ) (a keep drop : ℕ)
    (w : ℕ→ℚ) (c : ℚ) : Prop where
  witness : ∃ M⊆V\{a,drop}, ∃i∈R, ∃j∈M, D i j=true ∧
    (∀t∈M,t≠j → D i t=false) ∧ keep∈M ∧ M.card=q ∧
    let U := V\{a,drop}
    let S := outN D V a ∩ outN D V drop
    let C := S∩M
    let H := outN D V a ∪ M
    let B := ballSet D U H (q-2)
    ForwardMerge.rounds q D V w U (q-1)=S ∧ keep∉S ∧ C.card<q ∧
    (C.Nonempty → (C.card:ℚ)*(c-1)<((q:ℚ)-1)*mass C w) ∧
    (q:ℚ)^2*mass C w≤C.card ∧ q*mass C w<mass U w ∧
    (mass U w≤q*mass S w → (q:ℚ)*((q:ℚ)-C.card)-2≤(q:ℚ)^3*mass (S\M) w) ∧
    q*mass S w<mass U w ∧
    (mass U w-q*mass S w=((q:ℚ)-1)*w a-(c-1)+q*mass (outN D V drop\insert a S) w ∧
      0<((q:ℚ)-1)*w a-(c-1)) ∧
    mass U w<q*mass H w ∧ M⊆B ∧
    (∀v∈V,row q D U w v=c-(q:ℚ)*outW D {a,drop} w v) ∧
    (∀b∈B,∀e∈U\B,
      (mass U w≤((q:ℚ)-1)*(row q D U w b-mass U w)+row q D U w e ↔
        ((q:ℚ)-1)*outW D {a,drop} w b + outW D {a,drop} w e ≤ c-mass U w)) ∧
    (∃b∈B,(∀t∈B,row q D U w b≤row q D U w t) ∧
      (row q D U w b≤mass U w ∨ ∃e∈U\B,((q:ℚ)-1)*(row q D U w b-mass U w)+row q D U w e<mass U w) ∧
      ((D b a=true ∧ ∃m∈M\outN D V a,b∈ball D U m (q-2)) ∨
        (D b a=false ∧ D b drop=true ∧ w a≤w drop))) ∧
    ∃ K,ShenCycleSuccessor.Cycle D V q K ∧ i∈K ∧ j∈K ∧
      ∀F : MarkedCyclePeeling.Family,
        (∀z∈V,z∉K → (inN (graph D F) K z).card≤1) →
          SmallRow q (graph D (insert K F)) V

theorem from_marked_menu {q n} (X : Model q n) {R a keep drop w c}
    (menu : FreshMenu q X.D X.V R a keep drop)
    (hq : 3≤q) (small : SmallerSmallRow q X.V.card)
    (av : a∈X.V) (kp : keep∈inN X.D X.V a) (dp : drop∈inN X.D X.V a)
    (pos : ∀i∈X.V,0<w i) (unit : mass X.V w=1) (high : 1<c)
    (flat : ∀i∈X.V,row q X.D X.V w i=c) (cap : ∀i∈X.V,(q:ℚ)^2*w i≤1) :
    Report q X.D X.V R a keep drop w c := by
  classical
  obtain ⟨A,i,ir,j,jh,kept,fresh,miss,size,asub,iv⟩ := menu.witness
  let U := X.V\{a,drop}
  let M := insert j A
  let H := outN X.D X.V a
  let S := H∩outN X.D X.V drop
  have ms : M⊆U := insert_subset (outN_subset jh) asub
  have us : U⊆X.V := sdiff_subset
  have km : keep∈M := mem_insert_of_mem kept
  have dv := (mem_inN.mp dp).1
  have da := (mem_inN.mp dp).2
  have ad : a≠drop := fun eq=>loopfree X.free (by omega) dv (eq ▸ da)
  have sub : ({a,drop}:Finset ℕ)⊆X.V := insert_subset av (singleton_subset_iff.mpr dv)
  have ps : ({a,drop}:Finset ℕ).card=2 := card_pair ad
  have count := card_sdiff_add_card_eq_card sub
  have room : U.card+1<X.V.card := by dsimp [U]; omega
  have live : U.Nonempty := ⟨keep,ms km⟩
  have um : mass U w+(w a+w drop)=1 := by
    simpa only [U,mass,sum_pair ad] using (sum_sdiff sub (f:=w)).trans unit
  have same : ForwardMerge.rounds q X.D X.V w U (q-1)=S := by
    rw [native_survivors X (by omega) small (fun z zv=>(pos z zv).le) (unit ▸ high) flat sub]
    ext z
    simp [S,H,mem_outN,and_assoc,and_left_comm]
  have notKeep : keep∉S := fun member=>digonfree X.free (by omega) (mem_inN.mp kp).1 av
    (mem_inN.mp kp).2 (mem_outN.mp (mem_inter.mp member).1).2
  have cs : S∩M ⊆ M.erase keep := fun z zm=>mem_erase.mpr
    ⟨fun eq=>notKeep (eq ▸ (mem_inter.mp zm).1),(mem_inter.mp zm).2⟩
  have short : (S∩M).card<q := by
    have le := card_le_card cs
    have gone := card_erase_add_one km
    change M.card=q at size
    omega
  have nativeFloor := strict_atom_floor_of_proper (by omega : 2≤q) X.free
    (small.induced X.free) w (fun z zv=>(pos z zv).le) c (unit ▸ high) (fun z zv=>(flat z zv).ge)
  rw [unit] at nativeFloor
  have pair := menu_mass (S:=S) (M:=M) (fun z zm=>nativeFloor z (us (ms (mem_inter.mp zm).2)))
    (fun z zm=>cap z (us (ms (mem_inter.mp zm).2)))
  rw [mul_one] at pair
  have menuShort : q*mass (S∩M) w<mass U w := by
    have step : ((S∩M).card:ℚ)+1≤q := by exact_mod_cast short
    by_contra! paid
    have scaled := mul_le_mul_of_nonneg_left paid (sq_nonneg (q:ℚ))
    have qt : (3:ℚ)≤q := by exact_mod_cast hq
    nlinarith only [scaled,congrArg (fun t:ℚ=>(q:ℚ)^2*t) um,cap a av,cap drop dv,
      mul_le_mul_of_nonneg_left pair.2 (Nat.cast_nonneg (α:=ℚ) q),
      mul_le_mul_of_nonneg_left step (Nat.cast_nonneg (α:=ℚ) q),qt]
  have blocked := ForwardMerge.decay (by omega : 2≤q) X.free small us room live w pos
    (fun z zv=>by rw [unit,flat z zv]; exact high)
  rw [same] at blocked
  have hs : H⊆U := by
    intro h hh
    have hv := outN_subset hh
    have ah := (mem_outN.mp hh).2
    exact mem_sdiff.mpr ⟨hv,fun m=>by
      rcases mem_insert.mp m with eq|one
      · exact loopfree X.free (by omega) av (eq ▸ ah)
      · exact digonfree X.free (by omega) dv av da ((mem_singleton.mp one) ▸ ah)⟩
  have ar := flat a av
  rw [WeightedSD.row,outW_eq_mass] at ar
  change w a+q*mass H w=c at ar
  have rich : mass U w<q*mass H w := by linarith [pos drop dv]
  have hl : H.Nonempty := by
    by_contra! empty
    rw [empty] at rich
    simp [mass] at rich
    exact rich.not_ge (mass_nonneg (fun z zu=>(pos z (us zu)).le))
  have rank := enlarge_ranked (by omega : 2≤q) (X.free.mono_set us) small room hs ms hl
    (fun z zu=>pos z (us zu)) rich
  obtain ⟨b,bb,least,bad⟩ := rank.2.2
  have abill (i) (iv : i∈X.V) := restricted_row sub (flat i iv)
  have turn := minimum_turn (by omega : 2≤q) X.free av ad us km (mem_inN.mp kp).2
    (pos a av) (pos drop dv).le ms abill bb least
  obtain ⟨K,ck,ik,jk⟩ := ShortestCycleWeights.edge_cycle X (by omega) iv (us (outN_subset jh)) (mem_outN.mp jh).2
  constructor
  exact ⟨M,ms,i,ir,j,mem_insert_self ..,(mem_outN.mp jh).2,fun t tm ne=>
    miss t ((mem_insert.mp tm).resolve_left ne),km,size,same,notKeep,short,pair.1,pair.2,menuShort,
    off_menu_needed um (cap a av) (cap drop dv) pair.2,blocked,
    arc_gap (by omega) X.free dv (mem_outN.mpr ⟨av,da⟩) unit (flat drop dv) (nativeFloor a av),
    rank.1,rank.2.1,abill,
    fun b bb e ee=>(ranked_costs (by omega : 0<q) sub (flat b (us (ballSet_subset bb)))
      (flat e (us (mem_sdiff.mp ee).1))).2,⟨b,bb,least,bad,turn⟩,
    K,ck,ik,jk,fun F single=>smallRow_of_realDual (EndpointBills.uniform_attach (by omega) ck single).2⟩

/-- The attachment consumer is independent of how a candidate cycle was
found. It applies to the current boundary and preserves every marked input. -/
theorem progress_of_candidate {q n F L K} {X : Model q n}
    {inv : Matrix X.V X.V ℝ} {prices : ℕ→ℚ} {value : ℚ}
    (small : SmallerSmallRow q X.V.card) (boundary : SharedArcBarrier.Boundary X F L)
    (failed : ¬SmallRow q (graph X.D (insert L F)) X.V)
    (candidate : SharedArcBarrier.Boundary X F K)
    (paid : SmallRow q (graph X.D (insert K F)) X.V) :
    SharedArcPivotGate.ProgressAt X F L inv prices value :=
  Or.inl (Or.inl (Or.inr ⟨K,candidate,(SharedArcCompression.winning_iff X small boundary failed K).mpr paid⟩))

/-- Carry the candidate's actual labels to the original attachment. At a
stopped boundary its uniform price has a named exterior double receiver. -/
theorem actual_attachment {q n F L K} {X : Model q n}
    {inv : Matrix X.V X.V ℝ} {prices : ℕ→ℚ} {value : ℚ}
    (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    (boundary : SharedArcBarrier.Boundary X F L)
    (stop : ∀M,SharedArcBarrier.Boundary X F M→¬SmallRow q (graph X.D (insert M F)) X.V)
    (ck : ShenCycleSuccessor.Cycle X.D X.V q K) :
    K∉F → (∃A∈F,SharedArcExpansion.Touch X.D A K) →
    (∃z∈X.V,z∉K ∧ 2≤(inN (graph X.D F) K z).card) ∧
    ((∀z∈X.V,z∉K→(inN (graph X.D F) K z).card≤1) →
      SharedArcPivotGate.ProgressAt X F L inv prices value) := by
  classical
  intro fresh along
  have eligible : SharedArcBarrier.Boundary X F K :=
    ⟨mem_filter.mpr ⟨mem_powerset.mpr ck.sub,ck⟩,fresh,along⟩
  exact ⟨EndpointBills.doubly_fed hq ck (stop K eligible),
    fun single=>progress_of_candidate small boundary (stop L boundary) eligible
      (smallRow_of_realDual (EndpointBills.uniform_attach hq ck single).2)⟩

structure PricedParents {q n} (X : Model q n) (w : ℕ→ℚ) (a x y : ℕ) : Prop where
  root : a∈X.V
  first : x∈inN X.D X.V a
  second : y∈inN X.D X.V a
  ne : x≠y
  cap : ∀j∈X.V,(q:ℚ)^2*w j≤1

@[aesop safe forward (immediate := [s,hq]) (rule_sets := [CHGraphFamilies])]
theorem seed_parents {q n w c} {X : Model q n}
    (s : TwoHeadRepairReplay.Seeds q X.D X.V w c) (hq : 2≤q) :
    PricedParents X w s.a s.x s.y := by
  have h := MissedFreshCut.first_parents X hq s (Or.inl ⟨rfl,rfl⟩)
  exact ⟨s.av,h.2,h.1,s.ne,s.diffuse⟩

@[aesop safe forward (immediate := [side]) (rule_sets := [CHGraphFamilies])]
theorem swap_parents {q n w a x y} {X : Model q n} (side : PricedParents X w a x y) :
    PricedParents X w a y x := ⟨side.root,side.second,side.first,side.ne.symm,side.cap⟩

@[aesop safe forward (immediate := [menu,side,hq,small,pos,unit,high,flat]) (rule_sets := [CHGraphFamilies])]
theorem replay_missed {q n R a keep drop w c} {X : Model q n}
    (menu : FreshMenu q X.D X.V R a keep drop)
    (side : PricedParents X w a keep drop) (hq : 3≤q) (small : SmallerSmallRow q X.V.card)
    (pos : ∀z∈X.V,0<w z) (unit : mass X.V w=1) (high : 1<c)
    (flat : ∀z∈X.V,row q X.D X.V w z=c) :
    Report q X.D X.V R a keep drop w c :=
  from_marked_menu X menu hq small side.root side.first side.second
    pos unit high flat side.cap

structure NativeTest {q n} (X : Model q n) (w : ℕ→ℚ) : Prop where
  rounds : ∀W⊆X.V,ForwardMerge.rounds q X.D X.V w (X.V\W) (q-1) =
    X.V.filter (fun i=>∀z∈W,X.D z i=true)
  deficit : ¬RetainedBill q X.D X.V w
  marked : ∀d∈X.V,∀a∈outN X.D X.V d,
    let S := outN X.D X.V a ∩ outN X.D X.V d
    let c := row q X.D X.V w d
    mass (X.V\{a,d}) w-q*mass S w=((q:ℚ)-1)*w a-(c-1)+q*mass (outN X.D X.V d\insert a S) w ∧
      0<((q:ℚ)-1)*w a-(c-1)

@[aesop safe forward (immediate := [hq,small,pos,unit,high,flat]) (rule_sets := [CHGraphFamilies])]
theorem native_test {q n w c} {X : Model q n} (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    (pos : ∀i∈X.V,0<w i) (unit : mass X.V w=1) (high : 1<c)
    (flat : ∀i∈X.V,row q X.D X.V w i=c) : NativeTest X w := by
  refine ⟨fun W ws=>native_survivors X hq small (fun i iv=>(pos i iv).le) (unit ▸ high) flat ws,?_,?_⟩
  · rintro ⟨U,us,room,live,bill⟩
    exact (ForwardMerge.decay hq X.free small us room live w pos
      (fun i iv=>by rw [unit,flat i iv]; exact high)).not_ge bill
  · intro d dv a hit S lev
    have floor := strict_atom_floor_of_proper hq X.free (small.induced X.free) w
      (fun i iv=>(pos i iv).le) c (unit ▸ high) (fun i iv=>(flat i iv).ge) a (outN_subset hit)
    rw [unit] at floor
    dsimp only [lev]
    rw [flat d dv]
    exact arc_gap hq X.free dv hit unit (flat d dv) floor

#print axioms replay_missed
#print axioms native_test
#print axioms progress_of_candidate
#print axioms actual_attachment
#print axioms star_deficit

end LeanCH.BR.FreshMenuExitRules
