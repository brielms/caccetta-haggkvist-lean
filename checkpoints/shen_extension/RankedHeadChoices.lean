import checkpoints.shen_extension.RankedCommonBank
import LeanCH.BR.BRWeightedBallExit

namespace LeanCH.BR.RankedHeadChoices
open Finset BRq2 BRq3 BR45 BRsub WeightedSD Closure

/-- Row tests for a fixed labelled carrier, arc set, prices and head set. -/
def RowBills (q : ℕ) (D : CH.Digraph) (U H : Finset ℕ) (w : ℕ → ℚ) (k : ℕ) : Prop :=
  ∀ i ∈ ballSet D U H k, mass U w < row q D U w i ∧
    ∀ j ∈ U \ ballSet D U H k, mass U w ≤
      ((q : ℚ) - 1) * (row q D U w i - mass U w) + row q D U w j

def Allowed (q : ℕ) (D : CH.Digraph) (U : Finset ℕ) (w : ℕ → ℚ) (i : ℕ) : Prop :=
  mass U w < row q D U w i ∧ ∀ j ∈ U, mass U w ≤
    ((q : ℚ) - 1) * (row q D U w i - mass U w) + row q D U w j

noncomputable def heads (q : ℕ) (D : CH.Digraph) (U : Finset ℕ) (w : ℕ → ℚ) (k : ℕ) : Finset ℕ := by
  classical
  exact U.filter (fun h => ∀ i ∈ ball D U h k, Allowed q D U w i)

/-- All admissible head sets are precisely the subsets of one explicit set.
    Rows inside the ball already cover their own side of the pair inequality. -/
theorem row_bills_iff {q D U H w k} (hq : 1 ≤ q) (hs : H ⊆ U) :
    RowBills q D U H w k ↔ H ⊆ heads q D U w k := by
  classical
  have qnn : (0 : ℚ) ≤ q - 1 := sub_nonneg.mpr (by exact_mod_cast hq)
  constructor
  · intro ok h hh
    apply mem_filter.mpr
    refine ⟨hs hh,fun i ih => ?_⟩
    have ib := mem_ballSet.mpr ⟨h,hh,ih⟩
    obtain ⟨inner,outer⟩ := ok i ib
    refine ⟨inner, fun j ju => ?_⟩
    by_cases jb : j ∈ ballSet D U H k
    · exact ((ok j jb).1.le).trans (le_add_of_nonneg_left (mul_nonneg qnn (sub_nonneg.mpr inner.le)))
    · exact outer j (mem_sdiff.mpr ⟨ju,jb⟩)
  · intro all i ib
    obtain ⟨h,hh,ih⟩ := mem_ballSet.mp ib
    have ok := (mem_filter.mp (all hh)).2 i ih
    exact ⟨ok.1,fun j jb => ok.2 j (mem_sdiff.mp jb).1⟩

theorem exists_menu_iff {q : ℕ} {D U w k} (hq : 1 ≤ q) (nn : ∀i∈U,0≤w i) :
    (∃H⊆U,H.Nonempty ∧ mass U w < q * mass H w ∧ RowBills q D U H w k) ↔
      mass U w < q * mass (heads q D U w k) w := by
  classical
  let K := heads q D U w k
  have ks : K ⊆ U := filter_subset _ _
  constructor
  · rintro ⟨H,hs,_,heavy,ok⟩
    exact heavy.trans_le (mul_le_mul_of_nonneg_left (mass_mono ((row_bills_iff hq hs).mp ok)
      (fun i ih => nn i (ks ih))) (Nat.cast_nonneg q))
  · intro heavy
    have live : K.Nonempty := by
      by_contra! empty
      change mass U w < q * mass K w at heavy
      rw [empty] at heavy
      simp [mass] at heavy
      exact heavy.not_ge (mass_nonneg nn)
    exact ⟨K,ks,live,heavy,(row_bills_iff hq ks).mpr Subset.rfl⟩

/-- The actual ranked exit, including the freedom to change arcs and prices. -/
theorem pair_iff {q D V} (hq : 1 ≤ q) :
    RankedMerge.PairPays q D V ↔ ∃ U ⊆ V, U.card + 1 < V.card ∧
      ∃ E : CH.Digraph, (∀i j,E i j=true → D i j=true) ∧ ∃ w : ℕ → ℚ,
      (∀i∈U,0<w i) ∧ mass U w < q * mass (heads q E U w (q-2)) w := by
  constructor
  · rintro ⟨U,us,room,E,sub,H,hs,live,w,pos,bill,rows⟩
    exact ⟨U,us,room,E,sub,w,pos,(exists_menu_iff hq (fun i iu=>(pos i iu).le)).mp
      ⟨H,hs,live,bill,rows⟩⟩
  · rintro ⟨U,us,room,E,sub,w,pos,bill⟩
    obtain ⟨H,hs,live,heavy,ok⟩ := (exists_menu_iff hq (fun i iu=>(pos i iu).le)).mpr bill
    exact ⟨U,us,room,E,sub,H,hs,live,w,pos,heavy,ok⟩

/-- At flat original weights, the largest retained loss sets one common pair
    threshold for every proposed inner row. -/
theorem loss_test {q D V W w c i e} (hq : 0<q) (sub : W⊆V)
    (flat : ∀j∈V,row q D V w j=c) (iu : i∈V\W) (eu : e∈V\W)
    (worst : ∀j∈V\W,outW D W w j ≤ outW D W w e) :
    Allowed q D (V\W) w i ↔
      (q:ℚ)*outW D W w i < c-mass (V\W) w ∧
        ((q:ℚ)-1)*outW D W w i + outW D W w e ≤ c-mass (V\W) w := by
  have tests (j) (ju : j∈V\W) := FreshMenuExitRules.ranked_costs (q:=q) hq sub
    (flat i (mem_sdiff.mp iu).1) (flat j (mem_sdiff.mp ju).1)
  constructor
  · rintro ⟨inner,all⟩
    exact ⟨(tests e eu).1.mp inner,(tests e eu).2.mp (all e eu)⟩
  · rintro ⟨inner,outer⟩
    exact ⟨(tests e eu).1.mpr inner,fun j ju => (tests j ju).2.mpr
      ((add_le_add_right (worst j ju) _).trans (by simpa [add_comm] using outer))⟩

/-- When one retained row hits the entire erased set, a single lost head is
    already too expensive. Rows losing no head satisfy both tests. -/
theorem all_hit_threshold {q D V W w c e} (hq : 2≤q) (sub : W⊆V)
    (nn : ∀j∈W,0≤w j) (high : mass V w<c) (flat : ∀j∈V,row q D V w j=c)
    (floor : ∀j∈W,c-mass V w<((q:ℚ)-1)*w j) (eu : e∈V\W)
    (all : ∀j∈W,D e j=true) {i} (iu : i∈V\W) :
    Allowed q D (V\W) w i ↔ ∀j∈W,D i j≠true := by
  have top : outW D W w e = mass W w := by
    unfold outW mass
    exact sum_congr rfl (fun j jw => by simp [all j jw])
  have worst (j) (_ : j∈V\W) : outW D W w j ≤ outW D W w e := by
    rw [top,outW_eq_mass]
    exact mass_mono outN_subset nn
  have split : mass (V\W) w + mass W w = mass V w := sum_sdiff sub
  rw [loss_test (by omega : 0<q) sub flat iu eu worst,top]
  constructor
  · intro ok j jw hit
    have base : w j ≤ outW D W w i := by
      rw [outW_eq_mass]
      simpa [mass] using mass_mono (singleton_subset_iff.mpr (mem_outN.mpr ⟨jw,hit⟩))
        (w:=w) (fun u uh=>nn u (outN_subset uh))
    have one : (1:ℚ)≤q := by exact_mod_cast (show 1≤q by omega)
    linarith only [ok.2,split,floor j jw,mul_le_mul_of_nonneg_left base (sub_nonneg.mpr one)]
  · intro off
    have zero : outW D W w i=0 := sum_eq_zero (fun j jw=>by simp [off j jw])
    rw [zero,mul_zero,mul_zero,zero_add]
    constructor <;> linarith only [split,high,mass_nonneg nn]

/-- Hitting the erased set within k+1 native steps is detected at its first
    actual crossing, whose tail is still in the punctured k-ball. -/
theorem avoid_iff {D V W h k} (sub : W⊆V) (hv : h∈V\W) :
    (∀i∈ball D (V\W) h k,∀j∈W,D i j≠true) ↔ ball D V h (k+1) ⊆ V\W := by
  constructor
  · intro avoid j reached
    refine mem_sdiff.mpr ⟨ball_subset reached,fun jw=>?_⟩
    obtain ⟨_,m,hm,p⟩ := mem_ball.mp reached
    obtain ⟨l,i,b,bound,iu,bu,path,hit⟩ := first_exit_of_walk p hv (fun ju=>(mem_sdiff.mp ju).2 jw)
    have bw : b∈W := by
      by_contra off
      exact (mem_sdiff.mp bu).2 (mem_sdiff.mpr ⟨(mem_sdiff.mp bu).1,off⟩)
    exact avoid i (mem_ball.mpr ⟨iu,l,by omega,path⟩) b bw hit
  · intro inside i reached j jw hit
    obtain ⟨_,m,hm,p⟩ := mem_ball.mp reached
    have jv := sub jw
    exact (mem_sdiff.mp (inside (mem_ball.mpr ⟨jv,m+1,by omega,(p.mono sdiff_subset).snoc jv hit⟩))).2 jw

/-- One retained common parent identifies the best head bank for every head
    choice, on any erased set. Saturation identifies the labels exactly. -/
theorem all_hit_heads {q n} (X : ShortestCycleWeights.Model q n) (hq : 2≤q)
    {W w c e} (sub : W⊆X.V) (nn : ∀j∈W,0≤w j) (high : mass X.V w<c)
    (flat : ∀i∈X.V,row q X.D X.V w i=c)
    (floor : ∀j∈W,c-mass X.V w<((q:ℚ)-1)*w j)
    (eu : e∈X.V\W) (all : ∀j∈W,X.D e j=true) :
    heads q X.D (X.V\W) w (q-2) = X.V.filter (fun h=>∀j∈W,X.D j h=true) := by
  classical
  have same {i} (iu : i∈X.V\W) := all_hit_threshold hq sub nn high flat floor eu all iu
  have rad : q-2+1=q-1 := by omega
  ext h
  simp only [heads,mem_filter]
  constructor
  · rintro ⟨hu,ok⟩
    have inside := (avoid_iff (k:=q-2) sub hu).mp (fun i ib=>(same (ball_subset ib)).mp (ok i ib))
    rw [rad] at inside
    refine ⟨(mem_sdiff.mp hu).1,fun j jw=>?_⟩
    by_contra off
    have back := (DepositTrace.returns_iff_not_head X (by omega) (sub jw) (mem_sdiff.mp hu).1).mpr off
    exact (mem_sdiff.mp (inside back)).2 jw
  · rintro ⟨hv,hit⟩
    have hu : h∈X.V\W := mem_sdiff.mpr ⟨hv,fun hw=>loopfree X.free (by omega) hv (hit h hw)⟩
    have inside : ball X.D X.V h (q-2+1)⊆X.V\W := by
      rw [rad]
      intro j back
      exact mem_sdiff.mpr ⟨ball_subset back,fun jw=>
        (DepositTrace.returns_iff_not_head X (by omega) (sub jw) hv).mp back (hit j jw)⟩
    exact ⟨hu,fun i ib=>(same (ball_subset ib)).mpr ((avoid_iff sub hu).mpr inside i ib)⟩

/-- An independently obtained common parent. A positive lower bound on the
    native row surplus suffices; rows need not all take the same value. -/
theorem forced_parent {q D V w σ} (hq : 2≤q) (free : QFree D V q)
    (small : SmallerSmallRow q V.card) (pos : ∀i∈V,0<w i) (sur : 0<σ)
    (lower : ∀i∈V,σ≤ForwardMerge.surplus q D V w i) {d a : V} (da : D d a=true)
    (tail : ((q:ℚ)-2)*w d ≤ σ) (turn : ((q:ℚ)-1)*w d < σ+w a) :
    ∃j∈V\{a.val,d.val},D j a=true ∧ D j d=true := by
  let U := (V.erase a.val).erase d.val
  have us : U⊆V := (erase_subset _ _).trans (erase_subset _ _)
  obtain ⟨i,ir,_,_,_,_,bad⟩ := RankedMerge.arc_pair hq free small w pos (a:=a) (b:=d)
    (fun i iv _=>by have h:=sur.trans_le (lower i iv); exact sub_pos.mp h) da
  have li := lower i (us (ballSet_subset ir))
  rcases bad with one|⟨j,jout,bad⟩
  · linarith only [one,turn,li]
  · have ju : j∈U := (mem_sdiff.mp jout).1
    have lj := lower j (us ju)
    have floor : (q:ℚ)*σ ≤ ((q:ℚ)-1)*ForwardMerge.surplus q D V w i+
        ForwardMerge.surplus q D V w j := by
      have qp : (1:ℚ)≤q := by exact_mod_cast (show 1≤q by omega)
      linarith only [mul_le_mul_of_nonneg_left li (sub_nonneg.mpr qp),lj]
    have cut := (mul_lt_mul_iff_right₀ (show (0:ℚ)<q by exact_mod_cast (show 0<q by omega))).mp
      (floor.trans_lt bad)
    refine ⟨j,mem_sdiff.mpr ⟨us ju,fun jj=>?_⟩,?_⟩
    · rcases mem_insert.mp jj with aa|dd
      · exact (mem_erase.mp (mem_erase.mp ju).2).1 aa
      · exact (mem_erase.mp ju).1 (mem_singleton.mp dd)
    · cases ja : D j a <;> cases jd : D j d <;>
        simp only [ja,jd,Bool.false_eq_true,ite_false,ite_true] at cut ⊢
      all_goals first | trivial | linarith only [cut,tail,turn,pos d d.property,pos a a.property]

structure SourceChoices {q n} (X : ShortestCycleWeights.Model q n) (w : ℕ→ℚ) (c : ℚ) : Prop where
  cap : ∀U⊆X.V,U.card+1<X.V.card → ∀E : CH.Digraph,(∀i j,E i j=true → X.D i j=true) →
    ∀v : ℕ→ℚ,(∀i∈U,0<v i) → (q:ℚ)*mass (heads q E U v (q-2)) v ≤ mass U v
  common : ∀W⊆X.V,∀e∈X.V\W,(∀j∈W,X.D e j=true) →
    heads q X.D (X.V\W) w (q-2) = X.V.filter (fun h=>∀j∈W,X.D j h=true)
  force : ∀d∈X.V,∀a∈outN X.D X.V d,
    ((q:ℚ)-2)*w d ≤ c-mass X.V w → ((q:ℚ)-1)*w d < c-mass X.V w+w a →
      ∃j∈X.V\{a,d},X.D j a=true ∧ X.D j d=true

@[aesop safe forward (immediate := [hq,small,pos,high,unit,flat]) (rule_sets := [CHGraphFamilies])]
theorem source_rule {q n w c} {X : ShortestCycleWeights.Model q n} (hq : 2≤q)
    (small : SmallerSmallRow q X.V.card) (pos : ∀i∈X.V,0<w i) (high : 1<c)
    (unit : mass X.V w=1) (flat : ∀i∈X.V,row q X.D X.V w i=c) : SourceChoices X w c := by
  have strict : mass X.V w<c := unit ▸ high
  have atom := strict_atom_floor_of_proper hq X.free (small.induced X.free) w
    (fun i iv=>(pos i iv).le) c strict (fun i iv=>(flat i iv).ge)
  constructor
  · intro U us room E sub v vp
    exact le_of_not_gt (fun bill=>RankedMerge.no_pair hq X.free small
      ((pair_iff (by omega)).mpr ⟨U,us,room,E,sub,v,vp,bill⟩))
  · intro W ws e eu all
    exact all_hit_heads X hq ws (fun i iw=>(pos i (ws iw)).le) strict flat
      (fun i iw=>atom i (ws iw)) eu all
  · intro d dv a ah cheap turn
    exact forced_parent hq X.free small pos (sub_pos.mpr strict)
      (fun i iv=>by simp [ForwardMerge.surplus,flat i iv]) (d:=⟨d,dv⟩) (a:=⟨a,outN_subset ah⟩)
      (mem_outN.mp ah).2 cheap turn

/-- Keep the actual erased labels. The numerical test can supply the parent
    on this graph; a parent supplied by any other rule works as well. -/
structure MarkedChoices (q : ℕ) (D : CH.Digraph) (V : Finset ℕ) (w : ℕ→ℚ) (c : ℚ) (a d : ℕ) : Prop where
  force : ((q:ℚ)-2)*w d ≤ c-mass V w → ((q:ℚ)-1)*w d < c-mass V w+w a →
    (RankedCommonBank.commonParents D (V\{a,d}) a d).Nonempty
  menus : (RankedCommonBank.commonParents D (V\{a,d}) a d).Nonempty →
    let U := V\{a,d}
    let S := outN D V a ∩ outN D V d
    heads q D U w (q-2)=S ∧ (q:ℚ)*mass S w < mass U w ∧
      ∀H⊆U,RowBills q D U H w (q-2) ↔ H⊆S

@[aesop safe forward (immediate := [facts,arc,hq,native,pos]) (rule_sets := [CHGraphFamilies])]
theorem marked_rule {q n w c a d keep} {X : ShortestCycleWeights.Model q n}
    (facts : SourceChoices X w c) (arc : FreshMenuExitRules.PricedParents X w a keep d)
    (hq : 2≤q) (native : FreshMenuExitRules.NativeTest X w) (pos : ∀i∈X.V,0<w i) :
    MarkedChoices q X.D X.V w c a d := by
  obtain ⟨dv,da⟩ := mem_inN.mp arc.second
  have ah := mem_outN.mpr ⟨arc.root,da⟩
  constructor
  · intro cheap turn
    obtain ⟨j,ju,ja,jd⟩ := facts.force d dv a ah cheap turn
    exact ⟨j,mem_filter.mpr ⟨ju,ja,jd⟩⟩
  · rintro ⟨j,jc⟩ U S
    obtain ⟨ju,ja,jd⟩ := mem_filter.mp jc
    have eq := facts.common {a,d} (insert_subset arc.root (singleton_subset_iff.mpr dv)) j ju (by
      intro k hk
      rcases mem_insert.mp hk with rfl|s
      · exact ja
      · exact mem_singleton.mp s ▸ jd)
    have geom : heads q X.D U w (q-2)=S := by
      rw [eq]
      ext i
      simp [S,mem_outN,and_left_comm,and_assoc]
    obtain ⟨budget,gap⟩ := native.marked d dv a ah
    have hnn : 0 ≤ mass (outN X.D X.V d \ insert a S) w := by
      exact mass_nonneg (fun i ii=>(pos i (outN_subset (mem_sdiff.mp ii).1)).le)
    have lt : (q:ℚ)*mass S w < mass U w := by
      change mass U w-(q:ℚ)*mass S w = _ at budget
      linarith only [budget,gap,mul_nonneg (Nat.cast_nonneg (α:=ℚ) q) hnn]
    exact ⟨geom,lt,fun H hs=>by rw [row_bills_iff (by omega : 1≤q) hs,geom]⟩

#print axioms pair_iff
#print axioms all_hit_heads
#print axioms forced_parent
#print axioms source_rule
#print axioms marked_rule
end LeanCH.BR.RankedHeadChoices
