import checkpoints.shen_extension.MinimumOrderProfile
import checkpoints.shen_extension.DeleteRepairUnlock
import checkpoints.shen_extension.dot_tensor_research.DotKernelSharedHead_20261118
import LeanCH.BR.BRNearBoundaryRows

namespace LeanCH.BR.ShenCycleSuccessor
open Finset BRq2 BRq3 BR45 ShenMinimumOrder ShenKernelHead ShenPrimeTransition

/-- One parent works for the whole row of y, on the original labels. -/
theorem fixed_parent {q s} (X : Source q s) (hq : 2 ≤ q) (hs : 0 < s)
    {y} (hy : y ∈ X.V) :
    ∃ p ∈ X.V, X.D p y = true ∧ (outN X.D X.V p).card = s ∧
      (outN X.D X.V y \ outN X.D X.V p).Nonempty ∧
      ∀ w ∈ outN X.D X.V y \ outN X.D X.V p,
        Walk X.D (X.V \ {y}) w p (q-1) := by
  have pos := X.degree y hy
  obtain ⟨b,hb⟩ := card_pos.mp (show 0 < (outN X.D X.V y).card by omega)
  have different (w) (hw : w ∈ outN X.D X.V y) : w ≠ y := by
    rintro rfl
    exact loopfree X.free (by omega) hy (mem_outN.mp hw).2
  have live : (X.V \ {y}).Nonempty :=
    ⟨b,mem_sdiff.mpr ⟨outN_subset hb,by simpa using different b hb⟩⟩
  obtain ⟨p,hp,py,tight,row⟩ :=
    DeleteRepair.half_zone_parent X.free X.least X.degree hy live
  have missing : (outN X.D X.V y \ outN X.D X.V p).Nonempty := by
    by_contra empty
    have sub : outN X.D X.V y ⊆ outN X.D X.V p := by
      intro w hw
      by_contra hn
      exact empty ⟨w,mem_sdiff.mpr ⟨hw,hn⟩⟩
    have eq := eq_of_subset_of_card_le sub (tight.trans_le pos)
    exact loopfree X.free (by omega) hy
      (mem_outN.mp (eq.symm ▸ (mem_outN.mpr ⟨hy,py⟩ : y ∈ outN X.D X.V p))).2
  refine ⟨p,hp,py,tight,missing,?_⟩
  intro w hw
  obtain ⟨yw,absent⟩ := mem_sdiff.mp hw
  have far (a m) (ay : X.D a y = true) (ret : Walk X.D (X.V \ {y}) w a m) :
      q < m+2 := by
    by_contra! small
    exact X.free y (m+2) (by omega) small
      (.step (outN_subset yw) (mem_outN.mp yw).2 ((ret.mono sdiff_subset).snoc hy ay))
  rcases row w (outN_subset yw) (different w yw) with arc | ⟨m,budget,ret⟩ | ⟨a,_,ay,_,m,budget,ret⟩
  · exact (absent (mem_outN.mpr ⟨outN_subset yw,arc⟩)).elim
  · have := far p m py ret
    simpa only [show q-1=m by omega] using ret
  · have := far a m ay ret
    omega

/-- A walk can be replayed on at most one destination label per step. -/
private theorem small_carrier {D V a b m} (walk : Walk D V a b m) :
    ∃ U ⊆ V, U.card ≤ m ∧ Walk D U a b m := by
  induction walk with
  | refl => exact ⟨∅,empty_subset _,by simp,.refl _⟩
  | @step a b c k hb arc rest ih =>
    obtain ⟨U,sub,small,ret⟩ := ih
    exact ⟨insert b U,insert_subset hb sub,(card_insert_le _ _).trans (by omega),
      .step (mem_insert_self _ _) arc (ret.mono (subset_insert _ _))⟩

/-- An induced shortest cycle on named labels. -/
structure Cycle (D : CH.Digraph) (V : Finset ℕ) (q : ℕ) (M : Finset ℕ) : Prop where
  sub : M ⊆ V
  size : M.card = q+1
  heads : OutEq 1 D M
  incoming : ∀ z ∈ M, (parents D M z).card = 1

/-- The successor contains the specified three labels, including the shared head. -/
theorem marked_cycle {D V q p y w} (hq : 2 ≤ q) (free : QFree D V q)
    (hy : y ∈ V) (hw : w ∈ V) (py : D p y = true) (yw : D y w = true)
    (ret : Walk D (V \ {y}) w p (q-1)) :
    ∃ M, Cycle D V q M ∧ p ∈ M ∧ y ∈ M ∧ w ∈ M := by
  obtain ⟨U,sub,small,path⟩ := small_carrier ret
  let K := insert y (insert w U)
  have subK : K ⊆ V := insert_subset hy (insert_subset hw (sub.trans sdiff_subset))
  have yK : y ∈ K := mem_insert_self _ _
  have wK : w ∈ K := mem_insert_of_mem (mem_insert_self _ _)
  have pK : p ∈ K := by
    rcases path.end_mem_or with eq | mem
    · simpa only [eq] using wK
    · exact mem_insert_of_mem (mem_insert_of_mem mem)
  have room : K.card ≤ q+1 := by
    have h1 := card_insert_le w U
    have h2 := card_insert_le y (insert w U)
    dsimp [K]
    omega
  have closed : Walk D K p p (q-1+1+1) :=
    .step yK py (.step wK yw (path.mono ((subset_insert w U).trans (subset_insert y _))))
  rw [show q-1+1+1=q+1 by omega] at closed
  obtain ⟨M,subM,size,degree⟩ := BRq2.boundary_closed_walk_support (free.mono_set subK) closed
  have same := eq_of_subset_of_card_le subM (size ▸ room)
  subst M
  have reg := dt_reg (by omega : 1≤q) (ball_q_one q (by omega)) (free.mono_set subK)
    degree (by simpa using size)
  exact ⟨K,⟨subK,size,reg.1,reg.2⟩,pK,yK,wK⟩

/-- Every rich exterior head of every cycle is eligible. The parent is fixed
before choosing the shortcut head, and the successor is in the very same graph. -/
theorem successors {q s} (X : Source q s) (hq : 2 ≤ q) (hs : 0 < s)
    (order : X.V.card ≤ q*s) {M} (C : Cycle X.D X.V q M) :
    (∃ y ∈ X.V \ M, 2 ≤ (parents X.D M y).card) ∧
    ∀ y ∈ X.V \ M, 2 ≤ (parents X.D M y).card →
      ∃ p ∈ X.V, X.D p y = true ∧ (outN X.D X.V p).card = s ∧
        (outN X.D X.V y \ outN X.D X.V p).Nonempty ∧
        ∀ w ∈ outN X.D X.V y \ outN X.D X.V p,
          ∃ N, Cycle X.D X.V q N ∧ N ≠ M ∧ p ∈ N ∧ y ∈ N ∧ w ∈ N := by
  constructor
  · have strict : Strict q X.D X.V (fun _ => 1) := by
      apply nat_strict.mpr
      intro v hv
      have le := Nat.mul_le_mul_left q (X.degree v hv)
      simpa [score,outN] using (show X.V.card < 1+q*(outN X.D X.V v).card by omega)
    obtain ⟨y,hy,rich⟩ := cycle_samples strict C.sub (fun z hz => (C.incoming z hz).le)
      (Subset.rfl : M ⊆ M) (by have := C.size; omega)
    refine ⟨y,hy,?_⟩
    by_contra! low
    have le := Nat.mul_le_mul_left q (show (parents X.D M y).card ≤ 1 by omega)
    rw [Nat.mul_one] at le
    have := C.size
    omega
  · intro y hy _
    obtain ⟨p,hp,py,tight,ne,row⟩ := fixed_parent X hq hs (mem_sdiff.mp hy).1
    refine ⟨p,hp,py,tight,ne,?_⟩
    intro w hw
    have yw := mem_outN.mp (mem_sdiff.mp hw).1
    obtain ⟨N,cyc,pN,yN,wN⟩ := marked_cycle hq X.free (mem_sdiff.mp hy).1 yw.1 py yw.2 (row w hw)
    exact ⟨N,cyc,fun eq => (mem_sdiff.mp hy).2 (eq ▸ yN),pN,yN,wN⟩

/-- A successor through y retains an actual tight parent and its full return row. -/
def Via {q s} (X : Source q s) (y : ℕ) (N : Finset ℕ) : Prop :=
  ∃ p ∈ X.V, X.D p y = true ∧ (outN X.D X.V p).card = s ∧
    (∀ w ∈ outN X.D X.V y \ outN X.D X.V p, Walk X.D (X.V \ {y}) w p (q-1)) ∧
    ∃ w ∈ outN X.D X.V y \ outN X.D X.V p, Cycle X.D X.V q N ∧ p ∈ N ∧ y ∈ N ∧ w ∈ N

theorem via_exists {q s} (X : Source q s) (hq : 2 ≤ q) (hs : 0 < s) {y} (hy : y ∈ X.V) :
    ∃ N, Via X y N ∧ y ∈ N := by
  obtain ⟨p,hp,py,tight,⟨w,miss⟩,returns⟩ := fixed_parent X hq hs hy
  have yw := mem_outN.mp (mem_sdiff.mp miss).1
  obtain ⟨N,C,pN,yN,wN⟩ := marked_cycle hq X.free hy yw.1 py yw.2 (returns w miss)
  exact ⟨N,⟨p,hp,py,tight,returns,w,miss,C,pN,yN,wN⟩,yN⟩

/-- The paper bridge on the given source, before any regular thinning.
Every large sample of the same tight cycle supplies an exterior root at
which a successor cycle can be taken in this original graph. -/
theorem tight_cycle_samples {q s} (X : Source q s) (hq : 2 ≤ q) (hs : 0 < s)
    (order : X.V.card ≤ q*s) :
    ∃ M ⊆ X.V, q < M.card ∧ OutEq 1 X.D M ∧
      QFree X.D M (M.card-1) ∧ (∀ p ∈ M, (outN X.D X.V p).card = s) ∧
      ∀ S ⊆ M, q < S.card → ∃ y ∈ X.V \ M, S.card < q*(parents X.D S y).card ∧
        ∃ N, Via X y N ∧ y ∈ N := by
  classical
  let T := X.V.filter fun p => (outN X.D X.V p).card=s
  have owner (v) (hv : v ∈ X.V) : ∃ p ∈ T, X.D p v = true := by
    obtain ⟨p,hp,arc,tight,_⟩ := fixed_parent X hq hs hv
    exact ⟨p,mem_filter.mpr ⟨hp,tight⟩,arc⟩
  obtain ⟨v,hv⟩ := X.nonempty
  obtain ⟨p,hp,_⟩ := owner v hv
  let rev : CH.Digraph := fun a b => X.D b a
  have deg (u) (hu : u ∈ T) : 1 ≤ (outN rev T u).card := by
    obtain ⟨a,ha,au⟩ := owner u (mem_filter.mp hu).1
    exact card_pos.mpr ⟨a,mem_outN.mpr ⟨ha,au⟩⟩
  obtain ⟨k,M,kq,free,sub,size,one⟩ := BRsGen.exists_minimal_cycle_support
    (by omega : 1≤q) (X.free.reverse.mono_set (filter_subset _ _)) deg ⟨p,hp⟩
  have subV := sub.trans (filter_subset _ _)
  have reg := dt_reg (by omega : 1 ≤ k) (ball_q_one k (by omega)) (free.mono_set sub)
    (fun z hz => (one z hz).ge) (by simpa using size)
  have strict : Strict q X.D X.V (fun _ => 1) := by
    apply nat_strict.mpr
    intro z hz
    have := Nat.mul_le_mul_left q (X.degree z hz)
    simpa [score,outN] using (show X.V.card < 1+q*(outN X.D X.V z).card by omega)
  refine ⟨M,subV,by omega,reg.2,?_,fun z hz => (mem_filter.mp (sub hz)).2,?_⟩
  · rw [show M.card-1=k by omega]
    exact (free.mono_set sub).reverse
  · intro S sm big
    obtain ⟨y,hy,rich⟩ := cycle_samples strict subV (fun z hz => (one z hz).le) sm big
    exact ⟨y,hy,rich,via_exists X hq hs (mem_sdiff.mp hy).1⟩

/-- The second hop, when needed, is always through an exterior shared head.
The first root can already be a shared head or can be a label on the old cycle. -/
theorem cover_head_in_two {q s} (X : Source q s) (hq : 2 ≤ q) (hs : 0 < s)
    {y w} (hy : y ∈ X.V) (hw : w ∈ outN X.D X.V y) :
    ∃ N, Via X y N ∧ (w ∈ N ∨
      (w ∉ N ∧ 2 ≤ (parents X.D N w).card ∧ ∃ K, Via X w K ∧ w ∈ K)) := by
  obtain ⟨p,hp,py,tight,ne,returns⟩ := fixed_parent X hq hs hy
  have build (v) (miss : v ∈ outN X.D X.V y \ outN X.D X.V p) :
      ∃ N, Via X y N ∧ Cycle X.D X.V q N ∧ p ∈ N ∧ y ∈ N ∧ v ∈ N := by
    have yv := mem_outN.mp (mem_sdiff.mp miss).1
    obtain ⟨N,C,pN,yN,vN⟩ := marked_cycle hq X.free hy yv.1 py yv.2 (returns v miss)
    exact ⟨N,⟨p,hp,py,tight,returns,v,miss,C,pN,yN,vN⟩,C,pN,yN,vN⟩
  by_cases pw : w ∈ outN X.D X.V p
  · obtain ⟨v,hv⟩ := ne
    obtain ⟨N,via,C,pN,yN,_⟩ := build v hv
    have distinct : p ≠ y := by
      rintro rfl
      exact loopfree X.free (by omega) hp py
    have rich : 1 < (parents X.D N w).card := one_lt_card.mpr
      ⟨p,mem_filter.mpr ⟨pN,(mem_outN.mp pw).2⟩,
       y,mem_filter.mpr ⟨yN,(mem_outN.mp hw).2⟩,distinct⟩
    exact ⟨N,via,Or.inr ⟨fun h => (C.incoming w h ▸ rich).false,rich,
      via_exists X hq hs (outN_subset hw)⟩⟩
  · obtain ⟨N,via,_,_,_,mem⟩ := build w (mem_sdiff.mpr ⟨hw,pw⟩)
    exact ⟨N,via,Or.inl mem⟩

def Step {q s} (X : Source q s) (M N : Finset ℕ) : Prop :=
  Cycle X.D X.V q M ∧ ∃ y ∈ X.V, (y ∈ M ∨ 2 ≤ (parents X.D M y).card) ∧ Via X y N

theorem via_cycle {q s} {X : Source q s} {y N} (h : Via X y N) : Cycle X.D X.V q N := by
  obtain ⟨_,_,_,_,_,_,_,C,_⟩ := h
  exact C

/-- Starting at any shortest cycle, the two rules reach cycles covering the entire least host. -/
theorem reachable_covers {q s} (X : Source q s) (hq : 2 ≤ q) (hs : 0 < s)
    {M} (C : Cycle X.D X.V q M) :
    ∀ z ∈ X.V, ∃ N, Relation.ReflTransGen (Step X) M N ∧ z ∈ N := by
  classical
  let U := X.V.filter (fun z => ∃ N, Relation.ReflTransGen (Step X) M N ∧ z ∈ N)
  have csub : M ⊆ U := fun z hz => mem_filter.mpr ⟨C.sub hz,M,.refl,hz⟩
  have nonempty : U.Nonempty := (card_pos.mp (show 0<M.card by have := C.size; omega)).mono csub
  have closed (y) (hy : y ∈ U) : outN X.D X.V y ⊆ U := by
    obtain ⟨hyV,A,path,yA⟩ := mem_filter.mp hy
    have CA : Cycle X.D X.V q A := by
      cases path with
      | refl => exact C
      | tail _ step => obtain ⟨_,_,_,_,v⟩ := step; exact via_cycle v
    intro w hw
    obtain ⟨N,via,either⟩ := cover_head_in_two X hq hs hyV hw
    have reached := path.tail (show Step X A N from ⟨CA,y,hyV,Or.inl yA,via⟩)
    apply mem_filter.mpr
    refine ⟨outN_subset hw,?_⟩
    rcases either with wN | ⟨_,rich,K,second,wK⟩
    · exact ⟨N,reached,wN⟩
    · exact ⟨K,reached.tail ⟨via_cycle via,w,outN_subset hw,Or.inr rich,second⟩,wK⟩
  have sub : U ⊆ X.V := filter_subset _ _
  have deg (y) (hy : y ∈ U) : s ≤ (outN X.D U y).card := by
    apply (X.degree y (sub hy)).trans
    apply card_le_card
    intro w hw
    exact mem_outN.mpr ⟨closed y hy hw,(mem_outN.mp hw).2⟩
  have eq := eq_of_subset_of_card_le sub (X.least X.D U (X.free.mono_set sub) deg nonempty)
  intro z hz
  exact (mem_filter.mp (show z ∈ U from eq.symm ▸ hz)).2

/-- A minimum-order source may be thinned first: all rows on every reachable cycle are tight. -/
theorem regular_source {q s} (X : Source q s) :
    ∃ Y : Source q s, Y.V = X.V ∧ OutEq s Y.D Y.V ∧
      ∀ a b, Y.D a b = true → X.D a b = true := by
  obtain ⟨F,sub,reg⟩ := exists_outEq X.degree
  exact ⟨⟨F,X.V,X.nonempty,qfree_sub sub X.free,fun v hv => (reg v hv).ge,X.least⟩,rfl,reg,sub⟩

/-- Every rich head has its entire row in the union of a family closed under
the shared-head rule alone. The option of restarting at an internal root
in Step is absent from the hypothesis. -/
theorem rich_row_inside {q s} (X : Source q s) (hq : 2 ≤ q) (hs : 0 < s)
    {F : Finset ℕ → Prop} {U : Finset ℕ} (inside : ∀ N, F N → N ⊆ U)
    (closed : ∀ A, F A → ∀ y ∈ X.V, 2 ≤ (parents X.D A y).card → ∀ N, Via X y N → F N)
    {M y} (mem : F M) (hy : y ∈ X.V) (rich : 2 ≤ (parents X.D M y).card) :
    outN X.D X.V y ⊆ U := by
  intro w hw
  obtain ⟨N,first,one | ⟨_,next,K,second,wK⟩⟩ := cover_head_in_two X hq hs hy hw
  · exact inside N (closed M mem y hy rich N first) one
  · exact inside K (closed N (closed M mem y hy rich N first) w (outN_subset hw) next K second) wK

/-- On a regular source this is an exact count. Only vertices whose whole
outgoing row is in U can carry a repeated parent from M. -/
theorem closed_family_count {q s} (X : Source q s) (hq : 2 ≤ q) (hs : 0 < s)
    (reg : OutEq s X.D X.V) {F : Finset ℕ → Prop} {U : Finset ℕ}
    (inside : ∀ N, F N → N ⊆ U)
    (closed : ∀ A, F A → ∀ y ∈ X.V, 2 ≤ (parents X.D A y).card → ∀ N, Via X y N → F N)
    {M} (mem : F M) (C : Cycle X.D X.V q M) :
    X.V.card + (∑ y ∈ X.V, if outN X.D X.V y ⊆ U then (parents X.D M y).card-1 else 0) =
      (q+1)*s + (X.V.filter (fun y => (parents X.D M y).card = 0)).card := by
  classical
  have total : (∑ y ∈ X.V, (parents X.D M y).card) = (q+1)*s := calc
    _ = ∑ y ∈ X.V, ∑ x ∈ M, if X.D x y = true then 1 else 0 := by simp [parents]
    _ = ∑ x ∈ M, ∑ y ∈ X.V, if X.D x y = true then 1 else 0 := sum_comm
    _ = ∑ x ∈ M, (outN X.D X.V x).card := by simp [outN]
    _ = _ := by rw [sum_congr rfl (fun x hx => reg x (C.sub hx))]; simp [C.size]
  have part (y) (hy : y ∈ X.V) :
      1 + (if outN X.D X.V y ⊆ U then (parents X.D M y).card-1 else 0) =
      (parents X.D M y).card + (if (parents X.D M y).card=0 then 1 else 0) := by
    by_cases h : (parents X.D M y).card=0
    · simp [h]
    by_cases inc : outN X.D X.V y ⊆ U
    · simp [h,inc]; omega
    · have low : ¬ 2 ≤ (parents X.D M y).card :=
        fun rich => inc (rich_row_inside X hq hs inside closed mem hy rich)
      simp [h,inc]; omega
  have eq := sum_congr (s₁ := X.V) rfl part
  simpa [sum_add_distrib,total] using eq

theorem from_candidate {q s D V} (free : QFree D V q) (degree : ∀ v∈V, s ≤ (outN D V v).card)
    (live : V.Nonempty) (hq : 2 ≤ q) (hs : 0 < s) :
    ∃ X : Source q s, X.V.card ≤ V.card ∧ OutEq s X.D X.V ∧
      ∃ M, Cycle X.D X.V q M ∧ ∀ z ∈ X.V, ∃ N, Relation.ReflTransGen (Step X) M N ∧ z ∈ N := by
  obtain ⟨S,order⟩ := exists_source free degree live
  obtain ⟨X,same,reg,_⟩ := regular_source S
  obtain ⟨y,hy⟩ := X.nonempty
  obtain ⟨M,via,_⟩ := via_exists X hq hs hy
  exact ⟨X,same ▸ order,reg,M,via_cycle via,reachable_covers X hq hs (via_cycle via)⟩

/-- Each repeated parent needs a distinct reachable label. Labels available
for payment are holes of M or exterior heads of the same chosen cycle root. -/
structure Payment {q s} (X : Source q s) (M : Finset ℕ) (x : ℕ) where
  labels : ℕ → Finset ℕ
  enough : ∀ y ∈ X.V, (parents X.D M y).card-1 ≤ (labels y).card
  separate : (X.V : Set ℕ).PairwiseDisjoint labels
  usable : ∀ y ∈ X.V, labels y ⊆ ball X.D X.V y (q-1) ∩
    ((X.V.filter fun z => (parents X.D M z).card=0) ∪ (outN X.D X.V x \ M))

/-- A single payment at one root of one cycle pays the whole critical deficit. -/
theorem order_of_payment {q s} (X : Source q s) (hq : 2 ≤ q) (hs : 0 < s)
    (reg : OutEq s X.D X.V) {M x} (C : Cycle X.D X.V q M) (hx : x ∈ M)
    (pay : Payment X M x) : q*s < X.V.card := by
  classical
  let holes := X.V.filter fun z => (parents X.D M z).card=0
  have count := closed_family_count X hq hs reg (F := Cycle X.D X.V q) (U := X.V)
    (fun _ c => c.sub) (fun _ _ _ _ _ _ v => via_cycle v) C C
  simp only [outN_subset,ite_true] at count
  change X.V.card + _ = (q+1)*s + holes.card at count
  have spent : (∑ y ∈ X.V, ((parents X.D M y).card-1)) ≤ holes.card + (outN X.D X.V x \ M).card := calc
    _ ≤ ∑ y ∈ X.V, (pay.labels y).card := sum_le_sum pay.enough
    _ = (X.V.biUnion pay.labels).card := (card_biUnion pay.separate).symm
    _ ≤ (holes ∪ (outN X.D X.V x \ M)).card := card_le_card (by
      intro w hw
      obtain ⟨y,hy,mem⟩ := mem_biUnion.mp hw
      exact (mem_inter.mp (pay.usable y hy mem)).2)
    _ ≤ _ := card_union_le _ _
  have one : outN X.D X.V x ∩ M = outN X.D M x := by
    ext z
    simp only [mem_inter,mem_outN]
    exact ⟨fun h => ⟨h.2,h.1.2⟩,fun h => ⟨⟨C.sub h.1,h.2⟩,h.1⟩⟩
  have split := card_sdiff_add_card_inter (outN X.D X.V x) M
  rw [one,C.heads x hx,reg x (C.sub hx)] at split
  rw [Nat.add_mul,Nat.one_mul] at count
  omega

#print axioms order_of_payment
#print axioms tight_cycle_samples
#print axioms closed_family_count
#print axioms from_candidate
#print axioms reachable_covers
#print axioms cover_head_in_two
#print axioms regular_source
#print axioms fixed_parent
#print axioms marked_cycle
#print axioms successors
end LeanCH.BR.ShenCycleSuccessor
