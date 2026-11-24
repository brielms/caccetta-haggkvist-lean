import checkpoints.shen_extension.MinimalCutReturns
import LeanCH.BR.BRSmallHighCycle

namespace LeanCH.BR.ShenReturnCut
open BRq2 BRq3 BR45 BRsGen
open Classical

/-- Missing entries in the outgoing row of the cut, indexed by actual exit labels. -/
def holes (D : CH.Digraph) (V K : Finset ℕ) (x : ℕ) :=
  (boundary D V K).filter (fun c => D x c ≠ true)

theorem row_pays_holes {D : CH.Digraph} {V K : Finset ℕ} {q s x}
    (M : Minimal D V K s) (hf : QFree D V q) (hq : 1≤q)
    (hm : ∀ w∈V,s≤(outN D V w).card) (hx : x∈K) :
    1+(holes D V K x).card≤(outN D K x).card := by
  let C := boundary D V K
  have cover : outN D V x ⊆ outN D K x ∪ outN D C x := by
    intro c hc
    by_cases h : c∈K
    · exact Finset.mem_union_left _ (mem_outN.mpr ⟨h,(mem_outN.mp hc).2⟩)
    · exact Finset.mem_union_right _ (mem_outN.mpr ⟨Finset.mem_sdiff.mpr
        ⟨Finset.mem_biUnion.mpr ⟨x,hx,hc⟩,h⟩,(mem_outN.mp hc).2⟩)
  have bound := (hm x (M.inside hx)).trans ((Finset.card_le_card cover).trans (Finset.card_union_le _ _))
  have part : (outN D C x).card+(holes D V K x).card=C.card := by
    apply Finset.card_filter_add_card_filter_not
  have size : C.card+1=s := boundary_size M hf hq hm
  omega

private theorem cyclic_row {D : CH.Digraph} {V K : Finset ℕ} {q s x}
    (M : Minimal D V K s) (hf : QFree D V q) (hq : 1≤q)
    (hm : ∀ w∈V,s≤(outN D V w).card) (hx : x∈K) :
    ∃ j,0<j ∧ Walk D K x x j := by
  obtain ⟨y,hy,yx⟩ := predecessor hf hq hm M hx
  have reach : y∈ball D K x (K.card-1) := by rw [internal_reach M hx]; exact hy
  obtain ⟨_,j,_,walk⟩ := mem_ball.mp reach
  exact ⟨j+1,by omega,walk.snoc hx yx⟩

/-- Use the cutoff inside K, which can exceed the ambient cutoff. For a cut
with p+1+t vertices and no internal return through p, at most 2t rows
miss an exit, each by at most t, throughout the range |K| ≤ 2p. -/
theorem sparse_exit_rows {D : CH.Digraph} {V K : Finset ℕ} {q p s t}
    (M : Minimal D V K s) (hf : QFree D V q) (hq : 1≤q)
    (hm : ∀ w∈V,s≤(outN D V w).card) (hp : 1≤p) (inner : QFree D K p)
    (size : K.card=p+1+t) (small : K.card≤2*p) :
    let E := K.filter (fun x => (holes D V K x).Nonempty)
    E.card≤2*t ∧ (∀ x∈K,(holes D V K x).card≤t) ∧
      (∑ x∈K,(holes D V K x).card)≤2*t*t := by
  intro E
  have pay := fun x hx => row_pays_holes M hf hq hm (x:=x) hx
  have deg (x) (hx : x∈K) : 1≤(outN D K x).card := by have := pay x hx; omega
  have high (x) (hx : x∈E) : 2≤(outN D K x).card := by
    obtain ⟨xK,nonempty⟩ := Finset.mem_filter.mp hx
    have := Finset.card_pos.mpr nonempty
    have := pay x xK
    omega
  have eK : E⊆K := Finset.filter_subset _ _
  have many := small_one_core_high_count hp inner deg M.nonempty small eK high
  have ne : E.card≤2*t := by omega
  have per (x) (hx : x∈K) : (holes D V K x).card≤t := by
    obtain ⟨j,jp,walk⟩ := cyclic_row M hf hq hm hx
    have := cyclic_row_degree_cap hp inner jp walk
    have := pay x hx
    omega
  refine ⟨ne,per,?_⟩
  have sum := Finset.sum_le_sum (fun x (hx : x∈E) => per x (eK hx))
  rw [Finset.sum_const_nat (fun _ _ => rfl)] at sum
  have zero : (∑ x∈K \ E,(holes D V K x).card)=0 := by
    apply Finset.sum_eq_zero
    intro x hx
    obtain ⟨xK,outside⟩ := Finset.mem_sdiff.mp hx
    exact Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp
      (fun h => outside (Finset.mem_filter.mpr ⟨xK,h⟩)))
  have split := Finset.sum_sdiff eK (f:=fun x => (holes D V K x).card)
  have := Nat.mul_le_mul_right t ne
  omega

/-- Every verified degree-d ball bound prices the same missing arc table,
with at most d-1 charges per row. -/
theorem clipped_exit_budget {D : CH.Digraph} {V K : Finset ℕ} {q p s d}
    (M : Minimal D V K s) (hf : QFree D V q) (hq : 1≤q)
    (hm : ∀ w∈V,s≤(outN D V w).card) (hp : 1≤p) (inner : QFree D K p)
    (hb : Ball p d) (small : K.card≤p*d) (hd : 1≤d) :
    p*d+2+(∑ x∈K,min (d-1) (holes D V K x).card)≤K.card*d := by
  have pay := fun x hx => row_pays_holes M hf hq hm (x:=x) hx
  have deg (x) (hx : x∈K) : 1≤(outN D K x).card := by have := pay x hx; omega
  have bound := deficiency_strict_of_order_le hp hb inner deg M.nonempty small
  have one (x) (hx : x∈K) : d-(outN D K x).card+min (d-1) (holes D V K x).card≤d-1 := by
    have := pay x hx; omega
  have sum := Finset.sum_le_sum one
  rw [Finset.sum_add_distrib,Finset.sum_const_nat (fun _ _ => rfl)] at sum
  have eq := congrArg (fun k : ℕ => K.card*k) (show d-1+1=d by omega)
  simp only [Nat.mul_add,Nat.mul_one] at eq
  omega

#print axioms sparse_exit_rows
#print axioms clipped_exit_budget

/-- A set of boundary labels with paths to the same root forces an entire
rectangle of absent arcs. Each of its rows has |Z|+1 internal successors.
While their growing ball is acyclic, a sink supplies that many new labels. -/
theorem return_rectangle {D : CH.Digraph} {V K Z : Finset ℕ} {q p s x r k}
    (M : Minimal D V K s) (hf : QFree D V q) (hq : 1≤q)
    (hm : ∀ w∈V,s≤(outN D V w).card) (inner : QFree D K p)
    (zc : Z⊆boundary D V K) (hx : x∈K)
    (back : ∀ c∈Z,∃ j≤r,Walk D V c x j) (room : r+k+1≤q) :
    let B := ball D K x k
    (∀ y∈B,Z⊆holes D V K y) ∧ min (p+1) (1+(Z.card+1)*k)≤B.card := by
  intro B
  have avoid (i) (hi : i≤k) (y) (hy : y∈ball D K x i) : Z⊆holes D V K y := by
    intro c hc
    refine Finset.mem_filter.mpr ⟨zc hc,?_⟩
    intro yc
    obtain ⟨j,hj,cx⟩ := back c hc
    obtain ⟨_,l,hl,xy⟩ := mem_ball.mp hy
    obtain ⟨w,_,entry⟩ := Finset.mem_biUnion.mp (Finset.mem_sdiff.mp (zc hc)).1
    exact hf c _ (by omega : 1≤j+l+1) (by omega) ((cx.append (xy.mono M.inside)).snoc (mem_outN.mp entry).1 yc)
  refine ⟨avoid k le_rfl,?_⟩
  have grow (i) (hi : i≤k) : min (p+1) (1+(Z.card+1)*i)≤(ball D K x i).card := by
    induction i with
    | zero => simpa using (show min (p+1) 1≤(ball D K x 0).card from
        (min_le_right _ _).trans (Finset.card_pos.mpr ⟨x,self_mem_ball hx⟩))
    | succ i ih =>
      let P := ball D K x i
      have inc : P⊆ball D K x (i+1) := ball_mono_radius (by omega)
      by_cases large : p<P.card
      · exact (min_le_left _ _).trans ((show p+1≤P.card by omega).trans (Finset.card_le_card inc))
      obtain ⟨y,hy,sink⟩ := exists_sink (inner.mono_set (ball_subset : P⊆K)) ⟨x,self_mem_ball hx⟩ (by omega : P.card≤p)
      have fresh : outN D K y ⊆ ball D K x (i+1) \ P := by
        intro z hz
        obtain ⟨zK,yz⟩ := mem_outN.mp hz
        exact Finset.mem_sdiff.mpr ⟨ball_step hy zK yz,fun zP => sink z zP yz⟩
      have pay := row_pays_holes M hf hq hm (ball_subset hy)
      have nZ := Finset.card_le_card (avoid i (by omega) y hy)
      have addition := Finset.card_sdiff_add_card_eq_card inc
      have next := Finset.card_le_card fresh
      have prev : min (p+1) (1+(Z.card+1)*i)≤P.card := ih (by omega)
      rw [Nat.mul_succ]
      omega
  exact grow k le_rfl

/-- Different columns may return to different roots, with different lengths.
The same missing incidence pays only once in the sum across columns. -/
theorem return_ledger {D : CH.Digraph} {V K Z : Finset ℕ} {q p s}
    (M : Minimal D V K s) (hf : QFree D V q) (hq : 1≤q)
    (hm : ∀ w∈V,s≤(outN D V w).card) (inner : QFree D K p)
    (zc : Z⊆boundary D V K) (root radius depth : ℕ → ℕ)
    (roots : ∀ c∈Z,root c∈K) (back : ∀ c∈Z,∃ j≤radius c,Walk D V c (root c) j)
    (room : ∀ c∈Z,radius c+depth c+1≤q) :
    (∑ c∈Z,min (p+1) (1+2*depth c))≤∑ x∈K,min Z.card (holes D V K x).card := by
  let F := fun c => K.filter (fun x => c∈holes D V K x)
  have one (c) (hc : c∈Z) : min (p+1) (1+2*depth c)≤(F c).card := by
    have pair := return_rectangle (Z:={c}) M hf hq hm inner (Finset.singleton_subset_iff.mpr (zc hc))
      (roots c hc) (fun w hw => (Finset.mem_singleton.mp hw) ▸ back c hc) (room c hc)
    have sub : ball D K (root c) (depth c)⊆F c := by
      intro x hx
      exact Finset.mem_filter.mpr ⟨ball_subset hx,pair.1 x hx (Finset.mem_singleton_self _)⟩
    simpa using pair.2.trans (Finset.card_le_card sub)
  have byRow (x : ℕ) : (Z.filter (fun c => c∈holes D V K x)).card≤min Z.card (holes D V K x).card :=
    le_min (Finset.card_le_card (Finset.filter_subset _ _))
      (Finset.card_le_card (fun _ h => (Finset.mem_filter.mp h).2))
  have equal : (∑ c∈Z,(F c).card)=∑ x∈K,(Z.filter (fun c => c∈holes D V K x)).card := by
    simp only [F,Finset.card_filter]
    exact Finset.sum_comm
  exact (Finset.sum_le_sum one).trans (equal ▸ Finset.sum_le_sum (fun x _ => byRow x))

#print axioms return_rectangle
#print axioms return_ledger

/-- The full rows see the very same external columns. At a cutoff p with
|K| ≤ 2p there are at least 2p+2-|K| such rows. -/
theorem full_exit_rectangle {D : CH.Digraph} {V K : Finset ℕ} {q p s}
    (M : Minimal D V K s) (hf : QFree D V q) (hq : 1≤q)
    (hm : ∀ w∈V,s≤(outN D V w).card) (hp : 1≤p) (inner : QFree D K p)
    (small : K.card≤2*p) :
    ∃ F⊆K,2*p+2≤K.card+F.card ∧ ∀ x∈F,∀ c∈boundary D V K,D x c=true := by
  let E := K.filter (fun x => (holes D V K x).Nonempty)
  have eK : E⊆K := Finset.filter_subset _ _
  have high (x) (hx : x∈E) : 2≤(outN D K x).card := by
    obtain ⟨xK,nonempty⟩ := Finset.mem_filter.mp hx
    have := Finset.card_pos.mpr nonempty
    have := row_pays_holes M hf hq hm xK
    omega
  have count := small_one_core_high_count hp inner (fun x hx => by
    have := row_pays_holes M hf hq hm hx; omega) M.nonempty small eK high
  have split := Finset.card_sdiff_add_card_eq_card eK
  refine ⟨K \ E,Finset.sdiff_subset,by omega,?_⟩
  intro x hx c hc
  obtain ⟨xK,outside⟩ := Finset.mem_sdiff.mp hx
  by_contra missed
  exact outside (Finset.mem_filter.mpr ⟨xK,⟨c,Finset.mem_filter.mpr ⟨hc,missed⟩⟩⟩)

/-- A cut either has two distinct rows paying every external column or
contains a closed walk through half its order (rounded up). -/
theorem cut_alternative {D : CH.Digraph} {V K : Finset ℕ} {q s}
    (M : Minimal D V K s) (hf : QFree D V q) (hq : 1≤q)
    (hm : ∀ w∈V,s≤(outN D V w).card) :
    (∃ x∈K,∃ y∈K,x≠y ∧ boundary D V K ⊆ ShenSharedHead.commonOut D V x y) ∨
      (2*q<K.card ∧ ¬QFree D K ((K.card+1)/2)) := by
  let p := max q ((K.card+1)/2)
  by_cases inner : QFree D K p
  · left
    have small : K.card≤2*p := by dsimp only [p]; omega
    obtain ⟨F,fK,count,all⟩ := full_exit_rectangle M hf hq hm (p:=p)
      (by dsimp only [p]; omega) inner small
    obtain ⟨x,hx,y,hy,diff⟩ := Finset.one_lt_card.mp (by omega : 1<F.card)
    refine ⟨x,fK hx,y,fK hy,diff,?_⟩
    intro c hc
    obtain ⟨_,_,arc⟩ := Finset.mem_biUnion.mp (Finset.mem_sdiff.mp hc).1
    have cV := (mem_outN.mp arc).1
    exact Finset.mem_inter.mpr ⟨mem_outN.mpr ⟨cV,all x hx c hc⟩,mem_outN.mpr ⟨cV,all y hy c hc⟩⟩
  · right
    have localFree := hf.mono_set M.inside
    have below : q<(K.card+1)/2 := by
      by_contra! le
      exact inner (by simpa [p,max_eq_left le] using localFree)
    exact ⟨by omega,by simpa [p,max_eq_right below.le] using inner⟩

/-- A sufficient condition on each punctured half-ball of the input graph.
Acyclic carriers are allowed directly. For a cyclic carrier with low pair
codegrees it suffices to exclude cycles through half its order, rounded up. -/
theorem cycle_of_half_ball_rectangles {D : CH.Digraph} {q s n : ℕ} (hq : 2≤q) (hn : 0<n)
    (ord : n≤q*s) (hl : CH.Loopless D n) (hm : CH.MinOutdegreeAtLeast D n s)
    (localTest : ∀ u∈Finset.range n, let V := Finset.range n
      let S := (ball D V u ((q-1)/2)).erase u
      QFree D S S.card ∨ ((S.card≤2*q ∨ QFree D S ((S.card+1)/2)) ∧
        ∀ x∈S,∀ y∈S,x≠y → (ShenSharedHead.commonOut D V x y).card+1<s)) :
    CH.HasDirectedCycleAtMost D n q := by
  by_contra no
  have free := qfree_of_noShort hl no
  have degree (x) (hx : x∈Finset.range n) := Compose.FloorSix.out_card hm (Finset.mem_range.mp hx)
  obtain ⟨u,hu,k,rad,K,sub,M⟩ := half_ball_cut free hq degree ⟨0,Finset.mem_range.mpr hn⟩ (by simpa using ord)
  let S := (ball D (Finset.range n) u ((q-1)/2)).erase u
  have ks : K⊆S := by
    intro y hy
    obtain ⟨diff,h⟩ := Finset.mem_erase.mp (sub hy)
    exact Finset.mem_erase.mpr ⟨diff,ball_mono_radius (by omega : k≤(q-1)/2) h⟩
  have size := Finset.card_le_card ks
  rcases localTest u hu with acyclic | ⟨width,pairs⟩
  · have f := (acyclic.mono_set ks).mono_bound size
    obtain ⟨x,hx,sink⟩ := exists_sink f M.nonempty le_rfl
    have high := row_pays_holes M free (by omega) degree hx
    obtain ⟨y,hy⟩ := Finset.card_pos.mp (by omega : 0<(outN D K x).card)
    exact sink y (mem_outN.mp hy).1 (mem_outN.mp hy).2
  · rcases cut_alternative M free (by omega) degree with ⟨x,hx,y,hy,ne,shared⟩|⟨large,cycle⟩
    · have := pairs x (ks hx) y (ks hy) ne
      have := Finset.card_le_card shared
      have := boundary_size M free (by omega) degree
      omega
    · rcases width with small|freeHalf
      · change S.card≤2*q at small
        omega
      · exact cycle ((freeHalf.mono_set ks).mono_bound (by change (K.card+1)/2≤(S.card+1)/2; omega))

#print axioms full_exit_rectangle
#print axioms cut_alternative
#print axioms cycle_of_half_ball_rectangles

/-- Sum over a shortest internal cycle. Each absent boundary incidence at a
cycle vertex can pay for only its incoming and outgoing cycle arcs. -/
theorem cycle_transfer {D : CH.Digraph} {V K : Finset ℕ} {q s b}
    (M : Minimal D V K s) (hf : QFree D V q) (hq : 1≤q)
    (hm : ∀ w∈V,s≤(outN D V w).card)
    (cap : ∀ x∈K,∀ y∈outN D K x,(ShenSharedHead.commonOut D V x y).card≤b) :
    (q+1)*((s-1)-b)≤2*∑ x∈K,(holes D V K x).card := by
  let miss := fun x => (holes D V K x).card
  let h := (s-1)-b
  have one (x) (hx : x∈K) (y) (hy : y∈outN D K x) : h≤miss x+miss y := by
    have cover : boundary D V K ⊆ ShenSharedHead.commonOut D V x y ∪ (holes D V K x ∪ holes D V K y) := by
      intro c hc
      obtain ⟨_,_,edge⟩ := Finset.mem_biUnion.mp (Finset.mem_sdiff.mp hc).1
      have cV := (mem_outN.mp edge).1
      by_cases xc : D x c=true
      · by_cases yc : D y c=true
        · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨mem_outN.mpr ⟨cV,xc⟩,mem_outN.mpr ⟨cV,yc⟩⟩)
        · exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hc,yc⟩))
      · exact Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hc,xc⟩))
    have count := (Finset.card_le_card cover).trans (Finset.card_union_le _ _)
    have joined := Finset.card_union_le (holes D V K x) (holes D V K y)
    have width := cap x hx y hy
    have exits := boundary_size M hf hq hm
    dsimp only [miss,h]; omega
  have positive (x) (hx : x∈K) : 1≤(outN D K x).card := by
    have := row_pays_holes M hf hq hm hx; omega
  obtain ⟨p,L,pq,free,lk,length,reg⟩ := exists_minimal_cycle_support hq (hf.mono_set M.inside) positive M.nonempty
  have incoming := (dt_reg (by omega : 1≤p) (ball_q_one p (by omega)) (free.mono_set lk)
    (fun x hx => (reg x hx).ge) (by simpa using length)).2
  have row := Finset.sum_le_sum (fun x (hx : x∈L) => Finset.sum_le_sum
    (fun y (hy : y∈outN D L x) => one x (lk hx) y (outN_mono lk x hy)))
  have counts : ShenSharedHead.edges D L (fun _ _ => h) ≤ ShenSharedHead.edges D L (fun x _ => miss x) +
      ShenSharedHead.edges D L (fun _ y => miss y) := by
    simpa only [ShenSharedHead.edges,Finset.sum_add_distrib] using row
  have tails : ShenSharedHead.edges D L (fun x _ => miss x)=∑ x∈L,miss x := by
    unfold ShenSharedHead.edges
    apply Finset.sum_congr rfl
    intro x hx; simp [reg x hx]
  have heads : ShenSharedHead.edges D L (fun _ y => miss y)=∑ y∈L,miss y := by
    rw [ShenSharedHead.transpose]
    apply Finset.sum_congr rfl
    intro y hy; simp [incoming y hy]
  rw [ShenSharedHead.edges_const reg,tails,heads,Nat.mul_one] at counts
  have long := Nat.mul_le_mul_right h (show q+1≤L.card by omega)
  have total := Finset.sum_le_sum_of_subset_of_nonneg (f:=miss) lk (fun _ _ _ => Nat.zero_le _)
  change (q+1)*h≤2*∑ x∈K,miss x
  omega

/-- A triangle follows from a uniform bound on the common successors of
actual arcs. The deficient bank is obtained after trimming to exact degree;
the large bank found inside it persists in the original graph. -/
theorem triangle_of_arc_cap {D : CH.Digraph} {n s b : ℕ} (hn : 0<n) (hs : 0<s)
    (ord : n≤3*s) (hl : CH.Loopless D n) (hm : CH.MinOutdegreeAtLeast D n s)
    (small : b≤6) (price : (b-4)*(b-4)+b+1<s)
    (cap : ∀ u∈Finset.range n,∀ v∈outN D (Finset.range n) u,
      (ShenSharedHead.commonOut D (Finset.range n) u v).card≤b) : CH.HasDirectedCycleAtMost D n 3 := by
  by_contra no
  let V := Finset.range n
  have degree (x) (hx : x∈V) := Compose.FloorSix.out_card hm (Finset.mem_range.mp hx)
  obtain ⟨F,sub,reg⟩ := exists_outEq degree
  have free := qfree_sub sub (qfree_of_noShort hl no)
  have lift {U : Finset ℕ} {x} : outN F U x⊆outN D U x :=
    fun _ hy => mem_outN.mpr ⟨(mem_outN.mp hy).1,sub _ _ (mem_outN.mp hy).2⟩
  have bound (u) (hu : u∈V) (v) (hv : v∈outN F V u) : (ShenSharedHead.commonOut F V u v).card≤b :=
    (Finset.card_le_card (Finset.inter_subset_inter lift lift)).trans (cap u hu v (lift hv))
  obtain ⟨u,hu,v,hv,K,bank,M⟩ := common_head_cut free reg ⟨0,Finset.mem_range.mpr hn⟩ hs (by simpa [V] using ord)
  have wide := (Finset.card_le_card bank).trans (bound u hu v hv)
  have minF := fun x (hx : x∈V) => (reg x hx).ge
  obtain ⟨x,hx⟩ := M.nonempty
  have low := missing_exits M free (by decide) minF hx
  let t := K.card-4
  have size : K.card=3+1+t := by dsimp [t]; omega
  have total := (sparse_exit_rows M free (by decide) minF (by decide : 1≤3)
    (free.mono_set M.inside) size (by omega)).2.2
  have bill := cycle_transfer M free (by decide) minF (fun x hx y hy =>
    bound x (M.inside hx) y (outN_mono M.inside x hy))
  have tt := Nat.mul_self_le_mul_self (show t≤b-4 by omega)
  nlinarith only [bill,total,tt,price,Nat.sub_add_cancel (show b≤s-1 by omega),
    Nat.sub_add_cancel (show 1≤s by omega)]

#print axioms cycle_transfer
#print axioms triangle_of_arc_cap

end LeanCH.BR.ShenReturnCut
