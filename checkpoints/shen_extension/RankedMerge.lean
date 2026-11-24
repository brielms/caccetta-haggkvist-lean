import checkpoints.shen_extension.ForwardMerge

namespace LeanCH.BR.Closure.RankedMerge
open Finset BRq2 BRq3 BR45 WeightedSD ShortestCycleWeights

/-- A retained native arc can lower the assigned level by at most one. -/
def retained (D : CH.Digraph) (level : ℕ → ℕ) : CH.Digraph :=
  fun i j => D i j && decide (level i ≤ level j + 1)

private theorem along {D level U i j k} (p : Walk (retained D level) U i j k) :
    level i ≤ level j + k := by
  induction p with
  | refl => omega
  | step _ e _ ih =>
    have := of_decide_eq_true (Bool.and_eq_true_iff.mp e).2
    omega

def bottom (U : Finset ℕ) (level : ℕ → ℕ) := U.filter (fun i => level i = 0)
def top (q : ℕ) (U : Finset ℕ) (level : ℕ → ℕ) := U.filter (fun i => q-1 ≤ level i)

/-- The two boundary layers are attached to opposite sides of the new vertex. -/
theorem safe {q D U b} (hq : 2≤q) (free : QFree D U q) (bu : b∉U) (level : ℕ → ℕ) :
    QFree (coreTwoSidedExtension (retained D level) U (bottom U level) (top q U level) b)
      (insert b U) q := by
  apply coreTwoSidedExtension_qfree bu (filter_subset _ _) (qfree_sub
    (fun i j (e : retained D level i j=true) => (Bool.and_eq_true_iff.mp e).1) free)
  intro o ho i hi k hk path
  have a := (mem_filter.mp ho).2
  have z := (mem_filter.mp hi).2
  have d := along path
  change q-1 ≤ level o at a
  change level i = 0 at z
  omega

theorem contacts_balance {q n E U B H} (hq : 2≤q) (free : QFree E U q) (small : SmallerSmallRow q n)
    (room : U.card+1<n) (bs : B⊆U) (hs : H⊆U)
    (blocked : ∀h∈H,∀i∈B,∀k,k≤q-2 → ¬Walk E U h i k)
    (w : ℕ → ℚ) (pos : ∀i∈U,0<w i) (t : ℚ) (tp : 0<t)
    (heads : mass U w ≤ q*mass H w)
    (rows : ∀i∈U,mass U w+t ≤ WeightedSD.row q E U w i + q*(if i∈B then t else 0)) :
    q*mass H w = mass U w ∧ ∀i∈U,WeightedSD.row q E U w i +
      q*(if i∈B then t else 0) = mass U w+t := by
  classical
  obtain ⟨b,bu⟩ := Infinite.exists_notMem_finset U
  let K := coreTwoSidedExtension E U B H b
  let z (i : ℕ) := if i=b then t else w i
  have zi {i} (iu : i∈U) : z i=w i := by simp [z,show i≠b from fun eq => bu (eq ▸ iu)]
  have zb : z b=t := by simp [z]
  have zm : mass (insert b U) z=t+mass U w := by
    rw [mass,sum_insert bu,zb,sum_congr rfl (fun i iu => zi iu)]; rfl
  have old {i j} (iu : i∈U) (ju : j∈U) : K i j=E i j := by
    have ib : i≠b := fun eq => bu (eq ▸ iu)
    have jb : j≠b := fun eq => bu (eq ▸ ju)
    simp [K,coreTwoSidedExtension,coreOutgoingExtension,iu,ju,ib,jb]
  have score (i) (iu : i∈U) : WeightedSD.row q K (insert b U) z i =
      WeightedSD.row q E U w i + q*(if i∈B then t else 0) := by
    have visit : K i b=true ↔ i∈B := by
      simp [K,coreTwoSidedExtension,coreOutgoingExtension,bu]
    simp only [WeightedSD.row,outW,sum_insert bu,zi iu,zb,visit]
    rw [sum_congr rfl (fun j ju => by rw [old iu ju,zi ju])]
    ring
  have bridge : WeightedSD.row q K (insert b U) z b=t+q*mass H w := by
    have bb : K b b=false := by simp [K,coreTwoSidedExtension,coreOutgoingExtension,bu,show b∉B from fun hb => bu (bs hb)]
    have arc (j) (ju : j∈U) : K b j=true ↔ j∈H := by
      have jb : j≠b := fun eq => bu (eq ▸ ju)
      simp [K,coreTwoSidedExtension,coreOutgoingExtension,bu,ju,jb]
    simp only [WeightedSD.row,zb,outW,sum_insert bu,bb,Bool.false_eq_true,ite_false,zero_add]
    congr 2
    calc
      _ = ∑j∈U, if j∈H then w j else 0 := sum_congr rfl (fun j ju => by rw [zi ju,if_congr (arc j ju) rfl rfl])
      _ = mass H w := by rw [← sum_filter]; congr 1; ext j; simp; exact fun jh => hs jh
  have weak (i) (iv : i∈insert b U) : mass (insert b U) z≤WeightedSD.row q K (insert b U) z i := by
    rw [zm]
    rcases mem_insert.mp iv with rfl|iu
    · rw [bridge]; exact add_le_add_right heads _
    · rw [score i iu,add_comm t]; exact rows i iu
  have positive (i) (iv : i∈insert b U) : 0<z i := by
    rcases mem_insert.mp iv with rfl|iu
    · rwa [zb]
    · rw [zi iu]; exact pos i iu
  have eq := positive_feasible_rows_tight_of_smallRow hq
    (small K _ (by simpa [bu] using room) (coreTwoSidedExtension_qfree bu bs free blocked)) z positive weak
  constructor
  · have e := eq b (mem_insert_self _ _)
    rw [bridge,zm] at e
    exact add_left_cancel e
  · intro i iu
    simpa only [score i iu,zm,add_comm t (mass U w)] using eq i (mem_insert_of_mem iu)

/-- Local test at an independently chosen bridge weight. At the weak boundary
    the entire labelled table must balance, including the bridge. -/
theorem balance {q n D U} (hq : 2≤q) (free : QFree D U q) (small : SmallerSmallRow q n)
    (room : U.card+1<n) (level : ℕ → ℕ) (w : ℕ → ℚ) (pos : ∀i∈U,0<w i)
    (t : ℚ) (tp : 0<t)
    (heads : mass U w ≤ q*mass (top q U level) w)
    (rows : ∀i∈U,mass U w+t ≤ WeightedSD.row q (retained D level) U w i +
      q*(if level i=0 then t else 0)) :
    q*mass (top q U level) w = mass U w ∧
    ∀i∈U,WeightedSD.row q (retained D level) U w i +
      q*(if level i=0 then t else 0) = mass U w+t := by
  have eq := contacts_balance hq (qfree_sub
    (fun i j (e : retained D level i j=true) => (Bool.and_eq_true_iff.mp e).1) free) small room
    (B:=bottom U level) (H:=top q U level) (filter_subset _ _) (filter_subset _ _) (by
      intro o ho i hi k hk path
      have a := (mem_filter.mp ho).2
      have z := (mem_filter.mp hi).2
      have d := along path
      change q-1 ≤ level o at a
      change level i = 0 at z
      omega) w pos t tp heads (fun i iu => by simpa [bottom,iu] using rows i iu)
  exact ⟨eq.1, fun i iu => by simpa [bottom,iu] using eq.2 i iu⟩

/-- A heavy set of heads forces an actual low row within q−2 steps, or
    two rows on opposite sides whose combined capacity is too small.
    No ambient weight or strictness on the whole source is assumed. -/
theorem pair_obstruction {q n D U H} (hq : 2≤q) (free : QFree D U q) (small : SmallerSmallRow q n)
    (room : U.card+1<n) (hs : H⊆U) (live : H.Nonempty) (w : ℕ → ℚ) (pos : ∀i∈U,0<w i)
    (heavy : mass U w < q*mass H w) :
    let R := BRsub.ballSet D U H (q-2)
    ∃i∈R,(∀j∈R,WeightedSD.row q D U w i≤WeightedSD.row q D U w j) ∧
      (WeightedSD.row q D U w i ≤ mass U w ∨ ∃j∈U\R,
        (q-1:ℚ)*(WeightedSD.row q D U w i-mass U w)+WeightedSD.row q D U w j < mass U w) := by
  classical
  intro R
  obtain ⟨h,hh⟩ := live
  have rr : R.Nonempty := ⟨h,BRsub.mem_ballSet.mpr ⟨h,hh,mem_ball.mpr ⟨hs hh,0,Nat.zero_le _,.refl _⟩⟩⟩
  obtain ⟨i,ir,least⟩ := R.exists_min_image (WeightedSD.row q D U w) rr
  refine ⟨i,ir,least,?_⟩
  by_contra! fail
  let t := WeightedSD.row q D U w i-mass U w
  have tp : 0<t := sub_pos.mpr fail.1
  have bound := contacts_balance hq free small room (B:=U\R) sdiff_subset hs (by
    intro a ha j jb k hk p
    exact (mem_sdiff.mp jb).2 (BRsub.mem_ballSet.mpr ⟨a,ha,mem_ball.mpr ⟨(mem_sdiff.mp jb).1,k,hk,p⟩⟩)) w pos t tp heavy.le (by
    intro j ju
    by_cases jr : j∈R
    · simp only [mem_sdiff,ju,jr,not_true_eq_false,and_false,ite_false,mul_zero,add_zero]
      dsimp [t]
      linarith [least j jr]
    · have jb : j∈U\R := mem_sdiff.mpr ⟨ju,jr⟩
      simp only [jb,ite_true]
      have short := fail.2 j jb
      change mass U w ≤ ((q:ℚ)-1)*t+WeightedSD.row q D U w j at short
      linarith only [short, show ((q:ℚ)-1)*t=(q:ℚ)*t-t by ring])
  exact heavy.ne' bound.1

/-- A directly checkable alternative in the capstone. The weights are
    supported entirely on the retained vertices. -/
def PairPays (q : ℕ) (D : CH.Digraph) (V : Finset ℕ) : Prop :=
  ∃ U⊆V, U.card+1<V.card ∧ ∃E : CH.Digraph,
    (∀i j,E i j=true → D i j=true) ∧ ∃H⊆U,H.Nonempty ∧ ∃w : ℕ→ℚ,
    (∀i∈U,0<w i) ∧ mass U w<q*mass H w ∧
    ∀i∈BRsub.ballSet E U H (q-2),mass U w<WeightedSD.row q E U w i ∧
      ∀j∈U\BRsub.ballSet E U H (q-2),
        mass U w≤(q-1:ℚ)*(WeightedSD.row q E U w i-mass U w)+WeightedSD.row q E U w j

theorem no_pair {q D V} (hq : 2≤q) (free : QFree D V q) (small : SmallerSmallRow q V.card) :
    ¬PairPays q D V := by
  rintro ⟨U,us,room,E,sub,H,hs,live,w,pos,heavy,ok⟩
  obtain ⟨i,ir,_,low⟩ := pair_obstruction hq (qfree_sub sub (free.mono_set us)) small room hs live w pos heavy
  rcases low with short|⟨j,jb,short⟩
  · exact (ok i ir).1.not_ge short
  · exact short.not_ge ((ok i ir).2 j jb)

/-- On a native arc b → a the minimizing inner row is a parent of b at
    the exact last possible distance. If its surplus is large, a second
    row must lie outside the entire ball and jointly overspend the budget. -/
theorem arc_pair {q D V} (hq : 2≤q) (free : QFree D V q) (small : SmallerSmallRow q V.card)
    (w : ℕ→ℚ) (pos : ∀i∈V,0<w i) {b a : V}
    (strict : ∀i∈V,i≠b.val → mass V w<WeightedSD.row q D V w i) (ba : D b a=true) :
    let U := (V.erase a.val).erase b.val
    let H := outN D U a
    let R := BRsub.ballSet D U H (q-2)
    ∃i∈R,D i b=true ∧ D i a=false ∧ (∃h∈H,Walk D U h i (q-2)) ∧
      (∀k∈R,WeightedSD.row q D U w i≤WeightedSD.row q D U w k) ∧
      (ForwardMerge.surplus q D V w i+w a ≤ ((q:ℚ)-1)*w b ∨ ∃j∈U\R,
        ((q:ℚ)-1)*ForwardMerge.surplus q D V w i+ForwardMerge.surplus q D V w j <
          (q:ℚ)*(((q:ℚ)-2)*w b+(if D j b=true then w b else 0)-
            (if D j a=true then 0 else w a))) := by
  classical
  intro U H R
  have diff : b.val≠a.val := fun eq => loopfree free (by omega) a.property (eq ▸ ba)
  have bu : b.val∈V.erase a.val := mem_erase.mpr ⟨diff,b.property⟩
  have ca := card_erase_add_one a.property
  have cb := card_erase_add_one bu
  have us : U⊆V := (erase_subset _ _).trans (erase_subset _ _)
  have total (f : ℕ→ℚ) : (∑i∈V,f i)=(∑i∈U,f i)+f b+f a := by
    rw [sum_erase_add _ _ bu,sum_erase_add _ _ a.property]
  have wm : mass V w=mass U w+w b+w a := total w
  have split (i) : WeightedSD.row q D V w i=WeightedSD.row q D U w i+
      q*((if D i b=true then w b else 0)+(if D i a=true then w a else 0)) := by
    unfold WeightedSD.row outW
    rw [total]
    ring
  have aa : D a a=false := Bool.eq_false_iff.mpr (loopfree free (by omega) a.property)
  have ab : D a b=false := Bool.eq_false_iff.mpr (fun ed =>
    free b 2 (by decide) hq (.step a.property ba (.step b.property ed (.refl _))))
  have pa := pos a a.property
  have pb := pos b b.property
  have heavy : mass U w < q*mass H w := by
    have e := strict a a.property diff.symm
    rw [wm,split a] at e
    simp only [aa,ab,Bool.false_eq_true,ite_false,add_zero,mul_zero,WeightedSD.row,outW_eq_mass] at e
    dsimp [H]; linarith
  have live : H.Nonempty := by
    by_contra! empty
    rw [empty,show mass ∅ w=0 by simp [mass],mul_zero] at heavy
    exact heavy.not_ge (mass_nonneg (fun i iu => (pos i (us iu)).le))
  obtain ⟨i,ir,least,short⟩ := pair_obstruction hq (free.mono_set us) small
    (show U.card+1<V.card by dsimp [U]; omega) outN_subset live w (fun j ju => pos j (us ju)) heavy
  obtain ⟨h,hh,reach⟩ := BRsub.mem_ballSet.mp ir
  obtain ⟨iu,k,hk,p⟩ := mem_ball.mp reach
  have head := mem_outN.mp hh
  have ia : D i a=false := Bool.eq_false_iff.mpr (fun ed =>
    free a (k+1+1) (by omega) (by omega) (.step (us head.1) head.2 ((p.mono us).snoc a.property ed)))
  have hi := strict i (us iu) (mem_erase.mp iu).1
  have qi : (0:ℚ)≤(q:ℚ)-1 := sub_nonneg.mpr (by exact_mod_cast (show 1≤q by omega))
  have ib : D i b=true := by
    by_contra! off
    have ib0 : D i b=false := Bool.eq_false_iff.mpr off
    rw [wm,split i] at hi
    simp only [ia,ib0,Bool.false_eq_true,ite_false,add_zero,mul_zero] at hi
    rcases short with low|⟨j,jb,low⟩
    · linarith
    · have hj := strict j (us (mem_sdiff.mp jb).1) (mem_erase.mp (mem_sdiff.mp jb).1).1
      rw [wm,split j] at hj
      have loss : (if D j b=true then w b else 0)+(if D j a=true then w a else 0)≤w b+w a := by
        split <;> split <;> linarith
      have c := mul_le_mul_of_nonneg_left loss (Nat.cast_nonneg q : (0:ℚ)≤q)
      have d := mul_le_mul_of_nonneg_left (show w b+w a≤WeightedSD.row q D U w i-mass U w by linarith) qi
      nlinarith only [c,d,hj,low]
  have len : k=q-2 := by
    by_contra ne
    exact free b (k+1+1+1) (by omega) (by omega)
      (.step a.property ba (.step (us head.1) head.2 ((p.mono us).snoc b.property ib)))
  refine ⟨i,ir,ib,ia,⟨h,hh,len ▸ p⟩,least,?_⟩
  have ri : ForwardMerge.surplus q D V w i=WeightedSD.row q D U w i+
      q*w b-(mass U w+w b+w a) := by simp [ForwardMerge.surplus,split i,wm,ia,ib]
  rcases short with low|⟨j,jb,low⟩
  · left; rw [ri]; linarith
  · right; refine ⟨j,jb,?_⟩
    rw [ri,ForwardMerge.surplus,split j,wm]
    cases D j a <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> nlinarith only [low]

/-- Near the atom floor, an arc to a sufficiently heavy head must sit
    in a transitive triangle. The other parent of b on its shortest
    return misses a; the two required parents are distinct. -/
theorem common_parent {q D V} (hq : 2≤q) (free : QFree D V q) (small : SmallerSmallRow q V.card)
    (w : ℕ→ℚ) (pos : ∀i∈V,0<w i) {g : ℚ} (gp : 0<g)
    (floor : ∀i∈V,g≤ForwardMerge.surplus q D V w i)
    {b a : V} (ba : D b a=true) (light : ((q:ℚ)-2)*w b≤g)
    (rise : ((q:ℚ)-1)*w b<w a+g) :
    ∃i∈V,∃j∈V,i≠j ∧ D i b=true ∧ D i a=false ∧ D j b=true ∧ D j a=true := by
  have strict (i) (iv : i∈V) : mass V w<WeightedSD.row q D V w i :=
    sub_pos.mp (gp.trans_le (floor i iv))
  obtain ⟨i,ir,ib,ia,_,_,low⟩ := arc_pair hq free small w pos (b:=b) (a:=a) (fun i iv _ => strict i iv) ba
  have us : (V.erase a.val).erase b.val⊆V := (erase_subset _ _).trans (erase_subset _ _)
  obtain ⟨_,_,reach⟩ := BRsub.mem_ballSet.mp ir
  have iv := us (mem_ball.mp reach).1
  rcases low with low|⟨j,jb,low⟩
  · linarith [floor i iv]
  have jv := us (mem_sdiff.mp jb).1
  have qi : (0:ℚ)≤(q:ℚ)-1 := sub_nonneg.mpr (by exact_mod_cast (show 1≤q by omega))
  have priced : (q:ℚ)*g ≤ ((q:ℚ)-1)*ForwardMerge.surplus q D V w i+ForwardMerge.surplus q D V w j := by
    nlinarith only [mul_le_mul_of_nonneg_left (floor i iv) qi,floor j jv]
  have qp : (0:ℚ)<q := by exact_mod_cast (show 0<q by omega)
  have gap := lt_of_mul_lt_mul_left (priced.trans_lt low) qp.le
  have pa := pos a a.property
  have pb := pos b b.property
  have ja : D j a=true := by
    cases e : D j a <;> simp only [e,Bool.false_eq_true,ite_false,ite_true] at gap ⊢
    · cases f : D j b <;> simp only [f,Bool.false_eq_true,ite_false,ite_true] at gap <;> nlinarith
  have hit : D j b=true := by
    cases e : D j b <;> simp only [ja,e,Bool.false_eq_true,ite_false,ite_true,add_zero,sub_zero] at gap ⊢
    · linarith
  exact ⟨i,iv,j,jv,fun eq => Bool.noConfusion (ia.symm.trans (eq ▸ ja)),ib,ia,hit,ja⟩

/-- Follow only arcs whose two endpoints have no common parent in V. -/
def exposed (D : CH.Digraph) (V : Finset ℕ) : CH.Digraph :=
  fun b a => D b a && decide (∀j∈V,¬(D j b=true ∧ D j a=true))

/-- Every exposed step starting below the threshold loses at least its
    positive starting gap. In particular a loop cannot remain there. -/
theorem exposed_drop {q D V} (hq : 2≤q) (free : QFree D V q) (small : SmallerSmallRow q V.card)
    (w : ℕ→ℚ) (pos : ∀i∈V,0<w i) {g : ℚ} (gp : 0<g)
    (floor : ∀i∈V,g≤ForwardMerge.surplus q D V w i)
    {b a : V} (edge : exposed D V b a=true) (light : ((q:ℚ)-2)*w b≤g) :
    w a+(g-((q:ℚ)-2)*w b) ≤ w b := by
  obtain ⟨ba,block⟩ := Bool.and_eq_true_iff.mp edge
  by_contra! more
  obtain ⟨_,_,j,jv,_,_,_,jb,ja⟩ := common_parent hq free small w pos gp floor ba light (by linarith)
  exact (of_decide_eq_true block j jv) ⟨jb,ja⟩

/-- A light root either starts at a vertex with all heads covered, or
    reaches one by exposed arcs. The path costs a fixed positive amount
    per step and stays within the native graph. -/
theorem covered_sink {q D V} (hq : 2≤q) (free : QFree D V q) (small : SmallerSmallRow q V.card)
    (w : ℕ→ℚ) (pos : ∀i∈V,0<w i) {g : ℚ} (gp : 0<g)
    (floor : ∀i∈V,g≤ForwardMerge.surplus q D V w i)
    {b : V} (light : ((q:ℚ)-2)*w b<g) :
    ∃u∈V,∃k,Walk (exposed D V) V b u k ∧
      w u+k*(g-((q:ℚ)-2)*w b)≤w b ∧
      ∀a∈V,D u a=true → ∃j∈V,D j u=true ∧ D j a=true := by
  classical
  let gap := g-((q:ℚ)-2)*w b
  have gap_pos : 0<gap := sub_pos.mpr light
  let S := V.filter (fun u => ∃k,Walk (exposed D V) V b u k ∧ w u+k*gap≤w b)
  have start : b.val∈S := mem_filter.mpr ⟨b.property,0,.refl _,by simp⟩
  obtain ⟨u,uu,least⟩ := S.exists_min_image w ⟨b.val,start⟩
  obtain ⟨uv,k,path,cost⟩ := mem_filter.mp uu
  refine ⟨u,uv,k,path,cost,?_⟩
  intro a av ua
  by_contra! absent
  have exposedArc : exposed D V u a=true := Bool.and_eq_true_iff.mpr ⟨ua,decide_eq_true (by
    intro j jv pair
    exact (absent j jv pair.1) pair.2)⟩
  have ub := least b start
  have two : (0:ℚ)≤(q:ℚ)-2 := sub_nonneg.mpr (by exact_mod_cast hq)
  have mono := mul_le_mul_of_nonneg_left ub two
  have step := exposed_drop hq free small w pos gp floor (b:=⟨u,uv⟩) (a:=⟨a,av⟩)
    exposedArc (mono.trans light.le)
  have paid : w a+gap≤w u := by dsimp [gap]; linarith
  have aS : a∈S := mem_filter.mpr ⟨av,k+1,path.snoc av exposedArc,by
    push_cast; linarith only [cost,paid,show ((k:ℚ)+1)*gap=(k:ℚ)*gap+gap by ring]⟩
  linarith only [paid,gap_pos,least a aS]

/-- Saturation in the single puncture identifies the exterior of the
    return ball exactly with the remaining parents of its root. -/
theorem puncture_ball {q D V} (hq : 2≤q) (free : QFree D V q) {a b : V}
    (ba : D b a=true) (sat : BRsub.Sat q D (V.erase b.val)) :
    let U := (V.erase a.val).erase b.val
    ∀j∈U, j∈BRsub.ballSet D U (outN D U a) (q-2) ↔ D j a=false := by
  classical
  intro U j ju
  have us : U⊆V := (erase_subset _ _).trans (erase_subset _ _)
  have ab : a.val≠b.val := fun e => loopfree free (by omega) b.property (e ▸ ba)
  have av : a.val∈V.erase b.val := mem_erase.mpr ⟨ab,a.property⟩
  have ja := (mem_erase.mp (mem_erase.mp ju).2).1
  have jv : j∈V.erase b.val := mem_erase.mpr ⟨(mem_erase.mp ju).1,us ju⟩
  constructor
  · intro jr
    obtain ⟨h,hh,hit⟩ := BRsub.mem_ballSet.mp jr
    obtain ⟨_,k,hk,p⟩ := mem_ball.mp hit
    have head := mem_outN.mp hh
    exact Bool.eq_false_iff.mpr (fun edge => free a (k+1+1) (by omega) (by omega)
      (.step (us head.1) head.2 ((p.mono us).snoc a.property edge)))
  · intro off
    obtain ⟨_,l,le,path⟩ := mem_ball.mp (sat _ av _ jv (Bool.eq_false_iff.mp off))
    have clean : Walk D U a j l := by
      rcases path.lastVisit a.val with ok|⟨k,m,hk,len,cycle,_⟩
      · exact ok.mono (fun x hx => mem_erase.mpr ⟨(mem_erase.mp (mem_erase.mp hx).2).1,
          mem_erase.mpr ⟨(mem_erase.mp hx).1,mem_of_mem_erase (mem_of_mem_erase hx)⟩⟩)
      · exact (free a k hk (by omega) (cycle.mono (erase_subset _ _))).elim
    cases clean with
    | refl => exact (ja rfl).elim
    | step hu ed p =>
      exact BRsub.mem_ballSet.mpr ⟨_,mem_outN.mpr ⟨hu,ed⟩,mem_ball.mpr ⟨ju,_,by omega,p⟩⟩

open SharedArcBarrier SharedArcComponentExchange FirstPacketBarrier MarkedCyclePeeling

/-- The same minimizing fresh parent can be priced against every stalled
    fresh head at this pivot. The second row, if required, is a parent of
    that particular head. -/
theorem stopped_prices {q n} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    {F B} (step : Boundary X F B)
    (least : ∀M,Boundary X F M → (targets X.D X.V F B).card≤(targets X.D X.V F M).card)
    (multi : 1<(targets X.D X.V F B).card) {b a : X.V} (edge : Fresh X F (b,a))
    (no : ¬SharedArcReachMargin.StrictColumns q (insertArc (graph X.D F) b a) X.V)
    (w : ℕ→ℚ) (pos : ∀i∈X.V,0<w i)
    (strict : ∀i∈X.V,i≠b.val → mass X.V w<WeightedSD.row q X.D X.V w i)
    {p : X.V} (minPrice : ∀i : X.V,Fresh X F (i,b) →
      ForwardMerge.surplus q X.D X.V w p≤ForwardMerge.surplus q X.D X.V w i) :
    ForwardMerge.surplus q X.D X.V w p+w a ≤ ((q:ℚ)-1)*w b ∨
      ∃j∈(X.V.erase a.val).erase b.val,X.D j a=true ∧
        ((q:ℚ)-1)*ForwardMerge.surplus q X.D X.V w p+ForwardMerge.surplus q X.D X.V w j <
          (q:ℚ)*(((q:ℚ)-2)*w b+(if X.D j b=true then w b else 0)) := by
  classical
  have sat := ((SharedArcPivot.alternatives X hq small step least multi edge).resolve_left no).2.1
  have ba := edge.2.2.1
  obtain ⟨i,ir,ib,ia,_,_,low⟩ := arc_pair hq X.free small w pos strict (b:=b) (a:=a) ba
  obtain ⟨_,_,reach⟩ := BRsub.mem_ballSet.mp ir
  have iv := mem_of_mem_erase (mem_of_mem_erase (mem_ball.mp reach).1)
  have old := SharedArcPivot.classify_parents X hq small step least multi edge no ⟨i,iv⟩ ib
  have fresh : Fresh X F (i,b) := ⟨iv,b.property,ib,Bool.eq_false_iff.mpr
    (fun ed => Bool.noConfusion (ia.symm.trans (old.mp ed)))⟩
  have cheap := minPrice ⟨i,iv⟩ fresh
  rcases low with low|⟨j,jb,low⟩
  · left; linarith
  · have ju := (mem_sdiff.mp jb).1
    have ja : X.D j a=true := by
      cases h : X.D j a with
      | false => exact ((mem_sdiff.mp jb).2 ((puncture_ball hq X.free (a:=a) (b:=b) ba sat j ju).2 h)).elim
      | true => rfl
    refine Or.inr ⟨j,ju,ja,?_⟩
    simp only [ja,ite_true,sub_zero] at low
    have nonneg : (0:ℚ)≤(q:ℚ)-1 := sub_nonneg.mpr (by exact_mod_cast (show 1≤q by omega))
    linarith only [low,mul_le_mul_of_nonneg_left cheap nonneg]

private theorem add_ray {q D V} (w z : ℕ→ℚ) (t : ℚ) (i : ℕ) :
    ForwardMerge.surplus q D V (fun v => w v+t*z v) i =
      ForwardMerge.surplus q D V w i+t*ForwardMerge.surplus q D V z i := by
  have massAdd (S : Finset ℕ) : mass S (fun v => w v+t*z v)=mass S w+t*mass S z := by
    simp only [mass,sum_add_distrib,mul_sum]
  simp only [ForwardMerge.surplus,WeightedSD.row,outW_eq_mass,massAdd]
  ring

/-- Tilting by the exact puncture weights leaves all off-pivot surpluses
    and the pivot weight fixed. It eliminates the single-row alternative
    for every stalled head, with the same original prices on both sides. -/
theorem stopped_second_row {q n} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    {F B} (step : Boundary X F B)
    (least : ∀M,Boundary X F M → (targets X.D X.V F B).card≤(targets X.D X.V F M).card)
    (multi : 1<(targets X.D X.V F B).card) {b a : X.V} (edge : Fresh X F (b,a))
    (no : ¬SharedArcReachMargin.StrictColumns q (insertArc (graph X.D F) b a) X.V)
    (w : ℕ→ℚ) (pos : ∀i∈X.V,0<w i)
    (strict : ∀i∈X.V,i≠b.val → mass X.V w<WeightedSD.row q X.D X.V w i)
    {p : X.V} (pne : p≠b) (minPrice : ∀i : X.V,Fresh X F (i,b) →
      ForwardMerge.surplus q X.D X.V w p≤ForwardMerge.surplus q X.D X.V w i) :
    ∃j∈(X.V.erase a.val).erase b.val,X.D j a=true ∧
      ((q:ℚ)-1)*ForwardMerge.surplus q X.D X.V w p+ForwardMerge.surplus q X.D X.V w j <
        (q:ℚ)*(((q:ℚ)-2)*w b+(if X.D j b=true then w b else 0)) := by
  classical
  obtain ⟨_,_,_,z,zp,zm,zr⟩ := (SharedArcPivot.alternatives X hq small step least multi edge).resolve_left no
  let v (i : ℕ) := if i=b.val then 0 else z i
  have vb : v b=0 := by simp [v]
  have same {i} (ib : i≠b.val) : v i=z i := by simp [v,ib]
  have sm {S : Finset ℕ} (sub : S⊆X.V.erase b.val) : mass S v=mass S z :=
    sum_congr rfl (fun _ hi => same (mem_erase.mp (sub hi)).1)
  have m : mass X.V v=1 := by
    change (∑i∈X.V,v i)=1
    rw [← sum_erase_add X.V v b.property, vb,add_zero]
    exact (sm Subset.rfl).trans zm
  have exactPrice (i) (iv : i∈X.V) (ib : i≠b.val) : ForwardMerge.surplus q X.D X.V v i=0 := by
    have iu := mem_erase.mpr ⟨ib,iv⟩
    have cost := zr i iu
    rw [WeightedSD.row,outW_eq_mass] at cost
    rw [ForwardMerge.surplus,m,WeightedSD.row,outW_erase b.property,vb,ite_self,add_zero,outW_eq_mass,same ib,sm outN_subset,cost,sub_self]
  have an : a.val≠b.val := fun e => loopfree X.free (by omega) b.property (e ▸ edge.2.2.1)
  have pn : p.val≠b.val := fun e => pne (Subtype.ext e)
  have vpos : 0<v a := by rw [same an]; exact zp a (mem_erase.mpr ⟨an,a.property⟩)
  let t := (q:ℚ)*w b/v a
  have pay : t*v a=(q:ℚ)*w b := div_mul_cancel₀ _ vpos.ne'
  have tpos : 0≤t := div_nonneg (mul_nonneg (Nat.cast_nonneg _) (pos b b.property).le) vpos.le
  let f (i : ℕ) := w i+t*v i
  have fb : f b=w b := by simp [f,vb]
  have fa : f a=w a+(q:ℚ)*w b := by dsimp only [f]; rw [pay]
  have fp (i) (iv : i∈X.V) : 0<f i := by
    have nn : 0≤v i := by
      by_cases e : i=b.val
      · simp [v,e]
      · rw [same e]; exact (zp i (mem_erase.mpr ⟨e,iv⟩)).le
    exact add_pos_of_pos_of_nonneg (pos i iv) (mul_nonneg tpos nn)
  have equal (i) (iv : i∈X.V) (ib : i≠b.val) :
      ForwardMerge.surplus q X.D X.V f i=ForwardMerge.surplus q X.D X.V w i := by
    dsimp only [f]; rw [add_ray,exactPrice i iv ib,mul_zero,add_zero]
  have fs (i) (iv : i∈X.V) (ib : i≠b.val) : mass X.V f<WeightedSD.row q X.D X.V f i := by
    apply sub_pos.mp
    change 0<ForwardMerge.surplus q X.D X.V f i
    rw [equal i iv ib]
    exact sub_pos.mpr (strict i iv ib)
  have choice := stopped_prices X hq small step least multi edge no f fp fs (p:=p) (by
    intro i ib
    have ne : i.val≠b.val := fun e => loopfree X.free (by omega) b.property (e ▸ ib.2.2.1)
    rw [equal p p.property pn,equal i i.property ne]
    exact minPrice i ib)
  rw [equal p p.property pn,fb,fa] at choice
  rcases choice with cheap|⟨j,ju,ja,low⟩
  · have sp := sub_pos.mpr (strict p p.property pn)
    change 0<ForwardMerge.surplus q X.D X.V w p at sp
    nlinarith only [sp,cheap,pos a a.property,pos b b.property]
  · exact ⟨j,ju,ja,by rwa [equal j (mem_of_mem_erase (mem_of_mem_erase ju)) (mem_erase.mp ju).1] at low⟩

open Classical in
private theorem flat_off {q n} (X : Model q n) {F b} (center : ∀e : SharedArcFlatCut.Missing X F,
    e.val.1=b ∨ e.val.2=b) (u : ℕ→ℚ) (flat : ∀i∈X.V,WeightedSD.row q (graph X.D F) X.V u i=mass X.V u)
    (i : X.V) (ne : i≠b) :
    ForwardMerge.surplus q X.D X.V u i = if Fresh X F (i,b) then q*u b else 0 := by
  classical
  let G := graph X.D F
  have native {x y} (e : G x y=true) : X.D x y=true := by
    obtain ⟨_,hit⟩ := active.mp e
    exact (mem_col.mp hit).2.2.2
  have agree (j : ℕ) (ju : j∈X.V.erase b.val) : X.D i j=G i j := by
    cases ed : X.D i j <;> cases old : G i j <;> try rfl
    · exact (Bool.noConfusion (ed.symm.trans (native old)))
    · let e : SharedArcFlatCut.Missing X F := ⟨(i,⟨j,mem_of_mem_erase ju⟩),ed,old⟩
      rcases center e with bad|bad
      · exact (ne bad).elim
      · exact ((mem_erase.mp ju).1 (congrArg Subtype.val bad)).elim
  have keep : outW X.D (X.V.erase b.val) u i=outW G (X.V.erase b.val) u i :=
    sum_congr rfl (fun j ju => by rw [agree j ju])
  have price := flat i i.property
  change WeightedSD.row q G X.V u i=mass X.V u at price
  rw [WeightedSD.row,outW_erase b.property] at price
  rw [ForwardMerge.surplus,WeightedSD.row,outW_erase b.property,keep,←price]
  have on : Fresh X F (i,b) ↔ X.D i b=true ∧ G i b=false := by
    simp [Fresh,i.property,b.property,G]
  cases ed : X.D i b <;> cases old : G i b
  · simp [on,ed,old]
  · exact Bool.noConfusion (ed.symm.trans (native old))
  · simp [on,ed,old]; ring
  · simp [on,ed,old]

/-- Two independent weight directions force the second row into the old
    parent bank. Both prices in the conclusion are the original ones. -/
theorem two_banks {q n} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    {F B} (step : Boundary X F B)
    (least : ∀M,Boundary X F M → (targets X.D X.V F B).card≤(targets X.D X.V F M).card)
    (multi : 1<(targets X.D X.V F B).card) {b a : X.V} (edge : Fresh X F (b,a))
    (no : ¬SharedArcReachMargin.StrictColumns q (insertArc (graph X.D F) b a) X.V)
    (u : ℕ→ℚ) (up : ∀i∈X.V,0<u i)
    (flat : ∀i∈X.V,WeightedSD.row q (graph X.D F) X.V u i=mass X.V u)
    (w : ℕ→ℚ) (pos : ∀i∈X.V,0<w i)
    (strict : ∀i∈X.V,i≠b.val → mass X.V w<WeightedSD.row q X.D X.V w i)
    {p : X.V} (fresh : Fresh X F (p,b)) (minPrice : ∀i : X.V,Fresh X F (i,b) →
      ForwardMerge.surplus q X.D X.V w p≤ForwardMerge.surplus q X.D X.V w i) :
    ∃j : X.V,graph X.D F j b=true ∧ X.D j a=true ∧
      ((q:ℚ)-1)*ForwardMerge.surplus q X.D X.V w p+ForwardMerge.surplus q X.D X.V w j <
        (q:ℚ)*((q:ℚ)-1)*w b := by
  classical
  have center := ((SharedArcPivot.alternatives X hq small step least multi edge).resolve_left no).2.2.1
  have pne : p≠b := fun e => loopfree X.free (by omega) b.property (e ▸ fresh.2.2.1)
  let t := ((q:ℚ)-2)*w b/u b
  have qp : (0:ℚ)<q := by exact_mod_cast (show 0<q by omega)
  have q2 : (0:ℚ)≤(q:ℚ)-2 := sub_nonneg.mpr (by exact_mod_cast hq)
  have tp : 0≤t := div_nonneg (mul_nonneg q2 (pos b b.property).le) (up b b.property).le
  have pay : t*u b=((q:ℚ)-2)*w b := div_mul_cancel₀ _ (up b b.property).ne'
  let f (i : ℕ) := w i+t*u i
  have fp (i) (iv : i∈X.V) : 0<f i :=
    add_pos_of_pos_of_nonneg (pos i iv) (mul_nonneg tp (up i iv).le)
  have prices (i : X.V) (ib : i≠b) : ForwardMerge.surplus q X.D X.V f i =
      ForwardMerge.surplus q X.D X.V w i+t*(if Fresh X F (i,b) then q*u b else 0) := by
    rw [← flat_off X center u flat i ib]
    exact add_ray w u t i
  have fs (i) (iv : i∈X.V) (ib : i≠b.val) : mass X.V f<WeightedSD.row q X.D X.V f i := by
    apply sub_pos.mp
    change 0<ForwardMerge.surplus q X.D X.V f i
    have e := prices ⟨i,iv⟩ (fun h => ib (congrArg Subtype.val h))
    have sp := sub_pos.mpr (strict i iv ib)
    change 0<ForwardMerge.surplus q X.D X.V w i at sp
    rw [e]
    apply add_pos_of_pos_of_nonneg sp (mul_nonneg tp ?_)
    split
    · exact mul_nonneg qp.le (up b b.property).le
    · exact le_rfl
  obtain ⟨j,ju,ja,low⟩ := stopped_second_row X hq small step least multi edge no f fp fs pne (by
    intro i fr
    have ne : i≠b := fun e => loopfree X.free (by omega) b.property (e ▸ fr.2.2.1)
    simp only [prices p pne,prices i ne,fresh,fr,ite_true]
    exact add_le_add_left (minPrice i fr) _)
  let jv : X.V := ⟨j,mem_of_mem_erase (mem_of_mem_erase ju)⟩
  have jbne : jv≠b := fun h => (mem_erase.mp ju).1 (congrArg Subtype.val h)
  have old (hit : X.D jv b=true) := (SharedArcPivot.classify_parents X hq small step least multi edge no jv hit).2 ja
  have absent : ¬Fresh X F (jv,b) := fun fr => Bool.noConfusion (fr.2.2.2.symm.trans (old fr.2.2.1))
  change ((q:ℚ)-1)*ForwardMerge.surplus q X.D X.V f p+ForwardMerge.surplus q X.D X.V f jv < _ at low
  simp only [prices p pne,prices jv jbne,fresh,absent,ite_true,ite_false,mul_zero,add_zero] at low
  change ((q:ℚ)-1)*_+_ < (q:ℚ)*(((q:ℚ)-2)*(w b+t*u b)+(if X.D jv b=true then w b+t*u b else 0)) at low
  have ps := sub_pos.mpr (strict p p.property (fun e => pne (Subtype.ext e)))
  have js := sub_pos.mpr (strict jv jv.property (mem_erase.mp ju).1)
  change 0<ForwardMerge.surplus q X.D X.V w p at ps
  change 0<ForwardMerge.surplus q X.D X.V w jv at js
  cases ed : X.D jv b with
  | false =>
    simp only [ed,Bool.false_eq_true,ite_false,add_zero] at low
    have prod := mul_nonneg (show (0:ℚ)≤(q:ℚ)-1 by linarith) ps.le
    nlinarith only [low,prod,js,congrArg (fun z : ℚ => (q:ℚ)*z) pay]
  | true =>
    refine ⟨jv,old ed,ja,?_⟩
    simp only [ed,ite_true] at low
    linarith only [low]

/-- Deleting any subset of the exterior preserves the entire inner ball
    on its actual labels, including all realizing paths of the given length. -/
theorem ball_delete {D U H K d} (ks : K⊆U\BRsub.ballSet D U H d) :
    BRsub.ballSet D (U\K) H d=BRsub.ballSet D U H d := by
  classical
  ext j
  constructor
  · intro jr
    obtain ⟨h,hh,hit⟩ := BRsub.mem_ballSet.mp jr
    obtain ⟨ju,k,kd,p⟩ := mem_ball.mp hit
    exact BRsub.mem_ballSet.mpr ⟨h,hh,mem_ball.mpr ⟨(mem_sdiff.mp ju).1,k,kd,p.mono sdiff_subset⟩⟩
  · intro jr
    obtain ⟨h,hh,hit⟩ := BRsub.mem_ballSet.mp jr
    obtain ⟨ju,k,kd,p⟩ := mem_ball.mp hit
    have keep {x} (xu : x∈U) {l} (le : l≤d) (path : Walk D U h x l) : x∈U\K := by
      apply mem_sdiff.mpr ⟨xu,?_⟩
      intro xk
      exact (mem_sdiff.mp (ks xk)).2 (BRsub.mem_ballSet.mpr ⟨h,hh,mem_ball.mpr ⟨xu,l,le,path⟩⟩)
    have lift {x l} (le : l≤d) (path : Walk D U h x l) : Walk D (U\K) h x l := by
      induction l generalizing x with
      | zero => cases path; exact .refl _
      | succ l ih =>
        obtain ⟨y,front,xu,arc⟩ := path.unsnoc
        exact (ih (by omega) front).snoc (keep xu le path) arc
    exact BRsub.mem_ballSet.mpr ⟨h,hh,mem_ball.mpr ⟨keep ju kd p,k,kd,lift kd p⟩⟩

/-- The pair obstruction tested against every exterior deletion with the
    original inner ball and weights. Each loss is the actual weight of
    that row's heads in K. Witness rows may depend on K. -/
theorem exterior_cuts {q n D U H} (hq : 2≤q) (free : QFree D U q) (small : SmallerSmallRow q n)
    (hs : H⊆U) (live : H.Nonempty) (w : ℕ→ℚ) (pos : ∀i∈U,0<w i) :
    let R := BRsub.ballSet D U H (q-2)
    ∀K⊆U\R,(U\K).card+1<n → mass (U\K) w<q*mass H w →
      let s := fun i => ForwardMerge.surplus q D U w i+mass K w-q*outW D K w i
      ∃i∈R, (∀j∈R,s i≤s j) ∧ (s i≤0 ∨ ∃j∈(U\R)\K,((q:ℚ)-1)*s i+s j<0) := by
  classical
  intro R K ks room heavy s
  have ku : K⊆U := ks.trans sdiff_subset
  have same := ball_delete ks
  change BRsub.ballSet D (U\K) H (q-2)=R at same
  have hsub : H⊆U\K := by
    intro h hh
    exact mem_sdiff.mpr ⟨hs hh,fun hk => (mem_sdiff.mp (ks hk)).2
      (BRsub.mem_ballSet.mpr ⟨h,hh,mem_ball.mpr ⟨hs hh,0,Nat.zero_le _,.refl _⟩⟩)⟩
  have eq (i) : s i=WeightedSD.row q D (U\K) w i-mass (U\K) w := by
    have m : mass (U\K) w+mass K w=mass U w := sum_sdiff ku
    dsimp [s,ForwardMerge.surplus,WeightedSD.row]
    rw [outW_split ku]
    linarith only [m,show (q:ℚ)*(outW D K w i+outW D (U\K) w i)=
      q*outW D K w i+q*outW D (U\K) w i by ring]
  obtain ⟨i,ir,mn,ob⟩ := pair_obstruction hq (free.mono_set sdiff_subset) small room
    hsub live w (fun i iu => pos i (mem_sdiff.mp iu).1) heavy
  rw [same] at ir mn ob
  refine ⟨i,ir,fun j jr => by rw [eq,eq]; linarith only [mn j jr],?_⟩
  rcases ob with low|⟨j,jb,low⟩
  · exact Or.inl ((eq i).symm ▸ sub_nonpos.mpr low)
  · refine Or.inr ⟨j,?_,?_⟩
    · simp only [mem_sdiff] at jb ⊢; tauto
    · rw [eq,eq]; linarith only [low]

/-- Every nonempty subset K of the parents at a saturated exact root
    forces one maximizer on the same return ball. Either it pays the
    root and K, or it pays jointly with a parent outside K. -/
theorem unit_pool {q n D S} (hq : 2≤q) (free : QFree D S q) (sat : BRsub.Sat q D S)
    (small : SmallerSmallRow q n) (room : S.card≤n) (w : ℕ→ℚ) (pos : ∀i∈S,0<w i)
    (rows : ∀i∈S,WeightedSD.row q D S w i=mass S w) {a} (av : a∈S) :
    let U := S.erase a
    let P := inN D U a
    ∀K⊆P,K.Nonempty → ∃i∈U\P,
      (∀h∈U\P,outW D K w h≤outW D K w i) ∧
      (w a+mass K w≤q*outW D K w i ∨ ∃j∈P\K,
        mass K w<((q:ℚ)-1)*outW D K w i+outW D K w j) := by
  classical
  intro U P K ks live
  let H := outN D U a
  let R := BRsub.ballSet D U H (q-2)
  have us : U⊆S := erase_subset _ _
  have ku : K⊆U := fun i hi => (mem_inN.mp (ks hi)).1
  have wp : 0<mass K w := sum_pos (fun i hi => pos i (us (ku hi))) live
  have wm : mass U w+w a=mass S w := sum_erase_add S w av
  have diff (i) (iu : i∈U) : ForwardMerge.surplus q D U w i=
      w a-(q:ℚ)*(if D i a=true then w a else 0) := by
    have e := rows i (us iu)
    rw [WeightedSD.row,outW_erase av,←wm] at e
    unfold ForwardMerge.surplus WeightedSD.row
    linarith only [e,show (q:ℚ)*(outW D U w i+(if D i a=true then w a else 0)) =
      q*outW D U w i+q*(if D i a=true then w a else 0) by ring]
  have head : (q:ℚ)*mass H w=mass U w := by
    have e := rows a av
    rw [WeightedSD.row,outW_erase av,←wm] at e
    simp only [Bool.eq_false_iff.mpr (loopfree free (by omega) av),Bool.false_eq_true,ite_false,add_zero,
      outW_eq_mass] at e
    dsimp [H,U]; linarith only [e]
  have liveH : H.Nonempty := by
    by_contra! empty
    rw [empty,show mass ∅ w=0 by simp [mass],mul_zero] at head
    linarith [mass_mono ku (fun i iu => (pos i (us iu)).le)]
  have partition : R=U\P := by
    ext j
    constructor
    · intro jr
      obtain ⟨h,hh,reach⟩ := BRsub.mem_ballSet.mp jr
      obtain ⟨ju,k,kd,path⟩ := mem_ball.mp reach
      obtain ⟨hu,ah⟩ := mem_outN.mp hh
      exact mem_sdiff.mpr ⟨ju,fun jp => free a (k+1+1) (by omega) (by omega)
        (.step (us hu) ah ((path.mono us).snoc av (mem_inN.mp jp).2))⟩
    · intro jr
      obtain ⟨ju,jp⟩ := mem_sdiff.mp jr
      have off : ¬D j a=true := fun ja => jp (mem_inN.mpr ⟨ju,ja⟩)
      obtain ⟨_,k,kd,path⟩ := mem_ball.mp (sat _ av _ (us ju) off)
      rcases path.lastVisit a with clean|⟨l,m,lp,lm,cycle,_⟩
      · cases clean with
        | refl => exact ((mem_erase.mp ju).1 rfl).elim
        | step hu ah p => exact BRsub.mem_ballSet.mpr ⟨_,mem_outN.mpr ⟨hu,ah⟩,mem_ball.mpr ⟨ju,_,by omega,p⟩⟩
      · exact (free a l lp (by omega) cycle).elim
  have outside : U\R=P := by
    ext i; rw [partition]; simp only [mem_sdiff]; have inc : i∈P → i∈U := fun h => (mem_inN.mp h).1
    tauto
  have m : mass (U\K) w+mass K w=mass U w := sum_sdiff ku
  have size := card_sdiff_add_card_eq_card ku
  have uc := card_erase_add_one av
  change U.card+1=S.card at uc
  obtain ⟨i,ir,mn,ob⟩ := exterior_cuts hq (free.mono_set us) small (H:=H) outN_subset liveH w
    (fun i iu => pos i (us iu)) K (outside.symm ▸ ks)
    (by have := live.card_pos; omega) (by linarith only [head,m,wp])
  change i∈R at ir
  have inside {h} (hr : h∈R) : ForwardMerge.surplus q D U w h=w a := by
    obtain ⟨hu,hp⟩ := mem_sdiff.mp (partition ▸ hr)
    have off := Bool.eq_false_iff.mpr (fun e => hp (mem_inN.mpr ⟨hu,e⟩))
    simp [diff h hu,off]
  have qp : (0:ℚ)<q := by exact_mod_cast (show 0<q by omega)
  refine ⟨i,partition ▸ ir,?_,?_⟩
  · intro h hh
    have hr := partition.symm ▸ hh
    have e := mn h hr
    dsimp only at e
    rw [inside ir,inside hr] at e
    exact le_of_not_gt (fun lt => by linarith only [e,mul_lt_mul_of_pos_left lt qp])
  · dsimp only at ob
    rw [inside ir] at ob
    rcases ob with low|⟨j,jb,low⟩
    · exact Or.inl (by linarith only [low])
    · change j∈(U\R)\K at jb
      rw [outside] at jb
      obtain ⟨ju,ja⟩ := mem_inN.mp (mem_sdiff.mp jb).1
      simp only [diff j ju,ja,ite_true] at low
      refine Or.inr ⟨j,jb,?_⟩
      apply lt_of_mul_lt_mul_left (a:=(q:ℚ)) _ qp.le
      nlinarith only [low]

/-- Price the entire old common-parent bank at the actual stopped pivot.
    The second witness must be a parent of the head that misses the pivot. -/
theorem stopped_bank {q n} (X : Model q n) (hq : 2≤q) (small : SmallerSmallRow q X.V.card)
    {F B} (native : F⊆family X) (spans : SharedArcExpansion.support F=X.V)
    (step : Boundary X F B)
    (least : ∀M,Boundary X F M → (targets X.D X.V F B).card≤(targets X.D X.V F M).card)
    (multi : 1<(targets X.D X.V F B).card) {b a : X.V} (edge : Fresh X F (b,a))
    (no : ¬SharedArcReachMargin.StrictColumns q (insertArc (graph X.D F) b a) X.V) :
    let S := X.V.erase b.val
    let U := S.erase a.val
    let P := inN X.D U a
    let C := P ∩ inN X.D U b
    C.Nonempty ∧ ∃w : ℕ→ℚ,(∀i∈S,0<w i) ∧ mass S w=1 ∧
      (∀i∈S,WeightedSD.row q X.D S w i=1) ∧ ∃i∈U\P,
        Walk X.D (U\P) a i (q-1) ∧ (∃c∈C,X.D i c=true) ∧
        (∀h∈U\P,outW X.D C w h≤outW X.D C w i) ∧
        (w a+mass C w≤q*outW X.D C w i ∨ ∃j∈P,X.D j b=false ∧
          mass C w<((q:ℚ)-1)*outW X.D C w i+outW X.D C w j) := by
  classical
  intro S U P C
  obtain ⟨_,sat,_,w,wp,wm,wr⟩ := (SharedArcPivot.alternatives X hq small step least multi edge).resolve_left no
  have ab : a.val≠b.val := fun eq => loopfree X.free (by omega) b.property (eq ▸ edge.2.2.1)
  have av : a.val∈S := mem_erase.mpr ⟨ab,a.property⟩
  have inSupport : b.val∈SharedArcExpansion.support F := spans.symm ▸ b.property
  obtain ⟨M,mf,bm⟩ := mem_biUnion.mp inSupport
  have cyc : ShenCycleSuccessor.Cycle X.D X.V q M := (mem_filter.mp (native mf)).2
  obtain ⟨c,cm⟩ := card_pos.mp (show 0<(inN X.D M b).card by
    rw [show (inN X.D M b).card=1 from cyc.incoming b bm]; decide)
  obtain ⟨mc,cb⟩ := mem_inN.mp cm
  have cv : c∈X.V := cyc.sub mc
  have old : graph X.D F c b=true := active.mpr ⟨M,mem_col.mpr ⟨mf,mc,bm,cb⟩⟩
  have ca := (SharedArcPivot.classify_parents X hq small step least multi edge no ⟨c,cv⟩ cb).1 old
  have cu : c∈U := mem_erase.mpr ⟨fun eq => loopfree X.free (by omega) a.property (eq ▸ ca),
    mem_erase.mpr ⟨fun eq => loopfree X.free (by omega) b.property (eq ▸ cb),cv⟩⟩
  have live : C.Nonempty := ⟨c,mem_inter.mpr ⟨mem_inN.mpr ⟨cu,ca⟩,mem_inN.mpr ⟨cu,cb⟩⟩⟩
  obtain ⟨i,ir,mx,alt⟩ := unit_pool hq (X.free.mono_set (erase_subset b.val X.V)) sat small
    (card_le_card (erase_subset b.val X.V)) w wp (fun j js => (wr j js).trans wm.symm) av C inter_subset_left live
  have Inc : C⊆S := fun j jc => mem_of_mem_erase (mem_inN.mp (mem_inter.mp jc).1).1
  have witness : ∃c∈C,X.D i c=true := by
    by_contra! off
    have zero : outW X.D C w i=0 := sum_eq_zero (fun j jc => by simp [off j jc])
    rcases alt with big|⟨j,_,low⟩
    · rw [zero,mul_zero] at big
      linarith [wp a av,mass_nonneg (fun j jc => (wp j (Inc jc)).le)]
    · rw [zero,mul_zero,zero_add,outW_eq_mass] at low
      exact low.not_ge (mass_mono outN_subset (fun j jc => (wp j (Inc jc)).le))
  have walk : Walk X.D (U\P) a i (q-1) := by
    obtain ⟨d,dc,idArc⟩ := witness
    obtain ⟨iu,ip⟩ := mem_sdiff.mp ir
    have off : ¬X.D i a=true := fun ed => ip (mem_inN.mpr ⟨iu,ed⟩)
    obtain ⟨_,k,kd,path⟩ := mem_ball.mp (sat _ av _ (mem_of_mem_erase iu) off)
    have size : k=q-1 := by
      have da := (mem_inN.mp (mem_inter.mp dc).1).2
      by_contra ne
      exact X.free a (k+1+1) (by omega) (by omega)
        (((path.mono (erase_subset _ _)).snoc (mem_of_mem_erase (Inc dc)) idArc).snoc a.property da)
    have avoid {y l} (p : Walk X.D S a y l) (le : l≤q-1) : Walk X.D (U\P) a y l := by
      induction l generalizing y with
      | zero => cases p; exact .refl _
      | succ l ih =>
        obtain ⟨v,front,ys,vy⟩ := p.unsnoc
        have pV := p.mono (erase_subset b.val X.V)
        have ne : y≠a.val := fun eq => X.free a (l+1) (by omega) (by omega) (eq ▸ pV)
        have out : y∉P := fun yp => X.free a (l+1+1) (by omega) (by omega) (pV.snoc a.property (mem_inN.mp yp).2)
        exact (ih front (by omega)).snoc (mem_sdiff.mpr ⟨mem_erase.mpr ⟨ne,ys⟩,out⟩) vy
    exact size ▸ avoid path kd
  refine ⟨live,w,wp,wm,wr,i,ir,walk,witness,mx,?_⟩
  rcases alt with big|⟨j,jr,low⟩
  · exact Or.inl big
  · obtain ⟨jp,jc⟩ := mem_sdiff.mp jr
    exact Or.inr ⟨j,jp,Bool.eq_false_iff.mpr (fun jb =>
      jc (mem_inter.mpr ⟨jp,mem_inN.mpr ⟨(mem_inN.mp jp).1,jb⟩⟩)),low⟩

#print axioms stopped_bank
#print axioms unit_pool
#print axioms exterior_cuts
#print axioms ball_delete
#print axioms two_banks
#print axioms stopped_second_row
#print axioms stopped_prices
#print axioms puncture_ball
#print axioms covered_sink
#print axioms exposed_drop
#print axioms common_parent
#print axioms arc_pair
#print axioms contacts_balance
#print axioms pair_obstruction
#print axioms no_pair
#print axioms safe
#print axioms balance
end LeanCH.BR.Closure.RankedMerge
