import checkpoints.shen_extension.PairedArcAudit

namespace LeanCH.BR.Closure.CommonParentHeadRepair
open Finset BRq2 BRq3 BR45 WeightedSD ShortestCycleWeights

def margin (q : ℕ) (D : CH.Digraph) (U : Finset ℕ) (w : ℕ → ℚ) (i j : ℕ) :=
  ((q:ℚ)-1)*(WeightedSD.row q D U w i-mass U w)+WeightedSD.row q D U w j-mass U w

def Protected (q : ℕ) (D : CH.Digraph) (U : Finset ℕ) (w : ℕ → ℚ) (i : ℕ) :=
  mass U w < WeightedSD.row q D U w i ∧ ∀ j∈U, 0 < margin q D U w i j

/-- A single weighting simultaneously pays every row hitting the accumulated head set.
The bonus at h keeps the distinguished set heavy even when it misses K. -/
theorem deposit {q : ℕ} {D : CH.Digraph} {U H K : Finset ℕ} (hq : 2≤q)
    (hs : H⊆U) (hl : H.Nonempty) (ks : K⊆U) (cap : K.card+2≤q)
    (w : ℕ→ℚ) (pos : ∀i∈U,0<w i) :
    ∃ z : ℕ→ℚ, (∀i∈U, w i≤z i) ∧ (∀i∈U,0<z i) ∧ mass U z < q*mass H z ∧
      ∀i∈U,(∃k∈K,D i k=true) → Protected q D U z i := by
  classical
  obtain ⟨h,hh⟩ := hl
  let L := mass U w+1
  have lp : 0<L := by dsimp [L]; linarith [mass_nonneg (fun v hv => (pos v hv).le)]
  have qp : (0:ℚ)<q := by exact_mod_cast (show 0<q by omega)
  have cp : 0<(q:ℚ)-1 := by
    have : (2:ℚ)≤q := by exact_mod_cast hq
    linarith
  let z := fun v => w v+(if v∈K then L*q else 0)+(if v=h then L*((q:ℚ)-1) else 0)
  have inc (v) : w v≤z v := by
    dsimp [z]; split_ifs <;> linarith [mul_pos lp qp,mul_pos lp cp]
  have zp (v) (vu : v∈U) := (pos v vu).trans_le (inc v)
  have tot : mass U z=mass U w+(K.card:ℚ)*(L*q)+L*((q:ℚ)-1) := by
    simp only [mass,z,sum_add_distrib]
    rw [← sum_filter,show U.filter (fun v => v∈K)=K from filter_mem_eq_inter.trans (inter_eq_right.mpr ks)]
    simp [hs hh]
  have cq : (K.card:ℚ)+2≤q := by exact_mod_cast cap
  have bound : mass U z < ((q:ℚ)-1)*(L*q) := by
    rw [tot]
    have h := mul_le_mul_of_nonneg_right cq (mul_pos lp qp).le
    have l : mass U w<L := by dsimp [L]; linarith
    linarith
  have one (S : Finset ℕ) (sub : S⊆U) (v) (hv : v∈S) : z v ≤ mass S z :=
    single_le_sum (fun i hi => (zp i (sub hi)).le) hv
  have zh : L*((q:ℚ)-1)≤z h := by
    simp only [z,ite_true]
    split_ifs <;> linarith [pos h (hs hh),mul_pos lp qp]
  refine ⟨z,fun v _ => inc v,zp,?_,?_⟩
  · have e := mul_le_mul_of_nonneg_left (zh.trans (one H hs h hh)) qp.le
    linarith
  intro i iu hit
  obtain ⟨k,kk,ik⟩ := hit
  have zk : L*q≤z k := by
    simp only [z,ite_eq_left kk]
    split_ifs <;> linarith [pos k (ks kk),mul_pos lp cp,mul_pos lp qp]
  have zk' := zk.trans (one (outN D U i) outN_subset k (mem_outN.mpr ⟨ks kk,ik⟩))
  have row (v) (vu : v∈U) : 0<WeightedSD.row q D U z v := by
    rw [WeightedSD.row,outW_eq_mass]
    exact add_pos_of_pos_of_nonneg (zp v vu) (mul_nonneg qp.le (mass_nonneg (fun k hk => (zp k (outN_subset hk)).le)))
  have ri : q*(L*q)≤WeightedSD.row q D U z i := by
    rw [WeightedSD.row,outW_eq_mass]
    linarith [mul_le_mul_of_nonneg_left zk' qp.le,zp i iu]
  have gain : L*q < WeightedSD.row q D U z i-mass U z := by linarith
  refine ⟨by linarith [mul_pos lp qp],?_⟩
  intro j ju
  unfold margin
  linarith only [mul_lt_mul_of_pos_left gain cp,bound,row j ju]

/-- At the next obstruction the least unpaid inner row misses every protected head. -/
theorem next_blocker {q n D U H K} (hq : 2≤q) (free : QFree D U q)
    (small : SmallerSmallRow q n) (room : U.card+1<n)
    (hs : H⊆U) (hl : H.Nonempty) (ks : K⊆U) (cap : K.card+2≤q)
    (w : ℕ→ℚ) (pos : ∀i∈U,0<w i) :
    let R := BRsub.ballSet D U H (q-2)
    ∃ z : ℕ→ℚ, (∀i∈U,w i≤z i) ∧ (∀i∈U,0<z i) ∧ mass U z<q*mass H z ∧
      (∀i∈U,(∃k∈K,D i k=true) → Protected q D U z i) ∧
      ∃r∈R,(∀k∈K,D r k=false) ∧
        (WeightedSD.row q D U z r≤mass U z ∨ ∃e∈U\R,margin q D U z r e<0) := by
  intro R
  obtain ⟨z,inc,zp,heavy,paid⟩ := deposit (D:=D) hq hs hl ks cap w pos
  obtain ⟨r,rr,_,bad⟩ := RankedMerge.pair_obstruction hq free small room hs hl z zp heavy
  have ru : r∈U := by obtain ⟨_,_,reach⟩ := BRsub.mem_ballSet.mp rr; exact (mem_ball.mp reach).1
  refine ⟨z,inc,zp,heavy,paid,r,rr,?_,?_⟩
  · intro k kk
    apply Bool.eq_false_iff.mpr
    intro hit
    have p := paid r ru ⟨k,kk,hit⟩
    rcases bad with low | ⟨j,jr,low⟩
    · exact low.not_gt p.1
    · have e := p.2 j (mem_sdiff.mp jr).1
      unfold margin at e
      linarith
  · rcases bad with low | ⟨j,jr,low⟩
    · exact Or.inl low
    · exact Or.inr ⟨j,jr,sub_neg.mpr low⟩

/-- The recorded weights at each link pay every earlier protected row.
Each link carries the actual row that fails and the fresh head selected for it. -/
def Step (q : ℕ) (D : CH.Digraph) (U H : Finset ℕ)
    (p p' : Finset ℕ × (ℕ→ℚ)) : Prop :=
  let R := BRsub.ballSet D U H (q-2)
  (∀v∈U,p.2 v≤p'.2 v) ∧ (∀v∈U,0<p'.2 v) ∧ mass U p'.2<q*mass H p'.2 ∧
    (∀r∈U,(∃k∈p.1,D r k=true) → Protected q D U p'.2 r) ∧
    ∃r∈R,(WeightedSD.row q D U p'.2 r≤mass U p'.2 ∨ ∃e∈U\R,margin q D U p'.2 r e<0) ∧
      (∀k∈p.1,D r k=false) ∧ ∃k∈outN D U r,k∉p.1 ∧ p'.1=insert k p.1

/-- Iterate from a supplied set, passing the weights of each repair into the next.
At size q-1 the last fresh head has been identified. Paying it is a separate question. -/
theorem iterate {q n D U H} (hq : 2≤q) (free : QFree D U q)
    (small : SmallerSmallRow q n) (room : U.card+1<n) (hs : H⊆U) (hl : H.Nonempty)
    (K : Finset ℕ) (ks : K⊆U) (cap : K.card+1≤q) (w : ℕ→ℚ) (pos : ∀v∈U,0<w v) :
    ∃ T z,T⊆U ∧ Relation.ReflTransGen (Step q D U H) (K,w) (T,z) ∧
      (T.card+1=q ∨ ∃r∈BRsub.ballSet D U H (q-2),outN D U r=∅) := by
  classical
  by_cases done : K.card+1=q
  · exact ⟨K,w,ks,.refl,Or.inl done⟩
  obtain ⟨v,inc,vpos,heavy,paid,r,rr,miss,bad⟩ :=
    next_blocker hq free small room hs hl ks (by omega) w pos
  by_cases dead : outN D U r=∅
  · exact ⟨K,w,ks,.refl,Or.inr ⟨r,rr,dead⟩⟩
  obtain ⟨k,kr⟩ := nonempty_iff_ne_empty.mpr dead
  have ku := (mem_outN.mp kr).1
  have fresh : k∉K := fun kk => Bool.noConfusion ((miss k kk).symm.trans (mem_outN.mp kr).2)
  have size := card_insert_of_notMem fresh
  have step : Step q D U H (K,w) (insert k K,v) :=
    ⟨inc,vpos,heavy,paid,r,rr,bad,miss,k,kr,fresh,rfl⟩
  obtain ⟨T,z,ts,path,stop⟩ :=
    iterate hq free small room hs hl (insert k K) (insert_subset ku ks) (by omega) v vpos
  exact ⟨T,z,ts,(Relation.ReflTransGen.single step).trans path,stop⟩
termination_by q-K.card
decreasing_by rw [size]; omega

/-- A row with no surviving head can never meet the inner strict inequality. -/
theorem dead_row {q D U i} (iu : i∈U) (dead : outN D U i=∅) (v : ℕ→ℚ)
    (pos : ∀k∈U,0≤v k) : WeightedSD.row q D U v i≤mass U v := by
  rw [WeightedSD.row,outW_eq_mass,dead]
  simpa [mass] using (single_le_sum pos iu : v i≤∑k∈U,v k)

/-- Use the actual inner row and actual common parent at the deleted arc.
A surviving head lets the same two labels be strictly paid, with every exterior
partner of that inner row paid as well. The new failure belongs to a different row. -/
theorem from_common {q D V} (hq : 3≤q) (free : QFree D V q) (small : SmallerSmallRow q V.card)
    (w : ℕ→ℚ) (pos : ∀v∈V,0<w v) {c : ℚ} (high : mass V w<c)
    (flat : ∀v∈V,WeightedSD.row q D V w v=c) {b a : V} (ba : D b a=true) :
    let U := (V.erase a.val).erase b.val
    let H := outN D U a
    let R := BRsub.ballSet D U H (q-2)
    ∃i∈R, D i b=true ∧ D i a=false ∧ (∀r∈R,WeightedSD.row q D U w i≤WeightedSD.row q D U w r) ∧
      ∀j∈U,D j a=true → D j b=true →
        let deficit := (q:ℚ)*(((q:ℚ)-1)*w b-(c-mass V w))
        0<deficit ∧ margin q D U w i j= -deficit ∧
        (outN D U i=∅ ∨ ∀k∈outN D U i,∃z : ℕ→ℚ,
          (∀v∈U,w v≤z v) ∧ mass U z<q*mass H z ∧ Protected q D U z i ∧
          deficit < margin q D U z i j-margin q D U w i j ∧
          ∃r∈R,r≠i ∧ D r k=false ∧
            (WeightedSD.row q D U z r≤mass U z ∨ ∃e∈U\R,margin q D U z r e<0) ∧
            (outN D U r=∅ ∨ ∃l∈outN D U r,l≠k ∧ Step q D U H ({k},w) (insert l {k},z) ∧ ∃T v,T⊆U ∧
              Relation.ReflTransGen (Step q D U H) (insert l {k},z) (T,v) ∧
              (T.card+1=q ∨ ∃s∈R,outN D U s=∅))) := by
  classical
  intro U H R
  have h2 : 2≤q := by omega
  have ab : b.val≠a.val := fun eq => loopfree free (by omega) a.property (eq ▸ ba)
  have bv := mem_erase.mpr ⟨ab,b.property⟩
  have us : U⊆V := (erase_subset _ _).trans (erase_subset _ _)
  have room : U.card+1<V.card := by
    have ax := card_erase_add_one a.property
    have bx := card_erase_add_one bv
    dsimp only [U]; omega
  have total (f : ℕ→ℚ) : (∑v∈V,f v)=(∑v∈U,f v)+f b+f a := by
    rw [sum_erase_add _ _ bv,sum_erase_add _ _ a.property]
  have wm : mass V w=mass U w+w b+w a := total w
  have split (r) : WeightedSD.row q D V w r=WeightedSD.row q D U w r+
      q*((if D r b=true then w b else 0)+(if D r a=true then w a else 0)) := by
    unfold WeightedSD.row outW
    rw [total]; ring
  obtain ⟨i,ir,ib,ia,_,least,_⟩ := RankedMerge.arc_pair h2 free small w pos (b:=b) (a:=a)
    (fun v vv _ => flat v vv ▸ high) ba
  have iu : i∈U := by obtain ⟨_,_,reach⟩ := BRsub.mem_ballSet.mp ir; exact (mem_ball.mp reach).1
  refine ⟨i,ir,ib,ia,least,?_⟩
  intro j ju ja jb deficit
  have floor := strict_atom_floor_of_proper h2 free (small.induced free) w
    (fun v vv => (pos v vv).le) c high (fun v vv => (flat v vv).ge) b b.property
  have qp : (0:ℚ)<q := by exact_mod_cast (show 0<q by omega)
  have old : margin q D U w i j= -deficit := by
    have ei := split i
    have ej := split j
    rw [flat i (us iu),ib,ia] at ei
    rw [flat j (us ju),jb,ja] at ej
    simp only [ite_true,Bool.false_eq_true,ite_false,add_zero] at ei ej
    unfold margin
    dsimp [deficit]
    rw [wm]
    linear_combination (1-(q:ℚ))*ei-ej
  refine ⟨mul_pos qp (sub_pos.mpr floor),old,?_⟩
  by_cases empty : outN D U i=∅
  · exact Or.inl empty
  right
  intro k ik
  have ku := (mem_outN.mp ik).1
  have hit := (mem_outN.mp ik).2
  have heavy := (PairedArcAudit.rows_iff h2 free small w pos high flat ba).1
  have hl : H.Nonempty := by
    by_contra! em
    change mass U w<q*mass H w at heavy
    rw [em,show mass ∅ w=0 by simp [mass],mul_zero] at heavy
    exact heavy.not_ge (mass_nonneg (fun r ru => (pos r (us ru)).le))
  obtain ⟨z,inc,zp,zh,paid,r,rr,miss,bad⟩ := next_blocker h2 (free.mono_set us) small room
    (H:=H) outN_subset hl (K:={k}) (singleton_subset_iff.mpr ku) (by simpa using hq) w
    (fun r ru => pos r (us ru))
  have p := paid i iu ⟨k,mem_singleton_self _,hit⟩
  have rk := miss k (mem_singleton_self _)
  refine ⟨z,inc,zh,p,by linarith [p.2 j ju],r,rr,fun eq => Bool.noConfusion ((eq ▸ rk).symm.trans hit),rk,bad,?_⟩
  by_cases dead : outN D U r=∅
  · exact Or.inl dead
  obtain ⟨l,lr⟩ := nonempty_iff_ne_empty.mpr dead
  have lk : l≠k := fun eq => Bool.noConfusion (rk.symm.trans (eq ▸ (mem_outN.mp lr).2))
  have ks : insert l {k}⊆U := insert_subset (mem_outN.mp lr).1 (singleton_subset_iff.mpr ku)
  have cap : (insert l {k} : Finset ℕ).card+1≤q := by simp [lk]; omega
  obtain ⟨T,v,ts,path,stop⟩ := iterate h2 (free.mono_set us) small room outN_subset hl
    (insert l {k}) ks cap z zp
  have step : Step q D U H ({k},w) (insert l {k},z) :=
    ⟨inc,zp,zh,paid,r,rr,bad,miss,l,lr,by simpa using lk,rfl⟩
  exact Or.inr ⟨l,lr,lk,step,T,v,ts,path,stop⟩

/-- All remaining heads of an inner row together carry more than the common
parent's weight plus the original excess, divided by q. -/
theorem surviving_mass {q D V} (hq : 2≤q) (free : QFree D V q)
    (w : ℕ→ℚ) (pos : ∀v∈V,0<w v) {c : ℚ} (flat : ∀v∈V,WeightedSD.row q D V w v=c)
    {a b : V} (ba : D b a=true)
    (two : ∀r∈V,∀j∈V,r≠j → D r b=true → D j b=true → w r+w j+q*w b<mass V w) :
    let U := (V.erase a.val).erase b.val
    let R := BRsub.ballSet D U (outN D U a) (q-2)
    ∀j∈U,D j a=true → D j b=true → ∀r∈R,c-mass V w+w j<q*mass (outN D U r) w := by
  classical
  intro U R j ju ja jb r rr
  have ab : b.val≠a.val := fun eq => loopfree free (by omega) a.property (eq ▸ ba)
  have bv := mem_erase.mpr ⟨ab,b.property⟩
  have us : U⊆V := (erase_subset _ _).trans (erase_subset _ _)
  obtain ⟨h,hh,reach⟩ := BRsub.mem_ballSet.mp rr
  obtain ⟨ru,k,le,path⟩ := mem_ball.mp reach
  have head := mem_outN.mp hh
  have ra : D r a=false := Bool.eq_false_iff.mpr fun ed =>
    free a (k+1+1) (by omega) (by omega) (.step (us head.1) head.2 ((path.mono us).snoc a.property ed))
  have ne : r≠j := fun eq => Bool.noConfusion ((eq ▸ ra).symm.trans ja)
  have total (f : ℕ→ℚ) : (∑v∈V,f v)=(∑v∈U,f v)+f b+f a := by
    rw [sum_erase_add _ _ bv,sum_erase_add _ _ a.property]
  have e := flat r (us ru)
  unfold WeightedSD.row outW at e
  rw [total,ra] at e
  rw [← outW_eq_mass]
  unfold outW
  by_cases rb : D r b=true
  · simp only [rb,ite_true,Bool.false_eq_true,ite_false,add_zero] at e
    linarith [two r (us ru) j (us ju) ne rb jb]
  · simp only [rb,Bool.false_eq_true,ite_false,add_zero] at e
    have le : w r+w j≤mass U w := by
      have sub : ({r,j}:Finset ℕ)⊆U := insert_subset ru (singleton_subset_iff.mpr ju)
      have cap := sum_le_sum_of_subset_of_nonneg (f:=w) sub (fun v hv _ => (pos v (us hv)).le)
      simpa [ne,mass] using cap
    have wm : mass V w=mass U w+w b+w a := total w
    linarith [pos b b.property,pos a a.property]

/-- The common parent excludes every dead end of the construction.
This composes the first repair with its actual successors up to q-1 heads. -/
theorem live_run {q D V} (hq : 3≤q) (free : QFree D V q) (small : SmallerSmallRow q V.card)
    (w : ℕ→ℚ) (pos : ∀v∈V,0<w v) {c : ℚ} (high : mass V w<c)
    (flat : ∀v∈V,WeightedSD.row q D V w v=c) {b a : V} (ba : D b a=true)
    (two : ∀r∈V,∀j∈V,r≠j → D r b=true → D j b=true → w r+w j+q*w b<mass V w) :
    let U := (V.erase a.val).erase b.val
    let H := outN D U a
    let R := BRsub.ballSet D U H (q-2)
    ∃i∈R,D i b=true ∧ D i a=false ∧ (∀r∈R,WeightedSD.row q D U w i≤WeightedSD.row q D U w r) ∧
      ∀j∈U,D j a=true → D j b=true →
      let d := (q:ℚ)*(((q:ℚ)-1)*w b-(c-mass V w))
      0<d ∧ margin q D U w i j= -d ∧
      (∀r∈R,c-mass V w+w j<q*mass (outN D U r) w) ∧ (outN D U i).Nonempty ∧
      ∀k∈outN D U i, ∃l z T v, l≠k ∧ Protected q D U z i ∧
        d<margin q D U z i j-margin q D U w i j ∧
        Step q D U H ({k},w) (insert l {k},z) ∧
        Relation.ReflTransGen (Step q D U H) (insert l {k},z) (T,v) ∧ T⊆U ∧ T.card+1=q := by
  intro U H R
  obtain ⟨i,ir,ib,ia,least,go⟩ := from_common hq free small w pos high flat ba
  refine ⟨i,ir,ib,ia,least,?_⟩
  intro j ju ja jb d
  obtain ⟨dp,old,steps⟩ := go j ju ja jb
  have masses := surviving_mass (by omega : 2≤q) free w pos flat ba two j ju ja jb
  have us : U⊆V := (erase_subset _ _).trans (erase_subset _ _)
  have live (r) (rr : r∈R) : (outN D U r).Nonempty := by
    apply nonempty_iff_ne_empty.mpr
    intro em
    have bound := masses r rr
    change c-mass V w+w j<q*mass (outN D U r) w at bound
    rw [em,show mass ∅ w=0 by simp [mass],mul_zero] at bound
    linarith [pos j (us ju)]
  refine ⟨dp,old,masses,live i ir,?_⟩
  intro k kk
  obtain ⟨z,_,_,paid,gain,r,rr,_,_,_,next⟩ := (steps.resolve_left (live i ir).ne_empty) k kk
  obtain ⟨l,_,lk,step,T,v,ts,path,stop⟩ := next.resolve_left (live r rr).ne_empty
  exact ⟨l,z,T,v,lk,paid,gain,step,path,ts,stop.resolve_right (fun ⟨s,sr,dead⟩ => (live s sr).ne_empty dead)⟩

/-- Specialize the capstone's native biclique bound to two family parents
of the same label. Arcs are lifted to the native graph before applying it. -/
theorem two_rows {q : ℕ} {E D : CH.Digraph} {V : Finset ℕ} {w : ℕ→ℚ}
    (sub : ∀u v,E u v=true → D u v=true)
    (budget : ∀K⊆V,∀O⊆V,(∀k∈K,∀o∈O,D k o=true) →
      2≤K.card → O.Nonempty → mass K w+q*mass O w<mass V w) {b : V}
    (r) (rv : r∈V) (j) (jv : j∈V) (ne : r≠j) (rb : E r b=true) (jb : E j b=true) :
    w r+w j+q*w b<mass V w := by
  classical
  have cost := budget {r,j} (insert_subset rv (singleton_subset_iff.mpr jv))
    {b.val} (singleton_subset_iff.mpr b.property) (by
      intro x hx y hy
      obtain rfl : y=b.val := mem_singleton.mp hy
      rcases mem_insert.mp hx with eq|eq
      · exact eq ▸ sub r b rb
      · exact (mem_singleton.mp eq) ▸ sub j b jb)
    (by simp [ne]) (singleton_nonempty _)
  simpa only [mass,sum_pair ne,sum_singleton] using cost

/-- Column independence of the actual adjacency block on specified row and column labels. -/
def IndependentHeads (D : CH.Digraph) (R K : Finset ℕ) : Prop :=
  ∀f : ℕ→ℚ,(∀r∈R,(∑k∈K,if D r k=true then f k else 0)=0) → ∀k∈K,f k=0

private theorem step_independent {q D U H} {p p' : Finset ℕ × (ℕ→ℚ)}
    (step : Step q D U H p p') :
    let R := BRsub.ballSet D U H (q-2)
    IndependentHeads D R p.1 → IndependentHeads D R p'.1 := by
  classical
  intro R old f vanish
  obtain ⟨_,_,_,_,r,rr,_,miss,k,ku,fresh,add⟩ := step
  have rk := (mem_outN.mp ku).2
  have zero : f k=0 := by
    have e := vanish r rr
    rw [add,sum_insert fresh,ite_eq_left rk] at e
    have rest : (∑x∈p.1,if D r x=true then f x else 0)=0 :=
      sum_eq_zero fun x xx => by simp [miss x xx]
    linarith
  have prev := old f (by
    intro s sr
    have e := vanish s sr
    rw [add,sum_insert fresh,zero] at e
    simpa using e)
  rw [add]
  intro x xx
  rcases mem_insert.mp xx with eq|xin
  · exact eq ▸ zero
  · exact prev x xin

/-- Every successor contributes a column separated from all previous columns
by its own unpaid row. The first column is witnessed by the original inner row. -/
theorem trace_minor {q D U H i k l w z T v}
    (ir : i∈BRsub.ballSet D U H (q-2)) (hit : D i k=true)
    (step : Step q D U H ({k},w) (insert l {k},z))
    (path : Relation.ReflTransGen (Step q D U H) (insert l {k},z) (T,v)) :
    IndependentHeads D (BRsub.ballSet D U H (q-2)) T := by
  have first : IndependentHeads D (BRsub.ballSet D U H (q-2)) {k} := by
    intro f zero j hj
    obtain rfl := mem_singleton.mp hj
    simpa only [sum_singleton,hit,ite_true] using zero i ir
  have follow {s t : Finset ℕ × (ℕ→ℚ)} (walk : Relation.ReflTransGen (Step q D U H) s t)
      (initial : IndependentHeads D (BRsub.ballSet D U H (q-2)) s.1) :
      IndependentHeads D (BRsub.ballSet D U H (q-2)) t.1 := by
    induction walk with
    | refl => exact initial
    | tail _ edge ih => exact step_independent edge ih
  exact follow path (step_independent step first)

/-- Restrict to rows missing the previously bought head. Future failed rows
all lie in this same slice of the matrix. -/
theorem avoiding_minor {q D U H k l w z T v}
    (step : Step q D U H ({k},w) (insert l {k},z))
    (path : Relation.ReflTransGen (Step q D U H) (insert l {k},z) (T,v)) :
    let R := BRsub.ballSet D U H (q-2)
    k∈T ∧ IndependentHeads D (R.filter (fun r=>D r k=false)) (T.erase k) := by
  classical
  intro R
  let P := fun p : Finset ℕ × (ℕ→ℚ) =>
    k∈p.1 ∧ IndependentHeads D (R.filter (fun r=>D r k=false)) (p.1.erase k)
  have advance {p p'} (edge : Step q D U H p p') (prev : P p) : P p' := by
    obtain ⟨_,_,_,_,r,rr,_,miss,x,xr,fresh,add⟩ := edge
    have ne : x≠k := fun eq => fresh (eq ▸ prev.1)
    refine ⟨add ▸ mem_insert_of_mem prev.1,?_⟩
    intro f zero
    have er : p'.1.erase k=insert x (p.1.erase k) := by rw [add,erase_insert_of_ne ne]
    have nx : x∉p.1.erase k := fun h => fresh (mem_of_mem_erase h)
    have value : f x=0 := by
      have e := zero r (mem_filter.mpr ⟨rr,miss k prev.1⟩)
      rw [er,sum_insert nx,ite_eq_left (mem_outN.mp xr).2] at e
      have rem : (∑y∈p.1.erase k,if D r y=true then f y else 0)=0 :=
        sum_eq_zero fun y hy => by simp [miss y (mem_of_mem_erase hy)]
      linarith
    have old := prev.2 f (by
      intro s sr
      have e := zero s sr
      rw [er,sum_insert nx,value] at e
      simpa using e)
    rw [er]
    intro y hy
    rcases mem_insert.mp hy with eq|yy
    · exact eq ▸ value
    · exact old y yy
  have base : P ({k},w) := by
    refine ⟨mem_singleton_self _,?_⟩
    intro f vanish j hj
    simp at hj
  have iterateP {p p'} (route : Relation.ReflTransGen (Step q D U H) p p') (start : P p) : P p' := by
    induction route with
    | refl => exact start
    | tail _ e ih => exact advance e ih
  exact iterateP path (advance step base)

#print axioms avoiding_minor
#print axioms trace_minor
#print axioms two_rows
#print axioms surviving_mass
#print axioms live_run
#print axioms iterate
#print axioms dead_row
#print axioms from_common
#print axioms deposit
#print axioms next_blocker
end LeanCH.BR.Closure.CommonParentHeadRepair
