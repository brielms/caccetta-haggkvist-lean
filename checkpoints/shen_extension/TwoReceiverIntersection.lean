import checkpoints.shen_extension.RankedMerge
import LeanCH.BR.BRWeightedRetainedHeadTransfer
import LeanCH.BR.BRDonorWalks

namespace LeanCH.BR.Closure.TwoReceiverIntersection
open Finset BRq2 BRq3 BR45 WeightedSD ShortestCycleWeights

/-- Delete K and split all its weight between a and b, optimizing the
    split simultaneously over retained rows. Failure requires either a
    row missing both receivers, or two oppositely incident rows hitting
    the same deleted labels with strictly more than their combined slack. -/
theorem split_obstruction {q D V K} (hq : 2≤q) (free : QFree D V q) (small : SmallerSmallRow q V.card)
    (ks : K⊆V) (live : K.Nonempty) {a b : ℕ} (av : a∈V\K) (bv : b∈V\K)
    (noA : ∀k∈K,D a k=false) (w : ℕ→ℚ) (pos : ∀i∈V,0<w i)
    (strict : ∀i∈V,mass V w<WeightedSD.row q D V w i) :
    let e := ForwardMerge.surplus q D V w
    (∃j∈V\K,D j a=false ∧ D j b=false ∧ e j<q*outW D K w j) ∨
    ∃i∈V\K,∃j∈V\K,D i a=true ∧ D i b=false ∧ D j a=false ∧ D j b=true ∧
      e i+e j<(q:ℚ)*mass (outN D K i ∩ outN D K j) w := by
  classical
  intro e
  let U := V\K
  let m := mass K w
  let c (i : ℕ) := (q:ℚ)*outW D K w i-e i
  let bid (i : ℕ) := if D i a=true ∧ D i b=false then max 0 (c i) else 0
  have qp : (0:ℚ)<q := by exact_mod_cast (show 0<q by omega)
  have mp : 0<m := sum_pos (fun i ik => pos i (ks ik)) live
  have room : U.card<V.card := by
    have size := card_sdiff_add_card_eq_card ks
    have count := live.card_pos
    dsimp [U]; omega
  have split (i) : c i=mass V w-WeightedSD.row q D U w i := by
    dsimp [c,e,ForwardMerge.surplus,WeightedSD.row,U]
    rw [outW_split ks]
    ring
  have cap (i) (iu : i∈U) : c i<(q:ℚ)*m := by
    have lo := sub_pos.mpr (strict i (mem_sdiff.mp iu).1)
    change 0<e i at lo
    have bound : mass (outN D K i) w≤m := mass_mono outN_subset (fun j jk => (pos j (ks jk)).le)
    dsimp only [c]; rw [outW_eq_mass]
    linarith only [lo,mul_le_mul_of_nonneg_left bound qp.le]
  obtain ⟨i,iu,largest⟩ := U.exists_max_image bid ⟨a,av⟩
  let u := bid i
  have un : 0≤u := by
    dsimp [u,bid]
    split
    · exact le_max_left ..
    · exact le_rfl
  have ub : u<(q:ℚ)*m := by
    dsimp [u,bid]
    split
    · exact max_lt (mul_pos qp mp) (cap i iu)
    · exact mul_pos qp mp
  let A := u/(q:ℚ)
  let B := m-A
  have qA : (q:ℚ)*A=u := by dsimp [A]; field_simp
  have An : 0≤A := div_nonneg un qp.le
  have Bn : 0≤B := sub_nonneg.mpr ((div_le_iff₀ qp).mpr (by linarith only [ub.le, mul_comm m (q:ℚ)]))
  have qB : (q:ℚ)*B=q*m-u := by dsimp [B]; rw [mul_sub,qA]
  let z := addWeightAt (addWeightAt w a A) b B
  have total : mass U z=mass V w := by
    have part : mass U w+m=mass V w := sum_sdiff ks
    dsimp only [z]; rw [mass_addWeightAt bv,mass_addWeightAt av]; dsimp [B]; linarith
  have zp (v) (vv : v∈U) : 0<z v := by
    have old := pos v (mem_sdiff.mp vv).1
    dsimp [z,addWeightAt]; split_ifs <;> linarith
  have gain (v) : WeightedSD.row q D U z v=WeightedSD.row q D U w v+
      (if v=a then A else 0)+(if v=b then B else 0)+
      (if D v a=true then u else 0)+(if D v b=true then q*m-u else 0) := by
    dsimp only [z]; rw [row_addWeightAt bv,row_addWeightAt av]
    cases D v a <;> cases D v b <;> simp only [Bool.false_eq_true,ite_false,ite_true,mul_zero,qA,qB] <;> ring
  have bad : ∃j∈U,WeightedSD.row q D U z j<mass V w := by
    by_contra! allPaid
    have eq := positive_feasible_rows_tight_of_smallRow hq (small D U room (free.mono_set sdiff_subset))
      z zp (fun j ju => total.symm ▸ allPaid j ju) a av
    have zero : outW D K w a=0 := sum_eq_zero (fun k kk => by simp [noA k kk])
    have original := strict a (mem_sdiff.mp av).1
    have base : WeightedSD.row q D V w a=WeightedSD.row q D U w a := by
      simp only [WeightedSD.row,outW_split ks,zero,zero_add,U]
    rw [base] at original
    rw [gain,total] at eq
    split_ifs at eq <;> linarith only [original,eq,An,Bn,un,ub]
  obtain ⟨j,ju,low⟩ := bad
  rw [gain] at low
  have lost : (if D j a=true then u else 0)+(if D j b=true then q*m-u else 0)<c j := by
    rw [split]; split_ifs at low ⊢ <;> linarith
  cases ja : D j a <;> cases jb : D j b <;> simp only [ja,jb,Bool.false_eq_true,ite_false,ite_true,zero_add,add_zero] at lost
  · exact Or.inl ⟨j,ju,ja,jb,sub_pos.mp lost⟩
  · have up : 0<u := by linarith only [cap j ju,lost]
    have actual : D i a=true ∧ D i b=false := by
      by_contra off
      simp [u,bid,off] at up
    have clears : u=c i := by
      change (if D i a=true ∧ D i b=false then max 0 (c i) else 0)=c i
      have positive : 0<c i := by simpa [u,bid,actual.1,actual.2] using up
      simp [actual.1,actual.2,max_eq_right positive.le]
    have union : mass (outN D K i ∪ outN D K j) w≤m :=
      mass_mono (union_subset outN_subset outN_subset) (fun k kk => (pos k (ks kk)).le)
    have tally : mass (outN D K i ∪ outN D K j) w+mass (outN D K i ∩ outN D K j) w=
        outW D K w i+outW D K w j := by rw [outW_eq_mass,outW_eq_mass]; exact sum_union_inter
    refine Or.inr ⟨i,iu,j,ju,actual.1,actual.2,ja,jb,?_⟩
    rw [clears] at lost
    dsimp only [c] at lost
    nlinarith only [lost,mul_le_mul_of_nonneg_left union qp.le,congrArg (fun z : ℚ => (q:ℚ)*z) tally]
  · have bound := largest j ju
    change bid j≤u at bound
    have lower : c j≤bid j := by simp [bid,ja,jb]
    exact (lost.not_ge (lower.trans bound)).elim
  · exact (by linarith only [cap j ju,lost] : False).elim

private theorem positive_head {D : CH.Digraph} {K : Finset ℕ} {w : ℕ→ℚ} {i}
    (hit : 0<outW D K w i) : ∃c∈K,D i c=true := by
  by_contra! off
  have zero : outW D K w i=0 := sum_eq_zero (fun c ck => by simp [off c ck])
  exact hit.ne' zero

private theorem return_corridor {q D S a d} (hq : 2≤q) (free : QFree D S q)
    (reach : ∀d∈S,D d a=false → d∈ball D S a (q-1))
    (av : a∈S) (dv : d∈S) (off : D d a=false)
    (contact : ∃c∈S,D d c=true ∧ D c a=true) :
    Walk D ((S.erase a)\inN D (S.erase a) a) a d (q-1) := by
  obtain ⟨c,cv,dc,ca⟩ := contact
  obtain ⟨_,k,kd,p⟩ := mem_ball.mp (reach d dv off)
  have len : k=q-1 := by
    by_contra ne
    exact free a (k+1+1) (by omega) (by omega) ((p.snoc cv dc).snoc av ca)
  have lift {y l} (path : Walk D S a y l) (le : l≤q-1) :
      Walk D ((S.erase a)\inN D (S.erase a) a) a y l := by
    induction l generalizing y with
    | zero => cases path; exact .refl _
    | succ l ih =>
      obtain ⟨x,front,yv,edge⟩ := path.unsnoc
      have ne : y≠a := fun eq => free a (l+1) (by omega) (by omega) (eq ▸ path)
      have offParent : y∉inN D (S.erase a) a := fun h =>
        free a (l+1+1) (by omega) (by omega) (path.snoc av (mem_inN.mp h).2)
      exact (ih front (by omega)).snoc (mem_sdiff.mpr ⟨mem_erase.mpr ⟨ne,yv⟩,offParent⟩) edge
  exact len ▸ lift p kd

/-- Every nonempty part of the common-parent bank at the stopped pivot
    has a last row on a fixed length-(q−1) return. If that row also feeds
    the pivot, an exterior row feeds the very same deleted labels. -/
theorem corridor_cut {q D V} (hq : 2≤q) (free : QFree D V q) (small : SmallerSmallRow q V.card)
    {b a : V} (ba : D b a=true) (sat : BRsub.Sat q D V)
    (w : ℕ→ℚ) (pos : ∀i∈V,0<w i) (strict : ∀i∈V,mass V w<WeightedSD.row q D V w i) :
    let S := V.erase b.val
    let U := S.erase a.val
    let C := inN D U a ∩ inN D U b
    let e := ForwardMerge.surplus q D V w
    ∀K⊆C,K.Nonempty → ∃d∈V\K,D d a=false ∧
      Walk D (U\inN D U a) a d (q-1) ∧
      ((D d b=false ∧ e d<q*outW D K w d) ∨
       (D d b=true ∧ ∃j∈V\K,D j a=true ∧ D j b=false ∧
         e d+e j<(q:ℚ)*mass (outN D K d ∩ outN D K j) w)) := by
  classical
  intro S U C e K ks live
  have as : a.val∈S := mem_erase.mpr ⟨fun eq => loopfree free (by omega) b.property (eq ▸ ba),a.property⟩
  have ku {c} (ck : c∈K) : c∈U := (mem_inN.mp (mem_inter.mp (ks ck)).1).1
  have inc : K⊆V := fun c ck => mem_of_mem_erase (mem_of_mem_erase (ku ck))
  have ak : a.val∈V\K := mem_sdiff.mpr ⟨a.property,fun k => (mem_erase.mp (ku k)).1 rfl⟩
  have bk : b.val∈V\K := mem_sdiff.mpr ⟨b.property,fun k => (mem_erase.mp (mem_erase.mp (ku k)).2).1 rfl⟩
  have absent {y c} (yv : y∈V) (ck : c∈K) (cy : D c y=true) : D y c=false :=
    Bool.eq_false_iff.mpr (fun yc => free y 2 (by decide) hq (.step (inc ck) yc (.step yv cy (.refl _))))
  have missA (c) (ck : c∈K) := absent a.property ck (mem_inN.mp (mem_inter.mp (ks ck)).1).2
  have missB (c) (ck : c∈K) := absent b.property ck (mem_inN.mp (mem_inter.mp (ks ck)).2).2
  have reach (d) (ds : d∈S) (off : D d a=false) : d∈ball D S a (q-1) := by
    obtain ⟨_,l,le,p⟩ := mem_ball.mp (sat _ a.property _ (mem_of_mem_erase ds) (Bool.eq_false_iff.mp off))
    rcases p.lastVisit b with ok|⟨k,m,_,len,front,_⟩
    · exact mem_ball.mpr ⟨ds,l,le,ok⟩
    · exact (free a (k+1) (by omega) (by omega) (front.snoc a.property ba)).elim
  have corridor {d} (dv : d∈V\K) (da : D d a=false) (contact : ∃c∈K,D d c=true) :
      Walk D (U\inN D U a) a d (q-1) := by
    obtain ⟨c,ck,dc⟩ := contact
    have ds : d∈S := mem_erase.mpr ⟨fun eq => Bool.noConfusion ((missB c ck).symm.trans (eq ▸ dc)),(mem_sdiff.mp dv).1⟩
    exact return_corridor hq (free.mono_set (erase_subset _ _)) reach as ds da
      ⟨c,mem_of_mem_erase (ku ck),dc,(mem_inN.mp (mem_inter.mp (ks ck)).1).2⟩
  have qp : (0:ℚ)≤q := Nat.cast_nonneg _
  rcases split_obstruction hq free small inc live ak bk missA w pos strict with one|two
  · obtain ⟨d,dv,da,db,hit⟩ := one
    have paid := sub_pos.mpr (strict d (mem_sdiff.mp dv).1)
    change 0<e d at paid
    have reaches := positive_head (pos_of_mul_pos_right (paid.trans hit) qp)
    exact ⟨d,dv,da,corridor dv da reaches,Or.inl ⟨db,hit⟩⟩
  · obtain ⟨j,jv,d,dv,ja,jb,da,db,hit⟩ := two
    have paid : 0<e j+e d := add_pos (sub_pos.mpr (strict j (mem_sdiff.mp jv).1))
      (sub_pos.mpr (strict d (mem_sdiff.mp dv).1))
    have massPos := pos_of_mul_pos_right (paid.trans hit) qp
    have livePair : (outN D K j ∩ outN D K d).Nonempty := by
      by_contra! empty
      rw [empty,show mass ∅ w=0 by simp [mass]] at massPos
      exact lt_irrefl _ massPos
    obtain ⟨c,cc⟩ := livePair
    obtain ⟨ck,dc⟩ := mem_outN.mp (mem_inter.mp cc).2
    exact ⟨d,dv,da,corridor dv da ⟨c,ck,dc⟩,Or.inr ⟨db,j,jv,ja,jb,by
      simpa only [add_comm (e d),inter_comm (outN D K d)] using hit⟩⟩

/-- An incidence law with no numerical prices. Failure at any single arc
    of the native table eliminates the whole proposed source. -/
def AllCorners (q : ℕ) (D : CH.Digraph) (V : Finset ℕ) : Prop :=
  ∀b∈V,∀a∈V,D b a=true → ∀c∈V,D c b=true → D c a=true →
    let U := (V.erase b).erase a
    ∃d∈V,D d c=true ∧ D d a=false ∧ Walk D (U\inN D U a) a d (q-1) ∧
      (D d b=false ∨ ∃j∈V,D j c=true ∧ D j a=true ∧ D j b=false)

theorem all_corners {q D V} (hq : 2≤q) (free : QFree D V q) (small : SmallerSmallRow q V.card)
    (sat : BRsub.Sat q D V) (w : ℕ→ℚ) (pos : ∀i∈V,0<w i)
    (strict : ∀i∈V,mass V w<WeightedSD.row q D V w i) : AllCorners q D V := by
  classical
  intro b bv a av ba c cv cb ca U
  have cu : c∈U := mem_erase.mpr ⟨fun eq => loopfree free (by omega) av (eq ▸ ca),
    mem_erase.mpr ⟨fun eq => loopfree free (by omega) bv (eq ▸ cb),cv⟩⟩
  have box : c∈inN D U a ∩ inN D U b := mem_inter.mpr ⟨mem_inN.mpr ⟨cu,ca⟩,mem_inN.mpr ⟨cu,cb⟩⟩
  obtain ⟨d,dv,da,path,alt⟩ := corridor_cut hq free small (b:=⟨b,bv⟩) (a:=⟨a,av⟩) ba sat w pos strict
    {c} (singleton_subset_iff.mpr box) (singleton_nonempty c)
  have dV := (mem_sdiff.mp dv).1
  have e := sub_pos.mpr (strict d dV)
  have qp : (0:ℚ)≤q := Nat.cast_nonneg _
  rcases alt with ⟨db,hit⟩|⟨_,j,jv,ja,jb,hit⟩
  · obtain ⟨x,xc,ed⟩ := positive_head (pos_of_mul_pos_right (e.trans hit) qp)
    exact ⟨d,dV,mem_singleton.mp xc ▸ ed,da,path,Or.inl db⟩
  · have ej := sub_pos.mpr (strict j (mem_sdiff.mp jv).1)
    have value := pos_of_mul_pos_right ((add_pos e ej).trans hit) qp
    have live : (outN D {c} d ∩ outN D {c} j).Nonempty := by
      by_contra! eq
      rw [eq,show mass ∅ w=0 by simp [mass]] at value
      exact lt_irrefl _ value
    obtain ⟨z,zz⟩ := live
    obtain ⟨zc,dz⟩ := mem_outN.mp (mem_inter.mp zz).1
    obtain rfl := mem_singleton.mp zc
    exact ⟨d,dV,dz,da,path,Or.inr ⟨j,(mem_sdiff.mp jv).1,(mem_outN.mp (mem_inter.mp zz).2).2,ja,jb⟩⟩

/-- Reverse prices may come from a spanning cycle family's arc table.
    Its strict rows remain strict after restoring native arcs. -/
theorem reversed_family {q D V F} (hq : 2≤q) (free : QFree D V q) (small : SmallerSmallRow q V.card)
    (sat : BRsub.Sat q D V) (w : ℕ→ℚ) (pos : ∀i∈V,0<w i)
    (strict : ∀i∈V,mass V w<WeightedSD.row q (fun u v => FirstPacketBarrier.graph D F v u) V w i) :
    AllCorners q (fun u v => D v u) V := by
  apply all_corners hq free.reverse small (SerialChain.sat_reverse sat) w pos
  intro i iv
  apply (strict i iv).trans_le
  simp only [WeightedSD.row,outW_eq_mass]
  apply add_le_add_right (mul_le_mul_of_nonneg_left (mass_mono ?_ (fun j jh => (pos j (mem_outN.mp jh).1).le))
    (Nat.cast_nonneg q))
  intro j jh
  obtain ⟨jv,arc⟩ := mem_outN.mp jh
  obtain ⟨_,hit⟩ := FirstPacketBarrier.active.mp arc
  exact mem_outN.mpr ⟨jv,(MarkedCyclePeeling.mem_col.mp hit).2.2.2⟩

/-- Inside the parents of a fixed head, a backward-closed nonempty set
    whose vertices have internal successors must have an externally
    distinguished arc. A source component with no such distinction
    would be a module; a singleton source contradicts separation. -/
theorem distinguish_in_parents {q n} (X : Model q n) (hq : 2≤q) {a : X.V} {A : Finset ℕ}
    {seedTop seedNext : ℕ}
    (sub : A⊆inN X.D X.V a) (live : A.Nonempty)
    (closed : ∀x∈A,∀y∈inN X.D X.V a,X.D y x=true → y∈A)
    (out : ∀x∈A,∃y∈inN X.D X.V a,X.D x y=true ∧ (y∈A ∨ x=seedTop ∧ y=seedNext)) :
    ∃c∈A,∃b∈inN X.D X.V a,X.D c b=true ∧ (b∈A ∨ c=seedTop ∧ b=seedNext) ∧ ∃d∈X.V,
      X.D d c=true ∧ X.D d b=false ∧ X.D d a=false := by
  classical
  let P := inN X.D X.V a
  obtain ⟨S,sl,sa,sc,ss⟩ := exists_closed_strong_bank (fun u v => X.D v u) live
  have sv : S⊆X.V := fun i si => (mem_inN.mp (sub (sa si))).1
  have fromP {x y} (xs : x∈S) (yp : y∈P) (yx : X.D y x=true) : y∈S :=
    sc x xs y (closed x (sa xs) y yp yx) yx
  by_contra fail
  have passes {c b z} (cc : c∈S) (bs : b∈S) (cb : X.D c b=true)
      (zv : z∈X.V) (za : X.D z a=false) (zc : X.D z c=true) : X.D z b=true := by
    cases ed : X.D z b
    · exact (fail ⟨c,sa cc,b,sub (sa bs),cb,Or.inl (sa bs),z,zv,zc,ed,za⟩).elim
    · rfl
  by_cases big : 2≤S.card
  · have uniform : BRsub.InUniform X.D X.V S := by
      intro x xs y ys z zv zs
      by_cases zp : z∈P
      · have miss {v} (vs : v∈S) : X.D z v=false :=
          Bool.eq_false_iff.mpr (fun e => zs (fromP vs zp e))
        rw [miss xs,miss ys]
      · have za : X.D z a=false := Bool.eq_false_iff.mpr (fun e => zp (mem_inN.mpr ⟨zv,e⟩))
        have lift {u v k} (path : Walk (fun i j => X.D j i) S u v k) (us : u∈S) :
            X.D z v=true → X.D z u=true := by
          induction path with
          | refl => exact id
          | step vs ed _ ih => exact fun hit => passes vs us ed zv za (ih vs hit)
        obtain ⟨_,xy⟩ := ss x xs y ys
        obtain ⟨_,yx⟩ := ss y ys x xs
        exact Bool.eq_iff_iff.mpr ⟨lift yx ys,lift xy xs⟩
    have proper : S≠X.V := by
      intro eq
      have aS : a.val∈S := by rw [eq]; exact a.property
      have aa := (mem_inN.mp (sub (sa aS))).2
      exact loopfree X.free (by omega) a.property aa
    exact X.prime S sv big proper
      ⟨BRsub.outUniform_inUniform X.free.reverse (SerialChain.sat_reverse X.sat) sv uniform,uniform⟩
  · obtain ⟨c,cs⟩ := sl
    obtain ⟨b,bp,cb,trail⟩ := out c (sa cs)
    have bv := (mem_inN.mp bp).1
    have ne : b≠c := fun eq => loopfree X.free (by omega) bv (eq ▸ cb)
    obtain ⟨d,dv,dc,db⟩ := X.separated c (sv cs) b bv ne
    have da : X.D d a=false := Bool.eq_false_iff.mpr (fun da => by
      have ds := fromP cs (mem_inN.mpr ⟨dv,da⟩) dc
      have eq : d=c := card_le_one.mp (by omega : S.card≤1) d ds c cs
      exact loopfree X.free (by omega) (sv cs) (eq ▸ dc))
    exact fail ⟨c,sa cs,b,bp,cb,trail,d,dv,dc,db,da⟩

/-- Re-rooting among parents cannot recur forever without an independent
    predecessor. The new top still reaches the original top inside P,
    and the fixed head reaches that predecessor in exactly q−1 steps. -/
theorem upstream_corridor {q n} (X : Model q n) (hq : 2≤q) {a b₀ c₀ : X.V}
    (ba : X.D b₀ a=true) (ca : X.D c₀ a=true) (cb : X.D c₀ b₀=true) :
    let P := inN X.D X.V a
    ∃c∈P,∃b∈P,X.D c b=true ∧ ((c=c₀.val ∧ b=b₀.val) ∨ ∃l,Walk X.D P b c₀ l) ∧ ∃d∈X.V,
      X.D d c=true ∧ X.D d b=false ∧ X.D d a=false ∧
      Walk X.D ((X.V.erase a.val)\inN X.D (X.V.erase a.val) a) a d (q-1) := by
  classical
  intro P
  let A := P.filter (fun c => ∃l,Walk X.D P c c₀ l)
  have cp : c₀.val∈P := mem_inN.mpr ⟨c₀.property,ca⟩
  have bp : b₀.val∈P := mem_inN.mpr ⟨b₀.property,ba⟩
  have seed : c₀.val∈A := mem_filter.mpr ⟨cp,0,.refl _⟩
  have pred (x) (xa : x∈A) (y) (yp : y∈P) (edge : X.D y x=true) : y∈A := by
    obtain ⟨xp,k,path⟩ := mem_filter.mp xa
    exact mem_filter.mpr ⟨yp,k+1,.step xp edge path⟩
  have next (x) (xa : x∈A) : ∃y∈P,X.D x y=true ∧ (y∈A ∨ x=c₀.val ∧ y=b₀.val) := by
    obtain ⟨_,k,path⟩ := mem_filter.mp xa
    cases path with
    | refl => exact ⟨b₀,bp,cb,Or.inr ⟨rfl,rfl⟩⟩
    | step yp ed tail => exact ⟨_,yp,ed,Or.inl (mem_filter.mpr ⟨yp,_,tail⟩)⟩
  obtain ⟨c,cc,b,bp',ed,trail,d,dv,dc,db,da⟩ := distinguish_in_parents X hq (a:=a)
    (A:=A) (filter_subset _ _) ⟨c₀,seed⟩ pred next
  have fromA (y) (yv : y∈X.V) (off : X.D y a=false) := X.sat _ a.property y yv (Bool.eq_false_iff.mp off)
  have pc := (mem_filter.mp cc).1
  refine ⟨c,pc,b,bp',ed,?_,d,dv,dc,db,da,return_corridor hq X.free fromA a.property dv da
    ⟨c,(mem_inN.mp pc).1,dc,(mem_inN.mp pc).2⟩⟩
  exact trail.elim (fun ba => Or.inr (mem_filter.mp ba).2) Or.inl

#print axioms upstream_corridor
#print axioms distinguish_in_parents
#print axioms reversed_family
#print axioms all_corners
#print axioms corridor_cut
#print axioms split_obstruction
end LeanCH.BR.Closure.TwoReceiverIntersection
