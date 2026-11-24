import checkpoints.shen_extension.ParentReturnDeposit
import LeanCH.BR.BRWeightedRetainedHeadTransfer

namespace LeanCH.BR.Closure.TwoParentReturnPivot
open Finset BRq2 BRq3 BR45 WeightedSD LabelledLeakageCapacity

/-- The first heads on short returns from t to y in the surviving graph. -/
noncomputable def bank (q : ℕ) (E : CH.Digraph) (U : Finset ℕ) (t y : ℕ) : Finset ℕ :=
  (outN E U t).filter (fun h=>y∈ball E U h (q-2))

noncomputable def pivot (q : ℕ) (E : CH.Digraph) (U : Finset ℕ) (t y : ℕ) : CH.Digraph :=
  insertArc (bankKept E (bank q E U t y) t) y t

theorem legal {q E U t y} (hq : 2≤q) (free : QFree E U q) (tu : t∈U) (yu : y∈U)
    (ne : t≠y) : QFree (pivot q E U t y) U q := by
  let K := bankKept E (bank q E U t y) t
  have sub (i j) (ij : K i j=true) : E i j=true := (of_decide_eq_true ij).1
  apply qfree_insertArc (qfree_sub sub free) ⟨y,yu⟩ ⟨t,tu⟩
  intro ret
  obtain ⟨_,k,hk,path⟩ := mem_ball.mp ret
  cases path with
  | refl => exact ne rfl
  | @step _ h _ l hu th rest =>
    have inB : h∈bank q E U t y := mem_filter.mpr ⟨mem_outN.mpr ⟨hu,sub _ _ th⟩,
      mem_ball.mpr ⟨yu,l,by omega,walk_sub sub rest⟩⟩
    exact (of_decide_eq_true th).2 ⟨rfl,inB⟩

/-- Every legal edit that inserts y→t and only cuts at t must cut
every head in this bank. This supplies the converse to legality. -/
theorem necessary {q E U t y} (hq : 2≤q) (free : QFree E U q) (tu : t∈U)
    {G : CH.Digraph} (ok : QFree G U q) (new : G y t=true)
    (keeps : ∀i∈U,i≠t → ∀j∈U,E i j=true → G i j=true) :
    ∀h∈bank q E U t y,G t h=false := by
  intro h hb
  obtain ⟨oh,ret⟩ := mem_filter.mp hb
  obtain ⟨hu,th⟩ := mem_outN.mp oh
  have ht : h≠t := fun eq=>loopfree free (by omega) tu (eq ▸ th)
  obtain ⟨_,k,hk,suffix⟩ := mem_ball.mp ret
  rcases suffix.lastVisit t with avoid|⟨a,b,_,len,front,_⟩
  · have path := walk_mono_graph_on (D:=E) (E:=G) (K:=U.erase t)
      (fun i iv j jv ij=>keeps i (mem_of_mem_erase iv) (mem_erase.mp iv).1 j (mem_of_mem_erase jv) ij)
      avoid (mem_erase.mpr ⟨ht,hu⟩)
    cases edge : G t h
    · rfl
    · exact False.elim (ok t _ (by omega) (by omega)
        ((Walk.step hu edge (path.mono (erase_subset t U))).snoc tu new))
  · exact False.elim (free t _ (by omega) (by omega) (Walk.step hu th front))

/-- Exactly two rows change. The calculation also holds for signed weights. -/
theorem accounts {q E U t y} (tu : t∈U) (ne : t≠y) (miss : E y t=false) (z : ℕ→ℚ) :
    let B := bank q E U t y
    let G := pivot q E U t y
    WeightedSD.row q G U z t=WeightedSD.row q E U z t-q*mass B z ∧
    WeightedSD.row q G U z y=WeightedSD.row q E U z y+q*z t ∧
    ∀i,i≠t → i≠y → WeightedSD.row q G U z i=WeightedSD.row q E U z i := by
  intro B G
  have sub : B⊆outN E U t := filter_subset _ _
  have th : outN G U t=outN E U t \ B := by
    ext j
    simp [mem_outN,G,pivot,insertArc,bankKept,ne,B,and_assoc]
  have yh : outN G U y=insert t (outN E U y) := by
    ext j
    by_cases eq : j=t
    · subst j; simp [mem_outN,G,pivot,insertArc,tu]
    · simp [mem_outN,G,pivot,insertArc,bankKept,ne.symm,eq]
  have gone : mass (outN E U t \ B) z+mass B z=mass (outN E U t) z :=
    sum_sdiff sub
  have mt : t∉outN E U y := by simp [mem_outN,miss]
  refine ⟨?_,?_,?_⟩
  · simp only [WeightedSD.row,outW_eq_mass,th]
    linear_combination (q:ℚ)*gone
  · simp only [WeightedSD.row,outW_eq_mass,yh,mass,sum_insert mt]; ring
  · intro i it iy
    have eq : outN G U i=outN E U i := by ext j; simp [mem_outN,G,pivot,insertArc,bankKept,it,iy]
    simp only [WeightedSD.row,outW_eq_mass,eq]

/-- A retained head can receive all native slack. If its payment covered
t's remaining bill, y would be strictly paid on a positive feasible child. -/
theorem retained_bill {q G U t y} (hq : 2≤q) (proper : SmallRow q G U) (yu : y∈U)
    {z : ℕ→ℚ} (pos : ∀i∈U,0<z i) {c m bill : ℚ} (high : mass U z<c)
    (at_t : WeightedSD.row q G U z t=c+m-bill)
    (at_y : c<WeightedSD.row q G U z y) (other : ∀i∈U,i≠t → c≤WeightedSD.row q G U z i)
    (kept : (outN G U t).Nonempty) : m+q*(c-mass U z)<bill := by
  obtain ⟨u,uh⟩ := kept
  obtain ⟨uv,tu⟩ := mem_outN.mp uh
  let σ := c-mass U z
  have sp : 0≤σ := sub_nonneg.mpr high.le
  let f := addWeightAt z u σ
  have fp (i) (iv : i∈U) : 0<f i := by
    dsimp only [f,addWeightAt]; split_ifs <;> linarith [pos i iv]
  have total : mass U f=c := by rw [show f=addWeightAt z u σ from rfl,mass_addWeightAt uv]; dsimp [σ]; ring
  have increase (i) : WeightedSD.row q G U z i≤WeightedSD.row q G U f i := by
    rw [show f=addWeightAt z u σ from rfl,row_addWeightAt uv]
    split_ifs <;> nlinarith only [sp,mul_nonneg (Nat.cast_nonneg q : (0:ℚ)≤q) sp]
  by_contra! cheap
  have tight := positive_feasible_rows_tight_of_smallRow hq proper f fp (fun i iv=>by
    rw [total]
    by_cases it : i=t
    · subst i; rw [show f=addWeightAt z u σ from rfl,row_addWeightAt uv,at_t,ite_eq_left tu]
      change bill≤m+q*σ at cheap
      split_ifs <;> linarith
    · exact (other i iv it).trans (increase i))
  linarith only [tight y yu,total,at_y,increase y]

#print axioms legal
#print axioms accounts
#print axioms retained_bill

/-- Specialization to the native equalizer and its actual transferred
weights. With no retained head the bill is the entire original head weight. -/
theorem native {q n b p y t w c} (X : ShortestCycleWeights.Model q n) (hq : 2≤q)
    (small : SmallerSmallRow q X.V.card) (bv : b∈X.V) (parents : inN X.D X.V b={p,y})
    (tr : t∈region q X.D X.V b) (pt : X.D p t=true)
    (wp : ∀i∈X.V,0<w i) (high : mass X.V w<c) (rows : ∀i∈X.V,WeightedSD.row q X.D X.V w i=c) :
    let U := X.V.erase b
    let G := pivot q X.D U t y
    let z := transferWeight w b t
    let cost := (q:ℚ)*mass (bank q X.D U t y) w
    QFree G U q ∧ mass U z=mass X.V w ∧ WeightedSD.row q G U z p=c ∧
      WeightedSD.row q G U z y=c+q*w t ∧ WeightedSD.row q G U z t=c+w b-cost ∧
      (∀i∈U,i≠t → c≤WeightedSD.row q G U z i) ∧
      (w b+q*(c-mass X.V w)<cost ∨ (outN G U t=∅ ∧ cost=c-w t)) := by
  intro U G z cost
  have tv : t∈X.V := BRsub.ballSet_subset tr
  obtain ⟨tb,noBack⟩ := (saturated_region hq X.free X.sat bv tv).mp tr
  have tu : t∈U := mem_erase.mpr ⟨tb,tv⟩
  have parP : p∈inN X.D X.V b := parents ▸ mem_insert_self _ _
  have parY : y∈inN X.D X.V b := parents ▸ mem_insert_of_mem (mem_singleton_self _)
  have pu := (mem_inN.mp parP).1
  obtain ⟨yv,yb⟩ := mem_inN.mp parY
  have yu : y∈U := mem_erase.mpr ⟨fun eq=>loopfree X.free (by omega) bv (eq ▸ yb),yv⟩
  have ty : t≠y := fun eq=>noBack (eq ▸ yb)
  have tp : t≠p := fun eq=>noBack (eq ▸ (mem_inN.mp parP).2)
  obtain ⟨k,kp,kne,kt⟩ := OneParentReroot.other_parent X hq bv tr pt
  have ky : k=y := mem_singleton.mp ((mem_insert.mp (parents ▸ kp)).resolve_left kne)
  subst k
  have free := legal hq (X.free.mono_set (erase_subset b X.V)) tu yu ty
  have total : mass U z=mass X.V w := mass_transfer bv tv tb.symm w
  have old (i) (iv : i∈X.V) :
      WeightedSD.row q X.D U z i=c+(if i=t then w b else 0)+
        q*((if X.D i t=true then w b else 0)-(if X.D i b=true then w b else 0)) := by
    have e := rows i iv
    rw [WeightedSD.row,outW_erase bv] at e
    rw [WeightedSD.row,outW_transfer tu]
    dsimp only [z,transferWeight,U]
    linear_combination e
  have noLoop := loopfree X.free (by omega : 1≤q) tv
  have baseT := old t tv
  simp only [ite_true,ite_eq_right noLoop,ite_eq_right noBack,sub_self,mul_zero,add_zero] at baseT
  have baseY := old y yv
  simp [kt,yb,ty.symm] at baseY
  have baseP := old p pu
  simp [pt,(mem_inN.mp parP).2,tp.symm] at baseP
  obtain ⟨cut,add,same⟩ := accounts (q:=q) tu ty kt z
  have unchanged : mass (bank q X.D U t y) z=mass (bank q X.D U t y) w := by
    apply sum_congr rfl
    intro j jb
    have jt : j≠t := fun eq=>noLoop (eq ▸ (mem_outN.mp (mem_filter.mp jb).1).2)
    simp [z,transferWeight,jt]
  have atT : WeightedSD.row q G U z t=c+w b-cost := by simpa only [unchanged,baseT,cost] using cut
  have zt : z t=w t+w b := by simp [z,transferWeight]
  have atY : WeightedSD.row q G U z y=c+q*w t := by
    rw [baseY,zt] at add; linarith only [add]
  have atP := (same p tp.symm kne.symm).trans baseP
  have above : c<WeightedSD.row q G U z y := by
    rw [atY]; exact lt_add_of_pos_right _ (mul_pos (by exact_mod_cast (by omega : 0<q)) (wp t tv))
  have other (i) (iu : i∈U) (it : i≠t) : c≤WeightedSD.row q G U z i := by
    by_cases iy : i=y
    · exact iy ▸ above.le
    by_cases ip : i=p
    · exact ip ▸ atP.ge
    have no : X.D i b≠true := fun ib=>by
      have hits : i∈({p,y}:Finset ℕ) := parents ▸ mem_inN.mpr ⟨mem_of_mem_erase iu,ib⟩
      simp [ip,iy] at hits
    rw [same i it iy,old i (mem_of_mem_erase iu),ite_eq_right no,ite_eq_right it]
    split_ifs <;> nlinarith only [mul_nonneg (Nat.cast_nonneg q : (0:ℚ)≤q) (wp b bv).le]
  refine ⟨free,total,atP,atY,atT,other,?_⟩
  by_cases empty : outN G U t=∅
  · right; refine ⟨empty,?_⟩
    have bare : WeightedSD.row q G U z t=w t+w b := by
      simp [WeightedSD.row,outW_eq_mass,empty,mass,z,transferWeight]
    linarith only [bare,atT]
  · left
    have pos (i) (iu : i∈U) : 0<z i := by
      dsimp only [z,transferWeight]; split_ifs <;> linarith only [wp i (mem_of_mem_erase iu),wp b bv]
    rw [←total]
    exact retained_bill hq (small _ _ (card_erase_lt_of_mem bv) free)
      yu pos (total ▸ high) atT above other (nonempty_iff_ne_empty.mpr empty)

#print axioms necessary
#print axioms native
end LeanCH.BR.Closure.TwoParentReturnPivot
