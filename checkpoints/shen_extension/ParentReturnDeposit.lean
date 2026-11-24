import checkpoints.shen_extension.OneParentReroot
import checkpoints.shen_extension.EqualizerTransfer
import LeanCH.BR.BRWeightedSplitTransfer

namespace LeanCH.BR.Closure.ParentReturnDeposit
open Finset BRq2 BRq3 BR45 WeightedSD LabelledLeakageCapacity

/-- A singleton column of a separated native graph forces its parent's row
to be a singleton too. This bound is independent of how the root was found. -/
theorem singleton_heavy {q n b p w c} (X : ShortestCycleWeights.Model q n) (bv : b∈X.V)
    (one : inN X.D X.V b={p}) (high : 1<c)
    (rows : ∀i∈X.V,WeightedSD.row q X.D X.V w i=c) :
    outN X.D X.V p={b} ∧ w p+(q:ℚ)*w b=c ∧ 1<((q:ℚ)+1)*max (w p) (w b) := by
  have par : p∈inN X.D X.V b := one ▸ mem_singleton_self p
  have pv := (mem_inN.mp par).1
  have pb := (mem_inN.mp par).2
  have heads : outN X.D X.V p={b} := by
    refine Subset.antisymm (fun t th=>mem_singleton.mpr ?_) (singleton_subset_iff.mpr (mem_outN.mpr ⟨bv,pb⟩))
    by_contra ne
    obtain ⟨i,iv,ib,it⟩ := X.separated b bv t (outN_subset th) ne
    have eq : i=p := mem_singleton.mp (one ▸ mem_inN.mpr ⟨iv,ib⟩)
    exact Bool.noConfusion ((eq ▸ it).symm.trans (mem_outN.mp th).2)
  have row : w p+(q:ℚ)*w b=c := by simpa [WeightedSD.row,outW_eq_mass,heads,mass] using rows p pv
  refine ⟨heads,row,?_⟩
  linarith only [high,row,le_max_left (w p) (w b),
    mul_le_mul_of_nonneg_left (le_max_right (w p) (w b)) (Nat.cast_nonneg q : (0:ℚ)≤q)]

/-- Moving all of b's weight to its parent's named return t on V.erase b
pays p. The strict failures are exactly the surviving parents missing t. -/
theorem transfer {q E V b p t w c} (hq : 2≤q) (free : QFree E V q)
    (small : SmallerSmallRow q V.card) (bv : b∈V) (par : p∈inN E V b)
    (tr : t∈region q E V b) (pt : E p t=true)
    (sat : BRsub.Sat q E V) (wp : ∀i∈V,0≤w i) (high : mass V w<c)
    (rows : ∀i∈V,WeightedSD.row q E V w i=c) :
    let U := V.erase b
    let z := transferWeight w b t
    mass U z=mass V w ∧ mass U z<WeightedSD.row q E U z p ∧
      ∀i∈U,(WeightedSD.row q E U z i<mass U z ↔ i∈inN E V b \ inN E V t) ∧
        (mass U z<WeightedSD.row q E U z i ↔ i∉inN E V b \ inN E V t) := by
  intro U z
  have tv : t∈V := BRsub.ballSet_subset tr
  have ne := ((saturated_region hq free sat bv tv).mp tr).1
  have info (i) (iv : i∈U) := EqualizerTransfer.classify hq free small wp high rows bv tv ne.symm iv
  have pu : p∈U := mem_erase.mpr ⟨fun eq=>loopfree free (by omega) bv (eq ▸ (mem_inN.mp par).2),(mem_inN.mp par).1⟩
  refine ⟨mass_transfer bv tv ne.symm w,(info p pu).2.mpr (fun h=>Bool.noConfusion (pt.symm.trans h.2)),?_⟩
  intro i iu
  simpa [mem_inN,mem_of_mem_erase iu] using info i iu

/-- A fractional deposit g restoring every parent's lost head mass on the
puncture must cost strictly more than the removed weight plus native slack.
At a positive deposit label the diagonal term makes the inequality strict. -/
theorem cover_cost {q E V b w c} (hq : 2≤q) (proper : SmallRow q E (V.erase b))
    (bv : b∈V) (wp : ∀i∈V,0<w i) (rows : ∀i∈V,c≤WeightedSD.row q E V w i)
    (g : ℕ→ℚ) (nn : ∀i∈V.erase b,0≤g i) (live : ∃t∈V.erase b,0<g t)
    (cover : ∀i∈inN E V b, i≠b → w b≤outW E (V.erase b) g i) :
    c-mass V w+w b<mass (V.erase b) g := by
  classical
  let U := V.erase b
  let z := fun i=>w i+g i
  have positive : ∀i∈U,0<z i := fun i iu=>add_pos_of_pos_of_nonneg (wp i (mem_of_mem_erase iu)) (nn i iu)
  have price : mass U z=mass V w-w b+mass U g := by
    rw [show mass U z=mass U w+mass U g from mass_add_weights U w g]
    have eq : mass U w+w b=mass V w := sum_erase_add _ _ bv
    linarith
  have lower (i) (iu : i∈U) : c+g i≤WeightedSD.row q E U z i := by
    have old := rows i (mem_of_mem_erase iu)
    rw [WeightedSD.row,outW_erase bv] at old
    have sum : outW E U z i=outW E U w i+outW E U g i := by
      simp only [outW_eq_mass,z,mass_add_weights]
    rw [WeightedSD.row,sum]
    have funds : (if E i b=true then w b else 0)≤outW E U g i := by
      split_ifs with edge
      · exact cover i (mem_inN.mpr ⟨mem_of_mem_erase iu,edge⟩) (mem_erase.mp iu).1
      · rw [outW_eq_mass]; exact mass_nonneg (fun j hj=>nn j (outN_subset hj))
    dsimp only [z]
    linarith only [old,mul_le_mul_of_nonneg_left funds (Nat.cast_nonneg q : (0:ℚ)≤q)]
  by_contra! low
  have cheap : mass U z≤c := by linarith only [price,low]
  have tight := positive_feasible_rows_tight_of_smallRow hq proper z positive (fun i iu=>
    cheap.trans ((le_add_of_nonneg_right (nn i iu)).trans (lower i iu)))
  obtain ⟨t,tu,tp⟩ := live
  linarith only [tight t tu,cheap,lower t tu,tp]

/-- Give each label of an actual cover one copy of the removed weight. -/
theorem finite_cover {q E V b w c} (hq : 2≤q) (proper : SmallRow q E (V.erase b))
    (bv : b∈V) (wp : ∀i∈V,0<w i) (rows : ∀i∈V,c≤WeightedSD.row q E V w i)
    {K : Finset ℕ} (sub : K⊆V.erase b) (live : K.Nonempty)
    (cover : ∀i∈inN E V b, i≠b → ∃t∈K,E i t=true) :
    c-mass V w<((K.card:ℚ)-1)*w b := by
  classical
  let g := fun i=>if i∈K then w b else 0
  have gn (i) : 0≤g i := by dsimp [g]; split_ifs <;> linarith [wp b bv]
  obtain ⟨t,tk⟩ := live
  have hit (i) (ib : i∈inN E V b) (ne : i≠b) : w b≤outW E (V.erase b) g i := by
    obtain ⟨j,jk,ij⟩ := cover i ib ne
    rw [outW_eq_mass]
    have entry : j∈outN E (V.erase b) i := mem_outN.mpr ⟨sub jk,ij⟩
    simpa only [mass,show g j=w b from by simp [g,jk]] using (single_le_sum (f:=g) (fun k _=>gn k) entry)
  have paid := cover_cost hq proper bv wp rows g (fun i _=>gn i)
    ⟨t,sub tk,by simpa [g,tk] using wp b bv⟩ hit
  have cost : mass (V.erase b) g=K.card*w b := by
    simp only [mass,g,←sum_filter,filter_mem_eq_inter,inter_eq_right.mpr sub,sum_const,nsmul_eq_mul]
  linarith only [paid,cost]

/-- At a two-parent return root, the other parent is the unique deficient
row after a full transfer to t; depositing at both returns bounds the slack. -/
theorem two_parents {q n b p y t w c} (X : ShortestCycleWeights.Model q n)
    (hq : 2≤q) (small : SmallerSmallRow q X.V.card) (bv : b∈X.V)
    (parents : inN X.D X.V b={p,y})
    (backs : ∀i∈inN X.D X.V b,∃u∈region q X.D X.V b,X.D i u=true)
    (tr : t∈region q X.D X.V b) (pt : X.D p t=true)
    (wp : ∀i∈X.V,0<w i) (high : mass X.V w<c) (rows : ∀i∈X.V,WeightedSD.row q X.D X.V w i=c) :
    let U := X.V.erase b
    let z := transferWeight w b t
    c-mass X.V w<w b ∧ WeightedSD.row q X.D U z p=c ∧ WeightedSD.row q X.D U z y=c-q*w b ∧
      (∀i∈U,(WeightedSD.row q X.D U z i<mass U z ↔ i=y) ∧
      (mass U z<WeightedSD.row q X.D U z i ↔ i≠y)) := by
  intro U z
  have pp : p∈inN X.D X.V b := parents ▸ mem_insert_self _ _
  have yp : y∈inN X.D X.V b := parents ▸ mem_insert_of_mem (mem_singleton_self y)
  obtain ⟨k,kp,kne,kt⟩ := OneParentReroot.other_parent X hq bv tr pt
  have ky : k=y := (mem_insert.mp (parents ▸ kp)).resolve_left kne |> mem_singleton.mp
  subst k
  obtain ⟨u,ur,yu⟩ := backs y yp
  have tu : t≠u := fun eq=>Bool.noConfusion ((eq ▸ kt).symm.trans yu)
  have inside {j} (jr : j∈region q X.D X.V b) : j∈U := by
    have jv : j∈X.V := BRsub.ballSet_subset jr
    exact mem_erase.mpr ⟨((saturated_region hq X.free X.sat bv jv).mp jr).1,jv⟩
  have cost := finite_cover hq (small _ _ (card_erase_lt_of_mem bv) (X.free.mono_set (erase_subset _ _)))
    bv wp (fun i iv=>(rows i iv).ge) (K:={t,u}) (insert_subset (inside tr) (singleton_subset_iff.mpr (inside ur)))
    ⟨t,mem_insert_self _ _⟩ (by
      intro i ip _
      rcases mem_insert.mp (parents ▸ ip) with rfl|iy
      · exact ⟨t,mem_insert_self _ _,pt⟩
      · obtain rfl := mem_singleton.mp iy; exact ⟨u,mem_insert_of_mem (mem_singleton_self _),yu⟩)
  obtain ⟨_,_,classified⟩ := transfer hq X.free small bv pp tr pt X.sat (fun i iv=>(wp i iv).le) high rows
  have only : inN X.D X.V b \ inN X.D X.V t={y} := by
    ext i
    simp only [parents,mem_sdiff,mem_insert,mem_singleton]
    constructor
    · rintro ⟨rfl|e,miss⟩
      · exact (miss (mem_inN.mpr ⟨(mem_inN.mp pp).1,pt⟩)).elim
      · exact e
    · rintro rfl; exact ⟨Or.inr rfl,fun h=>Bool.noConfusion (kt.symm.trans (mem_inN.mp h).2)⟩
  have tmiss := ((saturated_region hq X.free X.sat bv (BRsub.ballSet_subset tr)).mp tr).2
  have account (i) (ip : i∈inN X.D X.V b) :
      WeightedSD.row q X.D U z i=c-(q:ℚ)*w b+q*(if X.D i t=true then w b else 0) := by
    have ne : i≠t := fun eq=>tmiss (eq ▸ (mem_inN.mp ip).2)
    have old := rows i (mem_inN.mp ip).1
    rw [WeightedSD.row,outW_erase bv] at old
    simp only [(mem_inN.mp ip).2,ite_true] at old
    dsimp only [z]
    rw [WeightedSD.row,outW_transfer (inside tr)]
    simp only [transferWeight,ne,ite_false,add_zero,U]
    linarith only [old]
  refine ⟨by norm_num [card_pair tu] at cost; exact cost,?_,?_,fun i iu=>by simpa [only] using classified i iu⟩
  · simpa [pt] using account p pp
  · simpa [kt] using account y yp

#print axioms singleton_heavy
#print axioms transfer
#print axioms cover_cost
#print axioms finite_cover
#print axioms two_parents

/-- On the two-parent puncture their remaining head sets are disjoint.
Every nonnegative redistribution of the deleted mass leaves a quantitative
joint deficit at these same two rows. -/
theorem split_deficit {q n b p y w c} (X : ShortestCycleWeights.Model q n)
    (hq : 3≤q) (bv : b∈X.V) (parents : inN X.D X.V b={p,y}) (ne : p≠y)
    (wb : 0<w b) (rows : ∀i∈X.V,WeightedSD.row q X.D X.V w i=c)
    (slack : c-mass X.V w<w b) (g : ℕ→ℚ)
    (gn : ∀i∈X.V.erase b,0≤g i) (budget : mass (X.V.erase b) g=w b) :
    let U := X.V.erase b
    let z := fun i=>w i+g i
    let deficit := fun i=>mass U z-WeightedSD.row q X.D U z i
    Disjoint (outN X.D U p) (outN X.D U y) ∧ mass U z=mass X.V w ∧
      ((q:ℚ)-1)*w b-2*(c-mass X.V w) ≤ deficit p+deficit y ∧
      0<((q:ℚ)-1)*w b-2*(c-mass X.V w) := by
  intro U z deficit
  have pp : p∈inN X.D X.V b := parents ▸ mem_insert_self _ _
  have yp : y∈inN X.D X.V b := parents ▸ mem_insert_of_mem (mem_singleton_self y)
  have survives {i} (par : i∈inN X.D X.V b) : i∈U :=
    mem_erase.mpr ⟨fun eq=>loopfree X.free (by omega) bv (eq ▸ (mem_inN.mp par).2),(mem_inN.mp par).1⟩
  have dis : Disjoint (outN X.D U p) (outN X.D U y) := by
    apply disjoint_left.mpr
    intro j jp jy
    obtain ⟨i,iv,ib,ij⟩ := X.separated b bv j (mem_of_mem_erase (outN_subset jp)) (mem_erase.mp (outN_subset jp)).1
    have ip : i∈({p,y}:Finset ℕ) := parents ▸ mem_inN.mpr ⟨iv,ib⟩
    rcases mem_insert.mp ip with rfl|eq
    · exact Bool.noConfusion (ij.symm.trans (mem_outN.mp jp).2)
    · obtain rfl := mem_singleton.mp eq
      exact Bool.noConfusion (ij.symm.trans (mem_outN.mp jy).2)
  have heads : outW X.D U g p+outW X.D U g y≤w b := by
    rw [outW_eq_mass,outW_eq_mass,←budget]
    change (∑ j∈_,g j)+(∑ j∈_,g j) ≤ _
    rw [←sum_union dis]
    exact mass_mono (union_subset outN_subset outN_subset) gn
  have diag : g p+g y≤w b := by
    rw [←budget,←sum_pair ne]
    exact mass_mono (insert_subset (survives pp) (singleton_subset_iff.mpr (survives yp))) gn
  have total : mass U z=mass X.V w := by
    rw [show mass U z=mass U w+mass U g from mass_add_weights U w g,budget]
    exact sum_erase_add _ _ bv
  have account (i) (par : i∈inN X.D X.V b) :
      WeightedSD.row q X.D U z i=c-q*w b+g i+q*outW X.D U g i := by
    have old := rows i (mem_inN.mp par).1
    rw [WeightedSD.row,outW_erase bv] at old
    simp only [(mem_inN.mp par).2,ite_true] at old
    have plus : outW X.D U z i=outW X.D U w i+outW X.D U g i := by simp only [outW_eq_mass,z,mass_add_weights]
    rw [WeightedSD.row,plus]; dsimp only [z,U]; linarith only [old]
  refine ⟨dis,total,?_,?_⟩
  · dsimp only [deficit]
    rw [account p pp,account y yp,total]
    linarith only [diag,mul_le_mul_of_nonneg_left heads (Nat.cast_nonneg q : (0:ℚ)≤q)]
  · have three : (3:ℚ)≤q := by exact_mod_cast hq
    linarith only [slack,mul_le_mul_of_nonneg_right three wb.le]

#print axioms split_deficit
end LeanCH.BR.Closure.ParentReturnDeposit
