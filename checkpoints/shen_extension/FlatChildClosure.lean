import checkpoints.shen_extension.RawTransferBill
import LeanCH.BR.BRUnitCoreExtensionGeometry

namespace LeanCH.BR.Closure.FlatChildClosure
open Finset Matrix BRq2 BRq3 BR45 BRsub WeightedSD
open scoped Matrix

/-- Positive mass at every label turns equality in an averaged column bound
into equality at each column. -/
private theorem all_tight {U : Finset ℕ} {w f : ℕ → ℝ}
    (pos : ∀ i ∈ U, 0 < w i) (cap : ∀ i ∈ U, f i ≤ 1)
    (eq : (∑ i ∈ U, w i * f i) = realMass U w) : ∀ i ∈ U, f i = 1 := by
  intro i hi
  apply le_antisymm (cap i hi)
  by_contra! low
  have lt := sum_lt_sum (s := U)
    (f := fun j => w j * f j) (g := w)
    (fun j hj => by simpa using mul_le_mul_of_nonneg_left (cap j hj) (pos j hj).le)
    ⟨i, hi, by simpa using mul_lt_mul_of_pos_left low (pos i hi)⟩
  exact lt.ne eq

private theorem unique_columns {q : ℕ} (hq : 2 ≤ q) {E : CH.Digraph}
    {U : Finset ℕ} {p r : ℕ → ℝ}
    (eq : ∀ i ∈ U, realCol q E U r i = realCol q E U p i) :
    ∀ i ∈ U, r i = p i := by
  let A := WeightedArithmetic.rationalMatrix q (adjacencyMatrix E U)
  have unit : IsUnit (realMatrix q E U) := by
    apply (Matrix.isUnit_iff_isUnit_det _).mpr
    apply isUnit_iff_ne_zero.mpr
    change ((Rat.castHom ℝ).mapMatrix A).det ≠ 0
    rw [← RingHom.map_det]
    change (A.det : ℝ) ≠ 0
    exact_mod_cast WeightedArithmetic.rational_det_ne_zero hq _
  have e : (fun i : ↥U => r i) ᵥ* realMatrix q E U =
      (fun i : ↥U => p i) ᵥ* realMatrix q E U := by
    funext i
    exact (realMatrix_col q E U r i).trans ((eq i i.property).trans (realMatrix_col q E U p i).symm)
  intro i hi
  exact congrFun (Matrix.vecMul_injective_iff_isUnit.mpr unit e) ⟨i,hi⟩

/-- A proper child with flat columns has a positive row equalizer. Every
admissible column certificate on that child agrees with the original one. -/
theorem rigidity {q N : ℕ} (hq : 2 ≤ q) (small : SmallerSmallRow q N)
    {E : CH.Digraph} {U : Finset ℕ} (size : U.card < N) (free : QFree E U q)
    (live : U.Nonempty) {p : ℕ → ℝ} (hp : RealDual q E U 1 p)
    (flat : ∀ i ∈ U, realCol q E U p i = 1) :
    ∃ z : ℕ → ℝ, realMass U z = 1 ∧ (∀ i ∈ U, 0 < z i) ∧
      (∀ i ∈ U, realRow q E U z i = 1) ∧
      ∀ r : ℕ → ℝ, RealDual q E U 1 r → ∀ i ∈ U, r i = p i := by
  obtain ⟨z,hz⟩ := realDual_of_smallRow (small _ U size free.reverse) live
  have pp := real_unit_columns_positive hq p hp.nonneg flat
  have cap (i) (hi : i ∈ U) : realRow q E U z i ≤ 1 := hz.columns i hi
  have balance := real_cross_rows q E U z p
  have rows := all_tight pp cap (by
    rw [balance, sum_congr rfl (fun i hi => by rw [flat i hi, mul_one])]
    exact hz.normalized.trans hp.normalized.symm)
  have zp := real_unit_columns_positive (D := fun i j => E j i) hq z hz.nonneg rows
  refine ⟨z,hz.normalized,zp,rows,?_⟩
  intro r hr
  apply unique_columns hq
  have rc := all_tight zp hr.columns (by
    rw [← real_cross_rows, sum_congr rfl (fun i hi => by rw [rows i hi,mul_one])]
    exact hr.normalized.trans hz.normalized.symm)
  intro i hi
  exact (rc i hi).trans (flat i hi).symm

/-- At a flat child, an additional short-cycle-free arc on its labels is
impossible. This holds for the particular law already used on the orbit. -/
theorem saturated {q N : ℕ} (hq : 2 ≤ q) (small : SmallerSmallRow q N)
    {E : CH.Digraph} {U : Finset ℕ} (size : U.card < N) (free : QFree E U q)
    (live : U.Nonempty) {p : ℕ → ℝ} (hp : RealDual q E U 1 p)
    (flat : ∀ i ∈ U, realCol q E U p i = 1) : Sat q E U := by
  obtain ⟨_,_,_,_,unique⟩ := rigidity hq small size free live hp flat
  intro j hj i hi missing
  by_contra far
  let F := insertArc E i j
  have safe := qfree_insertArc free (⟨i,hi⟩ : ↥U) ⟨j,hj⟩ far
  obtain ⟨r,hr⟩ := realDual_of_smallRow (small F U size safe) live
  have term (k t : ℕ) (hk : k ∈ U) :
      (if E k t = true then r k else 0) ≤ (if F k t = true then r k else 0) := by
    by_cases ed : E k t = true
    · simp [ed,show F k t = true from insertArc_mono E i j k t ed]
    · by_cases fd : F k t = true <;> simp [ed,fd,(hr.nonneg k hk)]
  have leCol (t) : realCol q E U r t ≤ realCol q F U r t := by
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
      (sum_le_sum (fun k hk => term k t hk)) (Nat.cast_nonneg q : (0 : ℝ) ≤ q))
  have same := unique r ⟨hr.nonneg,hr.normalized,fun t ht => (leCol t).trans (hr.columns t ht)⟩
  have rp : 0 < r i := (same i hi).symm ▸ real_unit_columns_positive hq p hp.nonneg flat i hi
  have gain : realInW E U r j < realInW F U r j :=
    sum_lt_sum (fun k hk => term k j hk) ⟨i,hi,by simp [F,insertArc,missing,rp]⟩
  have old : realCol q E U r j = 1 := by
    rw [← flat j hj]
    unfold realCol realInW
    rw [same j hj, sum_congr rfl (fun k hk => by rw [same k hk])]
  have gt := mul_lt_mul_of_pos_left gain (show (0:ℝ)<q by exact_mod_cast (show 0<q by omega))
  have rise : realCol q E U r j < realCol q F U r j := add_lt_add_of_le_of_lt le_rfl gt
  exact (hr.columns j hj).not_gt (old ▸ rise)

/-- A heavy set of heads for the row law reaches every heavy set of parents
for the column law in at most q−2 steps, provided one extra label still
fits below the induction order. The two laws may be different. -/
theorem heavy_return {q N v : ℕ} (hq : 2 ≤ q) (small : SmallerSmallRow q N)
    {E : CH.Digraph} {U I O : Finset ℕ} (free : QFree E U q)
    (fresh : v ∉ U) (room : (insert v U).card < N) (ins : I ⊆ U) (outs : O ⊆ U)
    {p z : ℕ → ℝ} (hp : RealDual q E U 1 p) (flat : ∀ i ∈ U, realCol q E U p i = 1)
    (zm : realMass U z = 1) (zp : ∀ i ∈ U, 0 < z i) (rows : ∀ i ∈ U, realRow q E U z i = 1)
    (outHeavy : 1 < (q:ℝ)*realMass O z) (inHeavy : 1 < (q:ℝ)*realMass I p) :
    ∃ o ∈ O, ∃ i ∈ I, ∃ k ≤ q-2, Walk E U o i k := by
  classical
  by_contra no
  let F := coreTwoSidedExtension E U I O v
  have safe : QFree F (insert v U) q := coreTwoSidedExtension_qfree fresh ins free
    (fun o ho i hi k hk path => no ⟨o,ho,i,hi,k,hk,path⟩)
  obtain ⟨r,hr⟩ := realDual_of_smallRow (small F _ room safe) (insert_nonempty v U)
  have old {i j} (hi : i ∈ U) (hj : j ∈ U) : F i j = E i j := by
    have iv : i ≠ v := fun h => fresh (h ▸ hi)
    have jv : j ≠ v := fun h => fresh (h ▸ hj)
    simp [F,coreTwoSidedExtension,coreOutgoingExtension,hi,hj,iv,jv]
  have new_out {j} (hj : j ∈ U) : F v j = true ↔ j ∈ O := by
    have jv : j ≠ v := fun h => fresh (h ▸ hj)
    simp [F,coreTwoSidedExtension,coreOutgoingExtension,hj,jv,fresh]
  have new_in {i} (hi : i ∈ U) : F i v = true ↔ i ∈ I := by
    simp [F,coreTwoSidedExtension,coreOutgoingExtension,fresh]
  have interior (i) (hi : i ∈ U) :
      realCol q F (insert v U) r i = realCol q E U r i +
        (q:ℝ)*(if i ∈ O then r v else 0) := by
    unfold realCol realInW
    rw [sum_insert fresh, if_congr (new_out hi) rfl rfl,
      sum_congr rfl (fun j hj => by rw [old hj hi])]
    ring
  have extMass : r v + realMass U r = 1 := by
    simpa only [realMass, sum_insert fresh] using hr.normalized
  have aggregate := sum_le_sum (s := U) (fun i hi =>
    mul_le_mul_of_nonneg_left (hr.columns i (mem_insert_of_mem hi)) (zp i hi).le)
  have cost : (∑ i ∈ U, z i * ((q:ℝ) * (if i ∈ O then r v else 0))) =
      (q:ℝ)*realMass O z*r v := by
    have cut : U.filter (· ∈ O) = O := by ext i; simp [and_iff_right_of_imp (fun h => outs h)]
    simp only [mul_ite, mul_zero]
    rw [← sum_filter,cut,realMass,← sum_mul]
    ring
  have avg : (∑ i ∈ U,z i*realCol q E U r i) = realMass U r := by
    rw [← real_cross_rows, sum_congr rfl (fun i hi => by rw [rows i hi,mul_one])]
    rfl
  have split (i) (hi : i ∈ U) : z i * realCol q F (insert v U) r i =
      z i * realCol q E U r i + z i * ((q:ℝ) * (if i ∈ O then r v else 0)) := by
    rw [interior i hi,mul_add]
  rw [sum_congr rfl split,sum_add_distrib,avg,cost] at aggregate
  simp only [mul_one] at aggregate
  change realMass U r + (q:ℝ)*realMass O z*r v ≤ realMass U z at aggregate
  have rv : r v = 0 := by
    apply le_antisymm _ (hr.nonneg v (mem_insert_self _ _))
    by_contra! pos
    nlinarith only [aggregate,zm,extMass,mul_pos (sub_pos.mpr outHeavy) pos]
  have cap (i) (hi : i ∈ U) : realCol q E U r i ≤ 1 := by
    simpa [interior i hi,rv] using hr.columns i (mem_insert_of_mem hi)
  have rm : realMass U r = 1 := by simpa [rv] using extMass
  have live : U.Nonempty := by
    by_contra! empty
    simp [empty,realMass] at zm
  have less : U.card < N := (card_le_card (subset_insert v U)).trans_lt room
  obtain ⟨_,_,_,_,unique⟩ := rigidity hq small less free live hp flat
  have same := unique r ⟨fun i hi => hr.nonneg i (mem_insert_of_mem hi),rm,cap⟩
  have inSum : realInW F (insert v U) r v = realMass I p := by
    unfold realInW realMass
    rw [sum_insert fresh]
    simp only [rv,ite_self,zero_add]
    rw [sum_congr rfl (fun i hi => by rw [if_congr (new_in hi) rfl rfl, same i hi]),
      ← sum_filter]
    congr 1
    ext i
    simp [and_iff_right_of_imp (fun h => ins h)]
  have bound := hr.columns v (mem_insert_self _ _)
  unfold realCol at bound
  rw [rv,inSum,zero_add] at bound
  exact inHeavy.not_ge bound

private theorem heavy_omission {q : ℕ} {E : CH.Digraph} {V U : Finset ℕ}
    (sub : U ⊆ V) {x p : ℕ → ℝ} {c : ℝ} (high : 1 < c)
    (xn : ∀ i ∈ V, 0 ≤ x i) (xm : realMass V x = 1)
    (rows : ∀ i ∈ V, realRow q E V x i = c)
    (pm : realMass U p = 1) (flat : ∀ j ∈ U, realCol q E U p j = 1) :
    ∃ j ∈ V \ U, 1 < (q:ℝ) * realInW E U p j := by
  by_contra! none
  let r := maskReal U p
  have cap (i) (hi : i ∈ V) : realCol q E V r i ≤ 1 := by
    by_cases hu : i ∈ U
    · rw [show realCol q E V r i = _ from maskReal_col sub p hu,flat i hu]
    · simpa [r,realCol,maskReal_inW sub,maskReal,hu] using none i (mem_sdiff.mpr ⟨hi,hu⟩)
  have paid := sum_le_sum (s := V) (fun i hi => mul_le_mul_of_nonneg_left (cap i hi) (xn i hi))
  rw [← real_cross_rows, sum_congr rfl (fun i hi => by rw [rows i hi]), ← sum_mul] at paid
  simp only [mul_one] at paid
  change realMass V r * c ≤ realMass V x at paid
  rw [maskReal_mass sub,pm,one_mul,xm] at paid
  exact high.not_ge paid

/-- On the capstone's strict source a flat child with two or more omissions
has two distinct omitted vertices. Any heavy sender and any heavy receiver
are linked through the surviving labels. -/
theorem on_child {q : ℕ} (hq : 2 ≤ q) {E : CH.Digraph} {V U : Finset ℕ}
    (small : SmallerSmallRow q V.card) (free : QFree E V q) (sub : U ⊆ V)
    (room : U.card+1 < V.card) (live : U.Nonempty)
    {x s p : ℕ → ℝ} {c : ℝ} (high : 1 < c)
    (xn : ∀ i ∈ V, 0 ≤ x i) (xm : realMass V x = 1)
    (sn : ∀ i ∈ V, 0 ≤ s i) (sm : realMass V s = 1)
    (rows : ∀ i ∈ V, realRow q E V x i = c)
    (cols : ∀ i ∈ V, realCol q E V s i = c)
    (hp : RealDual q E U 1 p) (flat : ∀ i ∈ U, realCol q E U p i = 1) :
    ∃ z : ℕ → ℝ, realMass U z = 1 ∧ (∀ i ∈ U, 0 < z i) ∧
      (∀ i ∈ U, realRow q E U z i = 1) ∧
      (∃ a ∈ V \ U, 1 < (q:ℝ) * realOutW E U z a) ∧
      (∃ b ∈ V \ U, 1 < (q:ℝ) * realInW E U p b) ∧
      ∀ a ∈ V \ U, ∀ b ∈ V \ U, 1 < (q:ℝ) * realOutW E U z a →
        1 < (q:ℝ) * realInW E U p b → a ≠ b ∧
        ∃ o ∈ outN E U a, ∃ i ∈ inN E U b, ∃ k ≤ q-2, Walk E U o i k := by
  have uf := free.mono_set sub
  obtain ⟨z,zm,zp,zrows,_⟩ := rigidity hq small (by omega) uf live hp flat
  have outgoing := heavy_omission (E := fun i j => E j i) sub high sn sm cols zm zrows
  have incoming := heavy_omission sub high xn xm rows hp.normalized flat
  refine ⟨z,zm,zp,zrows,outgoing,incoming,?_⟩
  intro a ha b hb ao bi
  have fresh := (mem_sdiff.mp ha).2
  have size : (insert a U).card < V.card := by rwa [card_insert_of_notMem fresh]
  have oHeavy : 1 < (q:ℝ)*realMass (outN E U a) z := by
    simpa only [realMass,outN,sum_filter,realOutW] using ao
  have iHeavy : 1 < (q:ℝ)*realMass (inN E U b) p := by
    simpa only [realMass,inN,sum_filter,realInW] using bi
  have route := heavy_return hq small uf fresh size
    (filter_subset _ _) (filter_subset _ _) hp flat zm zp zrows oHeavy iHeavy
  refine ⟨?_, route⟩
  obtain ⟨o,ho,i,hi,k,hk,path⟩ := route
  rintro rfl
  have tail : Walk E V i a 1 := .step (mem_sdiff.mp ha).1 (mem_inN.mp hi).2 (.refl _)
  have start : Walk E V a i (k+1) := .step (sub (mem_outN.mp ho).1) (mem_outN.mp ho).2 (path.mono sub)
  exact free a _ (by omega) (by omega) (start.append tail)

#print axioms rigidity
#print axioms saturated
#print axioms heavy_return
#print axioms on_child
end LeanCH.BR.Closure.FlatChildClosure
