import checkpoints.shen_extension.TwoParentReturnPivot

namespace LeanCH.BR.Closure.TwoParentOldWeight
open Finset BRq2 BRq3 BR45 WeightedSD LabelledLeakageCapacity TwoParentReturnPivot

/-- Withdraw μ at t and send μ plus the available slack to a retained
head u. Only parents of t that miss u need a reserve. -/
theorem transfer_bill {q G U t u} (hq : 2≤q) (free : QFree G U q) (proper : SmallRow q G U)
    (tv : t∈U) (uv : u∈U) (edge : G t u=true)
    {z : ℕ→ℚ} (zp : ∀i∈U,0<z i) {c m bill μ : ℚ} (high : mass U z<c) (mn : 0≤μ) (donor : μ<z t)
    (atT : WeightedSD.row q G U z t=c+m-bill)
    (other : ∀i∈U,i≠t → c≤WeightedSD.row q G U z i)
    (reserve : ∀i∈U,i≠t → G i t=true → G i u≠true → c+q*μ≤WeightedSD.row q G U z i) :
    m+q*(c-mass U z)+((q:ℚ)-1)*μ<bill := by
  let σ := c-mass U z
  let z' := addWeightAt z t (-μ)
  let f := addWeightAt z' u (σ+μ)
  have sp : 0<σ := sub_pos.mpr high
  have gain : 0<σ+μ := add_pos_of_pos_of_nonneg sp mn
  have qn : (0:ℚ)≤q := Nat.cast_nonneg _
  have tq : (0:ℚ)≤q*μ := mul_nonneg qn mn
  have sq := mul_nonneg qn sp.le
  have ne : t≠u := fun eq=>loopfree free (by omega) uv (eq ▸ edge)
  have no := loopfree free (by omega : 1≤q) tv
  have noBack := digonfree free hq tv uv edge
  have pos (i) (iv : i∈U) : 0<f i := by
    dsimp only [f,z',addWeightAt]
    by_cases eq : i=t
    · subst i; simp only [ite_true,ite_eq_right ne,add_zero]; linarith only [donor]
    · simp only [ite_eq_right eq,add_zero]; split_ifs <;> linarith only [zp i iv,gain]
  have total : mass U f=c := by
    dsimp only [f,z']; rw [mass_addWeightAt uv,mass_addWeightAt tv]; dsimp [σ]; ring
  have account (i) : WeightedSD.row q G U f i=
      WeightedSD.row q G U z i+(if i=t then -μ else 0)+q*(if G i t=true then -μ else 0)+
      (if i=u then σ+μ else 0)+q*(if G i u=true then σ+μ else 0) := by
    dsimp only [f,z']; rw [row_addWeightAt uv,row_addWeightAt tv]
  by_contra! cheap
  change bill≤m+q*σ+((q:ℚ)-1)*μ at cheap
  have feasible (i) (iv : i∈U) : mass U f≤WeightedSD.row q G U f i := by
    rw [total,account]
    by_cases it : i=t
    · subst i; simp only [ite_true,ite_eq_right no,ite_eq_right ne,ite_eq_left edge,atT]
      linarith only [cheap]
    have base := other i iv it
    rw [ite_eq_right it]
    by_cases iu : G i u=true
    · rw [ite_eq_left iu]; split_ifs <;> linarith only [base,tq,sq,gain]
    · rw [ite_eq_right iu]
      by_cases hit : G i t=true
      · have enough := reserve i iv it hit iu
        rw [ite_eq_left hit]; split_ifs <;> linarith only [enough,gain]
      · rw [ite_eq_right hit]; split_ifs <;> linarith only [base,gain]
  have tight := positive_feasible_rows_tight_of_smallRow hq proper f pos feasible u uv
  rw [total,account,ite_eq_right ne.symm,ite_eq_right noBack,ite_eq_left (rfl : u=u),
    ite_eq_right (loopfree free (by omega) uv)] at tight
  linarith only [tight,other u uv ne.symm,gain]

/-- An actual common head retained by p and t permits a positive
withdrawal of old t-weight in the exact two-parent transfer. -/
theorem native_withdrawal {q n b p y t u w c} (X : ShortestCycleWeights.Model q n) (hq : 2≤q)
    (small : SmallerSmallRow q X.V.card) (bv : b∈X.V) (parents : inN X.D X.V b={p,y})
    (tr : t∈region q X.D X.V b) (pt : X.D p t=true)
    (wp : ∀i∈X.V,0<w i) (high : mass X.V w<c) (rows : ∀i∈X.V,WeightedSD.row q X.D X.V w i=c)
    (kept : u∈outN X.D (X.V.erase b) t \ bank q X.D (X.V.erase b) t y) (pu : X.D p u=true) :
    w b+q*(c-mass X.V w)+((q:ℚ)-1)*min (w b) (w t)<q*mass (bank q X.D (X.V.erase b) t y) w := by
  let U := X.V.erase b
  let G := pivot q X.D U t y
  let z := transferWeight w b t
  let μ := min (w b) (w t)
  have leB : μ≤w b := min_le_left .. 
  have leT : μ≤w t := min_le_right ..
  have pp : p∈inN X.D X.V b := parents ▸ mem_insert_self _ _
  have yp : y∈inN X.D X.V b := parents ▸ mem_insert_of_mem (mem_singleton_self _)
  have tv : t∈X.V := BRsub.ballSet_subset tr
  obtain ⟨tb,noBack⟩ := (saturated_region hq X.free X.sat bv tv).mp tr
  have tu : t∈U := mem_erase.mpr ⟨tb,tv⟩
  have ty : t≠y := fun eq=>noBack (eq ▸ (mem_inN.mp yp).2)
  have tp : t≠p := fun eq=>noBack (eq ▸ (mem_inN.mp pp).2)
  obtain ⟨uh,notCut⟩ := mem_sdiff.mp kept
  obtain ⟨uv,oldTU⟩ := mem_outN.mp uh
  have gt : G t u=true := by simp [G,pivot,insertArc,bankKept,ty,notCut,oldTU,U]
  have gp : G p u=true := insertArc_mono _ _ _ _ _ (by simp [bankKept,tp.symm,pu])
  obtain ⟨free,total,_,atY,atT,other,_⟩ := native X hq small bv parents tr pt wp high rows
  have qn : (0:ℚ)≤q := Nat.cast_nonneg _
  have costBound (i) (iv : i∈U) (it : i≠t) (hit : G i t=true) (miss : G i u≠true) :
      c+q*μ≤WeightedSD.row q G U z i := by
    by_cases iy : i=y
    · subst i; rw [atY]; linarith only [mul_le_mul_of_nonneg_left leT qn]
    have ip : i≠p := fun eq=>miss (eq ▸ gp)
    have noB : X.D i b≠true := fun ib=>by
      have both : i∈({p,y}:Finset ℕ) := parents ▸ mem_inN.mpr ⟨mem_of_mem_erase iv,ib⟩
      simp [ip,iy] at both
    have orig : X.D i t=true := by simpa [G,pivot,insertArc,bankKept,it,iy] using hit
    have heads : outN G U i=outN X.D U i := by ext j; simp [G,pivot,insertArc,bankKept,mem_outN,it,iy]
    have same : WeightedSD.row q G U z i=WeightedSD.row q X.D U z i := by simp only [WeightedSD.row,outW_eq_mass,heads]
    have baseline := rows i (mem_of_mem_erase iv)
    rw [WeightedSD.row,outW_erase bv,ite_eq_right noB,add_zero] at baseline
    rw [same,WeightedSD.row,outW_transfer tu,ite_eq_left orig]
    dsimp only [z,transferWeight]; rw [ite_eq_right it]
    dsimp only [U] at *
    linarith only [baseline,mul_le_mul_of_nonneg_left leB qn]
  have pos (i) (iv : i∈U) : 0<z i := by
    dsimp only [z,transferWeight]; split_ifs <;> linarith only [wp i (mem_of_mem_erase iv),wp b bv]
  have enough : μ<z t := by simp only [z,transferWeight,ite_true]; linarith only [leT,wp b bv]
  have price : mass U z=mass X.V w := total
  rw [←price]
  exact transfer_bill hq free (small _ _ (card_erase_lt_of_mem bv) free) tu uv gt pos (price ▸ high)
    (le_min (wp b bv).le (wp t tv).le) enough atT other costBound

#print axioms transfer_bill
#print axioms native_withdrawal
end LeanCH.BR.Closure.TwoParentOldWeight
