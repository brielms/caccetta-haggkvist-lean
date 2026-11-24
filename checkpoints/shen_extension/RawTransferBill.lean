import checkpoints.shen_extension.CanonicalCycleLaw

namespace LeanCH.BR.Closure.RawTransferBill
open Finset BRq2 BRq3 BR45 WeightedSD ShenCycleSuccessor FullCycleTransfer CanonicalCycleLaw OpposedPairPrices

/-- A shared tail sees exactly the same total weight after a full matching,
including the diagonal. This equality holds even for signed allocations. -/
theorem shared_row {q E V A M} (a : Cycle E V q A) (m : Cycle E V q M) (P : Pairing E A M)
    (w : ℕ→ℝ) {b} (shared : b∈A∩M) :
    realRow q E (V\(A\M)) (fun v => w v+P.deposit w v) b=realRow q E V w b := by
  classical
  let Z := A\M
  let U := V\Z
  have noDep : P.deposit w b=0 := by
    unfold Pairing.deposit
    apply sum_eq_zero
    intro y hy
    rw [ite_eq_right (show P.label y≠b from fun h =>
      (mem_sdiff.mp (P.destination hy)).2 (h ▸ (mem_inter.mp shared).1))]
  have matching (y) (yh : y∈Z) : E b y=true ↔ P.label y∈outN E U b := by
    let Y : ↥A := ⟨y,(mem_sdiff.mp yh).1⟩
    have eq : P.label y=P.equiv Y := P.label_apply Y.property
    have ru : P.label y∈U := mem_sdiff.mpr ⟨m.sub (mem_sdiff.mp (P.destination yh)).1,
      fun h => (mem_sdiff.mp (P.destination yh)).2 (mem_sdiff.mp h).1⟩
    constructor
    · intro arc
      exact mem_outN.mpr ⟨ru,eq ▸ P.successor b shared Y arc⟩
    · intro arc
      have h := (flip a m P).successor b (mem_inter.mpr ⟨(mem_inter.mp shared).2,(mem_inter.mp shared).1⟩)
        (P.equiv Y) (eq ▸ (mem_outN.mp arc).2)
      change E b (P.equiv.symm (P.equiv Y))=true at h
      simpa only [Equiv.symm_apply_apply] using h
  have receipts : (∑z∈outN E U b,P.deposit w z)=∑y∈Z,if E b y=true then w y else 0 := by
    rw [P.receipts]
    exact sum_congr rfl (fun y hy => if_congr (matching y hy).symm rfl rfl)
  have split := sum_sdiff (sdiff_subset.trans a.sub : Z⊆V) (f:=fun y => if E b y=true then w y else 0)
  have paid : realOutW E U (fun v => w v+P.deposit w v) b=realOutW E V w b := by
    calc
      _ = (∑y∈U,if E b y=true then w y else 0)+∑z∈outN E U b,P.deposit w z := by
        simp only [realOutW,outN,sum_filter,←sum_add_distrib]
        exact sum_congr rfl (fun y _ => by cases E b y <;> simp)
      _ = _ := by rw [receipts]; exact split
  change w b+P.deposit w b+q*realOutW E U _ b=w b+q*realOutW E V w b
  rw [noDep,add_zero,paid]

/-- Conditioning does not lose any information about a matching's bill.
Equality with the baseline in even one matching forces every surviving
column tight and a specific child order modulo q. -/
theorem exact_bill {q E V A M} (hq : 2≤q) (a : Cycle E V q A) (m : Cycle E V q M)
    {x : ℕ→ℝ} {c : ℝ} (xp : ∀z∈V,0<x z) (xm : realMass V x=1)
    (rows : ∀z∈V,realRow q E V x z=c) {raw u : ℕ→ℝ}
    (hp : RealDual q E (V\(A\M)) 1 raw) (dp : 0<realMass (V\A) raw)
    (fromRaw : u=fun b => raw b/realMass (V\A) raw) (P : Pairing E A M) :
    let U := V\(A\M)
    let T := V\A
    let d := realMass T raw
    let w := fun z => x z+P.deposit x z
    let bill := d*debit P x (price q E T u)
    bill=(c-1)+internalDefect q E U w raw ∧
      (bill=c-1 ↔ ∀z∈U,realCol q E U raw z=1) ∧
      (bill=c-1 → (U.card : ZMod q)=1 ∧ ∀z∈U,0<raw z) ∧
      (((U.card : ZMod q)≠1) → c-1<bill) := by
  classical
  intro U T d w bill
  have tu : T⊆U := fun i hi => mem_sdiff.mpr ⟨(mem_sdiff.mp hi).1,
    fun h => (mem_sdiff.mp hi).2 (mem_sdiff.mp h).1⟩
  have same (b) (hb : b∈U\T) : realRow q E U w b=realRow q E V x b := by
    obtain ⟨bu,bt⟩ := mem_sdiff.mp hb
    have bv := (mem_sdiff.mp bu).1
    have ba : b∈A := by_contra fun no => bt (mem_sdiff.mpr ⟨bv,no⟩)
    have bm : b∈M := by_contra fun no => (mem_sdiff.mp bu).2 (mem_sdiff.mpr ⟨ba,no⟩)
    exact shared_row a m P x (mem_inter.mpr ⟨ba,bm⟩)
  let changeRow (b : ℕ) := realRow q E V x b-realRow q E U w b
  have scaled : bill=∑b∈T,raw b*changeRow b := by
    have e := OpposedPairPrices.bill a m P x u
    change (∑b∈T,u b*realRow q E V x b)-(∑b∈T,u b*realRow q E U w b)=debit P x (price q E T u) at e
    dsimp only [bill]
    rw [←e,←sum_sub_distrib,mul_sum]
    apply sum_congr rfl
    intro b _
    rw [fromRaw]
    change d*(raw b/d*_-raw b/d*_)=_
    dsimp only [changeRow]
    field_simp [(show d≠0 from dp.ne')]
  have allRows : (∑b∈T,raw b*changeRow b)=∑b∈U,raw b*changeRow b := by
    apply sum_subset tu
    intro b bu bt
    simp only [changeRow,same b (mem_sdiff.mpr ⟨bu,bt⟩),sub_self,mul_zero]
  have massW : realMass U w=1 := (P.mass_balance a m x).trans xm
  have exactCost : bill=c-1+internalDefect q E U w raw := by
    rw [scaled,allRows,internalDefect_eq,massW,←real_cross_rows]
    dsimp only [changeRow]
    simp_rw [mul_sub,sum_sub_distrib]
    have old : (∑b∈U,raw b*realRow q E V x b)=c := by
      rw [sum_congr rfl (fun b (hb : b∈U) => congrArg (raw b * ·) (rows b (mem_sdiff.mp hb).1)),←sum_mul]
      change realMass U raw*c=c
      rw [hp.normalized,one_mul]
    rw [old]; ring
  have wp (z) (zu : z∈U) : 0<w z := by
    apply add_pos_of_pos_of_nonneg (xp z (mem_sdiff.mp zu).1)
    exact sum_nonneg (fun y hy => by split_ifs <;> first | exact le_rfl | exact (xp y (a.sub (mem_sdiff.mp hy).1)).le)
  have term (z) (zu : z∈U) : 0≤w z*(1-realCol q E U raw z) :=
    mul_nonneg (wp z zu).le (sub_nonneg.mpr (hp.columns z zu))
  have iffT : bill=c-1 ↔ ∀z∈U,realCol q E U raw z=1 := by
    constructor
    · intro eq z zu
      have t := single_le_sum term zu
      change w z*(1-realCol q E U raw z)≤ internalDefect q E U w raw at t
      apply le_antisymm (hp.columns z zu)
      by_contra! no
      linarith only [eq,exactCost,t,mul_pos (wp z zu) (sub_pos.mpr no)]
    · intro flat
      have zero : internalDefect q E U w raw=0 := sum_eq_zero (fun z hz => by rw [flat z hz,sub_self,mul_zero])
      linarith only [zero,exactCost]
  have rigid (eq : bill=c-1) := unit_columns hq (iffT.mp eq)
  refine ⟨exactCost,iffT,fun eq => ⟨(rigid eq).1 hp.normalized,fun z hz =>
    lt_of_le_of_ne (hp.nonneg z hz) (Ne.symm ((rigid eq).2 z hz))⟩,?_⟩
  intro mismatch
  have lo : c-1≤bill := by rw [exactCost]; exact le_add_of_nonneg_right (sum_nonneg term)
  exact lt_of_le_of_ne lo (fun eq => mismatch ((rigid eq.symm).1 hp.normalized))

#print axioms exact_bill
#print axioms shared_row
end LeanCH.BR.Closure.RawTransferBill
