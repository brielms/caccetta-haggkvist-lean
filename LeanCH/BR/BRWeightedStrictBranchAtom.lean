import LeanCH.BR.BRWeightedRetainedHeadTransfer
import LeanCH.BR.BRWeightedArcCore

/-! A retained head repays an actual arc deletion and receives a strict diagonal
gain. The deleted host's own SmallRow supplies the strict atom floor. -/
namespace LeanCH.BR.WeightedSD
open Finset BRq2 BRq3 BR45 BRsub

theorem outW_eraseArc {D : CH.Digraph} {V : Finset ℕ} {u v : ℕ}
    (hv : v∈V) (euv : D u v=true) (a : ℕ→ℚ) (x : ℕ) :
    outW D V a x=outW (eraseArc D u v) V a x+if x=u then a v else 0 := by
  unfold outW
  have he : (∑j∈V,if D x j=true then a j else 0)=
      (∑j∈V,if eraseArc D u v x j=true then a j else 0)+
      ∑j∈V,if x=u ∧ j=v then a v else 0 := by
    rw [←sum_add_distrib]
    apply sum_congr rfl
    intro j hj
    by_cases hxu : x=u <;> by_cases hjv : j=v <;> simp [eraseArc,hxu,hjv,euv]
  rw [he]
  by_cases hxu : x=u <;> simp [hxu,hv]

/-- Algebraic repair on the unchanged vertex set. Only the transferred atom
needs a sign; the original weighting may otherwise be signed. The receiver may
equal the deleted tail, so no looplessness or y≠u premise is needed. -/
theorem branching_head_transfer_rows {q : ℕ} {D : CH.Digraph} {V : Finset ℕ}
    (a : ℕ→ℚ) {u v y : ℕ} (hv : v∈V) (hy : y∈V)
    (euv : D u v=true) (euy : D u y=true) (hyv : y≠v) (hav : 0≤a v)
    (x : ℕ) :
    row q D V a x+(if x=y then a v else 0)≤
      row q (eraseArc D u v) V (addWeightAt a y (a v)) x := by
  have he := outW_eraseArc hv euv a x
  rw [row_addWeightAt hy]
  by_cases hxu : x=u
  · subst x
    have hkeep : eraseArc D u v u y=true := by simp [eraseArc,hyv,euy]
    rw [hkeep]
    simp only [ite_true] at *
    simp only [row,he]
    ring_nf
    exact le_rfl
  · simp only [hxu,ite_false,add_zero] at he
    have hg : (0:ℚ)≤(q:ℚ)*(if eraseArc D u v x y=true then a v else 0) := by
      apply mul_nonneg (Nat.cast_nonneg q)
      split_ifs <;> simp [hav]
    simp only [row]
    rw [←he]
    linarith only [hg]

/-- The strict floor uses SmallRow only on the specified arc-deleted host.
The threshold c is arbitrary: c>mass, normalization, exact rows, girth,
inverse hypotheses and global induction are all unnecessary. -/
theorem deleted_branch_atom_strict {q : ℕ} (hq : 2≤q)
    {D : CH.Digraph} {V : Finset ℕ} (a : ℕ→ℚ) (ha : ∀x∈V,0<a x)
    (c : ℚ) (hr : ∀x∈V,c≤row q D V a x)
    {u v y : ℕ} (hv : v∈V) (hy : y∈V)
    (euv : D u v=true) (euy : D u y=true) (hyv : y≠v)
    (hdel : SmallRow q (eraseArc D u v) V) : c-mass V a<a v := by
  by_contra hn
  have hav : a v≤c-mass V a := le_of_not_gt hn
  let w := addWeightAt a y (a v)
  have hw : ∀x∈V,0<w x := by
    intro x hx
    dsimp [w,addWeightAt]
    split_ifs <;> linarith only [ha x hx,ha v hv]
  have hm : mass V w=mass V a+a v := mass_addWeightAt hy a (a v)
  have hb (x : ℕ) := branching_head_transfer_rows (q:=q) a hv hy euv euy hyv (ha v hv).le x
  have hf : ∀x∈V,mass V w≤row q (eraseArc D u v) V w x := by
    intro x hx
    have hg : (0:ℚ)≤(if x=y then a v else 0) := by split_ifs <;> simp [(ha v hv).le]
    have hh := hb x
    change row q D V a x+(if x=y then a v else 0)≤row q (eraseArc D u v) V w x at hh
    linarith only [hm,hav,hr x hx,hg,hh]
  have ht := positive_feasible_rows_tight_of_smallRow hq hdel w hw hf y hy
  have hh := hb y
  simp only [ite_true] at hh
  change row q D V a y+a v≤row q (eraseArc D u v) V w y at hh
  linarith only [hh,ht,hm,hav,hr y hy,ha v hv]

theorem ArcCritical.branch_atom_strict {q : ℕ} (hq : 2≤q)
    {D : CH.Digraph} {V : Finset ℕ} (hcrit : ArcCritical q D V)
    (a : ℕ→ℚ) (ha : ∀x∈V,0<a x) (c : ℚ) (hr : ∀x∈V,c≤row q D V a x)
    {u v y : ℕ} (hu : u∈V) (hv : v∈V) (hy : y∈V)
    (euv : D u v=true) (euy : D u y=true) (hyv : y≠v) :
    c-mass V a<a v :=
  deleted_branch_atom_strict hq a ha c hr hv hy euv euy hyv (hcrit u hu v hv euv)

/-- The column-law version consumes actual reversed arc criticality, derived
from the genuine global smaller-order hypothesis. It never replaces p by a. -/
theorem ArcCritical.reverse_branch_atom_strict {q : ℕ} (hq : 2≤q)
    {D : CH.Digraph} {V : Finset ℕ} (hcrit : ArcCritical q D V)
    (hsmall : SmallerSmallRow q V.card) (hf : QFree D V q)
    (p : ℕ→ℚ) (hp : ∀x∈V,0<p x) (c : ℚ) (hc : ∀x∈V,c≤col q D V p x)
    {u v y : ℕ} (hu : u∈V) (hv : v∈V) (hy : y∈V)
    (evu : D v u=true) (eyu : D y u=true) (hyv : y≠v) :
    c-mass V p<p v :=
  (hcrit.reverse hsmall hf).branch_atom_strict hq p hp c hc hu hv hy evu eyu hyv

end LeanCH.BR.WeightedSD
