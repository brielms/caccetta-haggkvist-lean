import checkpoints.shen_extension.FeederNativeDirections
import checkpoints.shen_extension.CrossValueOmissions
import checkpoints.shen_extension.OmittedCycleProgress

namespace LeanCH.BR.Closure.FeederRetainedIncidence
open Finset BRq2 BRq3 BR45 WeightedSD

/-- Vertices at which the selected graph omits an outgoing native arc. -/
def damaged (D E : CH.Digraph) (V : Finset ℕ) := V.filter (fun i => outN D V i ≠ outN E V i)

private theorem unit_row (q : ℕ) (D : CH.Digraph) (V : Finset ℕ) (i : ℕ) :
    WeightedSD.row q D V (fun _ => 1) i = 1+(q:ℚ)*(outN D V i).card := by
  simp [WeightedSD.row,outW_eq_mass,mass]

/-- Unit prices measure the strict native surplus in integer units. -/
theorem surplus_bound {q D V d} (hq : 2 ≤ q) (free : QFree D V q) (live : V.Nonempty)
    (small : SmallerSmallRow q V.card) (reg : ∀ i ∈ V, (outN D V i).card = d)
    (size : V.card ≤ q*d) : 1+q*d-V.card ≤ q-2 := by
  let c := (1+(q:ℚ)*d)
  have m : mass V (fun _ => (1:ℚ)) = V.card := by simp [mass]
  have h : mass V (fun _ => (1:ℚ)) < c := by
    rw [m]; dsimp [c]; exact_mod_cast (by omega : V.card < 1+q*d)
  obtain ⟨v,hv⟩ := live
  have f := strict_atom_floor_of_proper hq free (small.induced free) (fun _ => 1)
    (fun _ _ => by norm_num) c h (fun i hi => by rw [unit_row,reg i hi]) v hv
  rw [m,mul_one] at f
  dsimp [c] at f
  have lt : 1+q*d+1 < V.card+q := by exact_mod_cast (by linarith : 1+(q:ℚ)*d+1 < V.card+q)
  omega

/-- The original terminal allocation measures the loss of *all* native rows in one sum. -/
theorem damaged_mass {q D E V d} {p : ℕ → ℚ} {c : ℚ}
    (sub : ∀ i ∈ V, ∀ j ∈ V, E i j = true → D i j = true)
    (reg : ∀ i ∈ V, (outN D V i).card = d) (pos : ∀ i ∈ V, 0 ≤ p i)
    (prob : mass V p = 1) (cols : ∀ i ∈ V, col q E V p i = c) :
    (q:ℚ)*mass (damaged D E V) p ≤ 1+(q:ℚ)*d-V.card*c := by
  classical
  have account := NativeReturnAccounts.balance q E V (fun _ => 1) p
  simp only [unit_row,one_mul] at account
  rw [sum_congr rfl (fun i hi => cols i hi),sum_const,nsmul_eq_mul] at account
  have rowBill (i) (hi : i ∈ V) :
      (if outN D V i ≠ outN E V i then (q:ℚ)*p i else 0) ≤
        p i * ((1+(q:ℚ)*d)-(1+(q:ℚ)*(outN E V i).card)) := by
    have inc : outN E V i ⊆ outN D V i := by
      intro j hj
      exact mem_outN.mpr ⟨(mem_outN.mp hj).1,sub i hi j (mem_outN.mp hj).1 (mem_outN.mp hj).2⟩
    split_ifs with ne
    · have lt := card_lt_card (ssubset_of_subset_of_ne inc (Ne.symm ne))
      rw [reg i hi] at lt
      have lq : ((outN E V i).card:ℚ)+1 ≤ d := by exact_mod_cast lt
      have h := mul_le_mul_of_nonneg_left lq (Nat.cast_nonneg q : (0:ℚ) ≤ q)
      calc
        _ = p i * q := mul_comm ..
        _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith only [h]) (pos i hi)
    · rw [←not_ne_iff.mp ne,reg i hi]; simp
  have sum := sum_le_sum rowBill
  simp only [mul_sub,sum_sub_distrib,←sum_mul] at sum
  rw [show ∑ i ∈ V, p i = 1 from prob,one_mul,account] at sum
  convert sum using 1
  simp [damaged,mass,sum_filter,mul_sum,mul_ite]

private theorem price_ceiling {q E V} {x p : ℕ → ℚ} {c : ℚ}
    (xp : ∀ i ∈ V, 0 < x i) (pp : ∀ i ∈ V, 0 < p i) (pm : mass V p = 1)
    (high : 1 < c) (rows : ∀ i ∈ V, WeightedSD.row q E V x i = c) (cols : ∀ i ∈ V, col q E V p i = c)
    (j) (jv : j ∈ V) : (q:ℚ)*x j < c := by
  have one := (single_le_sum (s:=V) (fun i hi => (pp i hi).le) jv).trans_eq pm
  have ins := cols j jv
  change p j + (q:ℚ)*outW (fun i k => E k i) V p j = c at ins
  rw [outW_eq_mass] at ins
  obtain ⟨i,hi⟩ : (inN E V j).Nonempty := by
    by_contra! empty
    have eq : outN (fun i k => E k i) V j = ∅ := empty
    rw [eq] at ins
    simp [mass] at ins
    linarith
  obtain ⟨iv,edge⟩ := mem_inN.mp hi
  have out := rows i iv
  rw [WeightedSD.row,outW_eq_mass] at out
  have h := single_le_sum (fun k (hk : k ∈ outN E V i) => (xp k (mem_outN.mp hk).1).le)
    (mem_outN.mpr ⟨jv,edge⟩ : j ∈ outN E V i)
  have paid := mul_le_mul_of_nonneg_left h (Nat.cast_nonneg q : (0:ℚ) ≤ q)
  change (q:ℚ)*x j ≤ q*mass (outN E V i) x at paid
  linarith only [paid,out,xp i iv]

/-- The normalized joint mass on a vertex pair is its diagonal or arc contribution.
Its marginals are precisely the old column and row prices, respectively. -/
private def joint (q : ℕ) (E : CH.Digraph) (p x : ℕ → ℚ) (i j : ℕ) : ℚ :=
  (if i=j then p i*x j else 0) + if E i j=true then (q:ℚ)*p i*x j else 0

theorem crossing {q E V} {x p : ℕ → ℚ} {c : ℚ} {A B : Finset ℕ}
    (hq : 0 < q) (live : V.Nonempty) (xp : ∀ i ∈ V, 0 < x i) (pp : ∀ i ∈ V, 0 < p i)
    (pm : mass V p = 1) (high : 1 < c)
    (rows : ∀ i ∈ V, WeightedSD.row q E V x i = c) (cols : ∀ i ∈ V, col q E V p i = c)
    (av : A ⊆ V) (bv : B ⊆ V) (light : (q:ℚ)*(mass A p+mass B x) ≤ q-1) :
    ∃ i ∈ V, i ∉ A ∧ ∃ j ∈ V, j ∉ B ∧ E i j = true := by
  classical
  let g := joint q E p x
  have rowSum (i) (hi : i ∈ V) : (∑ j ∈ V, g i j) = p i*c := by
    rw [←rows i hi]
    simp [g,joint,WeightedSD.row,outW,sum_add_distrib,mul_add,mul_sum,mul_ite,hi,mul_assoc,mul_left_comm]
  have colSum (j) (hj : j ∈ V) : (∑ i ∈ V, g i j) = x j*c := by
    rw [←cols j hj]
    simp [g,joint,col,inW,sum_add_distrib,mul_add,mul_sum,mul_ite,hj,mul_comm]
  have total : (∑ i ∈ V, ∑ j ∈ V, g i j) = c := by
    rw [sum_congr rfl rowSum,←sum_mul,show ∑ i ∈ V,p i=1 from pm,one_mul]
  by_contra missing
  push Not at missing
  have nonneg (i) (iv : i ∈ V) (j) (jv : j ∈ V) : 0 ≤ g i j := by
    have hp := pp i iv
    have hx := xp j jv
    dsimp [g,joint]; split_ifs <;> positivity
  have point (i) (iv : i ∈ V) (j) (jv : j ∈ V) :
      g i j ≤ (if i ∈ A then g i j else 0) + (if j ∈ B then g i j else 0) +
        (if i=j then p i*x j else 0) := by
    have hp := pp i iv
    have hx := xp j jv
    have diag : 0 ≤ (if i=j then p i*x j else 0) := by split_ifs <;> positivity
    by_cases ia : i ∈ A <;> by_cases jb : j ∈ B
    · simp only [ia,jb,ite_true]; linarith [nonneg i iv j jv]
    · simpa [ia,jb] using le_add_of_nonneg_right (a:=g i j) diag
    · simpa [ia,jb] using le_add_of_nonneg_right (a:=g i j) diag
    · simp [ia,jb,g,joint,missing i iv ia j jv jb]
  have cover := sum_le_sum (s:=V) (fun i iv => sum_le_sum (s:=V) (point i iv))
  rw [total] at cover
  simp only [sum_add_distrib] at cover
  have first : (∑ i ∈ V, ∑ j ∈ V, if i ∈ A then g i j else 0) = mass A p*c := by
    simp_rw [←ite_sum_zero]
    rw [←sum_filter,filter_mem_eq_inter,inter_eq_right.mpr av,sum_congr rfl (fun i hi => rowSum i (av hi))]
    exact (sum_mul ..).symm
  have second : (∑ i ∈ V, ∑ j ∈ V, if j ∈ B then g i j else 0) = mass B x*c := by
    rw [sum_comm]
    simp_rw [←ite_sum_zero]
    rw [←sum_filter,filter_mem_eq_inter,inter_eq_right.mpr bv,sum_congr rfl (fun j hj => colSum j (bv hj))]
    exact (sum_mul ..).symm
  have diagonal : (∑ i ∈ V, ∑ j ∈ V, if i=j then p i*x j else 0) = ∑ i ∈ V, p i*x i :=
    sum_congr rfl fun i hi => by simp [hi]
  rw [first,second,diagonal] at cover
  have cheap (i) (hi : i ∈ V) : (q:ℚ)*(p i*x i) < p i*c := by
    rw [mul_left_comm]
    exact mul_lt_mul_of_pos_left (price_ceiling xp pp pm high rows cols i hi) (pp i hi)
  have diagBound := sum_lt_sum_of_nonempty live cheap
  rw [←mul_sum,←sum_mul,show ∑ i ∈ V,p i = 1 from pm,one_mul] at diagBound
  have bound := mul_le_mul_of_nonneg_right light (by linarith : (0:ℚ) ≤ c)
  have sumBound := mul_le_mul_of_nonneg_left cover (Nat.cast_nonneg q : (0:ℚ) ≤ q)
  linarith only [bound,sumBound,diagBound]

/-- The two sets of intact incidences use the *same* terminal allocation.
At cutoff three the numeric guard follows from the strict atom floor. -/
theorem at_attachment {q D E V w π x p c a} (hq : 2 ≤ q) (free : QFree D V q)
    (small : SmallerSmallRow q V.card) (av : a ∈ V)
    (sub : ∀ i ∈ V, ∀ j ∈ V, E i j = true → D i j = true)
    (terminal : OmittedCycleProgress.Flat q E V x p c)
    (reg : FeederPrivateHeadDescent.UniformOn D V w)
    (rev : FeederPrivateHeadDescent.UniformOn (fun i j => D j i) V π)
    (size : V.card ≤ q*(outN D V a).card) :
    let d := (outN D V a).card
    let gap := 1+q*d-V.card
    let A := damaged D E V
    let B := damaged (fun i j => D j i) (fun i j => E j i) V
    gap ≤ q-2 ∧ (q=3 → V.card=3*d) ∧
      (q:ℚ)*mass A p < gap ∧ (q:ℚ)*mass B x < gap ∧
      ((q=3 ∨ 2*(1+(q:ℚ)*d-V.card*c) ≤ q-1) →
        ∃ i ∈ V, outN E V i = outN D V i ∧
          ∃ j ∈ V, inN E V j = inN D V j ∧ E i j=true) := by
  classical
  intro d gap A B
  change V.card ≤ q*d at size
  obtain ⟨high,xp,pp,xm,pm,rows,cols⟩ := terminal
  have od (i) (hi : i ∈ V) : (outN D V i).card = d := (reg i hi a av).2
  have idg (i) (hi : i ∈ V) : (inN D V i).card = (inN D V a).card := (rev i hi a av).2
  have balance : (∑ i ∈ V, (outN D V i).card) = ∑ i ∈ V, (inN D V i).card :=
    Compose.ThinRigid.sum_out_eq_sum_in D V
  rw [sum_congr rfl od,sum_congr rfl idg] at balance
  simp only [sum_const,smul_eq_mul] at balance
  have vp := card_pos.mpr (show V.Nonempty from ⟨a,av⟩)
  have same := Nat.eq_of_mul_eq_mul_left vp balance
  have ins (i) (hi : i ∈ V) : (outN (fun i j => D j i) V i).card = d := (idg i hi).trans same.symm
  have hgap := surplus_bound hq free ⟨a,av⟩ small od size
  have left := damaged_mass sub od (fun i hi => (pp i hi).le) pm cols
  have right := damaged_mass (D:=fun i j => D j i) (E:=fun i j => E j i)
    (fun i iv j jv => sub j jv i iv) ins (fun i hi => (xp i hi).le) xm
    (show ∀ i ∈ V,col q (fun i j => E j i) V x i=c from rows)
  have cast : (gap:ℚ) = 1+(q:ℚ)*d-V.card := by
    unfold gap
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  have order : (0:ℚ) < V.card := by exact_mod_cast vp
  have drop : 1+(q:ℚ)*d-V.card*c < gap := by
    rw [cast]
    linarith only [mul_lt_mul_of_pos_left high order]
  have top (tri : q=3) : V.card=3*d := by
    subst q
    change 1+3*d-V.card ≤ 3-2 at hgap
    change V.card ≤ 3*d at size
    omega
  refine ⟨hgap,top,left.trans_lt drop,right.trans_lt drop,?_⟩
  intro guard
  have light : (q:ℚ)*(mass A p+mass B x) ≤ q-1 := by
    rw [mul_add]
    rcases guard with tri | room
    · have bound : gap ≤ 1 := by omega
      have floor : (gap:ℚ) ≤ 1 := by exact_mod_cast bound
      change (q:ℚ)*mass A p ≤ _ at left
      change (q:ℚ)*mass B x ≤ _ at right
      subst q
      norm_num only [Nat.cast_ofNat] at left right drop ⊢
      linarith only [left,right,drop,floor]
    · exact (add_le_add left right).trans (by linarith only [room])
  obtain ⟨i,iv,im,j,jv,jm,arc⟩ := crossing (by omega : 0<q) ⟨a,av⟩ xp pp pm high rows cols
    (filter_subset _ _) (filter_subset _ _) light
  have intact {D E : CH.Digraph} {k} (kv : k ∈ V) (miss : k ∉ damaged D E V) :
      outN E V k = outN D V k := by
    by_contra ne
    exact miss (mem_filter.mpr ⟨kv,Ne.symm ne⟩)
  exact ⟨i,iv,intact iv im,j,jv,intact jv jm,arc⟩

#print axioms surplus_bound
#print axioms damaged_mass
#print axioms crossing
#print axioms at_attachment
end LeanCH.BR.Closure.FeederRetainedIncidence
