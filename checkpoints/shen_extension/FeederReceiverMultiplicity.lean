import checkpoints.shen_extension.FeederCyclePeriod

namespace LeanCH.BR.Closure.FeederPrivateHeadDescent
open Finset Function BRq2 BRq3 BR45 WeightedSD ShenCycleSuccessor ShortestCycleWeights

private theorem sum_periods (f : ℕ → ℕ) {d : ℕ} (per : ∀ i, f (i+d) = f i) (n : ℕ) :
    ∑ i ∈ range (n*d), f i = n * ∑ i ∈ range d, f i := by
  have move (t j : ℕ) : f (t*d+j) = f j := by
    induction t with
    | zero => simp
    | succ t ih =>
      rw [Nat.succ_mul,show t*d+d+j=t*d+j+d by omega,per,ih]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.succ_mul,sum_range_add,ih,Nat.succ_mul]
    exact congrArg _ (sum_congr rfl (fun j _ => move n j))

/-- At an exterior column carrying none of the cycle prices, parents occur
in complete periods of the shift between the two original marked rows. -/
theorem receiver_multiplicity {D V q L a b} (hq : 1 ≤ q) (free : QFree D V q)
    (cy : Cycle D V q L) (ha : a ∈ L) (hb : b ∈ L) (ne : a ≠ b) (w : ℕ → ℚ)
    (tied : ∀ y, Compared D V (a,b) y → w y.1 = w y.2 ∧
      (outN D V y.1).card = (outN D V y.2).card ∧
      ∃ v > (0 : ℚ), ∀ i ∈ exclusive D V y.1 y.2 ∪ exclusive D V y.2 y.1, w i = v)
    {z} (zv : z ∈ V) (other : ∀ x ∈ L, w z ≠ w x) :
    (q+1) / Nat.gcd (MandatoryExcursion.span D V q a b) (q+1) ∣ (inN D L z).card := by
  classical
  let s := fun i => (nextOn D L)^[i] a
  let d := Nat.gcd (MandatoryExcursion.span D V q a b) (q+1)
  obtain ⟨inside,_,onto,inj⟩ := cycle_index hq free cy ha
  have word := tied_cycle_word hq free cy ha hb ne w tied
  let f (i : ℕ) : ℕ := if D (s i) z = true then 1 else 0
  have bit (i) : z ∈ (cycleWord D V w (s i) (s (i+1))).2.2 ↔ D (s i) z = true := by
    have diff : w z ≠ w (s (i+1)) := other _ (inside (i+1))
    simp [cycleWord,mem_outN,zv,diff]
  have per (i) : f (i+d) = f i := by
    have h := congrArg (fun e : ℚ × ℕ × Finset ℕ => z ∈ e.2.2) (word i)
    have edges := (bit (i+d)).symm.trans ((Iff.of_eq h).trans (bit i))
    simp only [f,propext edges]
  have count : (inN D L z).card = ∑ i ∈ range (q+1), f i := by
    change (L.filter (fun x => D x z = true)).card = _
    rw [Finset.card_filter,←onto,Finset.sum_image inj]
  have periods := sum_periods f per ((q+1)/d)
  rw [Nat.div_mul_cancel (show d ∣ q+1 from Nat.gcd_dvd_right _ _)] at periods
  exact ⟨_,count.trans periods⟩

/-- The marked spacing is proper, so the repetition factor is always > 1. -/
theorem repetition_factor {D V q L a b} (hq : 1 ≤ q) (free : QFree D V q)
    (cy : Cycle D V q L) (ha : a ∈ L) (hb : b ∈ L) (ne : a ≠ b) :
    let d := Nat.gcd (MandatoryExcursion.span D V q a b) (q+1)
    1 < (q+1)/d ∧ (q+1)/d ∣ q+1 := by
  intro d
  let k := MandatoryExcursion.span D V q a b
  obtain ⟨lo,hi,_,back⟩ := MandatoryExcursion.segments hq free cy ha hb
  change 1 ≤ k at lo
  change k ≤ q+1 at hi
  have kt : k < q+1 := by
    by_contra! bad
    change Walk D L b a (q+1-k) at back
    rw [Nat.sub_eq_zero_of_le bad] at back
    cases back
    exact ne rfl
  have dl : d ≤ k := Nat.le_of_dvd (by omega) (Nat.gcd_dvd_left _ _)
  have mult := Nat.div_mul_cancel (show d ∣ q+1 from Nat.gcd_dvd_right _ _)
  refine ⟨?_,⟨d,mult.symm⟩⟩
  by_contra! small
  have bound := Nat.mul_le_mul_right d small
  rw [Nat.one_mul,mult] at bound
  omega

def SignatureExit {q n : ℕ} (X : Model q n) (w π : ℕ → ℚ) (c : ℚ)
    (a b ell : ℕ) : Prop :=
  ∃ y, Compared X.D X.V (a,b) y ∧ gap w y ≠ 0 ∧ DegreeGap X.D X.V y ≠ 0 ∧
    padicNorm ell (gap w y) = padicNorm ell ((q : ℚ)*c*DegreeGap X.D X.V y) ∧
    ∃ j k, j ≠ k ∧ ((failsTransfer q X.D X.V π y.1 y.2 j ∧ failsTransfer q X.D X.V π y.1 y.2 k) ∨
      (failsTransfer q X.D X.V π y.2 y.1 j ∧ failsTransfer q X.D X.V π y.2 y.1 k))

/-- Capstone entry with no unequal-price assumption and no prime to supply.
The same spacing controls every receiver on this marked cycle. -/
theorem on_marked_cycle {q n : ℕ} (X : Model q n) (hq : 2 ≤ q) (small : SmallerSmallRow q X.V.card)
    {w π c} (posw : ∀ i ∈ X.V, 0 < w i) (flat : ∀ i ∈ X.V, WeightedSD.row q X.D X.V w i = c)
    (pos : ∀ i ∈ X.V, 0 < π i) (high : mass X.V π < c)
    (cols : ∀ i ∈ X.V, WeightedSD.col q X.D X.V π i = c)
    {L a b} (cy : Cycle X.D X.V q L) (ha : a ∈ L) (hb : b ∈ L) (ne : a ≠ b) :
    (∀ ell, ell.Prime → ell ∣ q → SignatureExit X w π c a b ell) ∨
    (let k := MandatoryExcursion.span X.D X.V q a b
     let d := Nat.gcd k (q+1)
     let s := fun i => (nextOn X.D L)^[i] a
     (∀ i, cycleWord X.D X.V w (s (i+d)) (s (i+d+1)) = cycleWord X.D X.V w (s i) (s (i+1))) ∧
     1 < (q+1)/d ∧ (q+1)/d ∣ q+1 ∧
     ∀ z ∈ X.V, (∃ x ∈ L, w z = w x) ∨ (q+1)/d ∣ (inN X.D L z).card) := by
  classical
  by_cases asym : ∃ x, Compared X.D X.V (a,b) x ∧ w x.1 ≠ w x.2
  · left
    intro ell prime dv
    let _ : Fact ell.Prime := ⟨prime⟩
    rcases comparison_fork X hq small dv posw flat pos high cols (cy.sub ha) (cy.sub hb) ne with win | tied
    · exact win
    obtain ⟨x,path,neq⟩ := asym
    exact (neq (tied x path).1).elim
  · right
    let _ : Fact q.minFac.Prime := ⟨Nat.minFac_prime (by omega)⟩
    rcases comparison_fork X hq small (Nat.minFac_dvd q) posw flat pos high cols
      (cy.sub ha) (cy.sub hb) ne with win | tied
    · obtain ⟨y,path,diff,_⟩ := win
      exact (asym ⟨y,path,sub_ne_zero.mp diff⟩).elim
    have one : 1 ≤ q := by omega
    obtain ⟨large,divides⟩ := repetition_factor one X.free cy ha hb ne
    refine ⟨tied_cycle_word one X.free cy ha hb ne w tied,large,divides,?_⟩
    intro z zv
    by_cases hit : ∃ x ∈ L, w z = w x
    · exact Or.inl hit
    · exact Or.inr (receiver_multiplicity one X.free cy ha hb ne w tied zv
        (fun x hx eq => hit ⟨x,hx,eq⟩))

#print axioms receiver_multiplicity
#print axioms repetition_factor
#print axioms on_marked_cycle
end LeanCH.BR.Closure.FeederPrivateHeadDescent
