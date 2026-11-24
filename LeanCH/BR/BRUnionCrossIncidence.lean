import LeanCH.BR.BRWeightedExtremalExchange

/-! Union safety from local incidence of differently colored edges.
No degree, order, or positive-cutoff assumption occurs in the master. -/
namespace LeanCH.BR.WeightedSD
open Finset BRq2 BRq3 BR45 BRsub

def arcUnion (D E : CH.Digraph) : CH.Digraph := fun x y => D x y || E x y

def CrossIncidence (D E : CH.Digraph) (V : Finset ℕ) : Prop :=
  ∀ a∈V, ∀ b∈V, ∀ c∈V, ∀ d∈V,
    D a b=true → ¬ E a b=true → E c d=true → ¬ D c d=true → a=c ∨ b=d

theorem qfree_union_cross_incidence {q : ℕ} {D E : CH.Digraph} {V : Finset ℕ}
    (hD : QFree D V q) (hE : QFree E V q) (hcross : CrossIncidence D E V) :
    QFree (arcUnion D E) V q := by
  suffices hh : ∀ k, k ≤ q → ∀ a, 0<k → Walk (arcUnion D E) V a a k → False by
    intro a k hk hkq w
    exact hh k hkq a hk w
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hkq a hk w
    have hshort : QFree (arcUnion D E) V (k-1) := by
      intro x m hm hmk wm
      exact ih m (by omega) (by omega) x hm wm
    obtain ⟨f,h0,hk',he⟩ := w.toFun
    have hmem : ∀ i, i ≤ k → f i∈V := by
      intro i hi
      by_cases hi0 : i=0
      · subst i
        rw [h0,←hk']
        simpa only [Nat.sub_add_cancel hk] using (he (k-1) (by omega)).1
      · simpa only [Nat.sub_add_cancel (by omega : 1 ≤ i)] using (he (i-1) (by omega)).1
    have hinj : ∀ i<k, ∀ j<k, f i=f j → i=j := by
      intro i hi j hj hij
      by_contra hn
      rcases Nat.lt_or_gt_of_ne hn with hlt | hgt
      · have wp := walk_between he hlt.le (by omega : j ≤ k)
        rw [←hij] at wp
        exact hshort (f i) (j-i) (by omega) (by omega) wp
      · have wp := walk_between he hgt.le (by omega : i ≤ k)
        rw [hij] at wp
        exact hshort (f j) (i-j) (by omega) (by omega) wp
    have hheads : ∀ i<k, ∀ j<k, f (i+1)=f (j+1) → i=j := by
      intro i hi j hj hij
      by_cases hil : i+1=k
      · by_cases hjl : j+1=k
        · omega
        · have heq : f 0=f (j+1) := by rw [h0,←hk',←hil]; exact hij
          have hh := hinj 0 hk (j+1) (by omega) heq
          omega
      · by_cases hjl : j+1=k
        · have heq : f (i+1)=f 0 := by rw [h0,←hk',←hjl]; exact hij
          have hh := hinj (i+1) (by omega) 0 hk heq
          omega
        · have hh := hinj (i+1) (by omega) (j+1) (by omega) hij
          omega
    by_cases hall : ∀ i, i<k → D (f i) (f (i+1))=true
    · have wd := walk_of_edges (f := f) (m := k) (fun i hi => ⟨(he i hi).1,hall i hi⟩)
      rw [h0,hk'] at wd
      exact hD a k hk hkq wd
    · push Not at hall
      obtain ⟨i,hi,hDi⟩ := hall
      have hEi : E (f i) (f (i+1))=true := by
        have hh := (he i hi).2
        simpa [arcUnion,hDi] using hh
      have hAllE : ∀ j, j<k → E (f j) (f (j+1))=true := by
        intro j hj
        by_contra hEj
        have hDj : D (f j) (f (j+1))=true := by
          have hh := (he j hj).2
          simpa [arcUnion,hEj] using hh
        have hsame := hcross (f j) (hmem j (by omega)) (f (j+1)) (hmem _ (by omega))
          (f i) (hmem i (by omega)) (f (i+1)) (hmem _ (by omega)) hDj hEj hEi hDi
        have hji : j=i := hsame.elim (hinj j hj i hi) (hheads j hj i hi)
        subst j
        exact hEj hEi
      have we := walk_of_edges (f := f) (m := k) (fun i hi => ⟨(he i hi).1,hAllE i hi⟩)
      rw [h0,hk'] at we
      exact hE a k hk hkq we

end LeanCH.BR.WeightedSD
