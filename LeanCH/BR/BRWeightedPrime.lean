import LeanCH.BR.BRWeightedSupport

/-! An actual contraction and saturation reduction to the positive prime
residual. The prime residual is an explicit, unproved supplier. -/
namespace LeanCH.BR.WeightedSD
open BRq2 BRq3 BR45 BRsub

def representativeSet (V M : Finset ℕ) (r : ℕ) : Finset ℕ := insert r (V \ M)
def representativeFiber (M : Finset ℕ) (r i : ℕ) : Finset ℕ :=
  if i = r then M else {i}

theorem representative_subset {V M : Finset ℕ} {r : ℕ} (hMV : M ⊆ V) (hr : r ∈ M) :
    representativeSet V M r ⊆ V := Finset.insert_subset (hMV hr) Finset.sdiff_subset

theorem representative_outside {V M : Finset ℕ} {r i : ℕ}
    (hi : i ∈ representativeSet V M r) (hne : i ≠ r) : i ∈ V ∧ i ∉ M :=
  Finset.mem_sdiff.mp ((Finset.mem_insert.mp hi).resolve_left hne)

def moduleSubstitution {D : CH.Digraph} {V M : Finset ℕ} {r : ℕ}
    (hMV : M ⊆ V) (hr : r ∈ M) (hout : OutUniform D V M) (hin : InUniform D V M)
    (hloop : ∀ v ∈ V, D v v = false) :
    Substitution D D V (representativeSet V M r) where
  fiber := representativeFiber M r
  cover := by
    ext v
    constructor
    · intro hv
      by_cases hvM : v ∈ M
      · exact Finset.mem_biUnion.mpr ⟨r, Finset.mem_insert_self _ _, by
          simpa [representativeFiber] using hvM⟩
      · have hvr : v ≠ r := by intro he; exact hvM (he ▸ hr)
        exact Finset.mem_biUnion.mpr ⟨v,
          Finset.mem_insert_of_mem (Finset.mem_sdiff.mpr ⟨hv, hvM⟩), by
            simp [representativeFiber, hvr]⟩
    · intro hv
      obtain ⟨i, hi, hvi⟩ := Finset.mem_biUnion.mp hv
      by_cases hir : i = r
      · subst i
        exact hMV (by simpa [representativeFiber] using hvi)
      · have hvi' : v = i := by simpa [representativeFiber, hir] using hvi
        subst v
        exact (representative_outside hi hir).1
  nonempty := by
    intro i hi
    by_cases hir : i = r
    · subst i
      exact ⟨r, by simpa [representativeFiber] using hr⟩
    · exact ⟨i, by simp [representativeFiber, hir]⟩
  disjoint := by
    intro i hi j hj hij
    apply Finset.disjoint_left.mpr
    intro v hvi hvj
    by_cases hir : i = r
    · subst i
      have hjr : j ≠ r := Ne.symm hij
      have hvM : v ∈ M := by simpa [representativeFiber] using hvi
      have hvj' : v = j := by simpa [representativeFiber, hjr] using hvj
      exact (representative_outside hj hjr).2 (hvj' ▸ hvM)
    · have hvi' : v = i := by simpa [representativeFiber, hir] using hvi
      subst v
      by_cases hjr : j = r
      · subst j
        exact (representative_outside hi hir).2 (by simpa [representativeFiber] using hvj)
      · have heq : i = j := by simpa [representativeFiber, hjr] using hvj
        exact hij heq
  loopless := fun i hi => hloop i (representative_subset hMV hr hi)
  cross := by
    intro i hi j hj hij a ha b hb
    by_cases hir : i = r
    · subst i
      have hjr : j ≠ r := Ne.symm hij
      have haM : a ∈ M := by simpa [representativeFiber] using ha
      have hbj : b = j := by simpa [representativeFiber, hjr] using hb
      subst b
      exact hout a haM r hr j (representative_outside hj hjr).1
        (representative_outside hj hjr).2
    · have hai : a = i := by simpa [representativeFiber, hir] using ha
      subst a
      by_cases hjr : j = r
      · subst j
        have hbM : b ∈ M := by simpa [representativeFiber] using hb
        exact hin b hbM r hr i (representative_outside hi hir).1
          (representative_outside hi hir).2
      · have hbj : b = j := by simpa [representativeFiber, hjr] using hb
        subst b
        rfl

theorem representative_ne {V M : Finset ℕ} {r : ℕ} (hMV : M ⊆ V)
    (hr : r ∈ M) (hM : 2 ≤ M.card) : representativeSet V M r ≠ V := by
  obtain ⟨a, ha, har⟩ := Finset.exists_mem_ne (by omega : 1 < M.card) r
  intro heq
  have haI : a ∈ representativeSet V M r := by rw [heq]; exact hMV ha
  exact (representative_outside haI har).2 ha

theorem selfDual_of_proper_module {q : ℕ} (hq : 1 ≤ q)
    {D : CH.Digraph} {V M : Finset ℕ} (hf : QFree D V q) (hsat : Sat q D V)
    (hproper : ∀ U ⊆ V, U ≠ V → SelfDual q D U)
    (hMV : M ⊆ V) (hM : 2 ≤ M.card) (hne : M ≠ V) (hout : OutUniform D V M) :
    SelfDual q D V := by
  obtain ⟨r, hr⟩ := Finset.card_pos.mp (by omega : 0 < M.card)
  have hin := outUniform_inUniform hf hsat hMV hout
  let P := moduleSubstitution hMV hr hout hin
    (fun v hv => Bool.eq_false_iff.mpr (loopfree hf hq hv))
  apply P.selfDual
  · exact hproper _ (representative_subset hMV hr) (representative_ne hMV hr hM)
  · intro i hi
    by_cases hir : i = r
    · subst i
      simpa [P, moduleSubstitution, representativeFiber] using hproper M hMV hne
    · have hiV : i ∈ V := (representative_outside hi hir).1
      have hsing : ({i} : Finset ℕ) ≠ V := by
        intro heq
        have hcard := Finset.card_le_card hMV
        rw [← heq] at hcard
        simp only [Finset.card_singleton] at hcard
        omega
      simpa [P, moduleSubstitution, representativeFiber, hir] using
        hproper {i} (Finset.singleton_subset_iff.mpr hiV) hsing

theorem outW_mono_graph {D E : CH.Digraph} {V : Finset ℕ}
    (hDE : ∀ a ∈ V, ∀ b ∈ V, D a b = true → E a b = true)
    {w : ℕ → ℚ} (hw : ∀ v ∈ V, 0 ≤ w v) {v : ℕ} (hv : v ∈ V) :
    outW D V w v ≤ outW E V w v := by
  apply Finset.sum_le_sum
  intro u hu
  by_cases hd : D v u = true
  · simp [hd, hDE v hv u hu hd]
  · by_cases he : E v u = true <;> simp [hd, he, hw u hu]

theorem inW_mono_graph {D E : CH.Digraph} {V : Finset ℕ}
    (hDE : ∀ a ∈ V, ∀ b ∈ V, D a b = true → E a b = true)
    {w : ℕ → ℚ} (hw : ∀ v ∈ V, 0 ≤ w v) {v : ℕ} (hv : v ∈ V) :
    inW D V w v ≤ inW E V w v := by
  exact outW_mono_graph (D := fun a b => D b a) (E := fun a b => E b a)
    (fun a ha b hb => hDE b hb a ha) hw hv

theorem selfDual_of_supergraph {q : ℕ} {D E : CH.Digraph} {V : Finset ℕ}
    (hDE : ∀ a ∈ V, ∀ b ∈ V, D a b = true → E a b = true)
    (hE : SelfDual q E V) : SelfDual q D V := by
  intro w hw hr
  have hrE : ∀ v ∈ V, mass V w ≤ row q E V w v := by
    intro v hv
    exact (hr v hv).trans (add_le_add le_rfl
      (mul_le_mul_of_nonneg_left (outW_mono_graph hDE hw hv) (Nat.cast_nonneg q)))
  intro v hv
  exact (add_le_add le_rfl
    (mul_le_mul_of_nonneg_left (inW_mono_graph hDE hw hv) (Nat.cast_nonneg q))).trans
    (hE w hw hrE v hv)

theorem selfDual_two {D : CH.Digraph} {V : Finset ℕ} (hf : QFree D V 2) :
    SelfDual 2 D V := by
  intro w hw hr v hv
  have hloop : D v v = false := Bool.eq_false_iff.mpr (loopfree hf (by omega) hv)
  have hsum := Finset.sum_erase_add V w hv
  change mass (V.erase v) w + w v = mass V w at hsum
  have hpair : outW D (V.erase v) w v + inW D (V.erase v) w v ≤
      mass (V.erase v) w := by
    rw [outW, inW, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro u hu
    have huV := (Finset.mem_erase.mp hu).2
    by_cases ho : D v u = true
    · have hi : ¬ D u v = true := fun hi => digonfree hf (by omega) hv huV ho hi
      simp [ho, hi]
    · by_cases hi : D u v = true <;> simp [ho, hi, hw u huV]
  have hrow := hr v hv
  rw [row, outW_erase hv w v, hloop] at hrow
  rw [col, inW_erase hv w v, hloop]
  simp only [Bool.false_eq_true, ite_false, add_zero, Nat.cast_ofNat] at hrow ⊢
  linarith

/-- The sole structural supplier: positive weights on saturated q-free
graphs with no nontrivial proper out-module, under smaller-instance SD. -/
def PositivePrimeSupplier : Prop :=
  ∀ q : ℕ, 3 ≤ q → ∀ (D : CH.Digraph) (V : Finset ℕ),
    QFree D V q → Sat q D V →
    (∀ U ⊆ V, U ≠ V → SelfDual q D U) →
    (∀ M ⊆ V, 2 ≤ M.card → M ≠ V → ¬ OutUniform D V M) →
    PositiveSelfDual q D V

theorem allSelfDual_of_positivePrimeSupplier (hP : PositivePrimeSupplier) : AllSelfDual := by
  intro q hq
  by_cases hthree : 3 ≤ q
  · have main : ∀ n : ℕ, ∀ V : Finset ℕ, V.card = n →
        ∀ D : CH.Digraph, QFree D V q → SelfDual q D V := by
      intro n
      induction n using Nat.strong_induction_on with
      | h n ih =>
        intro V hcard D hf
        obtain ⟨E, hDE, hEf, hsat⟩ := exists_satQ hf
        apply selfDual_of_supergraph hDE
        have hproper : ∀ U ⊆ V, U ≠ V → SelfDual q E U := by
          intro U hUV hne
          have hlt : U.card < n := by
            rw [← hcard]
            exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hUV, hne⟩)
          exact ih U.card hlt U rfl E (hEf.mono_set hUV)
        by_cases hprime : ∀ M ⊆ V, 2 ≤ M.card → M ≠ V → ¬ OutUniform E V M
        · exact selfDual_of_positive_and_proper (by omega) hEf
            (hP q hthree E V hEf hsat hproper hprime) hproper
        · push_neg at hprime
          obtain ⟨M, hMV, hM, hne, hout⟩ := hprime
          exact selfDual_of_proper_module (by omega) hEf hsat hproper hMV hM hne hout
    intro D V hf
    exact main V.card V rfl D hf
  · intro D V hf
    have heq : q = 1 ∨ q = 2 := by omega
    rcases heq with rfl | rfl
    · exact selfDual_one hf
    · exact selfDual_two hf

theorem caccettaHaggkvist_of_positivePrimeSupplier (h : PositivePrimeSupplier) :
    CH.CaccettaHaggkvistConjecture :=
  caccettaHaggkvist_of_allSelfDual (allSelfDual_of_positivePrimeSupplier h)

end LeanCH.BR.WeightedSD
