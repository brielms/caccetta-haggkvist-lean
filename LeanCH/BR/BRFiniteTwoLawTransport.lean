import LeanCH.BR.BRWeightedNormal

/-! Two distinct marginals transported across a rectangular matrix. Algebraic
identities allow signed data and do not assume normalized vectors. -/
namespace LeanCH.BR.TwoLawTransport
open Finset Matrix
open scoped Matrix

section Algebra
variable {I J 𝕜 : Type*} [Fintype I] [Fintype J] [Field 𝕜]

def forward (C : Matrix I J 𝕜) (a : J → 𝕜) (c : 𝕜) : Matrix I J 𝕜 :=
  fun i j => C i j * a j / c
def backward (C : Matrix I J 𝕜) (p : I → 𝕜) (c : 𝕜) : Matrix J I 𝕜 :=
  fun j i => C i j * p i / c
def coupling (C : Matrix I J 𝕜) (a : J → 𝕜) (p : I → 𝕜) (c : 𝕜) : Matrix I J 𝕜 :=
  fun i j => p i * forward C a c i j

omit [Fintype I] in
theorem forward_row_sum (C : Matrix I J 𝕜) (a : J → 𝕜) (c : 𝕜)
    (hc : c ≠ 0) (hr : ∀ i, ∑ j, C i j * a j = c) (i : I) :
    ∑ j, forward C a c i j = 1 := by
  simp only [forward,div_eq_mul_inv,← Finset.sum_mul,hr i,mul_inv_cancel₀ hc]

omit [Fintype J] in
theorem backward_row_sum (C : Matrix I J 𝕜) (p : I → 𝕜) (c : 𝕜)
    (hc : c ≠ 0) (hp : ∀ j, ∑ i, p i * C i j = c) (j : J) :
    ∑ i, backward C p c j i = 1 := by
  simp only [backward,mul_comm (C _ _),div_eq_mul_inv,← Finset.sum_mul,hp j,
    mul_inv_cancel₀ hc]

omit [Fintype J] in
theorem transport_forward (C : Matrix I J 𝕜) (a : J → 𝕜) (p : I → 𝕜)
    (c : 𝕜) (hc : c ≠ 0) (hp : ∀ j, ∑ i, p i * C i j = c) :
    p ᵥ* forward C a c = a := by
  funext j
  change (∑ i, p i * (C i j * a j / c)) = a j
  calc
    _ = (∑ i, p i*C i j)*a j/c := by
      simp only [div_eq_mul_inv,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = a j := by rw [hp]; field_simp

omit [Fintype I] in
theorem transport_backward (C : Matrix I J 𝕜) (a : J → 𝕜) (p : I → 𝕜)
    (c : 𝕜) (hc : c ≠ 0) (hr : ∀ i, ∑ j, C i j * a j = c) :
    a ᵥ* backward C p c = p := by
  funext i
  change (∑ j, a j * (C i j * p i / c)) = p i
  calc
    _ = (∑ j, C i j*a j)*p i/c := by
      simp only [div_eq_mul_inv,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = p i := by rw [hr]; field_simp

omit [Fintype I] [Fintype J] in
theorem coupling_balance (C : Matrix I J 𝕜) (a : J → 𝕜) (p : I → 𝕜)
    (c : 𝕜) (i : I) (j : J) :
    coupling C a p c i j = a j * backward C p c j i := by
  unfold coupling forward backward
  ring

omit [Fintype I] in
theorem coupling_left (C : Matrix I J 𝕜) (a : J → 𝕜) (p : I → 𝕜)
    (c : 𝕜) (hc : c ≠ 0) (hr : ∀ i, ∑ j, C i j * a j = c) (i : I) :
    ∑ j, coupling C a p c i j = p i := by
  simp only [coupling,← Finset.mul_sum,forward_row_sum C a c hc hr,mul_one]

omit [Fintype J] in
theorem coupling_right (C : Matrix I J 𝕜) (a : J → 𝕜) (p : I → 𝕜)
    (c : 𝕜) (hc : c ≠ 0) (hp : ∀ j, ∑ i, p i * C i j = c) (j : J) :
    ∑ i, coupling C a p c i j = a j := by
  exact congrFun (transport_forward C a p c hc hp) j

omit [Fintype I] in
theorem forward_backward_entry (C : Matrix I J 𝕜) (a : J → 𝕜) (p : I → 𝕜)
    (c : 𝕜) (i k : I) :
    (forward C a c * backward C p c) i k =
      p k / c^2 * ∑ j, C i j * C k j * a j := by
  simp only [Matrix.mul_apply,forward,backward,Finset.mul_sum,div_eq_mul_inv]
  apply Finset.sum_congr rfl
  intro j _
  ring

omit [Fintype J] in
theorem backward_forward_entry (C : Matrix I J 𝕜) (a : J → 𝕜) (p : I → 𝕜)
    (c : 𝕜) (j k : J) :
    (backward C p c * forward C a c) j k =
      a k / c^2 * ∑ i, C i j * C i k * p i := by
  simp only [Matrix.mul_apply,forward,backward,Finset.mul_sum,div_eq_mul_inv]
  apply Finset.sum_congr rfl
  intro i _
  ring

omit [Fintype I] in
theorem forward_backward_balance (C : Matrix I J 𝕜) (a : J → 𝕜) (p : I → 𝕜)
    (c : 𝕜) (i k : I) :
    p i * (forward C a c * backward C p c) i k =
      p k * (forward C a c * backward C p c) k i := by
  simp only [forward_backward_entry,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

omit [Fintype J] in
theorem backward_forward_balance (C : Matrix I J 𝕜) (a : J → 𝕜) (p : I → 𝕜)
    (c : 𝕜) (j k : J) :
    a j * (backward C p c * forward C a c) j k =
      a k * (backward C p c * forward C a c) k j := by
  simp only [backward_forward_entry,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem forward_backward_stationary (C : Matrix I J 𝕜) (a : J → 𝕜) (p : I → 𝕜)
    (c : 𝕜) (hc : c ≠ 0) (hr : ∀ i, ∑ j, C i j * a j = c)
    (hp : ∀ j, ∑ i, p i * C i j = c) :
    p ᵥ* (forward C a c * backward C p c) = p := by
  rw [← Matrix.vecMul_vecMul,transport_forward C a p c hc hp,
    transport_backward C a p c hc hr]

theorem backward_forward_stationary (C : Matrix I J 𝕜) (a : J → 𝕜) (p : I → 𝕜)
    (c : 𝕜) (hc : c ≠ 0) (hr : ∀ i, ∑ j, C i j * a j = c)
    (hp : ∀ j, ∑ i, p i * C i j = c) :
    a ᵥ* (backward C p c * forward C a c) = a := by
  rw [← Matrix.vecMul_vecMul,transport_backward C a p c hc hr,
    transport_forward C a p c hc hp]
end Algebra

section Order
variable {I J 𝕜 : Type*} [Fintype I] [Fintype J] [Field 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜]

omit [Fintype I] in
theorem forward_stochastic (C : Matrix I J 𝕜) (a : J → 𝕜) (c : 𝕜)
    (hC : ∀ i j, 0 ≤ C i j) (ha : ∀ j, 0 ≤ a j) (hc : 0 < c)
    (hr : ∀ i, ∑ j, C i j * a j = c) :
    (∀ i j, 0 ≤ forward C a c i j) ∧ (∀ i, ∑ j, forward C a c i j = 1) := by
  exact ⟨fun i j => div_nonneg (mul_nonneg (hC i j) (ha j)) hc.le,
    forward_row_sum C a c hc.ne' hr⟩

omit [Fintype J] in
theorem backward_stochastic (C : Matrix I J 𝕜) (p : I → 𝕜) (c : 𝕜)
    (hC : ∀ i j, 0 ≤ C i j) (hp : ∀ i, 0 ≤ p i) (hc : 0 < c)
    (hcol : ∀ j, ∑ i, p i * C i j = c) :
    (∀ j i, 0 ≤ backward C p c j i) ∧ (∀ j, ∑ i, backward C p c j i = 1) := by
  exact ⟨fun j i => div_nonneg (mul_nonneg (hC i j) (hp i)) hc.le,
    backward_row_sum C p c hc.ne' hcol⟩

omit [Fintype I] [Fintype J] in
theorem coupling_nonneg (C : Matrix I J 𝕜) (a : J → 𝕜) (p : I → 𝕜) (c : 𝕜)
    (hC : ∀ i j, 0 ≤ C i j) (ha : ∀ j, 0 ≤ a j) (hp : ∀ i, 0 ≤ p i)
    (hc : 0 ≤ c) (i : I) (j : J) : 0 ≤ coupling C a p c i j :=
  mul_nonneg (hp i) (div_nonneg (mul_nonneg (hC i j) (ha j)) hc)
end Order

section Cut
variable {I 𝕜 : Type*} [DecidableEq I] [CommRing 𝕜]

def cutFlow (f : I → I → 𝕜) (S T : Finset I) : 𝕜 := ∑ i ∈ S, ∑ j ∈ T, f i j

/-- Internal physical edges cancel once each; the cut retains two marginals. -/
theorem cut_divergence (f : I → I → 𝕜) {V S : Finset I} (hSV : S ⊆ V) :
    cutFlow f S (V \ S) - cutFlow f (V \ S) S =
      ∑ i ∈ S, ((∑ j ∈ V, f i j) - ∑ j ∈ V, f j i) := by
  have split (g : I → 𝕜) : (∑ j ∈ V, g j) = (∑ j ∈ S, g j)+(∑ j ∈ V \ S, g j) := by
    have h := Finset.sum_sdiff hSV (f := g)
    exact h.symm.trans (add_comm _ _)
  simp_rw [split]
  simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib,cutFlow]
  rw [show (∑ i ∈ S, ∑ j ∈ S, f j i) = ∑ i ∈ S, ∑ j ∈ S, f i j from Finset.sum_comm]
  rw [show (∑ i ∈ S, ∑ j ∈ V \ S, f j i) =
    ∑ i ∈ V \ S, ∑ j ∈ S, f i j from Finset.sum_comm]
  ring

theorem cut_of_marginals (f : I → I → 𝕜) {V S : Finset I} (hSV : S ⊆ V)
    (p a : I → 𝕜) (hl : ∀ i ∈ S, ∑ j ∈ V, f i j = p i)
    (hr : ∀ i ∈ S, ∑ j ∈ V, f j i = a i) :
    cutFlow f S (V \ S)-cutFlow f (V \ S) S = (∑ i ∈ S, p i)-(∑ i ∈ S, a i) := by
  rw [cut_divergence f hSV,← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun i hi => by rw [hl i hi,hr i hi])
end Cut

end LeanCH.BR.TwoLawTransport
