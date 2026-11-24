import checkpoints.shen_extension.PacketCompression

namespace LeanCH.BR.PacketCompression
open Finset Matrix
open scoped Matrix
variable {I : Type*} [Fintype I] [DecidableEq I]

def Feasible (K : Matrix I I ℝ) : Prop :=
  ∃ t : I → ℝ, Live t ∧ ∀ j, t j ≤ (t ᵥ* K) j

theorem pivot_pays {K : Matrix I I ℝ} (nn : ∀ i j, 0 ≤ K i j) (b : I)
    (loop : 1 ≤ K b b) : Feasible K := by
  let t : I → ℝ := fun i => if i = b then 1 else 0
  have value (j : I) : (t ᵥ* K) j = K b j := by simp [t,vecMul,dotProduct,ite_mul]
  refine ⟨t,⟨fun i => by dsimp [t]; split <;> norm_num, b,by simp [t]⟩,fun j => ?_⟩
  rw [value]
  by_cases h : j = b
  · subst j; simpa [t] using loop
  · simpa [t,h] using nn b j

/-- Eliminate b by summing every number of consecutive loops at b.
This equivalence includes equality at all other heads. -/
theorem eliminate {K : Matrix I I ℝ} (nn : ∀ i j, 0 ≤ K i j) (b : I)
    (loop : K b b < 1) :
    let F := (univ : Finset I).erase b
    let L : Matrix F F ℝ := fun i j => K i j + K i b * (K b j / (1-K b b))
    (∀ i j, 0 ≤ L i j) ∧ (Feasible K ↔ Feasible L) := by
  classical
  intro F L
  let d := 1 - K b b
  have hd : 0 < d := sub_pos.mpr loop
  have dec (t : I → ℝ) (j : I) :
      (t ᵥ* K) j = (∑ k : F, t k * K k j) + t b * K b j := by
    rw [sum_coe_sort F (fun k => t k * K k j)]
    exact (sum_erase_add (s:=univ) (fun k => t k * K k j) (mem_univ b)).symm
  have update (s : F → ℝ) (j : F) : (s ᵥ* L) j =
      (∑ i : F, s i * K i j) + (∑ i : F, s i * K i b)/d*K b j := by
    change (∑ i : F, s i * (K i j + K i b * (K b j / d))) = _
    simp only [mul_add,sum_add_distrib]
    congr 1
    simp only [div_eq_mul_inv,sum_mul]
    exact sum_congr rfl fun i _ => by ring
  refine ⟨fun i j => add_nonneg (nn _ _) (mul_nonneg (nn _ _) (div_nonneg (nn _ _) hd.le)),?_⟩
  constructor
  · rintro ⟨t,⟨tn,v,tv⟩,ok⟩
    let s : F → ℝ := fun i => t i
    have atb := ok b
    rw [dec] at atb
    have bound : t b ≤ (∑ i : F, s i * K i b)/d := by
      apply (le_div_iff₀ hd).mpr
      change t b * (1 - K b b) ≤ ∑ i : F, t i * K i b
      linarith
    have live : ∃ i : F, 0 < s i := by
      by_contra! no
      have zero (i : F) : s i = 0 := le_antisymm (no i) (tn i)
      simp [zero] at bound
      by_cases eq : v = b
      · exact tv.not_ge (eq ▸ bound)
      · exact tv.ne' (zero ⟨v,mem_erase.mpr ⟨eq,mem_univ v⟩⟩)
    refine ⟨s,⟨fun i => tn i,live⟩,fun j => ?_⟩
    rw [update]
    exact (ok j).trans ((dec t j) ▸ add_le_add_right
      (mul_le_mul_of_nonneg_right bound (nn b j)) _)
  · rintro ⟨s,⟨sn,v,sv⟩,ok⟩
    let a := (∑ i : F, s i * K i b)/d
    have an : 0 ≤ a := div_nonneg (sum_nonneg fun i _ => mul_nonneg (sn i) (nn i b)) hd.le
    let t : I → ℝ := fun i => if h : i ∈ F then s ⟨i,h⟩ else a
    have tb : t b = a := by simp [t,F]
    have keep (i : F) : t i = s i := by simp [t,i.property]
    refine ⟨t,⟨fun i => by dsimp [t]; split <;> first | apply sn | apply an,
      v,by simpa only [keep] using sv⟩,fun j => ?_⟩
    rw [dec,tb]
    simp only [keep]
    by_cases eq : j = b
    · subst j; rw [tb]
      have pay : a * (1 - K b b) = ∑ i : F, s i * K i b := div_mul_cancel₀ _ hd.ne'
      linarith
    · let k : F := ⟨j,mem_erase.mpr ⟨eq,mem_univ j⟩⟩
      change t k ≤ (∑ i : F, s i * K i k) + a * K b k
      rw [keep]
      exact (ok k).trans_eq (update s k)

end LeanCH.BR.PacketCompression

#print axioms LeanCH.BR.PacketCompression.pivot_pays
#print axioms LeanCH.BR.PacketCompression.eliminate

