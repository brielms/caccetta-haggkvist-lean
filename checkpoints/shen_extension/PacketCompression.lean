import LeanCH.BR.BRWeightedInverseComparison

namespace LeanCH.BR.PacketCompression
open Finset Matrix FiniteCutInverse WeightedSD
open scoped Matrix
variable {V K : Type*} [Fintype V] [DecidableEq V] [Fintype K]

/-- A distribution up to arbitrary positive scaling. -/
def Live {ι : Type*} (p : ι → ℝ) : Prop := (∀ i, 0 ≤ p i) ∧ ∃ i, 0 < p i

private theorem mono_vec {I J : Type*} [Fintype I] (A : Matrix I J ℝ)
    (hn : ∀ i j, 0 ≤ A i j) {u v : I → ℝ} (h : ∀ i, u i ≤ v i) (j : J) :
    (u ᵥ* A) j ≤ (v ᵥ* A) j :=
  sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (h i) (hn i j)

private theorem nn_vec {I J : Type*} [Fintype I] (A : Matrix I J ℝ)
    (hn : ∀ i j, 0 ≤ A i j) {u : I → ℝ} (h : ∀ i, 0 ≤ u i) (j : J) :
    0 ≤ (u ᵥ* A) j := sum_nonneg fun i _ => mul_nonneg (h i) (hn i j)

/-- If the removed nonnegative matrix factors as U*T, the complete
dual feasibility test lives on the intermediate index type K. -/
theorem paid_iff {R S H : Matrix V V ℝ} (inv : CommonInverse R H)
    (U : Matrix V K ℝ) (T : Matrix K V ℝ) (u0 : ∀ i j, 0 ≤ U i j) (t0 : ∀ i j, 0 ≤ T i j)
    (edit : excess S = excess R - U*T) :
    (∃ p : V → ℝ, Live p ∧ ∀ i, (p ᵥ* excess S) i ≤ 0) ↔
    ∃ t : K → ℝ, Live t ∧ ∀ j, t j ≤ (t ᵥ* (T*H*U)) j := by
  have recover (p : V → ℝ) : (p ᵥ* excess R) ᵥ* H = p := by
    rw [vecMul_vecMul,inv.right,vecMul_one]
  have back (t : K → ℝ) : ((t ᵥ* T) ᵥ* H) ᵥ* excess R = t ᵥ* T := by
    rw [vecMul_vecMul (t ᵥ* T),mul_eq_one_comm.mp inv.right,vecMul_one]
  have transfer (t : K → ℝ) : t ᵥ* (T*H*U) = ((t ᵥ* T) ᵥ* H) ᵥ* U := by
    rw [vecMul_vecMul,vecMul_vecMul,Matrix.mul_assoc]
  constructor
  · rintro ⟨p,⟨pn,v,pv⟩,ok⟩
    let t := p ᵥ* U
    let lifted := (t ᵥ* T) ᵥ* H
    have bound (i : V) : (p ᵥ* excess R) i ≤ (t ᵥ* T) i := by
      have h := ok i
      rw [edit,vecMul_sub,←vecMul_vecMul] at h
      exact sub_nonpos.mp h
    have larger (i : V) : p i ≤ lifted i := by
      simpa only [recover] using mono_vec H inv.nonneg bound i
    have tn := nn_vec U u0 pn
    have live : ∃ j, 0 < t j := by
      by_contra! none
      have z : t = 0 := funext fun j => le_antisymm (none j) (tn j)
      have e := larger v
      simp [lifted,z] at e
      exact pv.not_ge e
    refine ⟨t,⟨tn,live⟩,fun j => ?_⟩
    rw [transfer]
    exact mono_vec U u0 larger j
  · rintro ⟨t,⟨tn,j,tj⟩,ok⟩
    let p := (t ᵥ* T) ᵥ* H
    have pn := nn_vec H inv.nonneg (nn_vec T t0 tn)
    have below (k : K) : t k ≤ (p ᵥ* U) k := by simpa only [transfer] using ok k
    have live : ∃ i, 0 < p i := by
      by_contra! none
      have z : p = 0 := funext fun i => le_antisymm (none i) (pn i)
      have e := below j
      simp [z] at e
      exact tj.not_ge e
    refine ⟨p,⟨pn,live⟩,fun i => ?_⟩
    rw [edit,vecMul_sub,←vecMul_vecMul]
    change (((t ᵥ* T) ᵥ* H) ᵥ* excess R) i - ((p ᵥ* U) ᵥ* T) i ≤ 0
    rw [back]
    exact sub_nonpos.mpr (mono_vec T t0 below i)

theorem normalize {S : Matrix V V ℝ} :
    (∃ p : V → ℝ, Live p ∧ ∀ i, (p ᵥ* excess S) i ≤ 0) ↔
    ∃ p : V → ℝ, (∀ i, 0 ≤ p i) ∧ (∑ i, p i) = 1 ∧ ∀ i, (p ᵥ* S) i ≤ 1 := by
  constructor
  · rintro ⟨p,⟨pn,v,pv⟩,ok⟩
    have m : 0 < ∑ i, p i := sum_pos' (fun i _ => pn i) ⟨v,mem_univ v,pv⟩
    refine ⟨fun i => p i / ∑ j, p j,fun i => div_nonneg (pn i) m.le,?_,fun i => ?_⟩
    · simp only [div_eq_mul_inv,←sum_mul,mul_inv_cancel₀ m.ne']
    · have h := ok i
      rw [vecMul_excess] at h
      change (∑ k, (p k / ∑ j, p j) * S k i) ≤ 1
      calc
        _ = (p ᵥ* S) i / ∑ j, p j := by
          simp only [vecMul,dotProduct,div_eq_mul_inv,Finset.sum_mul]
          exact sum_congr rfl fun k _ => by ring
        _ ≤ 1 := (div_le_one m).mpr (sub_nonpos.mp h)
  · rintro ⟨p,pn,pm,ok⟩
    have live : ∃ i, 0 < p i := by
      by_contra! hn
      have le := sum_nonpos (s := (univ : Finset V)) (fun i _ => hn i)
      linarith
    exact ⟨p,⟨pn,live⟩,fun i => by rw [vecMul_excess,pm]; exact sub_nonpos.mpr (ok i)⟩

/-- Group all edits to the same head. Only these heads carry variables. -/
theorem on_heads {R S H : Matrix V V ℝ} (inv : CommonInverse R H)
    (sub : ∀ i j, S i j ≤ R i j) (F : Finset V)
    (outside : ∀ j, j ∉ F → ∀ i, S i j = R i j) :
    (∃ p : V → ℝ, (∀ i, 0 ≤ p i) ∧ (∑ i, p i) = 1 ∧ ∀ i, (p ᵥ* S) i ≤ 1) ↔
    ∃ t : F → ℝ, Live t ∧ ∀ j : F, t j ≤ ∑ k : F, t k * ∑ i, H k i * (R i j - S i j) := by
  classical
  let U : Matrix V F ℝ := fun i j => R i j - S i j
  let T : Matrix F V ℝ := fun k j => if (k : V) = j then 1 else 0
  have u0 (i : V) (k : F) : 0 ≤ U i k := sub_nonneg.mpr (sub i k)
  have t0 (k : F) (j : V) : 0 ≤ T k j := by dsimp [T]; split <;> norm_num
  have diff (i j : V) : (U*T) i j = R i j - S i j := by
    by_cases hj : j ∈ F
    · let z : F := ⟨j,hj⟩
      rw [Matrix.mul_apply,sum_eq_single z]
      · simp [z,U,T]
      · intro k _ ne
        have h : (k:V) ≠ j := fun eq => ne (Subtype.ext eq)
        simp [T,h]
      · simp
    · rw [outside j hj i,sub_self,Matrix.mul_apply]
      exact sum_eq_zero fun k _ => by
        have h : (k:V) ≠ j := fun e => hj (e ▸ k.property)
        simp [T,h]
  have edit : excess S = excess R - U*T := by
    ext i j
    simp only [Matrix.sub_apply,excess,diff]
    ring
  have entries (k j : F) : (T*H*U) k j = ∑ i, H k i * (R i j - S i j) := by
    have row (i : V) : (T*H) k i = H k i := by
      change (∑ l : V, (if (k : V) = l then (1:ℝ) else 0) * H l i) = H k i
      simp [ite_mul]
    change (∑ i : V, (T*H) k i * U i j) = _
    simp only [row,U]
  rw [← normalize,paid_iff inv U T u0 t0 edit]
  simp only [vecMul,dotProduct,entries]

/-- The graph-level equivalence uses the project's actual SmallRow predicate. -/
theorem graph_iff {q : ℕ} {D E : CH.Digraph} {V : Finset ℕ} (live : V.Nonempty)
    {H : Matrix V V ℝ} (inv : CommonInverse (realMatrix q D V) H)
    (sub : ∀ i∈V, ∀ j∈V, E i j=true → D i j=true) (F : Finset V)
    (outside : ∀ j : V, j ∉ F → ∀ i : V, E i j = D i j) :
    SmallRow q E V ↔ ∃ t : F → ℝ, Live t ∧ ∀ j : F, t j ≤ ∑ k : F, t k *
      ∑ i : V, H k i * (realMatrix q D V i j - realMatrix q E V i j) := by
  rw [← on_heads inv (realMatrix_mono_graph sub) F (by
    intro j hj i; simp only [realMatrix_entry,outside j hj i])]
  constructor
  · intro good
    obtain ⟨p,hp⟩ := realDual_of_smallRow good live
    refine ⟨fun i : V => p i,fun i => hp.nonneg i i.property,?_,fun i => ?_⟩
    · rw [sum_coe_sort]; exact hp.normalized
    · rw [realMatrix_col]; exact hp.columns i i.property
  · rintro ⟨p,pn,pm,pc⟩
    apply smallRow_of_realDual (p := realExtendWeight V p)
    constructor
    · intro i hi
      rw [realExtendWeight_on V p ⟨i,hi⟩]; exact pn _
    · rw [realMass_extendWeight]; exact pm
    · intro j hj
      have e : (fun i : V => realExtendWeight V p i) = p := funext (realExtendWeight_on V p)
      rw [←realMatrix_col q E V _ ⟨j,hj⟩,e]
      exact pc _

end LeanCH.BR.PacketCompression

#print axioms LeanCH.BR.PacketCompression.paid_iff
#print axioms LeanCH.BR.PacketCompression.graph_iff

