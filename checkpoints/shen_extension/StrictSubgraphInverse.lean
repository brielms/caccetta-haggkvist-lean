import LeanCH.BR.BRWeightedDeletionThreshold
import checkpoints.shen_extension.SharedArcFlatResponse

namespace LeanCH.BR.Closure.StrictSubgraphInverse
open Finset Matrix FiniteCutInverse WeightedSD
open scoped Matrix
variable {I : Type*} [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
/-- A positive supersolution of I-K gives the finite minimum principle. -/
private theorem minimum (K : Matrix I I ℝ) (kn : ∀ i j, 0 ≤ K i j) (x : I → ℝ)
    (xp : ∀ i, 0 < x i) (upper : ∀ i, (K *ᵥ x) i < x i)
    (y : I → ℝ) (lower : ∀ i, (K *ᵥ y) i ≤ y i) (a : I) : 0 ≤ y a := by
  classical
  obtain ⟨i,_,least⟩ := exists_min_image univ (fun j => y j / x j) ⟨a,mem_univ a⟩
  let t := y i / x i
  have atI : t * x i = y i := div_mul_cancel₀ _ (xp i).ne'
  have bound (j : I) : t * x j ≤ y j := (le_div_iff₀ (xp j)).mp (least j (mem_univ j))
  by_contra! negative
  have neg : t < 0 := lt_of_le_of_lt (least a (mem_univ a)) (div_neg_of_neg_of_pos negative (xp a))
  have le : t * (K *ᵥ x) i ≤ (K *ᵥ y) i := by
    change t * (∑ j, K i j * x j) ≤ ∑ j, K i j * y j
    rw [mul_sum]
    apply sum_le_sum
    intro j _
    calc
      _ = K i j * (t * x j) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (bound j) (kn i j)
  have contradiction := (mul_lt_mul_of_neg_left (upper i) neg).trans_le (le.trans (lower i))
  rw [atI] at contradiction
  exact contradiction.false

/-- One native common inverse and a strict witness on the subgraph
suffice. No induction on the subgraph or Neumann-series premise is needed. -/
theorem inherits {D G H : Matrix I I ℝ} (native : CommonInverse D H)
    (sub : ∀ i j, G i j ≤ D i j) (x : I → ℝ) (xn : ∀ i, 0 ≤ x i)
    (strict : ∀ i, 0 < (excess G *ᵥ x) i) :
    ∃ L : Matrix I I ℝ, CommonInverse G L ∧ ∀ i j, H i j ≤ L i j := by
  classical
  let B := excess G
  let K := H*(D-G)
  have kn (i j : I) : 0 ≤ K i j := sum_nonneg fun l _ =>
    mul_nonneg (native.nonneg i l) (sub_nonneg.mpr (sub l j))
  have edit : excess D = B+(D-G) := by ext i j; simp only [B,excess,Matrix.add_apply,Matrix.sub_apply]; ring
  have split (v : I → ℝ) : H *ᵥ (B *ᵥ v) + K *ᵥ v = v := by
    have left := mul_eq_one_comm.mp native.right
    calc
      _ = H *ᵥ (excess D *ᵥ v) := by rw [edit,add_mulVec,mulVec_add,mulVec_mulVec v H (D-G)]
      _ = v := by rw [mulVec_mulVec,left,one_mulVec]
  have hx (i : I) : 0 < (H *ᵥ (B *ᵥ x)) i := by
    obtain ⟨k,hk⟩ : ∃ k, 0 < H i k := by
      by_contra! no
      exact (inverse_row_sum_pos native i).not_ge (sum_nonpos fun k _ => no k)
    exact sum_pos' (fun j _ => mul_nonneg (native.nonneg i j) (strict j).le)
      ⟨k,mem_univ k,mul_pos hk (strict k)⟩
  have upper (i : I) : (K *ᵥ x) i < x i := by
    have h := congrFun (split x) i
    change (H *ᵥ (B *ᵥ x)) i + (K *ᵥ x) i = x i at h
    linarith [hx i]
  have xp (i : I) : 0<x i := (sum_nonneg (fun j _ => mul_nonneg (kn i j) (xn j))).trans_lt (upper i)
  have reflect (v : I → ℝ) (good : ∀ j, 0 ≤ (B *ᵥ v) j) : ∀ i, 0 ≤ v i := by
    apply minimum K kn x xp upper v
    intro i
    have nn : 0 ≤ (H *ᵥ (B *ᵥ v)) i := sum_nonneg fun j _ => mul_nonneg (native.nonneg i j) (good j)
    have h := congrFun (split v) i
    change (H *ᵥ (B *ᵥ v)) i + (K *ᵥ v) i = v i at h
    linarith
  have inj : Function.Injective B.mulVec := by
    intro v w eq
    have hi (i : I) : 0 ≤ (v-w) i := reflect (v-w) (by simp [mulVec_sub,eq]) i
    have lo (i : I) : 0 ≤ (w-v) i := reflect (w-v) (by simp [mulVec_sub,eq]) i
    exact funext fun i => le_antisymm (sub_nonneg.mp (lo i)) (sub_nonneg.mp (hi i))
  have unit := (Matrix.isUnit_iff_isUnit_det B).mp (Matrix.mulVec_injective_iff_isUnit.mp inj)
  have right := Matrix.mul_nonsing_inv B unit
  have inv : CommonInverse G B⁻¹ := by
    refine ⟨fun i j => reflect (fun k => B⁻¹ k j) (fun k => ?_) i,right⟩
    change 0 ≤ (B*B⁻¹) k j
    rw [right,Matrix.one_apply]; split <;> norm_num
  exact ⟨_,inv,inverse_antitone inv native sub⟩

/-- On a flat old graph the inverse of the single native host bounds every
tensor from below, on every pair of labels and for every native insertion. -/
theorem common_floor {q : ℕ} (hq : 2 ≤ q) {D E : CH.Digraph} {V : Finset ℕ}
    {H : Matrix V V ℝ} (native : CommonInverse (realMatrix q D V) H)
    (sub : ∀ i∈V, ∀ j∈V, E i j=true → D i j=true)
    (a b : V) (fresh : E a b=false) (present : D a b=true)
    {w p : ℕ→ℚ} (wp : ∀ i∈V, 0<w i ∧ 0<p i) (wm : mass V w=1)
    (wr : ∀ i∈V, WeightedSD.row q E V w i=1) (pc : ∀ i∈V, WeightedSD.col q E V p i=1)
    (v k : V) :
    ((q:ℝ)*(p a:ℝ)*(w b:ℝ))*H v k ≤
      SharedArcFlatResponse.test (realMatrix q E V)⁻¹ (fun i : V => (w i:ℝ)) (fun i : V => (p i:ℝ)) q a b v k := by
  let G := insertArc E a b
  have add (i) (hi : i∈V) (j) (hj : j∈V) (ed : G i j=true) : D i j=true := by
    by_cases here : i=(a:ℕ) ∧ j=(b:ℕ)
    · exact here.1 ▸ here.2 ▸ present
    · exact sub i hi j hj (by simpa [G,insertArc,here] using ed)
  have bad : ¬SmallRow q G V := positive_feasible_extension_not_smallRow (D:=E) (E:=G) hq
    (fun i _ j _ yes => insertArc_mono E a b i j yes) w (fun i hi => (wp i hi).1)
    (fun i hi => by rw [wm,wr i hi]) a.property b.property (by simp [fresh]) (by simp [G,insertArc])
  obtain ⟨z,zn,_,high⟩ := strict_witness_of_not_smallRow bad
  let X : V → ℝ := fun i => (z i : ℝ)
  have strict (i : V) : 0 < (excess (realMatrix q G V) *ᵥ X) i := by
    rw [mulVec_excess,sub_pos]
    have e := high i i.property
    rw [←matrix_row q G V z i,mass,←sum_coe_sort] at e
    change (∑ j : V, (z j:ℝ)) < ∑ j : V, (WeightedArithmetic.rationalMatrix q (adjacencyMatrix G V) i j:ℝ)*(z j:ℝ)
    exact_mod_cast e
  obtain ⟨L,inv,bound⟩ := inherits native (realMatrix_mono_graph add) X
    (fun i => by dsimp [X]; exact_mod_cast zn i i.property) strict
  have eq := SharedArcFlatResponse.rectangle_identity (Matrix.mul_nonsing_inv _ (SharedArcFlatResponse.matrix_unit hq E V))
    (realMatrix_insert_difference (q:=q) a b (by simp [fresh])) inv
    (by simpa using funext (realMatrix_rational_rows w 1 wr))
    (by simpa using funext (realMatrix_rational_columns p 1 pc)) (real_mass_of_rational_probability w wm) v k
  have pa : (0:ℝ) ≤ (p a:ℝ) := by exact_mod_cast (wp a a.property).2.le
  have wb : (0:ℝ) ≤ (w b:ℝ) := by exact_mod_cast (wp b b.property).1.le
  exact (mul_le_mul_of_nonneg_left (bound v k) (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) pa) wb)).trans_eq eq.symm

/-- The native inverse drops out of this necessary inequality. For each
tail i one can use a different fresh arc to bound the cost at (v,i). -/
theorem row_budget {q : ℕ} (hq : 2 ≤ q) {D E : CH.Digraph} {V : Finset ℕ}
    {H : Matrix V V ℝ} (native : CommonInverse (realMatrix q D V) H)
    (sub : ∀ i∈V, ∀ j∈V, E i j=true → D i j=true)
    (a b : V → V) (fresh : ∀ i, E (a i) (b i)=false) (present : ∀ i, D (a i) (b i)=true)
    {w p : ℕ→ℚ} (wp : ∀ i∈V, 0<w i ∧ 0<p i) (wm : mass V w=1)
    (wr : ∀ i∈V, WeightedSD.row q E V w i=1) (pc : ∀ i∈V, WeightedSD.col q E V p i=1)
    (v : V) :
    let W := fun i : V => (w i:ℝ)
    let P := fun i : V => (p i:ℝ)
    let U := realMatrix q D V - realMatrix q E V
    W v ≤ ∑ i : V, (SharedArcFlatResponse.test (realMatrix q E V)⁻¹ W P q (a i) (b i) v i /
      ((q:ℝ)*P (a i)*W (b i))) * (U *ᵥ W) i := by
  intro W P U
  have flat : excess (realMatrix q E V) *ᵥ W = 0 := by
    funext i
    rw [mulVec_excess,real_mass_of_rational_probability w wm]
    simpa only [Pi.zero_apply,sub_eq_zero] using (show (realMatrix q E V *ᵥ W) i=1 from by
      simpa [W] using realMatrix_rational_rows w 1 wr i)
  have edit : U=excess (realMatrix q D V)-excess (realMatrix q E V) := by
    ext i j; simp [U,excess]
  have back : H *ᵥ (U *ᵥ W) = W := by
    rw [edit,sub_mulVec,flat,sub_zero,mulVec_mulVec,mul_eq_one_comm.mp native.right,one_mulVec]
  have nn (i : V) : 0 ≤ (U *ᵥ W) i := sum_nonneg fun j _ =>
    mul_nonneg (sub_nonneg.mpr (realMatrix_mono_graph sub i j)) (by dsimp [W]; exact_mod_cast (wp j j.property).1.le)
  calc
    W v = (H *ᵥ (U *ᵥ W)) v := congrFun back.symm v
    _ ≤ _ := by
      apply sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_right _ (nn i)
      have scale : 0 < (q:ℝ)*P (a i)*W (b i) := by
        have hp : 0 < P (a i) := by dsimp [P]; exact_mod_cast (wp _ (a i).property).2
        have hw : 0 < W (b i) := by dsimp [W]; exact_mod_cast (wp _ (b i).property).1
        exact mul_pos (mul_pos (by exact_mod_cast (by omega : 0<q)) hp) hw
      apply (le_div_iff₀ scale).mpr
      rw [mul_comm (H v i)]
      exact common_floor hq native sub (a i) (b i) (fresh i) (present i) wp wm wr pc v i

end LeanCH.BR.Closure.StrictSubgraphInverse
#print axioms LeanCH.BR.Closure.StrictSubgraphInverse.inherits
#print axioms LeanCH.BR.Closure.StrictSubgraphInverse.common_floor
#print axioms LeanCH.BR.Closure.StrictSubgraphInverse.row_budget

