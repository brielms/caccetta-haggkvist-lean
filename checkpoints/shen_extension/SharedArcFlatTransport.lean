import checkpoints.shen_extension.SharedArcFlatBudget
import LeanCH.BR.BRWeightedOrderCongruence
import LeanCH.BR.BRFiniteUniformInverse

namespace LeanCH.BR.Closure.SharedArcFlatTransport
open Finset Matrix WeightedSD FiniteCutInverse ShortestCycleWeights FirstPacketBarrier MarkedCyclePeeling
open scoped Matrix

/-- A unit graph fixes the order modulo q. On the same labels every
nonnegative centered graph inverse is strictly positive, even on its diagonal. -/
theorem flat_inverse_positive {q : ℕ} (hq : 2 ≤ q) {E D : CH.Digraph} {V : Finset ℕ}
    {w : ℕ → ℚ} (wm : mass V w = 1) (wr : ∀ i ∈ V, WeightedSD.row q E V w i = 1)
    {H : Matrix V V ℝ} (inv : CommonInverse (realMatrix q D V) H) (i j : V) : 0 < H i j := by
  by_cases e : i=j
  · subst j
    apply lt_of_le_of_ne (inv.nonneg i i)
    intro zero
    let _ : Fact (1<q) := ⟨by omega⟩
    have one := normalized_rows_card_mod q E V w wm wr
    have two := UniformInverse.zero_diagonal_order hq (fun i j : V => D i j) inv
      (by intro i j; by_cases h : D i j=true <;> simp [realMatrix_entry,h]) i zero.symm
    rw [Fintype.card_coe] at two
    exact one_ne_zero (α := ZMod q) (by linear_combination one - two)
  · exact InverseOffDiagonal.graph_positive hq inv e

/-- Row mass on S plus the mass on the opposite rectangle equals column
mass outside T plus the mass crossing from S to T. -/
theorem rectangle {I : Type*} [Fintype I] [DecidableEq I]
    (K : I → I → ℝ) (r c : I → ℝ)
    (rows : ∀ i, ∑ j, K i j = r i) (cols : ∀ j, ∑ i, K i j = c j)
    (S T : Finset I) :
    (∑ i ∈ S, r i) + (∑ i ∈ Sᶜ, ∑ j ∈ Tᶜ, K i j) =
      (∑ j ∈ Tᶜ, c j) + ∑ i ∈ S, ∑ j ∈ T, K i j := by
  have rs (i : I) : (∑ j ∈ T, K i j) + (∑ j ∈ Tᶜ, K i j) = r i :=
    (sum_add_sum_compl T _).trans (rows i)
  have cs (j : I) : (∑ i ∈ S, K i j) + (∑ i ∈ Sᶜ, K i j) = c j :=
    (sum_add_sum_compl S _).trans (cols j)
  simp_rw [← rs, ← cs, sum_add_distrib]
  rw [sum_comm (s:=Tᶜ) (t:=S), sum_comm (s:=Tᶜ) (t:=Sᶜ)]
  ring

/-- Bounds on a rectangle, using a separately chosen native insertion in
each cell. Equality is excluded when a charged cell lies in
the opposite rectangle. All terms in the bound use only D, E and their
flat laws, without the inverse of the native graph. -/
def CutCondition {q n} (X : Model q n) (F : Family) (w p : ℕ → ℚ)
    (choose : X.V → X.V → SharedArcFlatCut.Missing X F) (S T : Finset X.V) : Prop :=
    let D := realMatrix q X.D X.V
    let R := realMatrix q (graph X.D F) X.V
    let W := fun i : X.V => (w i : ℝ)
    let P := fun i : X.V => (p i : ℝ)
    let x := P ᵥ* (D-R)
    let y := (D-R) *ᵥ W
    let bound := fun i j =>
      let f := (choose i j).val
      SharedArcFlatResponse.test R⁻¹ W P q f.1 f.2 i j / ((q : ℝ) * P f.1 * W f.2)
    let source := ∑ i ∈ S, x i * W i
    let capacity := (∑ j ∈ Tᶜ, P j * y j) + ∑ i ∈ S, ∑ j ∈ T, x i * bound i j * y j
    source ≤ capacity ∧
      ((∃ i ∈ Sᶜ, ∃ j ∈ Tᶜ, 0 < x i ∧ 0 < y j) → source < capacity)

theorem on_flat {q n} (X : Model q n) (hq : 2 ≤ q) (small : SmallerSmallRow q X.V.card)
    (F : Family) {w p : ℕ → ℚ} (pos : ∀ i ∈ X.V, 0 < w i ∧ 0 < p i)
    (wm : mass X.V w = 1) (pm : mass X.V p = 1)
    (wr : ∀ i ∈ X.V, WeightedSD.row q (graph X.D F) X.V w i = 1)
    (pc : ∀ i ∈ X.V, WeightedSD.col q (graph X.D F) X.V p i = 1)
    (choose : X.V → X.V → SharedArcFlatCut.Missing X F) (S T : Finset X.V) :
    CutCondition X F w p choose S T := by
  classical
  unfold CutCondition
  intro D R W P x y bound source capacity
  obtain ⟨H,inv⟩ := strict_inverse_of_proper_smallRow (small.induced X.free)
    (fun i => (X.weights i : ℚ)) (fun _ _ => Nat.cast_nonneg _) X.strict
  have sub : ∀ i ∈ X.V, ∀ j ∈ X.V, graph X.D F i j = true → X.D i j = true := by
    intro i _ j _ ed
    obtain ⟨A,hit⟩ := active.mp ed
    exact (mem_col.mp hit).2.2.2
  have wn (i : X.V) : 0 < W i := by dsimp [W]; exact_mod_cast (pos i i.property).1
  have pn (i : X.V) : 0 < P i := by dsimp [P]; exact_mod_cast (pos i i.property).2
  have un (i j : X.V) : 0 ≤ (D-R) i j := sub_nonneg.mpr (realMatrix_mono_graph sub i j)
  have xn (i : X.V) : 0 ≤ x i := sum_nonneg fun j _ => mul_nonneg (pn j).le (un j i)
  have yn (j : X.V) : 0 ≤ y j := sum_nonneg fun i _ => mul_nonneg (un j i) (wn i).le
  have flat : excess R *ᵥ W = 0 := by
    funext i; rw [mulVec_excess,real_mass_of_rational_probability w wm]
    simpa [R,W,sub_eq_zero] using realMatrix_rational_rows w 1 wr i
  have dual : P ᵥ* excess R = 0 := by
    funext i; rw [vecMul_excess,real_mass_of_rational_probability p pm]
    simpa [R,P,sub_eq_zero] using realMatrix_rational_columns p 1 pc i
  have edit : D-R = excess D-excess R := by ext i j; simp [excess]
  have back : H *ᵥ y = W := by
    dsimp only [y]
    rw [edit,sub_mulVec,flat,sub_zero,mulVec_mulVec,mul_eq_one_comm.mp inv.right,one_mulVec]
  have left : x ᵥ* H = P := by
    dsimp only [x]
    rw [edit,vecMul_sub,dual,sub_zero,vecMul_vecMul,inv.right,vecMul_one]
  let K (i j : X.V) := x i * H i j * y j
  have rows (i : X.V) : (∑ j, K i j) = x i * W i := by
    simp only [K,mul_assoc,←mul_sum]; rw [←back]; rfl
  have cols (j : X.V) : (∑ i, K i j) = P j * y j := by
    simp only [K,←sum_mul]; rw [←left]; rfl
  have le (i j : X.V) : H i j ≤ bound i j := by
    let f := choose i j
    apply (le_div_iff₀ (mul_pos (mul_pos (by exact_mod_cast (by omega : 0<q)) (pn f.val.1)) (wn f.val.2))).mpr
    rw [mul_comm (H i j)]
    exact StrictSubgraphInverse.common_floor hq inv sub f.val.1 f.val.2 f.property.2 f.property.1 pos wm wr pc i j
  have cap : (∑ i ∈ S, ∑ j ∈ T, K i j) ≤ ∑ i ∈ S, ∑ j ∈ T, x i * bound i j * y j :=
    sum_le_sum fun i _ => sum_le_sum fun j _ => mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (le i j) (xn i)) (yn j)
  have nn (i j : X.V) : 0 ≤ K i j := mul_nonneg (mul_nonneg (xn i) (inv.nonneg i j)) (yn j)
  have opposite : 0 ≤ ∑ i ∈ Sᶜ, ∑ j ∈ Tᶜ, K i j :=
    sum_nonneg fun i _ => sum_nonneg fun j _ => nn i j
  have identity := rectangle K _ _ rows cols S T
  change (∑ i ∈ S, x i * W i) ≤ _ ∧ _
  constructor
  · dsimp only [capacity]; linarith
  · rintro ⟨i,hi,j,hj,xi,yj⟩
    have cell : 0 < K i j := mul_pos (mul_pos xi (flat_inverse_positive hq wm wr inv i j)) yj
    have inner := sum_pos' (s:=Tᶜ) (fun k _ => nn i k) ⟨j,hj,cell⟩
    have extra := sum_pos' (s:=Sᶜ) (fun a _ => sum_nonneg fun k _ => nn a k) ⟨i,hi,inner⟩
    dsimp only [source,capacity]; linarith

/-- A witness on the old flat family directly supplies the literal
capstone's current progress goal for the selected attachment. -/
theorem progress_of_failed_cut {q n} (X : Model q n) (hq : 2 ≤ q) (small : SmallerSmallRow q X.V.card)
    (F : Family) (B : Finset ℕ) (H : Matrix X.V X.V ℝ) (prices : ℕ → ℚ) (c : ℚ)
    {w p : ℕ → ℚ} (pos : ∀ i ∈ X.V, 0 < w i ∧ 0 < p i)
    (wm : mass X.V w = 1) (pm : mass X.V p = 1)
    (wr : ∀ i ∈ X.V, WeightedSD.row q (graph X.D F) X.V w i = 1)
    (pc : ∀ i ∈ X.V, WeightedSD.col q (graph X.D F) X.V p i = 1)
    (choose : X.V → X.V → SharedArcFlatCut.Missing X F) (S T : Finset X.V)
    (failure : ¬CutCondition X F w p choose S T) : SharedArcFlatBudget.ProgressAt X F B H prices c :=
  (failure (on_flat X hq small F pos wm pm wr pc choose S T)).elim

end LeanCH.BR.Closure.SharedArcFlatTransport
#print axioms LeanCH.BR.Closure.SharedArcFlatTransport.flat_inverse_positive
#print axioms LeanCH.BR.Closure.SharedArcFlatTransport.rectangle
#print axioms LeanCH.BR.Closure.SharedArcFlatTransport.on_flat
#print axioms LeanCH.BR.Closure.SharedArcFlatTransport.progress_of_failed_cut
