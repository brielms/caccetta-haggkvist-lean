import checkpoints.shen_extension.SharedArcPivotSpread
import checkpoints.shen_extension.SharedArcPivotGate
import checkpoints.shen_extension.SharedArcFlatResponse
import LeanCH.BR.BRWeightedFoldBoundary

/-! General q-free subset merge, whole-side single-pivot mass bounds,
sharp clean-parent spread (eliminating in-regular and bounded-ratio punctures),
universal Schur-complement diagonal dominance of the native inverse,
and quantitative non-domination / small-degree regular closure for the flat branch. -/

namespace LeanCH.BR.Closure.SharedArcPivotMerge
open Finset Matrix BRq2 BRq3 BR45 WeightedSD FiniteCutInverse ShortestCycleWeights
open SharedArcBarrier SharedArcComponentExchange FirstPacketBarrier MarkedCyclePeeling
open SharedArcPivotDetour
open scoped Matrix

/-! ### Part 1: General q-Free Subset Merge -/

section SubsetMerge

/-- Collapse a subset `S ⊆ V` into a representative `z ∈ S`:
    out-arcs of `z` are common out-neighbors of all vertices in `S`,
    in-arcs of `z` come from vertices outside `S` having at least one arc into `S`,
    and arcs inside `V \ S` are preserved. Internal arcs of `S` may be arbitrary. -/
def mergeOut (D : CH.Digraph) (V S : Finset ℕ) (z : ℕ) : CH.Digraph :=
  fun x y =>
    if x = z then decide (y ∈ V \ S ∧ ∀ s ∈ S, D s y = true)
    else if y = z then decide (x ∈ V \ S ∧ ∃ s ∈ S, D x s = true)
    else decide (x ∈ V \ S ∧ y ∈ V \ S ∧ D x y = true)

def mergeV (V S : Finset ℕ) (z : ℕ) : Finset ℕ := insert z (V \ S)

theorem mergeV_card_lt {V S : Finset ℕ} {z : ℕ}
    (hSV : S ⊆ V) (hcard : 2 ≤ S.card) (hz : z ∈ S) :
    (mergeV V S z).card < V.card := by
  have hzNot : z ∉ V \ S := fun h => (mem_sdiff.mp h).2 hz
  rw [mergeV, card_insert_of_notMem hzNot, card_sdiff_of_subset hSV]
  have hle := card_le_card hSV
  omega

private theorem walk_append {D : CH.Digraph} {V : Finset ℕ} {a b c l₁ l₂ : ℕ}
    (w₁ : Walk D V a b l₁) (w₂ : Walk D V b c l₂) : Walk D V a c (l₁ + l₂) := by
  induction w₁ with
  | refl => simpa using w₂
  | @step u v _ k hv ed _ ih =>
    simpa [Nat.succ_add] using Walk.step hv ed (ih w₂)

private theorem walk_reverse {D : CH.Digraph} {V : Finset ℕ} {a b l : ℕ}
    (ha : a ∈ V) (w : Walk (fun u v => D v u) V a b l) : Walk D V b a l := by
  induction w with
  | refl => exact .refl _
  | @step u v c k hv ed _ ih =>
    exact (ih hv).snoc ha ed

private theorem walk_split_or_avoid {D : CH.Digraph} {V : Finset ℕ} (z : ℕ) {a b l : ℕ}
    (w : Walk D V a b l) :
    (∃ l₁ l₂, l₁ + l₂ = l ∧ 0 < l₁ ∧ Walk D V a z l₁ ∧ Walk D V z b l₂) ∨
    (a ≠ z → Nonempty (Walk (fun x y => decide (x ≠ z ∧ y ≠ z ∧ D x y = true)) (V.erase z) a b l)) := by
  induction w with
  | refl =>
    right
    intro _
    exact ⟨.refl _⟩
  | @step u v c k hv ed tail ih =>
    by_cases hvz : v = z
    · left
      subst hvz
      exact ⟨1, k, by omega, by omega, Walk.step hv ed (.refl _), tail⟩
    · rcases ih with ⟨l₁, l₂, hsum, hpos, w₁, w₂⟩ | hno
      · left
        exact ⟨l₁ + 1, l₂, by omega, by omega, Walk.step hv ed w₁, w₂⟩
      · right
        intro huz
        obtain ⟨wt⟩ := hno hvz
        exact ⟨Walk.step (mem_erase.mpr ⟨hvz, hv⟩) (decide_eq_true ⟨huz, hvz, ed⟩) wt⟩

private theorem walk_avoid_z {D : CH.Digraph} {V S : Finset ℕ} {z a b l : ℕ}
    (w : Walk (fun x y => decide (x ≠ z ∧ y ≠ z ∧ mergeOut D V S z x y = true))
      ((mergeV V S z).erase z) a b l) : Walk D V a b l := by
  induction w with
  | refl => exact .refl _
  | @step u v c k hv ed _ ih =>
    obtain ⟨huz, hvz, hmo⟩ := of_decide_eq_true ed
    simp only [mergeOut, huz, hvz, ↓reduceIte] at hmo
    obtain ⟨_, hvS, huv⟩ := of_decide_eq_true hmo
    exact Walk.step (mem_sdiff.mp hvS).1 huv ih

private theorem mergeOut_z_loop {D : CH.Digraph} {V S : Finset ℕ} {z : ℕ} (hz : z ∈ S) :
    mergeOut D V S z z z = false := by
  simp only [mergeOut, ↓reduceIte, decide_eq_false_iff_not, not_and]
  intro hzS _
  exact (mem_sdiff.mp hzS).2 hz

/-- Any closed walk of length `1 ≤ l ≤ q` in `mergeOut` lifts to a closed walk of length `≤ l` in `D`. -/
theorem mergeOut_qfree {q : ℕ} {D : CH.Digraph} {V S : Finset ℕ} {z : ℕ}
    (hf : QFree D V q) (hSV : S ⊆ V) (hz : z ∈ S) :
    QFree (mergeOut D V S z) (mergeV V S z) q := by
  intro v l hpos hle w
  induction l using Nat.strong_induction_on generalizing v with
  | _ l ih =>
    let G := mergeOut D V S z
    let W := mergeV V S z
    have lift_at_z (wz : Walk G W z z l) : False := by
      cases wz with
      | refl => omega
      | @step _ u _ m hu ed₁ tail =>
        have huz : u ≠ z := by
          intro eq; subst eq
          exact Bool.noConfusion ((mergeOut_z_loop hz).symm.trans ed₁)
        cases m with
        | zero => cases tail; exact huz rfl
        | succ m' =>
          obtain ⟨x, mid, _, ed₂⟩ := tail.unsnoc
          rcases walk_split_or_avoid z mid with
              ⟨a₁, a₂, hasum, ha1, _, wa₂⟩ | hmid
          · exact ih (a₂ + 1) (by omega) z (by omega) (by omega) (wa₂.snoc (mem_insert_self z _) ed₂)
          · by_cases hxz : x = z
            · subst hxz; exact Bool.noConfusion ((mergeOut_z_loop hz).symm.trans ed₂)
            · obtain ⟨mid'⟩ := hmid huz
              have midD : Walk D V u x m' := walk_avoid_z mid'
              simp only [G, mergeOut, ↓reduceIte] at ed₁
              obtain ⟨huS, hall⟩ := of_decide_eq_true ed₁
              simp only [G, mergeOut, hxz, ↓reduceIte] at ed₂
              obtain ⟨_, s, hsS, hxs⟩ := of_decide_eq_true ed₂
              exact hf s (m' + 1 + 1) (by omega) (by omega)
                (Walk.step (mem_sdiff.mp huS).1 (hall s hsS) (midD.snoc (hSV hsS) hxs))
    by_cases hvz : v = z
    · subst hvz; exact lift_at_z w
    · rcases walk_split_or_avoid z w with ⟨l₁, l₂, hsum, _, w₁, w₂⟩ | hno
      · exact lift_at_z (hsum ▸ (Nat.add_comm l₂ l₁ ▸ walk_append w₂ w₁))
      · obtain ⟨w'⟩ := hno hvz
        exact hf v l hpos hle (walk_avoid_z w')

/-- Row-sum bound from merging any subset `S` of size at least 2 into a single vertex. -/
theorem mergeOut_common_bound {q : ℕ} (hq : 2 ≤ q) {D : CH.Digraph} {V S : Finset ℕ}
    (hf : QFree D V q) (hsmall : SmallerSmallRow q V.card)
    (hSV : S ⊆ V) (hcard : 2 ≤ S.card)
    (w : ℕ → ℚ) (hnn : ∀ x ∈ V, 0 ≤ w x) (hSpos : 0 < mass S w)
    (hrow : ∀ x ∈ V, mass V w ≤ WeightedSD.row q D V w x) :
    mass S w + (q : ℚ) * mass (V.filter (fun y => ∀ s ∈ S, D s y = true)) w ≤ mass V w := by
  classical
  obtain ⟨z, hz⟩ := card_pos.mp (by omega : 0 < S.card)
  let G := mergeOut D V S z
  let W := mergeV V S z
  let w' : ℕ → ℚ := fun x => if x = z then mass S w else w x
  have hzNot : z ∉ V \ S := fun h => (mem_sdiff.mp h).2 hz
  have hmass : mass W w' = mass V w := by
    rw [mass, show W = insert z (V \ S) from rfl, sum_insert hzNot]
    have hrest : ∑ x ∈ V \ S, w' x = mass (V \ S) w := by
      apply sum_congr rfl
      intro x hx
      have hxz : x ≠ z := fun eq => hzNot (eq ▸ hx)
      simp [w', hxz]
    rw [hrest, show w' z = mass S w by simp [w'], mass, mass, mass, add_comm, sum_sdiff hSV]
  have hnn' : ∀ x ∈ W, 0 ≤ w' x := by
    intro x hx
    by_cases hxz : x = z
    · subst hxz; simp [w', hSpos.le]
    · simp only [w', hxz, ↓reduceIte]
      exact hnn x (mem_sdiff.mp ((mem_insert.mp hx).resolve_left hxz)).1
  have hcomm_sub : V.filter (fun y => ∀ s ∈ S, D s y = true) ⊆ V \ S := by
    intro y hy
    obtain ⟨hyV, hall⟩ := mem_filter.mp hy
    refine mem_sdiff.mpr ⟨hyV, fun hyS => ?_⟩
    exact loopfree hf (by omega) hyV (hall y hyS)
  have hout_z : outW G W w' z = mass (V.filter (fun y => ∀ s ∈ S, D s y = true)) w := by
    unfold outW
    rw [show W = insert z (V \ S) from rfl, sum_insert hzNot,
        show G z z = false from mergeOut_z_loop hz]
    simp only [Bool.false_eq_true, ↓reduceIte, zero_add]
    rw [mass, ← sum_filter]
    have hcongr : (V \ S).filter (fun y => G z y = true) =
        V.filter (fun y => ∀ s ∈ S, D s y = true) := by
      ext y
      simp only [mem_filter, G, mergeOut, ↓reduceIte, decide_eq_true_eq]
      constructor
      · rintro ⟨hyS, _, hall⟩; exact ⟨(mem_sdiff.mp hyS).1, hall⟩
      · rintro ⟨hyV, hall⟩
        have hyS := hcomm_sub (mem_filter.mpr ⟨hyV, hall⟩)
        exact ⟨hyS, hyS, hall⟩
    rw [← hcongr]
    apply sum_congr rfl
    intro y hy
    have hyz : y ≠ z := fun eq => hzNot (eq ▸ (mem_filter.mp hy).1)
    simp [w', hyz]
  have hrow_other : ∀ x ∈ V \ S, mass W w' ≤ WeightedSD.row q G W w' x := by
    intro x hx
    have hxz : x ≠ z := fun eq => hzNot (eq ▸ hx)
    have hxV : x ∈ V := (mem_sdiff.mp hx).1
    rw [hmass]
    apply (hrow x hxV).trans
    unfold WeightedSD.row
    have hwx : w' x = w x := by simp [w', hxz]
    rw [hwx]
    apply add_le_add le_rfl
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg q)
    unfold outW
    rw [show W = insert z (V \ S) from rfl, sum_insert hzNot]
    have hsplit : ∑ y ∈ V, (if D x y = true then w y else 0) =
        (∑ y ∈ S, if D x y = true then w y else 0) +
        (∑ y ∈ V \ S, if D x y = true then w y else 0) := by
      rw [← sum_sdiff hSV (f := fun y => if D x y = true then w y else 0), add_comm]
    rw [hsplit]
    have hrest_eq : (∑ y ∈ V \ S, if G x y = true then w' y else 0) =
        (∑ y ∈ V \ S, if D x y = true then w y else 0) := by
      apply sum_congr rfl
      intro y hy
      have hyz : y ≠ z := fun eq => hzNot (eq ▸ hy)
      simp [G, mergeOut, hxz, hyz, hx, hy, w']
    rw [hrest_eq]
    apply add_le_add _ le_rfl
    by_cases hhit : ∃ s ∈ S, D x s = true
    · have hGz : G x z = true := by simp [G, mergeOut, hxz, hx, hhit]
      rw [ite_eq_left hGz]
      simp only [w', ↓reduceIte, mass]
      exact sum_le_sum fun s hs => by split_ifs <;> [exact le_rfl; exact hnn s (hSV hs)]
    · have hzero : (∑ y ∈ S, if D x y = true then w y else 0) = 0 := by
        apply sum_eq_zero
        intro s hs
        have : D x s = false := Bool.eq_false_iff.mpr (fun e => hhit ⟨s, hs, e⟩)
        simp [this]
      rw [hzero]
      split_ifs <;> [simpa [w'] using hSpos.le; exact le_rfl]
  by_contra hn
  push Not at hn
  have hrow_all : ∀ x ∈ W, mass W w' ≤ WeightedSD.row q G W w' x := by
    intro x hx
    rcases mem_insert.mp hx with rfl | hxS
    · rw [hmass, WeightedSD.row, hout_z]
      simpa [w'] using hn.le
    · exact hrow_other x hxS
  have hfree : QFree G W q := mergeOut_qfree hf hSV hz
  have hsup : SmallRow q G (W.filter (fun x => 0 < w' x)) :=
    hsmall G _ ((card_le_card (filter_subset _ _)).trans_lt (mergeV_card_lt hSV hcard hz))
      (hfree.mono_set (filter_subset _ _))
  have hzpos : 0 < w' z := by simpa [w'] using hSpos
  have htight := positive_coordinate_tight_of_support_smallRow hq w' hnn' hsup hrow_all
    (mem_insert_self z _) hzpos
  rw [hmass, WeightedSD.row, hout_z] at htight
  simp only [w', ↓reduceIte] at htight
  linarith

/-- Column-sum bound from merging `S` (`|S| ≥ 2`) in the reversed digraph. -/
theorem mergeIn_common_bound {q : ℕ} (hq : 2 ≤ q) {D : CH.Digraph} {V S : Finset ℕ}
    (hf : QFree D V q) (hsmall : SmallerSmallRow q V.card)
    (hSV : S ⊆ V) (hcard : 2 ≤ S.card)
    (p : ℕ → ℚ) (hnn : ∀ x ∈ V, 0 ≤ p x) (hSpos : 0 < mass S p)
    (hcol : ∀ x ∈ V, mass V p ≤ WeightedSD.col q D V p x) :
    mass S p + (q : ℚ) * mass (V.filter (fun y => ∀ s ∈ S, D y s = true)) p ≤ mass V p := by
  have hrow : ∀ x ∈ V, mass V p ≤ WeightedSD.row q (fun a b => D b a) V p x := by
    intro x hx
    simpa only [WeightedSD.row, WeightedSD.col, outW, inW] using hcol x hx
  exact mergeOut_common_bound hq hf.reverse hsmall hSV hcard p hnn hSpos hrow

/-- Unified flat common-out-neighbor bound for ANY nonempty `S ⊆ V` (size 1 or ≥ 2). -/
theorem flat_common_out_bound {q : ℕ} (hq : 2 ≤ q) {D : CH.Digraph} {V S : Finset ℕ}
    (hf : QFree D V q) (hsmall : SmallerSmallRow q V.card)
    (hSV : S ⊆ V) (hSne : S.Nonempty)
    (w : ℕ → ℚ) (hpos : ∀ x ∈ V, 0 < w x)
    (hrow : ∀ x ∈ V, WeightedSD.row q D V w x = mass V w) :
    mass S w + (q : ℚ) * mass (V.filter (fun y => ∀ s ∈ S, D s y = true)) w ≤ mass V w := by
  by_cases hcard : 2 ≤ S.card
  · exact mergeOut_common_bound hq hf hsmall hSV hcard w
      (fun x hx => (hpos x hx).le)
      (sum_pos (fun s hs => hpos s (hSV hs)) hSne)
      (fun x hx => (hrow x hx).ge)
  · have h1 : S.card = 1 := by
      have := card_pos.mpr hSne
      omega
    obtain ⟨s, rfl⟩ := card_eq_one.mp h1
    have hsV : s ∈ V := hSV (mem_singleton_self s)
    have heq : V.filter (fun y => ∀ x ∈ ({s} : Finset ℕ), D x y = true) = outN D V s := by
      ext y; simp [mem_outN]
    rw [heq, mass, sum_singleton, ← outW_eq_mass]
    exact (hrow s hsV).le

/-- Unified flat common-in-neighbor bound for ANY nonempty `S ⊆ V` (size 1 or ≥ 2). -/
theorem flat_common_in_bound {q : ℕ} (hq : 2 ≤ q) {D : CH.Digraph} {V S : Finset ℕ}
    (hf : QFree D V q) (hsmall : SmallerSmallRow q V.card)
    (hSV : S ⊆ V) (hSne : S.Nonempty)
    (p : ℕ → ℚ) (hpos : ∀ x ∈ V, 0 < p x)
    (hcol : ∀ x ∈ V, WeightedSD.col q D V p x = mass V p) :
    mass S p + (q : ℚ) * mass (V.filter (fun y => ∀ s ∈ S, D y s = true)) p ≤ mass V p := by
  have hrow : ∀ x ∈ V, WeightedSD.row q (fun a b => D b a) V p x = mass V p := by
    intro x hx
    simpa only [WeightedSD.row, WeightedSD.col, outW, inW] using hcol x hx
  exact flat_common_out_bound hq hf.reverse hsmall hSV hSne p hpos hrow

end SubsetMerge

#print axioms mergeOut_qfree
#print axioms mergeOut_common_bound
#print axioms mergeIn_common_bound
#print axioms flat_common_out_bound
#print axioms flat_common_in_bound

/-! ### Part 2: Rational Puncture Weights & Whole-Side Single-Pivot Mass Bounds -/

section SinglePivot

private theorem row_eval_puncture {q : ℕ} {D : CH.Digraph} {V : Finset ℕ} (a i : V)
    (w : V → ℝ) (wa : w a = 0) :
    (realMatrix q D V *ᵥ w) i = w i + (q : ℝ) * ∑ j ∈ (rest a).filter (fun j : V => D i j = true), w j := by
  classical
  simp only [sum_filter]
  have zero : (if D i a = true then w a else 0) = 0 := by simp [wa]
  have eq := sum_erase_add univ (fun j : V => if D i j = true then w j else 0) (mem_univ a)
  rw [zero, add_zero] at eq
  rw [show (∑ j ∈ rest a, if D i j = true then w j else 0) = _ from eq]
  simp [mulVec, dotProduct, realMatrix_entry, add_mul, ite_mul, sum_add_distrib, mul_sum, mul_ite]

private theorem col_eval_puncture {q : ℕ} {D : CH.Digraph} {V : Finset ℕ} (a i : V)
    (p : V → ℝ) (pa : p a = 0) :
    (p ᵥ* realMatrix q D V) i = p i + (q : ℝ) * ∑ j ∈ (rest a).filter (fun j : V => D j i = true), p j := by
  classical
  have flip : (p ᵥ* realMatrix q D V) i = (realMatrix q (fun u v => D v u) V *ᵥ p) i := by
    simp only [vecMul, mulVec, dotProduct, realMatrix_entry]
    apply sum_congr rfl
    intro j _
    by_cases e : i = j <;> simp [e, Ne.symm, mul_comm]
  exact flip.trans (row_eval_puncture a i p pa)

/-- Rational flat row and column weights on the puncture `U = X.V.erase a`,
    matching the normalized column and row `a` of the native inverse `H`. -/
theorem puncture_flat_weights {q n} (X : Model q n) (hq : 2 ≤ q) (small : SmallerSmallRow q X.V.card)
    {F B} (step : Boundary X F B)
    (least : ∀ M, Boundary X F M → (targets X.D X.V F B).card ≤ (targets X.D X.V F M).card)
    (multi : 1 < (targets X.D X.V F B).card) {a b : X.V} (edge : Fresh X F (a, b))
    (no : ¬SharedArcReachMargin.StrictColumns q (insertArc (graph X.D F) a b) X.V)
    {H : Matrix X.V X.V ℝ} (inv : CommonInverse (realMatrix q X.D X.V) H) :
    let U := X.V.erase a.val
    0 < (∑ j : X.V, H j a) ∧ 0 < (∑ j : X.V, H a j) ∧
    ∃ w p : ℕ → ℚ,
      (∀ i ∈ U, 0 < w i ∧ 0 < p i) ∧
      mass U w = 1 ∧ mass U p = 1 ∧
      (∀ i ∈ U, WeightedSD.row q X.D U w i = 1 ∧ WeightedSD.col q X.D U p i = 1) ∧
      (∀ i : X.V, i ≠ a →
        (w i : ℝ) = H i a / (∑ j : X.V, H j a) ∧
        (p i : ℝ) = H a i / (∑ j : X.V, H a j)) := by
  classical
  intro U
  have diag : H a a = 0 := SharedArcPunctureExpansion.zero_diagonal X hq small step least multi edge no inv
  have ne_b : b ≠ a := fun eq => loopfree X.free (by omega) a.property (by simpa [eq] using edge.2.2.1)
  have hSw : 0 < ∑ j : X.V, H j a :=
    sum_pos' (fun j _ => inv.nonneg j a) ⟨b, mem_univ _, InverseOffDiagonal.graph_positive hq inv ne_b⟩
  have hSp : 0 < ∑ j : X.V, H a j :=
    sum_pos' (fun j _ => inv.nonneg a j) ⟨b, mem_univ _, InverseOffDiagonal.graph_positive hq inv ne_b.symm⟩
  let RQ : Matrix U U ℚ := WeightedArithmetic.rationalMatrix q (adjacencyMatrix X.D U)
  have hunitQ : IsUnit RQ.det := isUnit_iff_ne_zero.mpr (WeightedArithmetic.rational_det_ne_zero hq _)
  let wU : U → ℚ := RQ⁻¹ *ᵥ (fun _ => 1)
  let pU : U → ℚ := (fun _ => 1) ᵥ* RQ⁻¹
  have hwQ : RQ *ᵥ wU = fun _ => 1 := by
    dsimp [wU]; rw [mulVec_mulVec, mul_nonsing_inv RQ hunitQ, one_mulVec]
  have hpQ : pU ᵥ* RQ = fun _ => 1 := by
    dsimp [pU]; rw [vecMul_vecMul, nonsing_inv_mul RQ hunitQ, vecMul_one]
  let RR : Matrix U U ℝ := realMatrix q X.D U
  have hunitR : IsUnit RR.det := SharedArcFlatResponse.matrix_unit hq X.D U
  have hcast : ∀ i j : U, (RQ i j : ℝ) = RR i j := fun i j => by
    simp only [RQ, RR, realMatrix_entry, WeightedArithmetic.rationalMatrix,
      WeightedArithmetic.closedMatrix, adjacencyMatrix, RingHom.mapMatrix_apply, Matrix.map_apply,
      Int.coe_castRingHom]
    by_cases h : i = j
    · subst h; by_cases hd : X.D i.val i.val = true <;> simp [hd]
    · by_cases hd : X.D i.val j.val = true <;> simp [h, hd]
  let wR : U → ℝ := fun i => H ⟨i.val, (mem_erase.mp i.property).2⟩ a / (∑ j : X.V, H j a)
  let pR : U → ℝ := fun i => H a ⟨i.val, (mem_erase.mp i.property).2⟩ / (∑ j : X.V, H a j)
  have lift_row (i : U) : (RR *ᵥ wR) i = 1 := by
    have hiV : (⟨i.val, (mem_erase.mp i.property).2⟩ : X.V) ≠ a :=
      fun e => (mem_erase.mp i.property).1 (congrArg Subtype.val e)
    have hH := congrArg (fun M : Matrix X.V X.V ℝ => M ⟨i.val, (mem_erase.mp i.property).2⟩ a) inv.right
    change (excess (realMatrix q X.D X.V) *ᵥ (fun j => H j a)) _ = (1 : Matrix X.V X.V ℝ) _ a at hH
    rw [mulVec_excess, one_apply_ne hiV, sub_eq_zero] at hH
    rw [row_eval_puncture a _ (fun j => H j a) diag] at hH
    have hsum : (RR *ᵥ wR) i =
        (H ⟨i.val, (mem_erase.mp i.property).2⟩ a +
          (q : ℝ) * ∑ j ∈ (rest a).filter (fun j : X.V => X.D i.val j.val = true), H j a) /
          (∑ j : X.V, H j a) := by
      simp only [mulVec, dotProduct, RR, realMatrix_entry, wR, add_mul, ite_mul, one_mul, zero_mul,
        sum_add_distrib, sum_ite_eq, mem_univ, ite_true]
      rw [add_div]
      congr 1
      rw [mul_div_assoc, sum_filter, sum_div, mul_sum]
      refine Finset.sum_bij (fun j _ => (⟨j.val, (mem_erase.mp j.property).2⟩ : X.V)) ?_ ?_ ?_ ?_
      · intro j _
        exact mem_erase.mpr ⟨fun e => (mem_erase.mp j.property).1 (congrArg Subtype.val e), mem_univ _⟩
      · intro j₁ _ j₂ _ h
        exact Subtype.ext (congrArg (fun x : X.V => x.val) h)
      · intro j hj
        have hjne : j.val ≠ a.val := fun e => (mem_erase.mp hj).1 (Subtype.ext e)
        exact ⟨⟨j.val, mem_erase.mpr ⟨hjne, j.property⟩⟩, mem_univ _, rfl⟩
      · intro j _; by_cases hd : X.D i.val j.val = true <;> simp [hd]
    rw [hsum, hH, div_self hSw.ne']
  have lift_col (i : U) : (pR ᵥ* RR) i = 1 := by
    have hiV : (⟨i.val, (mem_erase.mp i.property).2⟩ : X.V) ≠ a :=
      fun e => (mem_erase.mp i.property).1 (congrArg Subtype.val e)
    have hH := congrArg (fun M : Matrix X.V X.V ℝ => M a ⟨i.val, (mem_erase.mp i.property).2⟩)
      (mul_eq_one_comm.mp inv.right)
    change ((fun j => H a j) ᵥ* excess (realMatrix q X.D X.V)) _ = (1 : Matrix X.V X.V ℝ) a _ at hH
    rw [vecMul_excess, one_apply_ne hiV.symm, sub_eq_zero] at hH
    rw [col_eval_puncture a _ (fun j => H a j) diag] at hH
    have hsum : (pR ᵥ* RR) i =
        (H a ⟨i.val, (mem_erase.mp i.property).2⟩ +
          (q : ℝ) * ∑ j ∈ (rest a).filter (fun j : X.V => X.D j.val i.val = true), H a j) /
          (∑ j : X.V, H a j) := by
      simp only [vecMul, dotProduct, RR, realMatrix_entry, pR, mul_add, mul_ite, mul_one, mul_zero,
        sum_add_distrib, sum_ite_eq', mem_univ, ite_true]
      rw [add_div]
      congr 1
      rw [mul_div_assoc, sum_filter, sum_div, mul_sum]
      refine Finset.sum_bij (fun j _ => (⟨j.val, (mem_erase.mp j.property).2⟩ : X.V)) ?_ ?_ ?_ ?_
      · intro j _
        exact mem_erase.mpr ⟨fun e => (mem_erase.mp j.property).1 (congrArg Subtype.val e), mem_univ _⟩
      · intro j₁ _ j₂ _ h
        exact Subtype.ext (congrArg (fun x : X.V => x.val) h)
      · intro j hj
        have hjne : j.val ≠ a.val := fun e => (mem_erase.mp hj).1 (Subtype.ext e)
        exact ⟨⟨j.val, mem_erase.mpr ⟨hjne, j.property⟩⟩, mem_univ _, rfl⟩
      · intro j _; by_cases hd : X.D j.val i.val = true <;> simp [hd, mul_comm]
    rw [hsum, hH, div_self hSp.ne']
  have hw_eq : ∀ i : U, (wU i : ℝ) = wR i := by
    have h1 : RR *ᵥ (fun i : U => (wU i : ℝ)) = RR *ᵥ wR := by
      funext i
      rw [lift_row i]
      have := congrFun hwQ i
      change (∑ j : U, RR i j * (wU j : ℝ)) = 1
      simp_rw [← hcast]
      exact_mod_cast this
    have h2 := congrArg (fun v => RR⁻¹ *ᵥ v) h1
    rw [mulVec_mulVec, mulVec_mulVec, nonsing_inv_mul RR hunitR, one_mulVec, one_mulVec] at h2
    exact congrFun h2
  have hp_eq : ∀ i : U, (pU i : ℝ) = pR i := by
    have h1 : (fun i : U => (pU i : ℝ)) ᵥ* RR = pR ᵥ* RR := by
      funext i
      rw [lift_col i]
      have := congrFun hpQ i
      change (∑ j : U, (pU j : ℝ) * RR j i) = 1
      simp_rw [← hcast]
      exact_mod_cast this
    have h2 := congrArg (fun v => v ᵥ* RR⁻¹) h1
    rw [vecMul_vecMul, vecMul_vecMul, mul_nonsing_inv RR hunitR, vecMul_one, vecMul_one] at h2
    exact congrFun h2
  let w := extendWeight U wU
  let p := extendWeight U pU
  have hmatch : ∀ i : X.V, i ≠ a →
      (w i : ℝ) = H i a / (∑ j : X.V, H j a) ∧
      (p i : ℝ) = H a i / (∑ j : X.V, H a j) := by
    intro i hi
    have hiU : i.val ∈ U := mem_erase.mpr ⟨fun e => hi (Subtype.ext e), i.property⟩
    dsimp only [w, p]
    rw [extendWeight_on U wU ⟨i.val, hiU⟩, extendWeight_on U pU ⟨i.val, hiU⟩]
    exact ⟨hw_eq ⟨i.val, hiU⟩, hp_eq ⟨i.val, hiU⟩⟩
  have hpos : ∀ i ∈ U, 0 < w i ∧ 0 < p i := by
    intro i hi
    have hiV : i ∈ X.V := (mem_erase.mp hi).2
    have hne : (⟨i, hiV⟩ : X.V) ≠ a := fun e => (mem_erase.mp hi).1 (congrArg Subtype.val e)
    obtain ⟨hwm, hpm⟩ := hmatch ⟨i, hiV⟩ hne
    constructor
    · exact_mod_cast (hwm ▸ div_pos (InverseOffDiagonal.graph_positive hq inv hne) hSw : (0 : ℝ) < (w i : ℝ))
    · exact_mod_cast (hpm ▸ div_pos (InverseOffDiagonal.graph_positive hq inv hne.symm) hSp : (0 : ℝ) < (p i : ℝ))
  have hmass_w : mass U w = 1 := by
    have hR : (mass U w : ℝ) = 1 := by
      rw [mass, Rat.cast_sum]
      have h1 : (∑ i ∈ U, (w i : ℝ)) = ∑ i ∈ rest a, (w i.val : ℝ) := by
        refine Finset.sum_bij (fun i hi => (⟨i, (mem_erase.mp hi).2⟩ : X.V)) ?_ ?_ ?_ ?_
        · intro i hi; exact mem_erase.mpr ⟨fun e => (mem_erase.mp hi).1 (congrArg Subtype.val e), mem_univ _⟩
        · intro _ _ _ _ h; exact congrArg Subtype.val h
        · intro i hi
          have hne : i.val ≠ a.val := fun e => (mem_erase.mp hi).1 (Subtype.ext e)
          exact ⟨i.val, mem_erase.mpr ⟨hne, i.property⟩, rfl⟩
        · intro _ _; rfl
      rw [h1]
      have h2 : (∑ i ∈ rest a, (w i.val : ℝ)) = ∑ i ∈ rest a, H i a / (∑ j : X.V, H j a) :=
        sum_congr rfl fun i hi => (hmatch i (mem_erase.mp hi).1).1
      rw [h2, ← sum_div]
      have h3 : (∑ i ∈ rest a, H i a) = ∑ j : X.V, H j a := by
        have eq := sum_erase_add univ (fun j : X.V => H j a) (mem_univ a)
        rw [diag, add_zero] at eq
        exact eq
      rw [h3, div_self hSw.ne']
    exact_mod_cast hR
  have hmass_p : mass U p = 1 := by
    have hR : (mass U p : ℝ) = 1 := by
      rw [mass, Rat.cast_sum]
      have h1 : (∑ i ∈ U, (p i : ℝ)) = ∑ i ∈ rest a, (p i.val : ℝ) := by
        refine Finset.sum_bij (fun i hi => (⟨i, (mem_erase.mp hi).2⟩ : X.V)) ?_ ?_ ?_ ?_
        · intro i hi; exact mem_erase.mpr ⟨fun e => (mem_erase.mp hi).1 (congrArg Subtype.val e), mem_univ _⟩
        · intro _ _ _ _ h; exact congrArg Subtype.val h
        · intro i hi
          have hne : i.val ≠ a.val := fun e => (mem_erase.mp hi).1 (Subtype.ext e)
          exact ⟨i.val, mem_erase.mpr ⟨hne, i.property⟩, rfl⟩
        · intro _ _; rfl
      rw [h1]
      have h2 : (∑ i ∈ rest a, (p i.val : ℝ)) = ∑ i ∈ rest a, H a i / (∑ j : X.V, H a j) :=
        sum_congr rfl fun i hi => (hmatch i (mem_erase.mp hi).1).2
      rw [h2, ← sum_div]
      have h3 : (∑ i ∈ rest a, H a i) = ∑ j : X.V, H a j := by
        have eq := sum_erase_add univ (fun j : X.V => H a j) (mem_univ a)
        rw [diag, add_zero] at eq
        exact eq
      rw [h3, div_self hSp.ne']
    exact_mod_cast hR
  have hrc : ∀ i ∈ U, WeightedSD.row q X.D U w i = 1 ∧ WeightedSD.col q X.D U p i = 1 := by
    intro i hi
    constructor
    · rw [row_extendWeight q X.D U wU ⟨i, hi⟩]
      exact congrFun hwQ ⟨i, hi⟩
    · have hcol_eq : WeightedSD.col q X.D U p i = (pU ᵥ* RQ) ⟨i, hi⟩ := by
        rw [WeightedArithmetic.rational_vecMul_apply, WeightedSD.col, inW]
        dsimp only [p]
        rw [extendWeight_on U pU ⟨i, hi⟩, ← Finset.sum_coe_sort U]
        congr 1; congr 1
        apply sum_congr rfl
        intro j _
        rw [extendWeight_on U pU j]
        simp only [adjacencyMatrix]
        by_cases hd : X.D j.val i = true <;> simp [hd]
      rw [hcol_eq]
      exact congrFun hpQ ⟨i, hi⟩
  exact ⟨hSw, hSp, w, p, hpos, hmass_w, hmass_p, hrc, hmatch⟩

private theorem sum_rest_filter_eq_mass {U V : Finset ℕ} {a : V}
    (hU : U = V.erase a.val) (P : ℕ → Prop) [DecidablePred P]
    (f : ℕ → ℚ) (g : V → ℝ) (S : ℝ)
    (hmatch : ∀ i : V, i ≠ a → (f i.val : ℝ) = g i / S) :
    (mass (U.filter P) f : ℝ) = (∑ i ∈ (rest a).filter (fun i : V => P i.val), g i) / S := by
  rw [mass, Rat.cast_sum, sum_div]
  refine Finset.sum_bij (fun x hx => (⟨x, (mem_erase.mp (hU ▸ (mem_filter.mp hx).1)).2⟩ : V)) ?_ ?_ ?_ ?_
  · intro x hx
    obtain ⟨hxU, hP⟩ := mem_filter.mp hx
    rw [hU] at hxU
    exact mem_filter.mpr ⟨mem_erase.mpr ⟨fun e => (mem_erase.mp hxU).1 (congrArg Subtype.val e), mem_univ _⟩, hP⟩
  · intro _ _ _ _ h; exact congrArg Subtype.val h
  · intro i hi
    obtain ⟨hirest, hP⟩ := mem_filter.mp hi
    have hne : i.val ≠ a.val := fun e => (mem_erase.mp hirest).1 (Subtype.ext e)
    exact ⟨i.val, mem_filter.mpr ⟨hU ▸ mem_erase.mpr ⟨hne, i.property⟩, hP⟩, rfl⟩
  · intro x hx
    have hxU := hU ▸ (mem_filter.mp hx).1
    exact hmatch ⟨x, (mem_erase.mp hxU).2⟩ (fun e => (mem_erase.mp hxU).1 (congrArg Subtype.val e))

/-- Whole-side collective mass bounds and star-deletion margins in the single-pivot branch
    (holds for BOTH clean and dirty pivots, all `q ≥ 3`).
    Strengthens `SharedArcPivotSpread.every_pair` from a single vertex `H t a < q H h a`
    to the ENTIRE fresh side `∑_{t ∈ T} H t a < q H h a` (and dually for `H1`). -/
theorem whole_side_merge_bounds {q n} (X : Model q n) (hq : 3 ≤ q) (small : SmallerSmallRow q X.V.card)
    {F B} (step : Boundary X F B)
    (least : ∀ M, Boundary X F M → (targets X.D X.V F B).card ≤ (targets X.D X.V F M).card)
    (stop : ∀ M, Boundary X F M → ¬SmallRow q (graph X.D (insert M F)) X.V)
    (multi : 1 < (targets X.D X.V F B).card) {a b : X.V} (edge : Fresh X F (a, b))
    (no : ¬SharedArcReachMargin.StrictColumns q (insertArc (graph X.D F) a b) X.V)
    {H : Matrix X.V X.V ℝ} (inv : CommonInverse (realMatrix q X.D X.V) H) :
    let T := (rest a).filter (fun t : X.V => X.D t a = true ∧ graph X.D F t a = false)
    let H1 := (rest a).filter (fun h : X.V => X.D a h = true ∧ graph X.D F a h = false)
    let P0 := (rest a).filter (fun x : X.V => graph X.D F x a = true)
    let H0 := (rest a).filter (fun x : X.V => graph X.D F a x = true)
    ((∑ t ∈ T, H t a) + (q : ℝ) * (∑ x ∈ H0, H x a) ≤ ∑ j : X.V, H j a) ∧
    ((∑ h ∈ H1, H a h) + (q : ℝ) * (∑ x ∈ P0, H a x) ≤ ∑ j : X.V, H a j) ∧
    (∀ h ∈ H1, (∑ j : X.V, H j a) < (q : ℝ) * (∑ x ∈ H0, H x a) + (q : ℝ) * H h a) ∧
    (∀ t ∈ T, (∑ j : X.V, H a j) < (q : ℝ) * (∑ x ∈ P0, H a x) + (q : ℝ) * H a t) ∧
    (∀ h ∈ H1, (∑ t ∈ T, H t a) < (q : ℝ) * H h a) ∧
    (∀ t ∈ T, (∑ h ∈ H1, H a h) < (q : ℝ) * H a t) ∧
    (∀ h ∈ H1, (q : ℝ) * (∑ h' ∈ H1.erase h, H h' a) < 1) ∧
    (∀ t ∈ T, (q : ℝ) * (∑ t' ∈ T.erase t, H a t') < 1) := by
  classical
  intro T H1 P0 H0
  have two : 2 ≤ q := by omega
  obtain ⟨hSw, hSp, w, p, hpos, hmw, hmp, hrc, hmatch⟩ :=
    puncture_flat_weights X two small step least multi edge no inv
  have diag : H a a = 0 := SharedArcPunctureExpansion.zero_diagonal X two small step least multi edge no inv
  let U := X.V.erase a.val
  have hsmallU : SmallerSmallRow q U.card := fun E K hlt hfr =>
    small E K (hlt.trans (card_erase_lt_of_mem a.property)) hfr
  have hfreeU : QFree X.D U q := X.free.mono_set (erase_subset _ _)
  have cross := SharedArcPivotPaths.crossed X two small step least multi edge no
  obtain ⟨t0, h0, ht0, hh0, _, _, _, _⟩ :=
    SharedArcPivotDetour.endpoint_escape X hq small step least multi edge no
  have ne_arc {i j : X.V} (e : X.D i j = true) : i ≠ j :=
    fun eq => loopfree X.free (by omega) j.property (eq ▸ e)
  -- 1. Merge bound on T in U
  let TU := U.filter (fun x => X.D x a.val = true ∧ graph X.D F x a.val = false)
  let H0U := U.filter (fun x => graph X.D F a.val x = true)
  have hTUne : TU.Nonempty := ⟨t0.val, mem_filter.mpr
    ⟨mem_erase.mpr ⟨fun e => ne_arc ht0.2.2.1 (Subtype.ext e), t0.property⟩, ht0.2.2.1, ht0.2.2.2⟩⟩
  have hH0sub : H0U ⊆ U.filter (fun y => ∀ s ∈ TU, X.D s y = true) := by
    intro y hy
    obtain ⟨hyU, hay⟩ := mem_filter.mp hy
    refine mem_filter.mpr ⟨hyU, fun s hs => ?_⟩
    obtain ⟨hsU, hsa, hsold⟩ := mem_filter.mp hs
    have hayD : X.D a.val y = true := (mem_col.mp (active.mp hay).choose_spec).2.2.2
    exact cross ⟨s, (mem_erase.mp hsU).2⟩ ⟨y, (mem_erase.mp hyU).2⟩ hsa hayD (by simp [hsold, hay])
  have hboundT_Q : mass TU w + (q : ℚ) * mass H0U w ≤ 1 := by
    have h1 := flat_common_out_bound two hfreeU hsmallU (filter_subset _ _) hTUne w
      (fun i hi => (hpos i hi).1) (fun i hi => (hrc i hi).1.trans hmw.symm)
    rw [hmw] at h1
    have h2 : mass H0U w ≤ mass (U.filter (fun y => ∀ s ∈ TU, X.D s y = true)) w :=
      sum_le_sum_of_subset_of_nonneg hH0sub fun i hi _ => (hpos i (mem_filter.mp hi).1).1.le
    have hq0 : (0 : ℚ) ≤ q := Nat.cast_nonneg q
    nlinarith
  have hboundT : (∑ t ∈ T, H t a) + (q : ℝ) * (∑ x ∈ H0, H x a) ≤ ∑ j : X.V, H j a := by
    have hR : (mass TU w : ℝ) + (q : ℝ) * (mass H0U w : ℝ) ≤ 1 := by exact_mod_cast hboundT_Q
    rw [sum_rest_filter_eq_mass rfl (fun x => X.D x a.val = true ∧ graph X.D F x a.val = false)
          w (fun i => H i a) _ (fun i hi => (hmatch i hi).1),
        sum_rest_filter_eq_mass rfl (fun x => graph X.D F a.val x = true)
          w (fun i => H i a) _ (fun i hi => (hmatch i hi).1)] at hR
    have hmul := mul_le_mul_of_nonneg_right hR hSw.le
    rw [add_mul, mul_div_assoc', div_mul_cancel₀ _ hSw.ne', div_mul_cancel₀ _ hSw.ne', one_mul] at hmul
    exact hmul
  -- 2. Merge bound on H1 in U^rev
  let H1U := U.filter (fun x => X.D a.val x = true ∧ graph X.D F a.val x = false)
  let P0U := U.filter (fun x => graph X.D F x a.val = true)
  have hH1Une : H1U.Nonempty := ⟨h0.val, mem_filter.mpr
    ⟨mem_erase.mpr ⟨fun e => (ne_arc hh0.2.2.1).symm (Subtype.ext e), h0.property⟩, hh0.2.2.1, hh0.2.2.2⟩⟩
  have hP0sub : P0U ⊆ U.filter (fun y => ∀ s ∈ H1U, X.D y s = true) := by
    intro y hy
    obtain ⟨hyU, hya⟩ := mem_filter.mp hy
    refine mem_filter.mpr ⟨hyU, fun s hs => ?_⟩
    obtain ⟨hsU, has, hsold⟩ := mem_filter.mp hs
    have hyaD : X.D y a.val = true := (mem_col.mp (active.mp hya).choose_spec).2.2.2
    exact cross ⟨y, (mem_erase.mp hyU).2⟩ ⟨s, (mem_erase.mp hsU).2⟩ hyaD has (by simp [hya, hsold])
  have hboundH1_Q : mass H1U p + (q : ℚ) * mass P0U p ≤ 1 := by
    have h1 := flat_common_in_bound two hfreeU hsmallU (filter_subset _ _) hH1Une p
      (fun i hi => (hpos i hi).2) (fun i hi => (hrc i hi).2.trans hmp.symm)
    rw [hmp] at h1
    have h2 : mass P0U p ≤ mass (U.filter (fun y => ∀ s ∈ H1U, X.D y s = true)) p :=
      sum_le_sum_of_subset_of_nonneg hP0sub fun i hi _ => (hpos i (mem_filter.mp hi).1).2.le
    have hq0 : (0 : ℚ) ≤ q := Nat.cast_nonneg q
    nlinarith
  have hboundH1 : (∑ h ∈ H1, H a h) + (q : ℝ) * (∑ x ∈ P0, H a x) ≤ ∑ j : X.V, H a j := by
    have hR : (mass H1U p : ℝ) + (q : ℝ) * (mass P0U p : ℝ) ≤ 1 := by exact_mod_cast hboundH1_Q
    rw [sum_rest_filter_eq_mass rfl (fun x => X.D a.val x = true ∧ graph X.D F a.val x = false)
          p (fun i => H a i) _ (fun i hi => (hmatch i hi).2),
        sum_rest_filter_eq_mass rfl (fun x => graph X.D F x a.val = true)
          p (fun i => H a i) _ (fun i hi => (hmatch i hi).2)] at hR
    have hmul := mul_le_mul_of_nonneg_right hR hSp.le
    rw [add_mul, mul_div_assoc', div_mul_cancel₀ _ hSp.ne', div_mul_cancel₀ _ hSp.ne', one_mul] at hmul
    exact hmul
  -- 3 & 4. Star strict margins
  have hstarH : ∀ h ∈ H1, (∑ j : X.V, H j a) < (q : ℝ) * (∑ x ∈ H0, H x a) + (q : ℝ) * H h a := by
    intro h hh
    obtain ⟨hhrest, hah, hahF⟩ := mem_filter.mp hh
    have hfresh : Fresh X F (a, h) := ⟨a.property, h.property, hah, hahF⟩
    obtain ⟨M, bm, pair, _, _⟩ :=
      SharedArcPivotSpread.at_pair X hq small step least stop multi edge no inv ht0 hfresh
    let J := graph X.D (insert M F)
    obtain ⟨ws, wn, _, strict⟩ := strict_witness_of_not_smallRow (stop M bm)
    obtain ⟨K, ki⟩ := strict_inverse_of_proper_smallRow
      (small.induced (PrivateArcEndpoints.graph_free X (insert M F))) ws wn strict
    have native {i j : ℕ} (e : J i j = true) : X.D i j = true :=
      (mem_col.mp (active.mp e).choose_spec).2.2.2
    have sub (i j : X.V) : realMatrix q J X.V i j ≤ realMatrix q X.D X.V i j :=
      realMatrix_mono_graph (fun _ _ _ _ e => native e) i j
    have row (i : X.V) (ni : i ≠ a) : (realMatrix q X.D X.V *ᵥ (fun j => H j a)) i = ∑ j, H j a := by
      have eq := congrArg (fun A : Matrix X.V X.V ℝ => A i a) inv.right
      change (excess (realMatrix q X.D X.V) *ᵥ (fun j => H j a)) i = (1 : Matrix X.V X.V ℝ) i a at eq
      simpa [mulVec_excess, one_apply_ne ni, sub_eq_zero] using eq
    have hiZ : (∑ j : X.V, H j a) < (realMatrix q J X.V *ᵥ (fun j => H j a)) a := by
      by_contra! low
      have all (i : X.V) : (excess (realMatrix q J X.V) *ᵥ (fun j => H j a)) i ≤ 0 := by
        rw [mulVec_excess, sub_nonpos]
        by_cases eq : i = a
        · exact eq ▸ low
        · exact (sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (sub i j) (inv.nonneg j a)).trans (row i eq).le
      have hz : (K *ᵥ (excess (realMatrix q J X.V) *ᵥ (fun j => H j a))) t0 ≤ 0 :=
        sum_nonpos (s := univ) fun j _ => mul_nonpos_of_nonneg_of_nonpos (ki.nonneg t0 j) (all j)
      rw [mulVec_mulVec, mul_eq_one_comm.mp ki.right, one_mulVec] at hz
      exact (InverseOffDiagonal.graph_positive two inv (ne_arc ht0.2.2.1)).not_ge hz
    rw [row_eval_puncture a a (fun j => H j a) diag, diag, zero_add] at hiZ
    have hJout : (rest a).filter (fun j : X.V => J a j = true) = insert h H0 := by
      ext j
      simp only [mem_filter, mem_insert, H0]
      constructor
      · rintro ⟨jrest, jaj⟩
        rcases union_arc.mp jaj with old | add
        · exact Or.inr ⟨jrest, old⟩
        · rw [pair] at add
          simp only [SharedArcPivotChoice.pair, mem_insert, mem_singleton, Prod.mk.injEq] at add
          rcases add with ⟨e, _⟩ | ⟨_, e⟩
          · exact (ne_arc ht0.2.2.1 (Subtype.ext e.symm)).elim
          · exact Or.inl (Subtype.ext e)
      · rintro (rfl | ⟨jrest, old⟩)
        · exact ⟨hhrest, union_arc.mpr (Or.inr (pair ▸ mem_insert_of_mem (mem_singleton_self _)))⟩
        · exact ⟨jrest, union_arc.mpr (Or.inl old)⟩
    have hhnot : h ∉ H0 := fun hm => Bool.noConfusion (hahF.symm.trans (mem_filter.mp hm).2)
    rw [hJout, sum_insert hhnot, mul_add] at hiZ
    linarith
  have hstarT : ∀ t ∈ T, (∑ j : X.V, H a j) < (q : ℝ) * (∑ x ∈ P0, H a x) + (q : ℝ) * H a t := by
    intro t ht
    obtain ⟨htrest, hta, htaF⟩ := mem_filter.mp ht
    have hfresh : Fresh X F (t, a) := ⟨t.property, a.property, hta, htaF⟩
    obtain ⟨M, bm, pair, _, _⟩ :=
      SharedArcPivotSpread.at_pair X hq small step least stop multi edge no inv hfresh hh0
    let J := graph X.D (insert M F)
    obtain ⟨ws, wn, _, strict⟩ := strict_witness_of_not_smallRow (stop M bm)
    obtain ⟨K, ki⟩ := strict_inverse_of_proper_smallRow
      (small.induced (PrivateArcEndpoints.graph_free X (insert M F))) ws wn strict
    have native {i j : ℕ} (e : J i j = true) : X.D i j = true :=
      (mem_col.mp (active.mp e).choose_spec).2.2.2
    have sub (i j : X.V) : realMatrix q J X.V i j ≤ realMatrix q X.D X.V i j :=
      realMatrix_mono_graph (fun _ _ _ _ e => native e) i j
    have col (i : X.V) (ni : i ≠ a) : ((fun j => H a j) ᵥ* realMatrix q X.D X.V) i = ∑ j, H a j := by
      have eq := congrArg (fun A : Matrix X.V X.V ℝ => A a i) (mul_eq_one_comm.mp inv.right)
      change ((fun j => H a j) ᵥ* excess (realMatrix q X.D X.V)) i = (1 : Matrix X.V X.V ℝ) a i at eq
      simpa [vecMul_excess, one_apply_ne ni.symm, sub_eq_zero] using eq
    have hiP : (∑ j : X.V, H a j) < ((fun j => H a j) ᵥ* realMatrix q J X.V) a := by
      by_contra! low
      have all (i : X.V) : ((fun j => H a j) ᵥ* excess (realMatrix q J X.V)) i ≤ 0 := by
        rw [vecMul_excess, sub_nonpos]
        by_cases eq : i = a
        · exact eq ▸ low
        · exact (sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (sub j i) (inv.nonneg a j)).trans (col i eq).le
      have hp : (((fun j => H a j) ᵥ* excess (realMatrix q J X.V)) ᵥ* K) h0 ≤ 0 :=
        sum_nonpos (s := univ) fun j _ => mul_nonpos_of_nonpos_of_nonneg (all j) (ki.nonneg j h0)
      rw [vecMul_vecMul, ki.right, vecMul_one] at hp
      exact (InverseOffDiagonal.graph_positive two inv (ne_arc hh0.2.2.1)).not_ge hp
    rw [col_eval_puncture a a (fun j => H a j) diag, diag, zero_add] at hiP
    have hJin : (rest a).filter (fun j : X.V => J j a = true) = insert t P0 := by
      ext j
      simp only [mem_filter, mem_insert, P0]
      constructor
      · rintro ⟨jrest, jja⟩
        rcases union_arc.mp jja with old | add
        · exact Or.inr ⟨jrest, old⟩
        · rw [pair] at add
          simp only [SharedArcPivotChoice.pair, mem_insert, mem_singleton, Prod.mk.injEq] at add
          rcases add with ⟨e, _⟩ | ⟨_, e⟩
          · exact Or.inl (Subtype.ext e)
          · exact (ne_arc hh0.2.2.1 (Subtype.ext e)).elim
      · rintro (rfl | ⟨jrest, old⟩)
        · exact ⟨htrest, union_arc.mpr (Or.inr (pair ▸ mem_insert_self _ _))⟩
        · exact ⟨jrest, union_arc.mpr (Or.inl old)⟩
    have htnot : t ∉ P0 := fun hm => Bool.noConfusion (htaF.symm.trans (mem_filter.mp hm).2)
    rw [hJin, sum_insert htnot, mul_add] at hiP
    linarith
  have hdomH : ∀ h ∈ H1, (∑ t ∈ T, H t a) < (q : ℝ) * H h a := fun h hh => by linarith [hboundT, hstarH h hh]
  have hdomT : ∀ t ∈ T, (∑ h ∈ H1, H a h) < (q : ℝ) * H a t := fun t ht => by linarith [hboundH1, hstarT t ht]
  obtain ⟨hacc1, hacc2⟩ := SharedArcPunctureExpansion.inverse_accounts X inv a
  rw [diag, zero_add] at hacc1 hacc2
  have hout_split : (∑ j : X.V, if X.D a j = true then H j a else 0) =
      (∑ x ∈ H0, H x a) + (∑ h ∈ H1, H h a) := by
    rw [← sum_filter, ← sum_union]
    · congr 1
      ext j
      simp only [mem_filter, mem_univ, true_and, mem_union, H0, H1, rest, mem_erase]
      constructor
      · intro haj
        have jne : j ≠ a := (ne_arc haj).symm
        cases hjF : graph X.D F a j
        · exact Or.inr ⟨by simp [jne], haj, rfl⟩
        · exact Or.inl ⟨by simp [jne], rfl⟩
      · rintro (⟨_, old⟩ | ⟨_, haj, _⟩)
        · exact (mem_col.mp (active.mp old).choose_spec).2.2.2
        · exact haj
    · rw [Finset.disjoint_left]
      intro x hx1 hx2
      exact Bool.noConfusion ((mem_filter.mp hx2).2.2.symm.trans (mem_filter.mp hx1).2)
  have hin_split : (∑ j : X.V, if X.D j a = true then H a j else 0) =
      (∑ x ∈ P0, H a x) + (∑ t ∈ T, H a t) := by
    rw [← sum_filter, ← sum_union]
    · congr 1
      ext j
      simp only [mem_filter, mem_univ, true_and, mem_union, P0, T, rest, mem_erase]
      constructor
      · intro hja
        have jne : j ≠ a := ne_arc hja
        cases hjF : graph X.D F j a
        · exact Or.inr ⟨by simp [jne], hja, rfl⟩
        · exact Or.inl ⟨by simp [jne], rfl⟩
      · rintro (⟨_, old⟩ | ⟨_, hja, _⟩)
        · exact (mem_col.mp (active.mp old).choose_spec).2.2.2
        · exact hja
    · rw [Finset.disjoint_left]
      intro x hx1 hx2
      exact Bool.noConfusion ((mem_filter.mp hx2).2.2.symm.trans (mem_filter.mp hx1).2)
  have hmarginH : ∀ h ∈ H1, (q : ℝ) * (∑ h' ∈ H1.erase h, H h' a) < 1 := by
    intro h hh
    have hsplit : (q : ℝ) * (∑ h' ∈ H1.erase h, H h' a) + (q : ℝ) * H h a = (q : ℝ) * ∑ h' ∈ H1, H h' a := by
      rw [← mul_add, sum_erase_add H1 (fun h' => H h' a) hh]
    rw [hout_split, mul_add] at hacc1
    linarith [hstarH h hh]
  have hmarginT : ∀ t ∈ T, (q : ℝ) * (∑ t' ∈ T.erase t, H a t') < 1 := by
    intro t ht
    have hsplit : (q : ℝ) * (∑ t' ∈ T.erase t, H a t') + (q : ℝ) * H a t = (q : ℝ) * ∑ t' ∈ T, H a t' := by
      rw [← mul_add, sum_erase_add T (fun t' => H a t') ht]
    rw [hin_split, mul_add] at hacc2
    linarith [hstarT t ht]
  exact ⟨hboundT, hboundH1, hstarH, hstarT, hdomH, hdomT, hmarginH, hmarginT⟩

/-- Every out-regular puncture (with NO in-degree assumption at all!) forces a UNIQUE clean fresh parent. -/
theorem out_regular_forces_clean_parent {q n k} (X : Model q n) (hq : 3 ≤ q)
    (small : SmallerSmallRow q X.V.card) {F B} (step : Boundary X F B)
    (least : ∀ M, Boundary X F M → (targets X.D X.V F B).card ≤ (targets X.D X.V F M).card)
    (stop : ∀ M, Boundary X F M → ¬SmallRow q (graph X.D (insert M F)) X.V)
    (multi : 1 < (targets X.D X.V F B).card) {a b : X.V} (edge : Fresh X F (a, b))
    (no : ¬SharedArcReachMargin.StrictColumns q (insertArc (graph X.D F) a b) X.V)
    (outdeg : ∀ x ∈ X.V.erase a.val, (outN X.D (X.V.erase a.val) x).card = k) :
    ∃ t : X.V, Fresh X F (t, a) ∧
      (∀ u : X.V, Fresh X F (u, a) → u = t) ∧
      (∀ x ∈ X.V.erase a.val, X.D t.val x = true → X.D a.val x = true) := by
  classical
  have two : 2 ≤ q := by omega
  obtain ⟨H, inv⟩ := strict_inverse_of_proper_smallRow (small.induced X.free)
    (fun i => (X.weights i : ℚ)) (fun _ _ => Nat.cast_nonneg _) X.strict
  obtain ⟨hSw, _, w, _, hpos, hmw, _, hrc, hmatch⟩ :=
    puncture_flat_weights X two small step least multi edge no inv
  let U := X.V.erase a.val
  have hden_pos : (0 : ℚ) < 1 + (q : ℚ) * k := by positivity
  let RQ : Matrix U U ℚ := WeightedArithmetic.rationalMatrix q (adjacencyMatrix X.D U)
  have hunitQ : IsUnit RQ.det := isUnit_iff_ne_zero.mpr (WeightedArithmetic.rational_det_ne_zero two _)
  have hconst_sol : RQ *ᵥ (fun _ : U => (1 + (q : ℚ) * k)⁻¹) = fun _ => 1 := by
    funext i
    rw [show (RQ *ᵥ (fun _ : U => (1 + (q : ℚ) * k)⁻¹)) i =
          WeightedSD.row q X.D U (fun _ => (1 + (q : ℚ) * k)⁻¹) i.val from
          matrix_row q X.D U (fun _ => (1 + (q : ℚ) * k)⁻¹) i,
        WeightedSD.row, outW_eq_mass, mass, sum_const, nsmul_eq_mul, outdeg i.val i.property]
    field_simp [hden_pos.ne']
  have hw_sol : RQ *ᵥ (fun i : U => w i.val) = fun _ => 1 := by
    funext i
    exact (matrix_row q X.D U w i).trans (hrc i.val i.property).1
  have hw_const : ∀ i ∈ U, w i = (1 + (q : ℚ) * k)⁻¹ := by
    have h2 := congrArg (fun v => RQ⁻¹ *ᵥ v) (hw_sol.trans hconst_sol.symm)
    rw [mulVec_mulVec, mulVec_mulVec, nonsing_inv_mul RQ hunitQ, one_mulVec, one_mulVec] at h2
    intro i hi
    exact congrFun h2 ⟨i, hi⟩
  have hcardU : U.card = 1 + q * k := by
    have h1 : mass U w = (U.card : ℚ) * (1 + (q : ℚ) * k)⁻¹ := by
      rw [mass, sum_congr rfl hw_const, sum_const, nsmul_eq_mul]
    rw [hmw] at h1
    have h2 : (U.card : ℚ) = 1 + (q : ℚ) * k := by
      have := congrArg (fun z : ℚ => z * (1 + (q : ℚ) * k)) h1
      rw [one_mul, mul_assoc, inv_mul_cancel₀ hden_pos.ne', mul_one] at this
      exact this.symm
    exact_mod_cast h2
  have hH_const : ∀ i ∈ rest a, H i a = (∑ j : X.V, H j a) / (1 + (q : ℝ) * k) := by
    intro i hi
    have hiU : i.val ∈ U := mem_erase.mpr ⟨fun e => (mem_erase.mp hi).1 (Subtype.ext e), i.property⟩
    have hm := (hmatch i (mem_erase.mp hi).1).1
    rw [hw_const i.val hiU] at hm
    push_cast at hm
    have h1 := congrArg (fun z => z * (∑ j : X.V, H j a)) hm
    rw [div_mul_cancel₀ _ hSw.ne'] at h1
    rw [← h1, div_eq_inv_mul]
  obtain ⟨hboundT, _, hstarH, _, _, _, _, _⟩ :=
    whole_side_merge_bounds X hq small step least stop multi edge no inv
  let T := (rest a).filter (fun t : X.V => X.D t a = true ∧ graph X.D F t a = false)
  let H1 := (rest a).filter (fun h : X.V => X.D a h = true ∧ graph X.D F a h = false)
  let H0 := (rest a).filter (fun x : X.V => graph X.D F a x = true)
  obtain ⟨t0, h0, ht0, hh0, _, _, _, _⟩ :=
    SharedArcPivotDetour.endpoint_escape X hq small step least multi edge no
  have ne_arc {i j : X.V} (e : X.D i j = true) : i ≠ j :=
    fun eq => loopfree X.free (by omega) j.property (eq ▸ e)
  have ht0T : t0 ∈ T := mem_filter.mpr ⟨mem_erase.mpr ⟨ne_arc ht0.2.2.1, mem_univ _⟩, ht0.2.2.1, ht0.2.2.2⟩
  have hh0H1 : h0 ∈ H1 := mem_filter.mpr ⟨mem_erase.mpr ⟨(ne_arc hh0.2.2.1).symm, mem_univ _⟩, hh0.2.2.1, hh0.2.2.2⟩
  have hposC : (0 : ℝ) < (∑ j : X.V, H j a) / (1 + (q : ℝ) * k) := div_pos hSw (by positivity)
  have hsumT : ∑ t ∈ T, H t a = (T.card : ℝ) * ((∑ j : X.V, H j a) / (1 + (q : ℝ) * k)) := by
    rw [sum_congr rfl (fun i hi => hH_const i (mem_filter.mp hi).1), sum_const, nsmul_eq_mul]
  have hsumH0 : ∑ x ∈ H0, H x a = (H0.card : ℝ) * ((∑ j : X.V, H j a) / (1 + (q : ℝ) * k)) := by
    rw [sum_congr rfl (fun i hi => hH_const i (mem_filter.mp hi).1), sum_const, nsmul_eq_mul]
  have hH0_ge : k ≤ H0.card := by
    have hs := hstarH h0 hh0H1
    rw [hsumH0, hH_const h0 (mem_filter.mp hh0H1).1] at hs
    have hden : (0 : ℝ) < 1 + (q : ℝ) * k := by positivity
    have h1 : (1 + (q : ℝ) * k) * ((∑ j : X.V, H j a) / (1 + (q : ℝ) * k)) <
        ((q : ℝ) * (H0.card : ℝ) + (q : ℝ)) * ((∑ j : X.V, H j a) / (1 + (q : ℝ) * k)) := by
      rw [mul_div_cancel₀ _ hden.ne']; linarith
    have h2 : (1 + (q : ℝ) * k) < (q : ℝ) * (H0.card : ℝ) + (q : ℝ) := lt_of_mul_lt_mul_right h1 hposC.le
    have h3 : 1 + q * k < q * H0.card + q := by exact_mod_cast h2
    nlinarith
  have hT_le : T.card + q * H0.card ≤ 1 + q * k := by
    rw [hsumT, hsumH0] at hboundT
    have hden : (0 : ℝ) < 1 + (q : ℝ) * k := by positivity
    have h1 : ((T.card : ℝ) + (q : ℝ) * (H0.card : ℝ)) * ((∑ j : X.V, H j a) / (1 + (q : ℝ) * k)) ≤
        (1 + (q : ℝ) * k) * ((∑ j : X.V, H j a) / (1 + (q : ℝ) * k)) := by
      rw [mul_div_cancel₀ _ hden.ne']; linarith
    have h2 : (T.card : ℝ) + (q : ℝ) * (H0.card : ℝ) ≤ 1 + (q : ℝ) * k :=
      le_of_mul_le_mul_right h1 hposC
    exact_mod_cast h2
  have hT1 : T.card = 1 := by
    have hTpos : 1 ≤ T.card := card_pos.mpr ⟨t0, ht0T⟩
    nlinarith
  have hH0eq : H0.card = k := by nlinarith
  have hTuniq : ∀ u : X.V, Fresh X F (u, a) → u = t0 := by
    intro u fu
    have huT : u ∈ T := mem_filter.mpr ⟨mem_erase.mpr ⟨ne_arc fu.2.2.1, mem_univ _⟩, fu.2.2.1, fu.2.2.2⟩
    exact card_le_one.mp hT1.le u huT t0 ht0T
  have cross := SharedArcPivotPaths.crossed X two small step least multi edge no
  let H0U := U.filter (fun x => graph X.D F a.val x = true)
  have hH0U_card : H0U.card = H0.card := by
    refine Finset.card_bij (fun x hx => (⟨x, (mem_erase.mp (mem_filter.mp hx).1).2⟩ : X.V)) ?_ ?_ ?_
    · intro x hx
      obtain ⟨hxU, hax⟩ := mem_filter.mp hx
      exact mem_filter.mpr ⟨mem_erase.mpr ⟨fun e => (mem_erase.mp hxU).1 (congrArg Subtype.val e), mem_univ _⟩, hax⟩
    · intro _ _ _ _ h; exact congrArg Subtype.val h
    · intro j hj
      obtain ⟨jrest, haj⟩ := mem_filter.mp hj
      have hne : j.val ≠ a.val := fun e => (mem_erase.mp jrest).1 (Subtype.ext e)
      exact ⟨j.val, mem_filter.mpr ⟨mem_erase.mpr ⟨hne, j.property⟩, haj⟩, rfl⟩
  have hH0U_sub : H0U ⊆ outN X.D U t0.val := by
    intro x hx
    obtain ⟨hxU, hax⟩ := mem_filter.mp hx
    have haxD : X.D a.val x = true := (mem_col.mp (active.mp hax).choose_spec).2.2.2
    exact mem_outN.mpr ⟨hxU, cross t0 ⟨x, (mem_erase.mp hxU).2⟩ ht0.2.2.1 haxD (by simp [ht0.2.2.2, hax])⟩
  have ht0U : t0.val ∈ U := mem_erase.mpr ⟨fun e => ne_arc ht0.2.2.1 (Subtype.ext e), t0.property⟩
  have hH0U_eq : H0U = outN X.D U t0.val :=
    eq_of_subset_of_card_le hH0U_sub (by rw [outdeg t0.val ht0U, hH0U_card, hH0eq])
  refine ⟨t0, ht0, hTuniq, fun x hx htx => ?_⟩
  have hxH0U : x ∈ H0U := hH0U_eq ▸ mem_outN.mpr ⟨hx, htx⟩
  exact (mem_col.mp (active.mp (mem_filter.mp hxH0U).2).choose_spec).2.2.2

end SinglePivot

#print axioms puncture_flat_weights
#print axioms whole_side_merge_bounds
#print axioms out_regular_forces_clean_parent

/-! ### Part 3: Sharp Clean-Parent Bounds & In-Regular / Bounded-Ratio Elimination -/

section CleanParent

/-- Every fresh parent `t` (clean OR dirty) satisfies `∑_{h ∈ H1} H a h < q * ∑_{y ∈ N^-_U(t) \ P0} H a y`
    via `fold_bank_strict_of_positive_retained` on `U^rev`. -/
theorem fresh_head_bank_bound {q n} (X : Model q n) (hq : 3 ≤ q) (small : SmallerSmallRow q X.V.card)
    {F B} (step : Boundary X F B)
    (least : ∀ M, Boundary X F M → (targets X.D X.V F B).card ≤ (targets X.D X.V F M).card)
    (multi : 1 < (targets X.D X.V F B).card) {a b : X.V} (edge : Fresh X F (a, b))
    (no : ¬SharedArcReachMargin.StrictColumns q (insertArc (graph X.D F) a b) X.V)
    {H : Matrix X.V X.V ℝ} (inv : CommonInverse (realMatrix q X.D X.V) H)
    {t : X.V} (ft : Fresh X F (t, a)) :
    let H1 := (rest a).filter (fun h : X.V => X.D a h = true ∧ graph X.D F a h = false)
    let Y := (rest a).filter (fun y : X.V => X.D y t = true ∧ graph X.D F y a = false)
    0 < (∑ h ∈ H1, H a h) ∧
    (∑ h ∈ H1, H a h) < (q : ℝ) * (∑ y ∈ Y, H a y) ∧
    Y.Nonempty := by
  classical
  intro H1 Y
  have two : 2 ≤ q := by omega
  obtain ⟨_, hSp, _, p, hpos, _, hmp, hrc, hmatch⟩ :=
    puncture_flat_weights X two small step least multi edge no inv
  let U := X.V.erase a.val
  have hsmallU : SmallerSmallRow q U.card := fun E K hlt hfr =>
    small E K (hlt.trans (card_erase_lt_of_mem a.property)) hfr
  have hfreeU : QFree X.D U q := X.free.mono_set (erase_subset _ _)
  have cross := SharedArcPivotPaths.crossed X two small step least multi edge no
  obtain ⟨_, h0, _, hh0, _, _, _, _⟩ :=
    SharedArcPivotDetour.endpoint_escape X hq small step least multi edge no
  have ne_arc {i j : X.V} (e : X.D i j = true) : i ≠ j :=
    fun eq => loopfree X.free (by omega) j.property (eq ▸ e)
  let H1U := U.filter (fun x => X.D a.val x = true ∧ graph X.D F a.val x = false)
  let YU := U.filter (fun y => X.D y t.val = true ∧ graph X.D F y a.val = false)
  have htU : t.val ∈ U := mem_erase.mpr ⟨fun e => ne_arc ft.2.2.1 (Subtype.ext e), t.property⟩
  have hh0H1U : h0.val ∈ H1U := mem_filter.mpr
    ⟨mem_erase.mpr ⟨fun e => (ne_arc hh0.2.2.1).symm (Subtype.ext e), h0.property⟩, hh0.2.2.1, hh0.2.2.2⟩
  have htNotH1 : t.val ∉ H1U := fun hm => by
    have hat : X.D a.val t.val = true := (mem_filter.mp hm).2.1
    exact X.free a.val 2 (by decide) two (.step t.property hat (.step a.property ft.2.2.1 (.refl _)))
  have hno_rev : ∀ s ∈ H1U, ¬ (fun u v => X.D v u) t.val s = true := by
    intro s hs hst
    have has : X.D a.val s = true := (mem_filter.mp hs).2.1
    have hsV : s ∈ X.V := (mem_erase.mp (mem_filter.mp hs).1).2
    exact X.free t.val 3 (by decide) hq
      (.step a.property ft.2.2.1 (.step hsV has (.step t.property hst (.refl _))))
  have hbank_sub : foldBank q (fun u v => X.D v u) U H1U t.val ⊆ YU := by
    intro z hz
    obtain ⟨hout, s, hsH1, hball⟩ := mem_filter.mp hz
    obtain ⟨hzU, hzt⟩ := mem_outN.mp hout
    refine mem_filter.mpr ⟨hzU, hzt, ?_⟩
    apply Bool.eq_false_iff.mpr
    intro hzaF
    have hzaD : X.D z a.val = true := (mem_col.mp (active.mp hzaF).choose_spec).2.2.2
    obtain ⟨hsU, has, hasF⟩ := mem_filter.mp hsH1
    have hzs : X.D z s = true :=
      cross ⟨z, (mem_erase.mp hzU).2⟩ ⟨s, (mem_erase.mp hsU).2⟩ hzaD has (by simp [hzaF, hasF])
    obtain ⟨_, l, hl, path_rev⟩ := mem_ball.mp hball
    have path_fwd : Walk X.D U s z l := walk_reverse hzU path_rev
    exact X.free s (l + 1) (by omega) (by omega)
      ((path_fwd.mono (erase_subset _ _)).snoc (mem_erase.mp hsU).2 hzs)
  have hH1pos_Q : 0 < mass H1U p := sum_pos (fun s hs => (hpos s (mem_filter.mp hs).1).2) ⟨h0.val, hh0H1U⟩
  have hfold_Q := fold_bank_strict_of_positive_retained two hfreeU.reverse hsmallU
    (filter_subset _ _) (mem_sdiff.mpr ⟨htU, htNotH1⟩) hno_rev p
    (fun i hi => (hpos i hi).2.le)
    (fun i hi => (hpos i (mem_sdiff.mp hi).1).2)
    hH1pos_Q
    (fun i hi => by
      have hc := (hrc i hi).2
      rw [hmp]
      simpa only [WeightedSD.row, WeightedSD.col, outW, inW] using hc.ge)
  have hle_YU : mass (foldBank q (fun u v => X.D v u) U H1U t.val) p ≤ mass YU p :=
    sum_le_sum_of_subset_of_nonneg hbank_sub fun i hi _ => (hpos i (mem_filter.mp hi).1).2.le
  have hstrict_Q : mass H1U p < (q : ℚ) * mass YU p := by
    have hq0 : (0 : ℚ) ≤ q := Nat.cast_nonneg q
    nlinarith
  have hH1pos_R : (0 : ℝ) < (mass H1U p : ℝ) := by exact_mod_cast hH1pos_Q
  have hstrict_R : (mass H1U p : ℝ) < (q : ℝ) * (mass YU p : ℝ) := by exact_mod_cast hstrict_Q
  rw [sum_rest_filter_eq_mass rfl (fun x => X.D a.val x = true ∧ graph X.D F a.val x = false)
        p (fun i => H a i) _ (fun i hi => (hmatch i hi).2)] at hH1pos_R hstrict_R
  rw [sum_rest_filter_eq_mass rfl (fun y => X.D y t.val = true ∧ graph X.D F y a.val = false)
        p (fun i => H a i) _ (fun i hi => (hmatch i hi).2)] at hstrict_R
  have hposH1 : 0 < ∑ h ∈ H1, H a h := by
    have := mul_pos hH1pos_R hSp
    rwa [div_mul_cancel₀ _ hSp.ne'] at this
  have hlt : (∑ h ∈ H1, H a h) < (q : ℝ) * (∑ y ∈ Y, H a y) := by
    have := mul_lt_mul_of_pos_right hstrict_R hSp
    rwa [mul_div_assoc', div_mul_cancel₀ _ hSp.ne', div_mul_cancel₀ _ hSp.ne'] at this
  have hYne : Y.Nonempty := by
    by_contra hE
    rw [not_nonempty_iff_eq_empty.mp hE, sum_empty, mul_zero] at hlt
    linarith
  exact ⟨hposH1, hlt, hYne⟩

/-- At a clean fresh parent `t`, we get the exact `Y`-gap identity, the chained strict inequality
    `0 < ∑_{H1} H a h < q * ∑_Y H a y = (q - 1) H a t - 1 < (q - 1) H a t`,
    and the unconditional `p`-spread `q * |Y| * L < (q - 1) * H a t` for any floor `L` on `Y`. -/
theorem clean_parent_sharp_bounds {q n} (X : Model q n) (hq : 3 ≤ q) (small : SmallerSmallRow q X.V.card)
    {F B} (step : Boundary X F B)
    (least : ∀ M, Boundary X F M → (targets X.D X.V F B).card ≤ (targets X.D X.V F M).card)
    (stop : ∀ M, Boundary X F M → ¬SmallRow q (graph X.D (insert M F)) X.V)
    (multi : 1 < (targets X.D X.V F B).card) {a b : X.V} (edge : Fresh X F (a, b))
    (no : ¬SharedArcReachMargin.StrictColumns q (insertArc (graph X.D F) a b) X.V)
    {H : Matrix X.V X.V ℝ} (inv : CommonInverse (realMatrix q X.D X.V) H)
    {t : X.V} (ft : Fresh X F (t, a))
    (clean : ∀ x ∈ X.V.erase a.val, X.D t.val x = true → X.D a.val x = true) :
    let H1 := (rest a).filter (fun h : X.V => X.D a h = true ∧ graph X.D F a h = false)
    let Y := (rest a).filter (fun y : X.V => X.D y t = true ∧ graph X.D F y a = false)
    ((q : ℝ) * (∑ y ∈ Y, H a y) = ((q : ℝ) - 1) * H a t - 1) ∧
    (0 < ∑ h ∈ H1, H a h) ∧
    ((∑ h ∈ H1, H a h) < (q : ℝ) * (∑ y ∈ Y, H a y)) ∧
    ((q : ℝ) * (∑ y ∈ Y, H a y) < ((q : ℝ) - 1) * H a t) ∧
    Y.Nonempty ∧
    (∀ L : ℝ, (∀ y ∈ Y, L ≤ H a y) → (q : ℝ) * (Y.card : ℝ) * L < ((q : ℝ) - 1) * H a t) := by
  classical
  intro H1 Y
  have two : 2 ≤ q := by omega
  have diag : H a a = 0 := SharedArcPunctureExpansion.zero_diagonal X two small step least multi edge no inv
  have ne_arc {i j : X.V} (e : X.D i j = true) : i ≠ j :=
    fun eq => loopfree X.free (by omega) j.property (eq ▸ e)
  have hta_ne : t ≠ a := ne_arc ft.2.2.1
  obtain ⟨_, sat, _, _⟩ := (SharedArcPivot.alternatives X two small step least multi edge).resolve_left no
  obtain ⟨hposH1, hbank, hYne⟩ := fresh_head_bank_bound X hq small step least multi edge no inv ft
  let P0 := (rest a).filter (fun x : X.V => graph X.D F x a = true)
  have hP0_to_t : ∀ x ∈ P0, X.D x t = true := by
    intro x hx
    obtain ⟨xrest, xold⟩ := mem_filter.mp hx
    have xa : X.D x a = true := (mem_col.mp (active.mp xold).choose_spec).2.2.2
    have hxt_ne : t.val ≠ x.val := fun e =>
      Bool.noConfusion (ft.2.2.2.symm.trans (by simpa [e] using xold))
    have htU : t.val ∈ X.V.erase a.val := mem_erase.mpr ⟨fun e => hta_ne (Subtype.ext e), t.property⟩
    have hxU : x.val ∈ X.V.erase a.val := mem_erase.mpr ⟨fun e => (mem_erase.mp xrest).1 (Subtype.ext e), x.property⟩
    exact SharedArcPivotGate.forced_parent X.free sat a.property htU hxU hxt_ne xa clean (by omega)
  have huniq : ∀ u : X.V, Fresh X F (u, a) → u = t := fun u fu =>
    SharedArcPivotGate.clean_parent_only X hq small step least stop multi edge no ft clean fu
  have hin_a : (∑ j : X.V, if X.D j a = true then H a j else 0) = (∑ x ∈ P0, H a x) + H a t := by
    rw [← sum_filter]
    have hset : univ.filter (fun j : X.V => X.D j a = true) = insert t P0 := by
      ext j
      simp only [mem_filter, mem_univ, true_and, mem_insert, P0, rest, mem_erase]
      constructor
      · intro hja
        have jne : j ≠ a := ne_arc hja
        cases hjF : graph X.D F j a
        · exact Or.inl (huniq j ⟨j.property, a.property, hja, hjF⟩)
        · exact Or.inr ⟨by simp [jne], rfl⟩
      · rintro (rfl | ⟨_, old⟩)
        · exact ft.2.2.1
        · exact (mem_col.mp (active.mp old).choose_spec).2.2.2
    have htNotP0 : t ∉ P0 := fun hm => Bool.noConfusion (ft.2.2.2.symm.trans (mem_filter.mp hm).2)
    rw [hset, sum_insert htNotP0, add_comm]
  have hcol_t : H a t + (q : ℝ) * ((∑ x ∈ P0, H a x) + (∑ y ∈ Y, H a y)) = ∑ j : X.V, H a j := by
    have eq := congrArg (fun M : Matrix X.V X.V ℝ => M a t) (mul_eq_one_comm.mp inv.right)
    change ((fun j => H a j) ᵥ* excess (realMatrix q X.D X.V)) t = (1 : Matrix X.V X.V ℝ) a t at eq
    rw [vecMul_excess, one_apply_ne hta_ne.symm, sub_eq_zero, col_eval_puncture a t (fun j => H a j) diag] at eq
    have hsplit : (rest a).filter (fun j : X.V => X.D j t = true) = P0 ∪ Y := by
      ext j
      simp only [mem_filter, mem_union, P0, Y]
      constructor
      · rintro ⟨jrest, hjt⟩
        cases hjF : graph X.D F j a
        · exact Or.inr ⟨jrest, hjt, rfl⟩
        · exact Or.inl ⟨jrest, rfl⟩
      · rintro (⟨jrest, old⟩ | ⟨jrest, hjt, _⟩)
        · exact ⟨jrest, hP0_to_t j (mem_filter.mpr ⟨jrest, old⟩)⟩
        · exact ⟨jrest, hjt⟩
    have hdisj : Disjoint P0 Y := Finset.disjoint_left.mpr fun j hj1 hj2 =>
      Bool.noConfusion ((mem_filter.mp hj2).2.2.symm.trans (mem_filter.mp hj1).2)
    rw [hsplit, sum_union hdisj] at eq
    exact eq
  have hacc := (SharedArcPunctureExpansion.inverse_accounts X inv a).2
  rw [diag, zero_add, hin_a] at hacc
  have hgap : (q : ℝ) * (∑ y ∈ Y, H a y) = ((q : ℝ) - 1) * H a t - 1 := by linarith
  have hspread : ∀ L : ℝ, (∀ y ∈ Y, L ≤ H a y) → (q : ℝ) * (Y.card : ℝ) * L < ((q : ℝ) - 1) * H a t := by
    intro L hL
    have hsumL : (Y.card : ℝ) * L ≤ ∑ y ∈ Y, H a y := by
      calc (Y.card : ℝ) * L = ∑ _ ∈ Y, L := by rw [sum_const, nsmul_eq_mul]
        _ ≤ ∑ y ∈ Y, H a y := sum_le_sum hL
    have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    nlinarith
  exact ⟨hgap, hposH1, hbank, by linarith, hYne, hspread⟩

/-- No puncture with column-weight ratio `≤ q / (q - 1)` can have a clean fresh parent
    (NO out-degree or row-weight hypothesis is needed). -/
theorem clean_parent_bounded_ratio_false {q n} (X : Model q n) (hq : 3 ≤ q)
    (small : SmallerSmallRow q X.V.card) {F B} (step : Boundary X F B)
    (least : ∀ M, Boundary X F M → (targets X.D X.V F B).card ≤ (targets X.D X.V F M).card)
    (stop : ∀ M, Boundary X F M → ¬SmallRow q (graph X.D (insert M F)) X.V)
    (multi : 1 < (targets X.D X.V F B).card) {a b : X.V} (edge : Fresh X F (a, b))
    (no : ¬SharedArcReachMargin.StrictColumns q (insertArc (graph X.D F) a b) X.V)
    {H : Matrix X.V X.V ℝ} (inv : CommonInverse (realMatrix q X.D X.V) H)
    {t : X.V} (ft : Fresh X F (t, a))
    (clean : ∀ x ∈ X.V.erase a.val, X.D t.val x = true → X.D a.val x = true)
    {L : ℝ} (hLpos : 0 ≤ L) (hfloor : ∀ i ∈ rest a, L ≤ H a i)
    (hcap : ((q : ℝ) - 1) * H a t ≤ (q : ℝ) * L) : False := by
  obtain ⟨_, _, _, _, hYne, hspread⟩ :=
    clean_parent_sharp_bounds X hq small step least stop multi edge no inv ft clean
  have hYcard : (1 : ℝ) ≤ ((rest a).filter (fun y : X.V => X.D y t = true ∧ graph X.D F y a = false)).card := by
    exact_mod_cast card_pos.mpr hYne
  have hlt := hspread L (fun y hy => hfloor y (mem_filter.mp hy).1)
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hmul : (q : ℝ) * L ≤ (q : ℝ) * (((rest a).filter (fun y : X.V => X.D y t = true ∧ graph X.D F y a = false)).card : ℝ) * L :=
    mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hq0 hYcard) hLpos
  linarith

/-- No in-regular puncture can have a clean fresh parent (NO out-degree hypothesis needed!). -/
theorem clean_parent_in_regular_false {q n k} (X : Model q n) (hq : 3 ≤ q)
    (small : SmallerSmallRow q X.V.card) {F B} (step : Boundary X F B)
    (least : ∀ M, Boundary X F M → (targets X.D X.V F B).card ≤ (targets X.D X.V F M).card)
    (stop : ∀ M, Boundary X F M → ¬SmallRow q (graph X.D (insert M F)) X.V)
    (multi : 1 < (targets X.D X.V F B).card) {a b : X.V} (edge : Fresh X F (a, b))
    (no : ¬SharedArcReachMargin.StrictColumns q (insertArc (graph X.D F) a b) X.V)
    {t : X.V} (ft : Fresh X F (t, a))
    (clean : ∀ x ∈ X.V.erase a.val, X.D t.val x = true → X.D a.val x = true)
    (indeg : ∀ x ∈ X.V.erase a.val, (inN X.D (X.V.erase a.val) x).card = k) : False := by
  classical
  have two : 2 ≤ q := by omega
  obtain ⟨H, inv⟩ := strict_inverse_of_proper_smallRow (small.induced X.free)
    (fun i => (X.weights i : ℚ)) (fun _ _ => Nat.cast_nonneg _) X.strict
  obtain ⟨_, hSp, _, p, _, _, _, hrc, hmatch⟩ :=
    puncture_flat_weights X two small step least multi edge no inv
  let U := X.V.erase a.val
  have hden_pos : (0 : ℚ) < 1 + (q : ℚ) * k := by positivity
  let RQ : Matrix U U ℚ := WeightedArithmetic.rationalMatrix q (adjacencyMatrix X.D U)
  have hunitQ : IsUnit RQ.det := isUnit_iff_ne_zero.mpr (WeightedArithmetic.rational_det_ne_zero two _)
  have hconst_sol : (fun _ : U => (1 + (q : ℚ) * k)⁻¹) ᵥ* RQ = fun _ => 1 := by
    funext i
    rw [WeightedArithmetic.rational_vecMul_apply]
    have hcount : (∑ j : U, (adjacencyMatrix X.D U j i : ℚ) * (1 + (q : ℚ) * k)⁻¹) =
        (k : ℚ) * (1 + (q : ℚ) * k)⁻¹ := by
      have hsum : (∑ j : U, (adjacencyMatrix X.D U j i : ℚ)) = k := by
        have h1 : (∑ j : U, (adjacencyMatrix X.D U j i : ℚ)) =
            ((univ.filter (fun j : U => X.D j.val i.val = true)).card : ℚ) := by
          simp [adjacencyMatrix, sum_boole]
        rw [h1]
        have hcard : (univ.filter (fun j : U => X.D j.val i.val = true)).card = (inN X.D U i.val).card := by
          refine Finset.card_bij (fun j _ => j.val) ?_ ?_ ?_
          · intro j hj; exact mem_inN.mpr ⟨j.property, (mem_filter.mp hj).2⟩
          · intro _ _ _ _ h; exact Subtype.ext h
          · intro x hx
            obtain ⟨hxU, hxi⟩ := mem_inN.mp hx
            exact ⟨⟨x, hxU⟩, mem_filter.mpr ⟨mem_univ _, hxi⟩, rfl⟩
        rw [hcard, indeg i.val i.property]
      rw [← sum_mul, hsum]
    rw [hcount]
    field_simp [hden_pos.ne']
  have hp_sol : (fun i : U => p i.val) ᵥ* RQ = fun _ => 1 := by
    funext i
    rw [WeightedArithmetic.rational_vecMul_apply]
    have hc := (hrc i.val i.property).2
    rw [WeightedSD.col, inW, ← Finset.sum_coe_sort U] at hc
    rw [← hc]
    congr 1; congr 1
    apply sum_congr rfl
    intro j _
    simp only [adjacencyMatrix]
    by_cases hd : X.D j.val i.val = true <;> simp [hd]
  have hp_const : ∀ i ∈ U, p i = (1 + (q : ℚ) * k)⁻¹ := by
    have h2 := congrArg (fun v => v ᵥ* RQ⁻¹) (hp_sol.trans hconst_sol.symm)
    rw [vecMul_vecMul, vecMul_vecMul, mul_nonsing_inv RQ hunitQ, vecMul_one, vecMul_one] at h2
    intro i hi
    exact congrFun h2 ⟨i, hi⟩
  let L : ℝ := (∑ j : X.V, H a j) / (1 + (q : ℝ) * k)
  have hH_const : ∀ i ∈ rest a, H a i = L := by
    intro i hi
    have hiU : i.val ∈ U := mem_erase.mpr ⟨fun e => (mem_erase.mp hi).1 (Subtype.ext e), i.property⟩
    have hm := (hmatch i (mem_erase.mp hi).1).2
    rw [hp_const i.val hiU] at hm
    push_cast at hm
    have h1 := congrArg (fun z => z * (∑ j : X.V, H a j)) hm
    rw [div_mul_cancel₀ _ hSp.ne'] at h1
    dsimp [L]
    rw [div_eq_inv_mul, ← h1]
    rfl
  have hLpos : 0 ≤ L := (div_pos hSp (by positivity)).le
  have ht_rest : t ∈ rest a := mem_erase.mpr ⟨fun eq =>
    loopfree X.free (by omega) a.property (eq ▸ ft.2.2.1), mem_univ _⟩
  apply clean_parent_bounded_ratio_false X hq small step least stop multi edge no inv ft clean hLpos
    (fun i hi => (hH_const i hi).ge)
  rw [hH_const t ht_rest]
  linarith

end CleanParent

#print axioms fresh_head_bank_bound
#print axioms clean_parent_sharp_bounds
#print axioms clean_parent_bounded_ratio_false
#print axioms clean_parent_in_regular_false

/-! ### Part 4: Universal Schur-Complement Diagonal Dominance of `H = (R_D - J)⁻¹` -/

section InverseDiagonal

private theorem erase_nonempty_of_model {q n} (X : Model q n) (hq : 2 ≤ q) (t : X.V) :
    (X.V.erase t.val).Nonempty := by
  by_contra hE
  have hcard : X.V.card ≤ 1 := by
    have h1 := card_erase_add_one t.property
    rw [not_nonempty_iff_eq_empty.mp hE, card_empty] at h1
    omega
  let tv : ℕ := t.val
  have htv : tv ∈ X.V := t.property
  have hsub : X.V = {tv} := Subset.antisymm
    (fun x hx => mem_singleton.mpr (card_le_one.mp hcard x hx tv htv))
    (singleton_subset_iff.mpr htv)
  have htriv : SmallRow q X.D X.V := by
    intro f _ _
    refine ⟨tv, htv, ?_⟩
    rw [hsub, WeightedSD.row, mass, sum_singleton, outW, sum_singleton,
        Bool.eq_false_iff.mpr (loopfree X.free (by omega) htv)]
    simp
  exact htriv.no_strict X.live (fun i => (X.weights i : ℚ)) (fun _ _ => Nat.cast_nonneg _) X.strict

/-- On ANY minimal CH counterexample (`Model q n` + `SmallerSmallRow`, all residues `|V| mod q`),
    no positive diagonal entry `H t t > 0` can dominate its column after row-sum normalization:
    `∃ i ≠ t, H t t * (∑ j, H i j) < (∑ j, H t j) * H i t`. -/
theorem inverse_diagonal_strict_column {q n} (X : Model q n) (hq : 2 ≤ q)
    (small : SmallerSmallRow q X.V.card)
    {H : Matrix X.V X.V ℝ} (inv : CommonInverse (realMatrix q X.D X.V) H)
    (t : X.V) (htt : 0 < H t t) :
    ∃ i : X.V, i ≠ t ∧ H t t * (∑ j : X.V, H i j) < (∑ j : X.V, H t j) * H i t := by
  classical
  by_contra! hall
  let w : X.V → ℝ := fun i => ∑ j : X.V, H i j
  let z : X.V → ℝ := fun i => H t t * w i - w t * H i t
  have hzt : z t = 0 := by simp [z, mul_comm]
  have hznn : ∀ i : X.V, 0 ≤ z i := by
    intro i
    by_cases hit : i = t
    · subst hit; rw [hzt]
    · exact sub_nonneg.mpr (hall i hit)
  have hCz : ∀ i : X.V, i ≠ t → (excess (realMatrix q X.D X.V) *ᵥ z) i = H t t := by
    intro i hit
    have hCw : (excess (realMatrix q X.D X.V) *ᵥ w) i = 1 := by
      have h1 : excess (realMatrix q X.D X.V) *ᵥ (H *ᵥ (fun _ => 1)) = fun _ => 1 := by
        rw [mulVec_mulVec, inv.right, one_mulVec]
      have hw_eq : w = H *ᵥ (fun _ => 1) := by
        funext x; simp [w, mulVec, dotProduct]
      rw [hw_eq]
      exact congrFun h1 i
    have hCH : (excess (realMatrix q X.D X.V) *ᵥ (fun j => H j t)) i = 0 := by
      have h1 := congrArg (fun M : Matrix X.V X.V ℝ => M i t) inv.right
      simpa [Matrix.mul_apply, mulVec, dotProduct, one_apply_ne hit] using h1
    have hlin : (excess (realMatrix q X.D X.V) *ᵥ z) i =
        H t t * (excess (realMatrix q X.D X.V) *ᵥ w) i -
        w t * (excess (realMatrix q X.D X.V) *ᵥ (fun j => H j t)) i := by
      simp only [z, mulVec, dotProduct, mul_sub, sum_sub_distrib, mul_sum]
      congr 1 <;> apply sum_congr rfl <;> intro j _ <;> ring
    rw [hlin, hCw, hCH, mul_one, mul_zero, sub_zero]
  let U := X.V.erase t.val
  have hUne : U.Nonempty := erase_nonempty_of_model X hq t
  have hsmallU : SmallRow q X.D U :=
    small X.D U (card_erase_lt_of_mem t.property) (X.free.mono_set (erase_subset _ _))
  obtain ⟨d, hd⟩ := realDual_of_smallRow hsmallU hUne
  let dV : X.V → ℝ := fun i => if i = t then 0 else d i.val
  have hdV_sum : ∑ i : X.V, dV i = 1 := by
    have h1 := sum_erase_add univ dV (mem_univ t)
    simp only [dV, ↓reduceIte, add_zero] at h1
    rw [← h1]
    have h2 : ∑ i ∈ univ.erase t, (if i = t then 0 else d i.val) = ∑ x ∈ U, d x := by
      refine Finset.sum_bij (fun i _ => i.val) ?_ ?_ ?_ ?_
      · intro i hi; exact mem_erase.mpr ⟨fun e => (mem_erase.mp hi).1 (Subtype.ext e), i.property⟩
      · intro _ _ _ _ h; exact Subtype.ext h
      · intro x hx
        have hxV : x ∈ X.V := (mem_erase.mp hx).2
        exact ⟨⟨x, hxV⟩, mem_erase.mpr ⟨fun e => (mem_erase.mp hx).1 (congrArg Subtype.val e), mem_univ _⟩, rfl⟩
      · intro i hi; simp [(mem_erase.mp hi).1]
    rw [h2]
    exact hd.normalized
  have hpos : ∑ i : X.V, dV i * (excess (realMatrix q X.D X.V) *ᵥ z) i = H t t := by
    have hterm : ∀ i : X.V, dV i * (excess (realMatrix q X.D X.V) *ᵥ z) i = dV i * H t t := by
      intro i
      by_cases hit : i = t
      · subst hit; simp [dV]
      · rw [hCz i hit]
    simp_rw [hterm, ← sum_mul, hdV_sum, one_mul]
  have hnonpos : ∑ i : X.V, dV i * (excess (realMatrix q X.D X.V) *ᵥ z) i ≤ 0 := by
    have hswap : ∑ i : X.V, dV i * (excess (realMatrix q X.D X.V) *ᵥ z) i =
        ∑ j : X.V, (dV ᵥ* excess (realMatrix q X.D X.V)) j * z j := by
      simp only [mulVec, vecMul, dotProduct, mul_sum, sum_mul, mul_assoc]
      exact Finset.sum_comm
    rw [hswap]
    apply sum_nonpos
    intro j _
    by_cases hjt : j = t
    · subst hjt; rw [hzt, mul_zero]
    · apply mul_nonpos_of_nonpos_of_nonneg _ (hznn j)
      rw [vecMul_excess, hdV_sum, sub_nonpos]
      have hjU : j.val ∈ U := mem_erase.mpr ⟨fun e => hjt (Subtype.ext e), j.property⟩
      have hcol := hd.columns j.val hjU
      rw [realCol] at hcol
      have heq : (dV ᵥ* realMatrix q X.D X.V) j = d j.val + (q : ℝ) * realInW X.D U d j.val := by
        simp only [vecMul, dotProduct, realMatrix_entry, mul_add, mul_ite, mul_one, mul_zero,
          sum_add_distrib, sum_ite_eq', mem_univ, ite_true]
        have hdj : dV j = d j.val := by simp [dV, hjt]
        rw [hdj]
        congr 1
        rw [realInW, mul_sum]
        have h1 := sum_erase_add univ (fun i : X.V => if X.D i.val j.val = true then dV i * (q : ℝ) else 0) (mem_univ t)
        have hzero : (if X.D t.val j.val = true then dV t * (q : ℝ) else 0) = 0 := by simp [dV]
        rw [hzero, add_zero] at h1
        rw [← h1]
        refine Finset.sum_bij (fun i _ => i.val) ?_ ?_ ?_ ?_
        · intro i hi; exact mem_erase.mpr ⟨fun e => (mem_erase.mp hi).1 (Subtype.ext e), i.property⟩
        · intro _ _ _ _ h; exact Subtype.ext h
        · intro x hx
          have hxV : x ∈ X.V := (mem_erase.mp hx).2
          exact ⟨⟨x, hxV⟩, mem_erase.mpr ⟨fun e => (mem_erase.mp hx).1 (congrArg Subtype.val e), mem_univ _⟩, rfl⟩
        · intro i hi
          have hne : i ≠ t := (mem_erase.mp hi).1
          by_cases hd : X.D i.val j.val = true <;> simp [dV, hne, hd, mul_comm]
      rw [heq]
      exact hcol
  linarith

/-- Dual row version of `inverse_diagonal_strict_column`:
    `∃ j ≠ t, H t t * (∑ i, H i j) < (∑ i, H i t) * H t j`. -/
theorem inverse_diagonal_strict_row {q n} (X : Model q n) (hq : 2 ≤ q)
    (small : SmallerSmallRow q X.V.card)
    {H : Matrix X.V X.V ℝ} (inv : CommonInverse (realMatrix q X.D X.V) H)
    (t : X.V) (htt : 0 < H t t) :
    ∃ j : X.V, j ≠ t ∧ H t t * (∑ i : X.V, H i j) < (∑ i : X.V, H i t) * H t j := by
  classical
  by_contra! hall
  let p : X.V → ℝ := fun j => ∑ i : X.V, H i j
  let y : X.V → ℝ := fun j => H t t * p j - p t * H t j
  have hyt : y t = 0 := by simp [y, mul_comm]
  have hynn : ∀ j : X.V, 0 ≤ y j := by
    intro j
    by_cases hjt : j = t
    · subst hjt; rw [hyt]
    · exact sub_nonneg.mpr (hall j hjt)
  have hyC : ∀ j : X.V, j ≠ t → (y ᵥ* excess (realMatrix q X.D X.V)) j = H t t := by
    intro j hjt
    have hpC : (p ᵥ* excess (realMatrix q X.D X.V)) j = 1 := by
      have h1 : ((fun _ => 1) ᵥ* H) ᵥ* excess (realMatrix q X.D X.V) = fun _ => 1 := by
        rw [vecMul_vecMul, mul_eq_one_comm.mp inv.right, vecMul_one]
      have hp_eq : p = (fun _ => 1) ᵥ* H := by
        funext x; simp [p, vecMul, dotProduct]
      rw [hp_eq]
      exact congrFun h1 j
    have hHC : ((fun i => H t i) ᵥ* excess (realMatrix q X.D X.V)) j = 0 := by
      have h1 := congrArg (fun M : Matrix X.V X.V ℝ => M t j) (mul_eq_one_comm.mp inv.right)
      simpa [Matrix.mul_apply, vecMul, dotProduct, one_apply_ne hjt.symm] using h1
    have hlin : (y ᵥ* excess (realMatrix q X.D X.V)) j =
        H t t * (p ᵥ* excess (realMatrix q X.D X.V)) j -
        p t * ((fun i => H t i) ᵥ* excess (realMatrix q X.D X.V)) j := by
      simp only [y, vecMul, dotProduct, sub_mul, sum_sub_distrib, mul_sum]
      congr 1 <;> apply sum_congr rfl <;> intro i _ <;> ring
    rw [hlin, hpC, hHC, mul_one, mul_zero, sub_zero]
  let U := X.V.erase t.val
  have hUne : U.Nonempty := erase_nonempty_of_model X hq t
  have hsmallUrev : SmallRow q (fun a b => X.D b a) U :=
    small _ U (card_erase_lt_of_mem t.property) (X.free.mono_set (erase_subset _ _)).reverse
  obtain ⟨d, hd⟩ := realDual_of_smallRow hsmallUrev hUne
  let dV : X.V → ℝ := fun i => if i = t then 0 else d i.val
  have hdV_sum : ∑ i : X.V, dV i = 1 := by
    have h1 := sum_erase_add univ dV (mem_univ t)
    simp only [dV, ↓reduceIte, add_zero] at h1
    rw [← h1]
    have h2 : ∑ i ∈ univ.erase t, (if i = t then 0 else d i.val) = ∑ x ∈ U, d x := by
      refine Finset.sum_bij (fun i _ => i.val) ?_ ?_ ?_ ?_
      · intro i hi; exact mem_erase.mpr ⟨fun e => (mem_erase.mp hi).1 (Subtype.ext e), i.property⟩
      · intro _ _ _ _ h; exact Subtype.ext h
      · intro x hx
        have hxV : x ∈ X.V := (mem_erase.mp hx).2
        exact ⟨⟨x, hxV⟩, mem_erase.mpr ⟨fun e => (mem_erase.mp hx).1 (congrArg Subtype.val e), mem_univ _⟩, rfl⟩
      · intro i hi; simp [(mem_erase.mp hi).1]
    rw [h2]
    exact hd.normalized
  have hpos : ∑ j : X.V, (y ᵥ* excess (realMatrix q X.D X.V)) j * dV j = H t t := by
    have hterm : ∀ j : X.V, (y ᵥ* excess (realMatrix q X.D X.V)) j * dV j = H t t * dV j := by
      intro j
      by_cases hjt : j = t
      · subst hjt; simp [dV]
      · rw [hyC j hjt]
    simp_rw [hterm, ← mul_sum, hdV_sum, mul_one]
  have hnonpos : ∑ j : X.V, (y ᵥ* excess (realMatrix q X.D X.V)) j * dV j ≤ 0 := by
    have hswap : ∑ j : X.V, (y ᵥ* excess (realMatrix q X.D X.V)) j * dV j =
        ∑ i : X.V, y i * (excess (realMatrix q X.D X.V) *ᵥ dV) i := by
      simp only [mulVec, vecMul, dotProduct, mul_sum, sum_mul, mul_assoc]
      exact Finset.sum_comm
    rw [hswap]
    apply sum_nonpos
    intro i _
    by_cases hit : i = t
    · subst hit; rw [hyt, zero_mul]
    · apply mul_nonpos_of_nonneg_of_nonpos (hynn i)
      rw [mulVec_excess, hdV_sum, sub_nonpos]
      have hiU : i.val ∈ U := mem_erase.mpr ⟨fun e => hit (Subtype.ext e), i.property⟩
      have hcol := hd.columns i.val hiU
      rw [realCol] at hcol
      have heq : (realMatrix q X.D X.V *ᵥ dV) i = d i.val + (q : ℝ) * realInW (fun a b => X.D b a) U d i.val := by
        simp only [mulVec, dotProduct, realMatrix_entry, add_mul, ite_mul, one_mul, zero_mul,
          sum_add_distrib, sum_ite_eq, mem_univ, ite_true]
        have hdi : dV i = d i.val := by simp [dV, hit]
        rw [hdi]
        congr 1
        rw [realInW, mul_sum]
        have h1 := sum_erase_add univ (fun j : X.V => if X.D i.val j.val = true then (q : ℝ) * dV j else 0) (mem_univ t)
        have hzero : (if X.D i.val t.val = true then (q : ℝ) * dV t else 0) = 0 := by simp [dV]
        rw [hzero, add_zero] at h1
        rw [← h1]
        refine Finset.sum_bij (fun j _ => j.val) ?_ ?_ ?_ ?_
        · intro j hj; exact mem_erase.mpr ⟨fun e => (mem_erase.mp hj).1 (Subtype.ext e), j.property⟩
        · intro _ _ _ _ h; exact Subtype.ext h
        · intro x hx
          have hxV : x ∈ X.V := (mem_erase.mp hx).2
          exact ⟨⟨x, hxV⟩, mem_erase.mpr ⟨fun e => (mem_erase.mp hx).1 (congrArg Subtype.val e), mem_univ _⟩, rfl⟩
        · intro j hj
          have hne : j ≠ t := (mem_erase.mp hj).1
          by_cases hd : X.D i.val j.val = true <;> simp [dV, hne, hd]
      rw [heq]
      exact hcol
  linarith

end InverseDiagonal

#print axioms inverse_diagonal_strict_column
#print axioms inverse_diagonal_strict_row

/-! ### Part 5: Flat-Branch Quantitative Non-Domination & Regular Small-d Closure -/

section FlatBranch

private theorem inN_sub {D : CH.Digraph} {V : Finset ℕ} {v : ℕ} : inN D V v ⊆ V :=
  filter_subset _ _

private theorem inW_eq_mass_local {D : CH.Digraph} {V : Finset ℕ} {p : ℕ → ℚ} {v : ℕ} :
    inW D V p v = mass (inN D V v) p := by
  simp [inW, inN, mass, sum_filter]

/-- Quantitative two-vertex non-domination on any flat `q`-free graph with `SmallerSmallRow`. -/
theorem flat_pair_non_domination {q : ℕ} (hq : 2 ≤ q) {E : CH.Digraph} {V : Finset ℕ}
    (hf : QFree E V q) (hsmall : SmallerSmallRow q V.card)
    {w p : ℕ → ℚ} (hpos : ∀ x ∈ V, 0 < w x ∧ 0 < p x)
    (hmw : mass V w = 1) (hmp : mass V p = 1)
    (hrow : ∀ x ∈ V, WeightedSD.row q E V w x = 1)
    (hcol : ∀ x ∈ V, WeightedSD.col q E V p x = 1)
    {a b : ℕ} (ha : a ∈ V) (hb : b ∈ V) (hab : a ≠ b) :
    (w a + w b + (q : ℚ) * mass (outN E V a ∩ outN E V b) w ≤ 1) ∧
    (p a + p b + (q : ℚ) * mass (inN E V a ∩ inN E V b) p ≤ 1) ∧
    (w b ≤ (q : ℚ) * mass (outN E V a \ outN E V b) w) ∧
    (p b ≤ (q : ℚ) * mass (inN E V a \ inN E V b) p) := by
  classical
  have hSab : ({a, b} : Finset ℕ) ⊆ V := insert_subset_iff.mpr ⟨ha, singleton_subset_iff.mpr hb⟩
  have hcard : 2 ≤ ({a, b} : Finset ℕ).card := by rw [card_pair hab]
  have hmass_ab_w : mass ({a, b} : Finset ℕ) w = w a + w b := by rw [mass, sum_pair hab]
  have hmass_ab_p : mass ({a, b} : Finset ℕ) p = p a + p b := by rw [mass, sum_pair hab]
  have hout_eq : V.filter (fun y => ∀ s ∈ ({a, b} : Finset ℕ), E s y = true) = outN E V a ∩ outN E V b := by
    ext y; simp [mem_outN, and_left_comm, and_assoc]
  have hin_eq : V.filter (fun y => ∀ s ∈ ({a, b} : Finset ℕ), E y s = true) = inN E V a ∩ inN E V b := by
    ext y; simp [mem_inN, and_left_comm, and_assoc]
  have h1 := mergeOut_common_bound hq hf hsmall hSab hcard w
    (fun x hx => (hpos x hx).1.le) (by rw [hmass_ab_w]; linarith [(hpos a ha).1, (hpos b hb).1])
    (fun x hx => by rw [hmw, hrow x hx])
  rw [hmass_ab_w, hout_eq, hmw] at h1
  have h2 := mergeIn_common_bound hq hf hsmall hSab hcard p
    (fun x hx => (hpos x hx).2.le) (by rw [hmass_ab_p]; linarith [(hpos a ha).2, (hpos b hb).2])
    (fun x hx => by rw [hmp, hcol x hx])
  rw [hmass_ab_p, hin_eq, hmp] at h2
  have hrow_a := hrow a ha
  rw [WeightedSD.row, outW_eq_mass] at hrow_a
  have hsplit_out : mass (outN E V a) w = mass (outN E V a \ outN E V b) w + mass (outN E V a ∩ outN E V b) w := by
    simp only [mass]
    rw [← sum_union (disjoint_sdiff_inter _ _), sdiff_union_inter]
  have hcol_a := hcol a ha
  rw [WeightedSD.col, inW_eq_mass_local] at hcol_a
  have hsplit_in : mass (inN E V a) p = mass (inN E V a \ inN E V b) p + mass (inN E V a ∩ inN E V b) p := by
    simp only [mass]
    rw [← sum_union (disjoint_sdiff_inter _ _), sdiff_union_inter]
  rw [hsplit_out, mul_add] at hrow_a
  rw [hsplit_in, mul_add] at hcol_a
  refine ⟨h1, h2, by linarith, by linarith⟩

/-- Weighted common-out-neighbor exclusion bound on a flat `q`-free graph (`q ≥ 3`):
    every vertex `x ∈ K = outN(a) ∩ outN(b)` cannot point to `{a, b} ∪ inN(a) ∪ inN(b)`. -/
theorem flat_common_out_exclusion {q : ℕ} (hq : 3 ≤ q) {E : CH.Digraph} {V : Finset ℕ}
    (hf : QFree E V q) (hsmall : SmallerSmallRow q V.card)
    {w : ℕ → ℚ} (hpos : ∀ x ∈ V, 0 < w x) (hmw : mass V w = 1)
    (hrow : ∀ x ∈ V, WeightedSD.row q E V w x = 1)
    {a b : ℕ} (ha : a ∈ V) (hb : b ∈ V) (hab : a ≠ b)
    (hnoab : E a b = false) (hnoba : E b a = false)
    (hKne : (outN E V a ∩ outN E V b).Nonempty) :
    let K := outN E V a ∩ outN E V b
    (q : ℚ) * mass (inN E V a ∪ inN E V b) w + ((q : ℚ) - 1) * mass K w + (q : ℚ) * (w a + w b) ≤ (q : ℚ) - 1 := by
  classical
  intro K
  have hKV : K ⊆ V := inter_subset_left.trans outN_subset
  have haNotK : a ∉ K := fun hm => loopfree hf (by omega) ha (mem_outN.mp (mem_inter.mp hm).1).2
  have hKlt : K.card < V.card := card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hKV, fun eq => haNotK (eq ▸ ha)⟩)
  obtain ⟨x, hxK, hxrow⟩ := hsmall E K hKlt (hf.mono_set hKV) w (fun u hu => (hpos u (hKV hu)).le) hKne
  have hxV : x ∈ V := hKV hxK
  have hax : E a x = true := (mem_outN.mp (mem_inter.mp hxK).1).2
  have hbx : E b x = true := (mem_outN.mp (mem_inter.mp hxK).2).2
  let F := ({a, b} : Finset ℕ) ∪ (inN E V a ∪ inN E V b) ∪ K
  have hFV : F ⊆ V := union_subset (union_subset (insert_subset_iff.mpr ⟨ha, singleton_subset_iff.mpr hb⟩)
    (union_subset inN_sub inN_sub)) hKV
  have hdisj_x : Disjoint (outN E V x \ K) F := by
    rw [Finset.disjoint_left]
    intro y hy hyF
    obtain ⟨hyOut, hyNotK⟩ := mem_sdiff.mp hy
    obtain ⟨hyV, hxy⟩ := mem_outN.mp hyOut
    rcases mem_union.mp hyF with hy1 | hyK
    · rcases mem_union.mp hy1 with hyab | hyIn
      · rcases mem_insert.mp hyab with hya | hyb
        · rw [hya] at hxy
          exact hf a 2 (by decide) (by omega) (.step hxV hax (.step ha hxy (.refl _)))
        · rw [mem_singleton.mp hyb] at hxy
          exact hf b 2 (by decide) (by omega) (.step hxV hbx (.step hb hxy (.refl _)))
      · rcases mem_union.mp hyIn with hya | hyb
        · exact hf a 3 (by decide) hq (.step hxV hax (.step hyV hxy (.step ha (mem_inN.mp hya).2 (.refl _))))
        · exact hf b 3 (by decide) hq (.step hxV hbx (.step hyV hxy (.step hb (mem_inN.mp hyb).2 (.refl _))))
    · exact hyNotK hyK
  have hdisj_ab_in : Disjoint ({a, b} : Finset ℕ) (inN E V a ∪ inN E V b) := by
    rw [Finset.disjoint_left]
    intro y hyab hyin
    rcases mem_insert.mp hyab with hya | hyb
    · rw [hya] at hyin
      rcases mem_union.mp hyin with h1 | h2
      · exact loopfree hf (by omega) ha (mem_inN.mp h1).2
      · exact Bool.noConfusion (hnoab.symm.trans (mem_inN.mp h2).2)
    · rw [mem_singleton.mp hyb] at hyin
      rcases mem_union.mp hyin with h1 | h2
      · exact Bool.noConfusion (hnoba.symm.trans (mem_inN.mp h1).2)
      · exact loopfree hf (by omega) hb (mem_inN.mp h2).2
  have hdisj_ab_K : Disjoint ({a, b} : Finset ℕ) K := by
    rw [Finset.disjoint_left]
    intro y hyab hyK
    rcases mem_insert.mp hyab with hya | hyb
    · exact haNotK (hya ▸ hyK)
    · rw [mem_singleton.mp hyb] at hyK
      exact loopfree hf (by omega) hb (mem_outN.mp (mem_inter.mp hyK).2).2
  have hdisj_in_K : Disjoint (inN E V a ∪ inN E V b) K := by
    rw [Finset.disjoint_left]
    intro y hyin hyK
    have hyV : y ∈ V := hKV hyK
    rcases mem_union.mp hyin with h1 | h2
    · exact hf a 2 (by decide) (by omega) (.step hyV (mem_outN.mp (mem_inter.mp hyK).1).2 (.step ha (mem_inN.mp h1).2 (.refl _)))
    · exact hf b 2 (by decide) (by omega) (.step hyV (mem_outN.mp (mem_inter.mp hyK).2).2 (.step hb (mem_inN.mp h2).2 (.refl _)))
  have hmass_F : mass F w = (w a + w b) + mass (inN E V a ∪ inN E V b) w + mass K w := by
    simp only [F, mass]
    rw [sum_union (disjoint_union_left.mpr ⟨hdisj_ab_K, hdisj_in_K⟩),
        sum_union hdisj_ab_in, sum_pair hab]
  have hsub_compl : outN E V x \ K ⊆ V \ F := by
    intro y hy
    exact mem_sdiff.mpr ⟨outN_subset (mem_sdiff.mp hy).1, fun hyF => Finset.disjoint_left.mp hdisj_x hy hyF⟩
  have hle_out : mass (outN E V x \ K) w ≤ 1 - mass F w := by
    have h1 : mass (outN E V x \ K) w ≤ mass (V \ F) w :=
      sum_le_sum_of_subset_of_nonneg hsub_compl fun u hu _ => (hpos u (mem_sdiff.mp hu).1).le
    have h2 : mass (V \ F) w + mass F w = mass V w := sum_sdiff hFV
    linarith
  have hrow_x := hrow x hxV
  rw [WeightedSD.row, outW_eq_mass] at hrow_x
  rw [WeightedSD.row, outW_eq_mass] at hxrow
  have houtK : outN E K x = outN E V x ∩ K := by
    ext y
    simp only [mem_outN, mem_inter]
    exact ⟨fun ⟨hyK, hxy⟩ => ⟨⟨hKV hyK, hxy⟩, hyK⟩, fun ⟨⟨_, hxy⟩, hyK⟩ => ⟨hyK, hxy⟩⟩
  have hsplit_x : mass (outN E V x) w = mass (outN E V x \ K) w + mass (outN E K x) w := by
    rw [houtK]
    simp only [mass]
    rw [← sum_union (disjoint_sdiff_inter _ _), sdiff_union_inter]
  have hq0 : (0 : ℚ) ≤ q := Nat.cast_nonneg q
  have hq_mul : (q : ℚ) * mass (outN E V x \ K) w ≤ (q : ℚ) * (1 - mass F w) :=
    mul_le_mul_of_nonneg_left hle_out hq0
  rw [hsplit_x, mul_add] at hrow_x
  rw [hmass_F] at hq_mul
  linarith

/-- Any `d`-regular 3-free digraph on `3d + 1` vertices (with `SmallerSmallRow`) that remains 3-free
    after adding a single arc must satisfy `d ≥ 5` (ruling out `n ∈ {4, 7, 10, 13}`). -/
theorem regular_three_free_unsaturated_ge_five {E : CH.Digraph} {V : Finset ℕ} {d : ℕ}
    (hf : QFree E V 3) (hsmall : SmallerSmallRow 3 V.card)
    (hcard : V.card = 3 * d + 1)
    (hout : ∀ x ∈ V, (outN E V x).card = d)
    (hin : ∀ x ∈ V, (inN E V x).card = d)
    {a b : ℕ} (ha : a ∈ V) (hb : b ∈ V) (hab : a ≠ b)
    (hnoab : E a b = false) (hins : QFree (insertArc E a b) V 3) : 5 ≤ d := by
  classical
  have hden_pos : (0 : ℚ) < 3 * d + 1 := by positivity
  let w : ℕ → ℚ := fun _ => (3 * d + 1 : ℚ)⁻¹
  have hpos : ∀ x ∈ V, 0 < w x ∧ 0 < w x := fun _ _ => ⟨inv_pos.mpr hden_pos, inv_pos.mpr hden_pos⟩
  have hmw : mass V w = 1 := by
    rw [mass, sum_const, nsmul_eq_mul, hcard]
    push_cast
    exact mul_inv_cancel₀ hden_pos.ne'
  have hrow : ∀ x ∈ V, WeightedSD.row 3 E V w x = 1 := by
    intro x hx
    rw [WeightedSD.row, outW_eq_mass, mass, sum_const, nsmul_eq_mul, hout x hx]
    dsimp [w]; field_simp [hden_pos.ne']; ring
  have hcol : ∀ x ∈ V, WeightedSD.col 3 E V w x = 1 := by
    intro x hx
    rw [WeightedSD.col, inW_eq_mass_local, mass, sum_const, nsmul_eq_mul, hin x hx]
    dsimp [w]; field_simp [hden_pos.ne']; ring
  have hnoba : E b a = false := Bool.eq_false_iff.mpr fun hba =>
    hins a 2 (by decide) (by decide)
      (.step hb (by simp [insertArc]) (.step ha (by simp [insertArc, hba]) (.refl _)))
  have hdisj_ba : Disjoint (outN E V b) (inN E V a) := by
    rw [Finset.disjoint_left]
    intro x hxb hxa
    have hxV : x ∈ V := outN_subset hxb
    exact hins a 3 (by decide) (by decide)
      (.step hb (by simp [insertArc])
        (.step hxV (by simp [insertArc, (mem_outN.mp hxb).2])
          (.step ha (by simp [insertArc, (mem_inN.mp hxa).2]) (.refl _))))
  let K1 := outN E V a ∩ outN E V b
  let K2 := inN E V a ∩ inN E V b
  have hK1ne : K1.Nonempty := by
    by_contra hE
    have hdisj1 : Disjoint (outN E V a) (outN E V b) :=
      Finset.disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp hE)
    have hdisj_a_in : Disjoint (outN E V a) (inN E V a) := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      exact hf a 2 (by decide) (by decide) (.step (outN_subset hx1) (mem_outN.mp hx1).2 (.step ha (mem_inN.mp hx2).2 (.refl _)))
    have haNot : a ∉ outN E V a ∪ outN E V b ∪ inN E V a := by
      intro hm
      rcases mem_union.mp hm with h1 | h2
      · rcases mem_union.mp h1 with h3 | h4
        · exact loopfree hf (by decide) ha (mem_outN.mp h3).2
        · exact Bool.noConfusion (hnoba.symm.trans (mem_outN.mp h4).2)
      · exact loopfree hf (by decide) ha (mem_inN.mp h2).2
    have hbNot : b ∉ outN E V a ∪ outN E V b ∪ inN E V a := by
      intro hm
      rcases mem_union.mp hm with h1 | h2
      · rcases mem_union.mp h1 with h3 | h4
        · exact Bool.noConfusion (hnoab.symm.trans (mem_outN.mp h3).2)
        · exact loopfree hf (by decide) hb (mem_outN.mp h4).2
      · exact Bool.noConfusion (hnoba.symm.trans (mem_inN.mp h2).2)
    have haNotIns : a ∉ insert b (outN E V a ∪ outN E V b ∪ inN E V a) := by
      intro hm
      rcases mem_insert.mp hm with rfl | h2
      · exact hab rfl
      · exact haNot h2
    have hsub : insert a (insert b (outN E V a ∪ outN E V b ∪ inN E V a)) ⊆ V :=
      insert_subset_iff.mpr ⟨ha, insert_subset_iff.mpr ⟨hb,
        union_subset (union_subset outN_subset outN_subset) inN_sub⟩⟩
    have hle := card_le_card hsub
    rw [card_insert_of_notMem haNotIns, card_insert_of_notMem hbNot,
        card_union_of_disjoint (disjoint_union_left.mpr ⟨hdisj_a_in, hdisj_ba⟩),
        card_union_of_disjoint hdisj1, hout a ha, hout b hb, hin a ha, hcard] at hle
    omega
  have hK2ne : K2.Nonempty := by
    by_contra hE
    have hdisj2 : Disjoint (inN E V a) (inN E V b) :=
      Finset.disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp hE)
    have hdisj_b_out : Disjoint (outN E V b) (inN E V b) := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      exact hf b 2 (by decide) (by decide) (.step (outN_subset hx1) (mem_outN.mp hx1).2 (.step hb (mem_inN.mp hx2).2 (.refl _)))
    have haNot : a ∉ inN E V a ∪ inN E V b ∪ outN E V b := by
      intro hm
      rcases mem_union.mp hm with h1 | h2
      · rcases mem_union.mp h1 with h3 | h4
        · exact loopfree hf (by decide) ha (mem_inN.mp h3).2
        · exact Bool.noConfusion (hnoab.symm.trans (mem_inN.mp h4).2)
      · exact Bool.noConfusion (hnoba.symm.trans (mem_outN.mp h2).2)
    have hbNot : b ∉ inN E V a ∪ inN E V b ∪ outN E V b := by
      intro hm
      rcases mem_union.mp hm with h1 | h2
      · rcases mem_union.mp h1 with h3 | h4
        · exact Bool.noConfusion (hnoba.symm.trans (mem_inN.mp h3).2)
        · exact loopfree hf (by decide) hb (mem_inN.mp h4).2
      · exact loopfree hf (by decide) hb (mem_outN.mp h2).2
    have haNotIns : a ∉ insert b (inN E V a ∪ inN E V b ∪ outN E V b) := by
      intro hm
      rcases mem_insert.mp hm with rfl | h2
      · exact hab rfl
      · exact haNot h2
    have hsub : insert a (insert b (inN E V a ∪ inN E V b ∪ outN E V b)) ⊆ V :=
      insert_subset_iff.mpr ⟨ha, insert_subset_iff.mpr ⟨hb,
        union_subset (union_subset inN_sub inN_sub) outN_subset⟩⟩
    have hle := card_le_card hsub
    rw [card_insert_of_notMem haNotIns, card_insert_of_notMem hbNot,
        card_union_of_disjoint (disjoint_union_left.mpr ⟨hdisj_ba.symm, hdisj_b_out.symm⟩),
        card_union_of_disjoint hdisj2, hin a ha, hin b hb, hout b hb, hcard] at hle
    omega
  obtain ⟨hnd1, hnd2, _, _⟩ := flat_pair_non_domination (by decide) hf hsmall hpos hmw hmw hrow hcol ha hb hab
  have hK1_le : K1.card + 1 ≤ d := by
    simp only [w, mass, sum_const, nsmul_eq_mul] at hnd1
    have h1 := mul_le_mul_of_nonneg_right hnd1 hden_pos.le
    have h2 : (2 : ℚ) + 3 * (K1.card : ℚ) ≤ 3 * (d : ℚ) + 1 := by
      have hmul : ((3 * d + 1 : ℚ)⁻¹ + (3 * d + 1 : ℚ)⁻¹ + 3 * ((K1.card : ℚ) * (3 * d + 1 : ℚ)⁻¹)) * (3 * d + 1 : ℚ) =
          2 + 3 * (K1.card : ℚ) := by field_simp [hden_pos.ne']; ring
      linarith
    have h3 : 2 + 3 * K1.card ≤ 3 * d + 1 := by exact_mod_cast h2
    omega
  have hK2_le : K2.card + 1 ≤ d := by
    simp only [w, mass, sum_const, nsmul_eq_mul] at hnd2
    have h1 := mul_le_mul_of_nonneg_right hnd2 hden_pos.le
    have h2 : (2 : ℚ) + 3 * (K2.card : ℚ) ≤ 3 * (d : ℚ) + 1 := by
      have hmul : ((3 * d + 1 : ℚ)⁻¹ + (3 * d + 1 : ℚ)⁻¹ + 3 * ((K2.card : ℚ) * (3 * d + 1 : ℚ)⁻¹)) * (3 * d + 1 : ℚ) =
          2 + 3 * (K2.card : ℚ) := by field_simp [hden_pos.ne']; ring
      linarith
    have h3 : 2 + 3 * K2.card ≤ 3 * d + 1 := by exact_mod_cast h2
    omega
  have hex1 := flat_common_out_exclusion (by decide) hf hsmall (fun x hx => (hpos x hx).1) hmw hrow ha hb hab hnoab hnoba hK1ne
  have hex2 := flat_common_out_exclusion (by decide) hf.reverse hsmall (fun x hx => (hpos x hx).1) hmw
    (fun x hx => by simpa only [WeightedSD.row, WeightedSD.col, outW, inW] using hcol x hx)
    ha hb hab hnoba hnoab (by
      have heq : outN (fun u v => E v u) V a ∩ outN (fun u v => E v u) V b = K2 := by
        ext x; simp [K2, mem_outN, mem_inN]
      rwa [heq])
  have hcard_in_union : (inN E V a ∪ inN E V b).card + K2.card = 2 * d := by
    have h1 := card_union_add_card_inter (inN E V a) (inN E V b)
    rw [hin a ha, hin b hb] at h1
    change (inN E V a ∪ inN E V b).card + K2.card = d + d at h1
    omega
  have hcard_out_union : (outN E V a ∪ outN E V b).card + K1.card = 2 * d := by
    have h1 := card_union_add_card_inter (outN E V a) (outN E V b)
    rw [hout a ha, hout b hb] at h1
    change (outN E V a ∪ outN E V b).card + K1.card = d + d at h1
    omega
  have hrel1 : 2 * K1.card + 4 ≤ 3 * K2.card := by
    simp only [w, mass, sum_const, nsmul_eq_mul] at hex1
    have h1 := mul_le_mul_of_nonneg_right hex1 hden_pos.le
    have h2 : 3 * ((inN E V a ∪ inN E V b).card : ℚ) + 2 * (K1.card : ℚ) + 6 ≤ 2 * (3 * (d : ℚ) + 1) := by
      have hmul : (3 * (((inN E V a ∪ inN E V b).card : ℚ) * (3 * d + 1 : ℚ)⁻¹) +
          (3 - 1) * ((K1.card : ℚ) * (3 * d + 1 : ℚ)⁻¹) +
          3 * ((3 * d + 1 : ℚ)⁻¹ + (3 * d + 1 : ℚ)⁻¹)) * (3 * d + 1 : ℚ) =
          3 * ((inN E V a ∪ inN E V b).card : ℚ) + 2 * (K1.card : ℚ) + 6 := by
        field_simp [hden_pos.ne']; ring
      linarith
    have h3 : 3 * (inN E V a ∪ inN E V b).card + 2 * K1.card + 6 ≤ 2 * (3 * d + 1) := by exact_mod_cast h2
    omega
  have hrel2 : 2 * K2.card + 4 ≤ 3 * K1.card := by
    have heq1 : outN (fun u v => E v u) V a ∩ outN (fun u v => E v u) V b = K2 := by
      ext x; simp [K2, mem_outN, mem_inN]
    have heq2 : inN (fun u v => E v u) V a ∪ inN (fun u v => E v u) V b = outN E V a ∪ outN E V b := by
      ext x; simp [mem_outN, mem_inN]
    rw [heq1, heq2] at hex2
    simp only [w, mass, sum_const, nsmul_eq_mul] at hex2
    have h1 := mul_le_mul_of_nonneg_right hex2 hden_pos.le
    have h2 : 3 * ((outN E V a ∪ outN E V b).card : ℚ) + 2 * (K2.card : ℚ) + 6 ≤ 2 * (3 * (d : ℚ) + 1) := by
      have hmul : (3 * (((outN E V a ∪ outN E V b).card : ℚ) * (3 * d + 1 : ℚ)⁻¹) +
          (3 - 1) * ((K2.card : ℚ) * (3 * d + 1 : ℚ)⁻¹) +
          3 * ((3 * d + 1 : ℚ)⁻¹ + (3 * d + 1 : ℚ)⁻¹)) * (3 * d + 1 : ℚ) =
          3 * ((outN E V a ∪ outN E V b).card : ℚ) + 2 * (K2.card : ℚ) + 6 := by
        field_simp [hden_pos.ne']; ring
      linarith
    have h3 : 3 * (outN E V a ∪ outN E V b).card + 2 * K2.card + 6 ≤ 2 * (3 * d + 1) := by exact_mod_cast h2
    omega
  omega

end FlatBranch

#print axioms flat_pair_non_domination
#print axioms flat_common_out_exclusion
#print axioms regular_three_free_unsaturated_ge_five

end LeanCH.BR.Closure.SharedArcPivotMerge
