import checkpoints.shen_extension.BoundaryReceiverWitness
import Mathlib.NumberTheory.Padics.PadicNorm

namespace LeanCH.BR.Closure.FeederPrivateHeadDescent

open Finset BRq2 BRq3 BR45 WeightedSD ShenCycleSuccessor ShortestCycleWeights
open FirstPacketBarrier SharedArcBarrier

abbrev Pair := ℕ × ℕ

def exclusive (D : CH.Digraph) (V : Finset ℕ) (a b : ℕ) :=
  outN D V a \ outN D V b

/-- Pair actual private heads, exhausting at least one side. The policy is chosen
before following any price discrepancy. -/
structure Matching (A B : Finset ℕ) where
  left : Finset ℕ
  right : Finset ℕ
  left_sub : left ⊆ A
  right_sub : right ⊆ B
  pair : ↥left ≃ ↥right
  full : left = A ∨ right = B

noncomputable def chooseMatching (A B : Finset ℕ) : Matching A B := by
  classical
  by_cases h : A.card ≤ B.card
  · let R := (exists_subset_card_eq (s := B) h).choose
    have spec : R ⊆ B ∧ R.card = A.card := (exists_subset_card_eq (s := B) h).choose_spec
    exact ⟨A,R,Subset.rfl,spec.1,equivOfCardEq spec.2.symm,Or.inl rfl⟩
  · have hb : B.card ≤ A.card := by omega
    let L := (exists_subset_card_eq (s := A) hb).choose
    have spec : L ⊆ A ∧ L.card = B.card := (exists_subset_card_eq (s := A) hb).choose_spec
    exact ⟨L,B,spec.1,Subset.rfl,equivOfCardEq spec.2,Or.inr rfl⟩

abbrev Policy (D : CH.Digraph) (V : Finset ℕ) :=
  ∀ a b : ℕ, Matching (exclusive D V a b) (exclusive D V b a)

def gap (w : ℕ → ℚ) (x : Pair) := w x.1 - w x.2

def remainder {A B : Finset ℕ} (m : Matching A B) (w : ℕ → ℚ) :=
  mass (A \ m.left) w - mass (B \ m.right) w

private theorem private_difference (S T : Finset ℕ) (w : ℕ → ℚ) :
    mass S w - mass T w = mass (S \ T) w - mass (T \ S) w := by
  have h₁ := sum_sdiff (f := w) (inter_subset_left : S ∩ T ⊆ S)
  have h₂ := sum_sdiff (f := w) (inter_subset_right : S ∩ T ⊆ T)
  rw [sdiff_inter_self_left] at h₁
  rw [sdiff_inter_self_right] at h₂
  unfold mass
  linarith

/-- Exact cancellation of common columns and accounting for every other column. -/
theorem matched_equation {D V q w c} (flat : ∀ i ∈ V, WeightedSD.row q D V w i = c)
    {a b} (av : a ∈ V) (bv : b ∈ V)
    (m : Matching (exclusive D V a b) (exclusive D V b a)) :
    gap w (a,b) = -(q : ℚ) *
      ((∑ i : ↥m.left, (w i - w (m.pair i))) + remainder m w) := by
  classical
  have arow := flat a av
  have brow := flat b bv
  rw [WeightedSD.row,outW_eq_mass] at arow brow
  have diff := private_difference (outN D V a) (outN D V b) w
  change _ = mass (exclusive D V a b) w - mass (exclusive D V b a) w at diff
  have hl := sum_sdiff (f := w) m.left_sub
  have hr := sum_sdiff (f := w) m.right_sub
  have pairs := m.pair.sum_comp (fun j : ↥m.right => w j)
  rw [sum_sub_distrib,pairs,sum_coe_sort,sum_coe_sort]
  unfold mass at diff arow brow
  unfold gap remainder mass
  dsimp only [Prod.fst,Prod.snd]
  linear_combination arow - brow + (q : ℚ) * (hl - hr - diff)

def Rises {D V} (policy : Policy D V) (w : ℕ → ℚ) (ell : ℕ) (x y : Pair) : Prop :=
  (∃ i : ↥(policy x.1 x.2).left, y = (i.val,((policy x.1 x.2).pair i).val)) ∧
    padicNorm ell (gap w x) < padicNorm ell (gap w y)

private theorem child_or_bank {D : CH.Digraph} {V : Finset ℕ} {q ell : ℕ} {w : ℕ → ℚ} {c : ℚ} [Fact ell.Prime] (divides : ell ∣ q)
    (flat : ∀ i ∈ V, WeightedSD.row q D V w i = c) (policy : Policy D V)
    {a b} (av : a ∈ V) (bv : b ∈ V) (unequal : w a ≠ w b) :
    (∃ y ∈ V ×ˢ V, Rises policy w ell (a,b) y) ∨
      padicNorm ell (gap w (a,b)) < padicNorm ell (remainder (policy a b) w) := by
  classical
  let m := policy a b
  let g := padicNorm ell (gap w (a,b))
  have gp : 0 < g := lt_of_le_of_ne (padicNorm.nonneg _) (Ne.symm (padicNorm.nonzero (sub_ne_zero.mpr unequal)))
  by_contra! no
  have terms (i : ↥m.left) : padicNorm ell (w i - w (m.pair i)) ≤ g := by
    by_contra! bigger
    have il := m.left_sub i.property
    have jr := m.right_sub (m.pair i).property
    exact no.1 (i.val,(m.pair i).val)
      (mem_product.mpr ⟨(mem_outN.mp (mem_sdiff.mp il).1).1,(mem_outN.mp (mem_sdiff.mp jr).1).1⟩)
      ⟨⟨i,rfl⟩,bigger⟩
  have sumle := padicNorm.sum_le' (p := ell) (s := univ) (fun i _ => terms i) gp.le
  have both := (padicNorm.nonarchimedean (p := ell)
    (q := ∑ i : ↥m.left, (w i - w (m.pair i))) (r := remainder m w)).trans
    (max_le sumle no.2)
  have eq := congrArg (padicNorm ell) (matched_equation flat av bv m)
  rw [padicNorm.mul,padicNorm.neg] at eq
  have small := mul_lt_mul_of_pos_right ((padicNorm.nat_lt_one_iff q).mpr divides) gp
  have bad := mul_le_mul_of_nonneg_left both (padicNorm.nonneg (q : ℚ) (p := ell))
  change g = _ at eq
  linarith

/-- For any fixed maximal matching policy and any unequal starting prices, a finite
chain of physical matched private heads ends at a one-sided unmatched bank. The
non-Archimedean size strictly increases again at the final, aggregate bank. -/
theorem trace_to_bank {D : CH.Digraph} {V : Finset ℕ} {q ell : ℕ} {w : ℕ → ℚ} {c : ℚ} [Fact ell.Prime] (divides : ell ∣ q)
    (flat : ∀ i ∈ V, WeightedSD.row q D V w i = c) (policy : Policy D V)
    {a b} (av : a ∈ V) (bv : b ∈ V) (unequal : w a ≠ w b) :
    ∃ y ∈ V ×ˢ V, Relation.ReflTransGen (Rises policy w ell) (a,b) y ∧
      w y.1 ≠ w y.2 ∧ (outN D V y.1).card ≠ (outN D V y.2).card ∧
      padicNorm ell (gap w y) < padicNorm ell (remainder (policy y.1 y.2) w) := by
  classical
  let reach := (V ×ˢ V).filter (fun y => Relation.ReflTransGen (Rises policy w ell) (a,b) y)
  have start : (a,b) ∈ reach := mem_filter.mpr ⟨mem_product.mpr ⟨av,bv⟩,.refl⟩
  obtain ⟨y,hy,maximal⟩ := reach.exists_max_image (fun x => padicNorm ell (gap w x)) ⟨_,start⟩
  obtain ⟨pair,chain⟩ := mem_filter.mp hy
  obtain ⟨yv,zv⟩ := mem_product.mp pair
  have pos : 0 < padicNorm ell (gap w y) := lt_of_lt_of_le
    (lt_of_le_of_ne (padicNorm.nonneg _) (Ne.symm (padicNorm.nonzero (sub_ne_zero.mpr unequal)))) (maximal _ start)
  have diff : w y.1 ≠ w y.2 := by
    intro eq
    simp [gap,eq] at pos
  obtain step | bank := child_or_bank divides flat policy yv zv diff
  · obtain ⟨v,vv,edge⟩ := step
    exact False.elim (edge.2.not_ge (maximal v (mem_filter.mpr ⟨vv,chain.tail edge⟩)))
  refine ⟨y,pair,chain,diff,?_,bank⟩
  intro degree
  let m := policy y.1 y.2
  have eqpriv : (exclusive D V y.1 y.2).card = (exclusive D V y.2 y.1).card := by
    have h := card_sdiff_add_card_inter (outN D V y.1) (outN D V y.2)
    have k := card_sdiff_add_card_inter (outN D V y.2) (outN D V y.1)
    rw [inter_comm] at k
    unfold exclusive
    omega
  have same : m.left.card = m.right.card := by simpa using Fintype.card_congr m.pair
  have full : m.left = exclusive D V y.1 y.2 ∧ m.right = exclusive D V y.2 y.1 := by
    rcases m.full with h | h
    · exact ⟨h,eq_of_subset_of_card_le m.right_sub (by rw [h] at same; omega)⟩
    · exact ⟨eq_of_subset_of_card_le m.left_sub (by rw [h] at same; omega),h⟩
  change _ < padicNorm ell (remainder m w) at bank
  simp [remainder,full.1,full.2,mass] at bank
  linarith

#print axioms matched_equation
#print axioms trace_to_bank

end LeanCH.BR.Closure.FeederPrivateHeadDescent
