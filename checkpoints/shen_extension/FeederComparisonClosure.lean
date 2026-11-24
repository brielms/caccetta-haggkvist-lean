import checkpoints.shen_extension.FeederDegreeSignature

namespace LeanCH.BR.Closure.FeederPrivateHeadDescent

open Finset BRq2 BRq3 BR45 WeightedSD ShenCycleSuccessor ShortestCycleWeights

/-- Keep both original graph labels even when their prices agree. -/
def PrivateStep (D : CH.Digraph) (V : Finset ℕ) (x y : Pair) : Prop :=
  y.1 ∈ exclusive D V x.1 x.2 ∧ y.2 ∈ exclusive D V x.2 x.1

abbrev Compared (D : CH.Digraph) (V : Finset ℕ) (seed y : Pair) :=
  Relation.ReflTransGen (PrivateStep D V) seed y

theorem compared_vertices {D V seed y} (start : seed.1 ∈ V ∧ seed.2 ∈ V)
    (path : Compared D V seed y) : y.1 ∈ V ∧ y.2 ∈ V := by
  cases path with
  | refl => exact start
  | tail _ edge =>
    exact ⟨(mem_outN.mp (mem_sdiff.mp edge.1).1).1, (mem_outN.mp (mem_sdiff.mp edge.2).1).1⟩

/-- All private heads of the two rows have one common price when every child
comparison is tied. Equal parent prices then give equal private cardinalities. -/
theorem tied_private_banks {D V q w c} (hq : 0 < q)
    (flat : ∀ i ∈ V, WeightedSD.row q D V w i = c) (pos : ∀ i ∈ V, 0 < w i)
    {a b} (av : a ∈ V) (bv : b ∈ V) (same : w a = w b)
    (left : (exclusive D V a b).Nonempty) (right : (exclusive D V b a).Nonempty)
    (ties : ∀ i ∈ exclusive D V a b, ∀ j ∈ exclusive D V b a, w i = w j) :
    (outN D V a).card = (outN D V b).card ∧
      ∃ v > (0 : ℚ), ∀ i ∈ exclusive D V a b ∪ exclusive D V b a, w i = v := by
  classical
  obtain ⟨i,hi⟩ := left
  obtain ⟨j,hj⟩ := right
  have l k (hk : k ∈ exclusive D V a b) : w k = w j := ties k hk j hj
  have r k (hk : k ∈ exclusive D V b a) : w k = w j := (ties i hi k hk).symm.trans (l i hi)
  have wp := pos j (mem_outN.mp (mem_sdiff.mp hj).1).1
  refine ⟨?_, w j, wp, fun k hk => (mem_union.mp hk).elim (l k) (r k)⟩
  have hA := flat a av
  have hB := flat b bv
  rw [WeightedSD.row,outW_eq_mass,same] at hA
  rw [WeightedSD.row,outW_eq_mass] at hB
  have qp : (0 : ℚ) < q := by exact_mod_cast hq
  have amounts : mass (outN D V a) w = mass (outN D V b) w := by
    nlinarith only [hA,hB,qp]
  have cancel (S T : Finset ℕ) :
      mass (S \ T) w + mass (S ∩ T) w = mass S w := by
    simpa [mass] using (sum_sdiff (f := w) (inter_subset_left : S ∩ T ⊆ S))
  have ca := cancel (outN D V a) (outN D V b)
  have cb := cancel (outN D V b) (outN D V a)
  rw [inter_comm (outN D V b)] at cb
  have bank : mass (exclusive D V a b) w = mass (exclusive D V b a) w := by
    unfold exclusive
    linarith only [ca,cb,amounts]
  have mc (S : Finset ℕ) (h : ∀ k ∈ S, w k = w j) :
      mass S w = (S.card : ℚ) * w j := by
    unfold mass
    calc
      _ = ∑ _k ∈ S, w j := sum_congr rfl h
      _ = _ := by simp
  rw [mc _ l,mc _ r] at bank
  have cnt : (exclusive D V a b).card = (exclusive D V b a).card := by
    exact_mod_cast (mul_right_cancel₀ wp.ne' bank)
  have m := card_sdiff_add_card_inter (outN D V a) (outN D V b)
  have n := card_sdiff_add_card_inter (outN D V b) (outN D V a)
  rw [inter_comm] at n
  unfold exclusive at cnt
  omega

def DegreeGap (D : CH.Digraph) (V : Finset ℕ) (y : Pair) : ℚ :=
  ((outN D V y.1).card : ℚ) - (outN D V y.2).card

/-- The price-free comparison queue either reaches the previous arithmetic
endpoint or is closed with tied prices, degrees and monochromatic private heads. -/
theorem comparison_fork {q n ell : ℕ} [Fact ell.Prime] (X : Model q n)
    (hq : 2 ≤ q) (small : SmallerSmallRow q X.V.card) (dv : ell ∣ q)
    {w π c} (posw : ∀ i ∈ X.V, 0 < w i) (flat : ∀ i ∈ X.V, WeightedSD.row q X.D X.V w i = c)
    (pos : ∀ i ∈ X.V, 0 < π i) (high : mass X.V π < c)
    (cols : ∀ i ∈ X.V, WeightedSD.col q X.D X.V π i = c)
    {a b} (av : a ∈ X.V) (bv : b ∈ X.V) (ne : a ≠ b) :
    (∃ y, Compared X.D X.V (a,b) y ∧ gap w y ≠ 0 ∧ DegreeGap X.D X.V y ≠ 0 ∧
      padicNorm ell (gap w y) = padicNorm ell ((q : ℚ)*c*DegreeGap X.D X.V y) ∧
      ∃ j k, j ≠ k ∧ ((failsTransfer q X.D X.V π y.1 y.2 j ∧ failsTransfer q X.D X.V π y.1 y.2 k) ∨
        (failsTransfer q X.D X.V π y.2 y.1 j ∧ failsTransfer q X.D X.V π y.2 y.1 k))) ∨
    (∀ y, Compared X.D X.V (a,b) y → w y.1 = w y.2 ∧
      (outN X.D X.V y.1).card = (outN X.D X.V y.2).card ∧
      ∃ v > (0 : ℚ), ∀ i ∈ exclusive X.D X.V y.1 y.2 ∪ exclusive X.D X.V y.2 y.1, w i = v) := by
  classical
  by_cases unequal : ∃ x, Compared X.D X.V (a,b) x ∧ w x.1 ≠ w x.2
  · obtain ⟨x,px,diff⟩ := unequal
    obtain ⟨xv,yv⟩ := compared_vertices ⟨av,bv⟩ px
    obtain ⟨y,hv,rise,yd,bound,sig⟩ := same_pair_signature X hq small dv posw flat pos high cols xv yv diff
    have tail : Compared X.D X.V x y := by
      clear hv yd bound sig
      induction rise with
      | refl => exact .refl
      | tail _ e ih => exact ih.tail ⟨e.1,e.2.1⟩
    have gapne : gap w y ≠ 0 := sub_ne_zero.mpr yd
    change padicNorm ell (gap w y) = padicNorm ell ((q : ℚ)*c*DegreeGap X.D X.V y) at sig
    have dg : DegreeGap X.D X.V y ≠ 0 := by
      intro zero
      rw [zero,mul_zero,padicNorm.zero] at sig
      exact padicNorm.nonzero gapne sig
    have dd : (outN X.D X.V y.1).card ≠ (outN X.D X.V y.2).card := by
      intro eq
      apply dg
      simp [DegreeGap,eq]
    exact Or.inl ⟨y,px.trans tail,gapne,dg,sig,two_failed_columns X hq small pos high cols
      (mem_product.mp hv).1 (mem_product.mp hv).2 dd⟩
  · right
    have eq (y) (h : Compared X.D X.V (a,b) y) : w y.1 = w y.2 := by
      by_contra d
      exact unequal ⟨y,h,d⟩
    intro y py
    have nd : y.1 ≠ y.2 := by
      cases py with
      | refl => exact ne
      | @tail x y _ e =>
        intro same
        exact (mem_sdiff.mp e.1).2 (same ▸ (mem_sdiff.mp e.2).1)
    obtain ⟨yv,zv⟩ := compared_vertices ⟨av,bv⟩ py
    exact ⟨eq y py,tied_private_banks (by omega : 0 < q) flat posw yv zv (eq y py)
      (has_exclusive X hq small pos high cols yv zv nd)
      (has_exclusive X hq small pos high cols zv yv nd.symm)
      (fun i hi j hj => eq (i,j) (py.tail ⟨hi,hj⟩))⟩

#print axioms compared_vertices
#print axioms tied_private_banks
#print axioms comparison_fork
end LeanCH.BR.Closure.FeederPrivateHeadDescent
