import checkpoints.shen_extension.FeederProtectedReceiver

namespace LeanCH.BR.Closure.FeederPrivateHeadDescent

open Finset BRq2 BRq3 BR45 WeightedSD ShenCycleSuccessor ShortestCycleWeights

/-- The two coordinates follow private physical arcs. A new matching may be
chosen at each pair. Strict increase prevents a pair from recurring. -/
def FreeRise {D : CH.Digraph} {V : Finset ℕ} (w : ℕ → ℚ) (ell : ℕ) (x y : Pair) : Prop :=
  y.1 ∈ exclusive D V x.1 x.2 ∧ y.2 ∈ exclusive D V x.2 x.1 ∧
    padicNorm ell (gap w x) < padicNorm ell (gap w y)

private theorem dominant_difference {ell : ℕ} [Fact ell.Prime] {a b : ℚ}
    (smaller : padicNorm ell (a-b) < padicNorm ell a) : padicNorm ell b = padicNorm ell a := by
  have sum := padicNorm.add_eq_max_of_ne (p := ell) (q := -(a-b)) (r := a)
    (by simpa only [padicNorm.neg] using smaller.ne)
  rw [padicNorm.neg,max_eq_right smaller.le,show -(a-b)+a=b by ring] at sum
  exact sum

/-- A flat nonzero row level fixes the absolute value of every native price
at every prime factor of q. -/
theorem flat_price_norm {q ell : ℕ} [Fact ell.Prime] (dv : ell ∣ q) {D V w c}
    (pos : ∀ i ∈ V, 0 < w i) (rows : ∀ i ∈ V, WeightedSD.row q D V w i = c)
    {u} (hu : u ∈ V) : padicNorm ell (w u) = padicNorm ell c := by
  classical
  obtain ⟨v,hv,top⟩ := V.exists_max_image (fun j => padicNorm ell (w j)) ⟨u,hu⟩
  let M := padicNorm ell (w v)
  have mp : 0 < M := lt_of_le_of_ne (padicNorm.nonneg _) (Ne.symm (padicNorm.nonzero (pos v hv).ne'))
  have err (i) (hi : i ∈ V) : padicNorm ell (c-w i) < M := by
    have roweq := rows i hi
    rw [WeightedSD.row,outW_eq_mass] at roweq
    rw [show c - w i = (q : ℚ) * mass (outN D V i) w by linarith only [roweq],padicNorm.mul]
    have le : padicNorm ell (mass (outN D V i) w) ≤ M :=
      padicNorm.sum_le' (fun j hj => top j (mem_outN.mp hj).1) mp.le
    exact (mul_le_mul_of_nonneg_left le (padicNorm.nonneg _)).trans_lt
      (by simpa using mul_lt_mul_of_pos_right ((padicNorm.nat_lt_one_iff q).mpr dv) mp)
  have atTop : padicNorm ell c = M := by
    apply dominant_difference (a := w v)
    rw [←padicNorm.neg,neg_sub]
    exact err v hv
  apply dominant_difference
  rw [atTop]
  exact err u hu

/-- A fixed terminal pair for all possible private-head comparisons at once.
The integer outdegree difference determines its exact normalized price norm. -/
theorem same_pair_signature {q n ell : ℕ} [Fact ell.Prime] (X : Model q n)
    (hq : 2 ≤ q) (small : SmallerSmallRow q X.V.card) (dv : ell ∣ q)
    {w π c} (posw : ∀ i ∈ X.V, 0 < w i) (flat : ∀ i ∈ X.V, WeightedSD.row q X.D X.V w i = c)
    (pos : ∀ i ∈ X.V, 0 < π i) (high : mass X.V π < c)
    (cols : ∀ i ∈ X.V, WeightedSD.col q X.D X.V π i = c)
    {a b} (av : a ∈ X.V) (bv : b ∈ X.V) (diff : w a ≠ w b) :
    ∃ y ∈ X.V ×ˢ X.V, Relation.ReflTransGen (FreeRise (D := X.D) (V := X.V) w ell) (a,b) y ∧
      w y.1 ≠ w y.2 ∧
      (∀ i ∈ exclusive X.D X.V y.1 y.2, ∀ j ∈ exclusive X.D X.V y.2 y.1,
        padicNorm ell (w i - w j) ≤ padicNorm ell (gap w y)) ∧
      padicNorm ell (gap w y) = padicNorm ell ((q : ℚ)*c*
        (((outN X.D X.V y.1).card : ℚ) - (outN X.D X.V y.2).card)) := by
  classical
  let rel := FreeRise (D := X.D) (V := X.V) w ell
  let K := (X.V ×ˢ X.V).filter (fun y => Relation.ReflTransGen rel (a,b) y)
  have start : (a,b) ∈ K := mem_filter.mpr ⟨mem_product.mpr ⟨av,bv⟩,.refl⟩
  obtain ⟨y,hy,top⟩ := K.exists_max_image (fun x => padicNorm ell (gap w x)) ⟨_,start⟩
  obtain ⟨yv,path⟩ := mem_filter.mp hy
  obtain ⟨v₁,v₂⟩ := mem_product.mp yv
  let g := padicNorm ell (gap w y)
  have gp : 0 < g := lt_of_lt_of_le (lt_of_le_of_ne (padicNorm.nonneg _)
    (Ne.symm (padicNorm.nonzero (sub_ne_zero.mpr diff)))) (top _ start)
  have ne : w y.1 ≠ w y.2 := by intro eq; simp [g,gap,eq] at gp
  let S := outN X.D X.V y.1
  let T := outN X.D X.V y.2
  let A := S \ T
  let B := T \ S
  have bound (i) (hi : i ∈ A) (j) (hj : j ∈ B) : padicNorm ell (w i-w j) ≤ g := by
    by_contra! gt
    have ij : (i,j) ∈ X.V ×ˢ X.V := mem_product.mpr ⟨(mem_outN.mp (mem_sdiff.mp hi).1).1,
      (mem_outN.mp (mem_sdiff.mp hj).1).1⟩
    have e : rel y (i,j) := ⟨hi,hj,gt⟩
    exact gt.not_ge (top _ (mem_filter.mpr ⟨ij,path.tail e⟩))
  refine ⟨y,yv,path,ne,bound,?_⟩
  have yn : y.1 ≠ y.2 := fun eq => ne (congrArg w eq)
  obtain ⟨u,hu⟩ := has_exclusive X hq small pos high cols v₂ v₁ yn.symm
  obtain ⟨v,hv⟩ := has_exclusive X hq small pos high cols v₁ v₂ yn
  let e := fun j => w j - w u
  have ae (i) (hi : i ∈ A) : padicNorm ell (e i) ≤ g := bound i hi u hu
  have be (j) (hj : j ∈ B) : padicNorm ell (e j) ≤ g := by
    have eq : e j = (w v - w u) - (w v - w j) := by dsimp [e]; ring
    rw [eq]
    exact padicNorm.sub.trans (max_le (bound v hv u hu) (bound v hv j hj))
  have cap : padicNorm ell (mass A e - mass B e) ≤ g :=
    padicNorm.sub.trans (max_le (padicNorm.sum_le' ae gp.le) (padicNorm.sum_le' be gp.le))
  have left := sum_sdiff (f := e) (inter_subset_left : S ∩ T ⊆ S)
  have right := sum_sdiff (f := e) (inter_subset_right : S ∩ T ⊆ T)
  rw [sdiff_inter_self_left] at left
  rw [sdiff_inter_self_right] at right
  have cancel : mass S e - mass T e = mass A e - mass B e := by
    dsimp [mass,A,B]; linarith only [left,right]
  have center (U : Finset ℕ) : mass U e = mass U w - (U.card : ℚ)*w u := by
    simp [mass,e,sum_sub_distrib]
  let total := mass S w - mass T w
  let d : ℚ := (S.card : ℚ) - T.card
  have close : padicNorm ell (total - d*w u) ≤ g := by
    rw [←cancel,center,center] at cap
    convert cap using 2
    dsimp [total,d]
    ring
  have r₁ := flat y.1 v₁
  have r₂ := flat y.2 v₂
  rw [WeightedSD.row,outW_eq_mass] at r₁ r₂
  have eq : gap w y = -(q : ℚ)*total := by
    dsimp [gap,total,S,T]; linear_combination r₁ - r₂
  have mult := congrArg (padicNorm ell) eq
  rw [padicNorm.mul,padicNorm.neg] at mult
  have tp : 0 < padicNorm ell total := by
    by_contra! npos
    have zero := le_antisymm npos (padicNorm.nonneg _)
    rw [zero,mul_zero] at mult
    exact gp.ne' mult
  have gt : g < padicNorm ell total := by
    dsimp [g]; rw [mult]
    simpa using mul_lt_mul_of_pos_right ((padicNorm.nat_lt_one_iff q).mpr dv) tp
  have same := dominant_difference (close.trans_lt gt)
  have un := flat_price_norm dv posw flat (mem_outN.mp (mem_sdiff.mp hu).1).1
  change padicNorm ell (gap w y) = padicNorm ell ((q : ℚ)*c*d)
  rw [mult,←same,padicNorm.mul,padicNorm.mul,padicNorm.mul,un]
  ring

/-- At the maximizing pair every maximal matching has the same large residual
norm, so changing which heads are retained never requires changing the pair. -/
theorem fixed_remainder {q ell : ℕ} [Fact ell.Prime] (dv : ell ∣ q) {D V w c}
    (flat : ∀ a ∈ V, WeightedSD.row q D V w a = c) {a b}
    (av : a ∈ V) (bv : b ∈ V) (diff : w a ≠ w b)
    (bound : ∀ i ∈ exclusive D V a b, ∀ j ∈ exclusive D V b a,
       padicNorm ell (w i-w j) ≤ padicNorm ell (gap w (a,b)))
    (m : Matching (exclusive D V a b) (exclusive D V b a)) :
    padicNorm ell (gap w (a,b)) = padicNorm ell ((q : ℚ)*remainder m w) := by
  classical
  let g := padicNorm ell (gap w (a,b))
  let s := ∑ i : ↥m.left, (w i - w (m.pair i))
  have gp : 0 < g := lt_of_le_of_ne (padicNorm.nonneg _) (Ne.symm (padicNorm.nonzero (sub_ne_zero.mpr diff)))
  have cap : padicNorm ell s ≤ g := padicNorm.sum_le'
    (fun i _ => bound _ (m.left_sub i.property) _ (m.right_sub (m.pair i).property)) gp.le
  have eq := congrArg (padicNorm ell) (matched_equation flat av bv m)
  rw [padicNorm.mul,padicNorm.neg] at eq
  change g = padicNorm ell (q : ℚ) * padicNorm ell (s + remainder m w) at eq
  have tp : 0 < padicNorm ell (s+remainder m w) := by
    by_contra! no
    rw [le_antisymm no (padicNorm.nonneg _),mul_zero] at eq
    exact gp.ne' eq
  have gt : g < padicNorm ell (s+remainder m w) := by
    rw [eq]; simpa using mul_lt_mul_of_pos_right ((padicNorm.nat_lt_one_iff q).mpr dv) tp
  have same := dominant_difference (a := s+remainder m w) (b := remainder m w)
    (by rw [add_sub_cancel_right]; exact cap.trans_lt gt)
  rw [padicNorm.mul,same]
  exact eq

/-- Two distinct columns fail simultaneously in one direction of this pair. -/
theorem two_failed_columns {q n} (X : Model q n) (hq : 2 ≤ q) (small : SmallerSmallRow q X.V.card)
    {π c} (pos : ∀ i ∈ X.V, 0 < π i) (high : mass X.V π < c)
    (cols : ∀ i ∈ X.V, WeightedSD.col q X.D X.V π i = c)
    {a b} (av : a ∈ X.V) (bv : b ∈ X.V) (deg : (outN X.D X.V a).card ≠ (outN X.D X.V b).card) :
    ∃ j k, j ≠ k ∧
      ((failsTransfer q X.D X.V π a b j ∧ failsTransfer q X.D X.V π a b k) ∨
       (failsTransfer q X.D X.V π b a j ∧ failsTransfer q X.D X.V π b a k)) := by
  classical
  have ne : a ≠ b := fun eq => deg (eq ▸ rfl)
  have count {u v : ℕ} (uv : u ∈ X.V) (vv : v ∈ X.V) (neq : u ≠ v)
      (gt : (outN X.D X.V v).card < (outN X.D X.V u).card) :
      ∃ j k, j ≠ k ∧ failsTransfer q X.D X.V π u v j ∧ failsTransfer q X.D X.V π u v k := by
    have hp := card_pos.mpr (has_exclusive X hq small pos high cols vv uv neq.symm)
    have h := card_sdiff_add_card_inter (outN X.D X.V u) (outN X.D X.V v)
    have t := card_sdiff_add_card_inter (outN X.D X.V v) (outN X.D X.V u)
    rw [inter_comm] at t
    have big : 1 < (exclusive X.D X.V u v).card := by unfold exclusive at hp ⊢; omega
    obtain ⟨j,hj,k,hk,jk⟩ := one_lt_card.mp big
    exact ⟨j,k,jk,(fails_iff_exclusive X hq small pos high cols uv vv neq).2 hj,
      (fails_iff_exclusive X hq small pos high cols uv vv neq).2 hk⟩
  rcases lt_or_gt_of_ne deg with lt | gt
  · obtain ⟨j,k,jk,fail⟩ := count bv av ne.symm lt
    exact ⟨j,k,jk,Or.inr fail⟩
  · obtain ⟨j,k,jk,fail⟩ := count av bv ne gt
    exact ⟨j,k,jk,Or.inl fail⟩

#print axioms flat_price_norm
#print axioms same_pair_signature
#print axioms fixed_remainder
#print axioms two_failed_columns

end LeanCH.BR.Closure.FeederPrivateHeadDescent
