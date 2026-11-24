import checkpoints.shen_extension.TwoParentReturnCapacity

namespace LeanCH.BR.Closure.TwoParentReverseCharge
open Finset BRq2 BRq3 BR45 WeightedSD LabelledLeakageCapacity TwoParentReturnPivot TwoParentReturnCapacity

/-- Each outgoing column of b retains the full contribution of its
other native parents. The equality needs only the two named columns. -/
theorem head_identity {q : ℕ} {E V b p y j} (bv : b∈V) (parents : inN E V b={p,y})
    (ne : p≠y) (bj : E b j=true) {π : ℕ→ℚ} {d : ℚ}
    (atB : WeightedSD.col q E V π b=d) (atJ : WeightedSD.col q E V π j=d) :
    (q:ℚ)^2*(π p+π y)=((q:ℚ)-1)*d+π j+q*mass ((inN E V j).erase b) π := by
  have root : π b+(q:ℚ)*(π p+π y)=d := by
    have col : π b+(q:ℚ)*mass (inN E V b) π=d := by
      simpa only [WeightedSD.col,inW,inN,mass,sum_filter] using atB
    simpa only [parents,mass,sum_pair ne] using col
  have col : π j+(q:ℚ)*mass (inN E V j) π=d := by
    simpa only [WeightedSD.col,inW,inN,mass,sum_filter] using atJ
  have split : mass ((inN E V j).erase b) π+π b=mass (inN E V j) π := sum_erase_add _ _ (mem_inN.mpr ⟨bv,bj⟩)
  linear_combination (q:ℚ)*root - col - (q:ℚ)*split

/-- With a live outgoing head at b, a parent itself carries a heavy
reverse price. The same parent works for every outgoing head of b. -/
theorem heavy_parent {q E V b p y π d} (hq : 3≤q) (bv : b∈V)
    (parents : inN E V b={p,y}) (ne : p≠y) (heads : (outN E V b).Nonempty)
    (pp : ∀i∈V,0<π i) (high : 1<d) (cols : ∀h∈V,WeightedSD.col q E V π h=d) :
    ∃i∈({p,y}:Finset ℕ), (∀j∈outN E V b,((q:ℚ)-1)*d+π j≤2*(q:ℚ)^2*π i) ∧
      d<(q:ℚ)^2*π i ∧ 1<(q:ℚ)^2*π i := by
  have col (j) (jv : j∈V) : π j+(q:ℚ)*mass (inN E V j) π=d := by
    simpa only [WeightedSD.col,inW,inN,mass,sum_filter] using cols j jv
  have eq := col b bv
  rw [parents,mass,sum_pair ne] at eq
  obtain ⟨i,iv,top⟩ := ({p,y}:Finset ℕ).exists_max_image π (insert_nonempty _ _)
  have hp := top p (mem_insert_self _ _)
  have hy := top y (mem_insert_of_mem (mem_singleton_self _))
  have qn : 0≤(q:ℚ) := Nat.cast_nonneg _
  have atHead (j) (jh : j∈outN E V b) : ((q:ℚ)-1)*d+π j≤2*(q:ℚ)^2*π i := by
    have inc : b∈inN E V j := mem_inN.mpr ⟨bv,(mem_outN.mp jh).2⟩
    have one : π b≤mass (inN E V j) π := single_le_sum (fun k hk=>(pp k (mem_inN.mp hk).1).le) inc
    have maxPair := add_le_add hp hy
    nlinarith only [col j (outN_subset jh),mul_le_mul_of_nonneg_left one qn,
      congrArg (fun z : ℚ=>(q:ℚ)*z) eq,mul_le_mul_of_nonneg_left maxPair (sq_nonneg (q:ℚ))]
  obtain ⟨j,jh⟩ := heads
  have three : (3:ℚ)≤q := by exact_mod_cast hq
  have hi : d<(q:ℚ)^2*π i := by
    nlinarith only [atHead j jh,pp j (outN_subset jh),mul_le_mul_of_nonneg_right three (by linarith only [high] : 0≤d)]
  exact ⟨i,iv,atHead,hi,high.trans hi⟩

/-- If a parent a lies outside the chosen return set, each of its old
arcs to a cut head reduces the reverse capacity available to the returns. -/
theorem charge {q : ℕ} {E V T K a} (sub : K⊆V) (av : a∈V) (off : a∉T)
    (w π : ℕ→ℚ) (wn : ∀h∈V,0≤w h) (pn : ∀i∈V,0≤π i) {d lhs : ℚ}
    (low : lhs<∑h∈K,w h*(d-π h-(q:ℚ)*mass (inN E V h \ T) π)) :
    lhs+q*π a*mass (K.filter (fun h=>E a h=true)) w<∑h∈K,w h*(d-π h) := by
  apply (add_lt_add_left low _).trans_le
  rw [show mass (K.filter (fun h=>E a h=true)) w=∑h∈K,if E a h=true then w h else 0 from sum_filter _ _,
    mul_sum,←sum_add_distrib]
  apply sum_le_sum
  intro h hk
  have nn (i) (hi : i∈inN E V h \ T) : 0≤π i := pn i (mem_inN.mp (mem_sdiff.mp hi).1).1
  have factor := mul_nonneg (Nat.cast_nonneg q : (0:ℚ)≤q) (wn h (sub hk))
  by_cases ah : E a h=true
  · have member : a∈inN E V h \ T := mem_sdiff.mpr ⟨mem_inN.mpr ⟨av,ah⟩,off⟩
    have enough : π a≤mass (inN E V h \ T) π := single_le_sum nn member
    rw [ite_eq_left ah]
    nlinarith only [mul_le_mul_of_nonneg_left enough factor]
  · rw [ite_eq_right ah,mul_zero,add_zero]
    have enough := mass_nonneg nn
    nlinarith only [mul_nonneg factor enough]

/-- Instantiate the subtraction at the sponsoring parent of actual
returns, using native columns of π on the same graph as the banks. -/
theorem native_sponsor {q n b p y w c π d} (X : ShortestCycleWeights.Model q n) (hq : 2≤q)
    (small : SmallerSmallRow q X.V.card) (bv : b∈X.V) (parents : inN X.D X.V b={p,y})
    (backs : ∀i∈inN X.D X.V b,∃j∈region q X.D X.V b,X.D i j=true)
    (wp : ∀i∈X.V,0<w i) (wm : mass X.V w=1) (high : mass X.V w<c)
    (rows : ∀i∈X.V,WeightedSD.row q X.D X.V w i=c)
    (diffuse : ∀i∈X.V,(q:ℚ)^2*w i≤1)
    (pp : ∀i∈X.V,0<π i) (cols : ∀h∈X.V,WeightedSD.col q X.D X.V π h=d)
    {T : Finset ℕ} (within : T⊆outN X.D (region q X.D X.V b) p) (live : T.Nonempty) :
    let K := T.biUnion (fun t=>bank q X.D (X.V.erase b) t y)
    (w b+q*(c-mass X.V w))*mass T π+q*π p*mass (K.filter (fun h=>X.D p h=true)) w <
      ∑h∈K,w h*(d-π h) := by
  intro K
  have par : p∈inN X.D X.V b := parents ▸ mem_insert_self _ _
  have pv := (mem_inN.mp par).1
  have sub : K⊆X.V := by
    intro h hk; obtain ⟨_,_,hb⟩ := mem_biUnion.mp hk
    exact mem_of_mem_erase (outN_subset (mem_filter.mp hb).1)
  have off : p∉T := fun ht=>loopfree X.free (by omega) pv (mem_outN.mp (within ht)).2
  exact charge sub pv off w π (fun i iv=>(wp i iv).le) (fun i iv=>(pp i iv).le)
    (native_return_gap X hq small bv parents backs wp wm high rows diffuse pp cols within live)

#print axioms heavy_parent
#print axioms head_identity
#print axioms charge
#print axioms native_sponsor
end LeanCH.BR.Closure.TwoParentReverseCharge
