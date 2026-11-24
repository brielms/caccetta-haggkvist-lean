import checkpoints.shen_extension.TwoParentOpposedBanks

namespace LeanCH.BR.Closure.TwoParentReturnCapacity
open Finset BRq2 BRq3 BR45 WeightedSD LabelledLeakageCapacity
open TwoParentReturnPivot TwoParentOpposedBanks

/-- Passing through the deleted b rules out every original head of b.
The only possible cut head outside the inner region is the opposite parent. -/
theorem location {q E V b p y t} (hq : 2≤q) (free : QFree E V q) (sat : BRsub.Sat q E V)
    (bv : b∈V) (parents : inN E V b={p,y}) (tv : t∈V) (pt : E p t=true) :
    let B := bank q E (V.erase b) t y
    Disjoint B (outN E V b) ∧ B⊆insert y (region q E V b \ outN E V b) := by
  intro B
  have yp : y∈inN E V b := parents ▸ mem_insert_of_mem (mem_singleton_self _)
  have avoids (h) (hb : h∈B) : h∉outN E V b := by
    intro hh
    obtain ⟨_,k,le,path⟩ := mem_ball.mp (mem_filter.mp hb).2
    exact free y _ (by omega) (by omega)
      (.step bv (mem_inN.mp yp).2 (.step (outN_subset hh) (mem_outN.mp hh).2 (path.mono (erase_subset b V))))
  refine ⟨disjoint_left.mpr (fun h hb=>avoids h hb),?_⟩
  intro h hb
  by_cases hy : h=y
  · exact mem_insert.mpr (Or.inl hy)
  obtain ⟨hu,th⟩ := mem_outN.mp (mem_filter.mp hb).1
  obtain ⟨ne,hv⟩ := mem_erase.mp hu
  have hp : h≠p := fun eq=>digonfree free hq (eq ▸ hv) tv pt (eq ▸ th)
  have no : E h b≠true := fun hit=>by
    have par : h∈({p,y}:Finset ℕ) := parents ▸ mem_inN.mpr ⟨hv,hit⟩
    simp [hp,hy] at par
  exact mem_insert_of_mem (mem_sdiff.mpr ⟨(saturated_region hq free sat bv hv).mpr ⟨ne,no⟩,avoids h hb⟩)

/-- With cutoff at least four, *one whole family* of return banks has
no exceptional opposite parent. The choice of side precedes the return. -/
theorem one_inner_side {q E V b p y} (hq : 4≤q) (free : QFree E V q) (sat : BRsub.Sat q E V)
    (bv : b∈V) (parents : inN E V b={p,y}) :
    let R := region q E V b \ outN E V b
    (∀t∈outN E V p,bank q E (V.erase b) t y⊆R) ∨
    (∀u∈outN E V y,bank q E (V.erase b) u p⊆R) := by
  intro R
  have pp : p∈inN E V b := parents ▸ mem_insert_self _ _
  have yp : y∈inN E V b := parents ▸ mem_insert_of_mem (mem_singleton_self _)
  have strip {B : Finset ℕ} {j} (sub : B⊆insert j R) (off : j∉B) : B⊆R :=
    fun h hb=>(mem_insert.mp (sub hb)).resolve_left (fun eq=>off (eq ▸ hb))
  by_cases cross : ∃t∈outN E V p,y∈bank q E (V.erase b) t y
  · obtain ⟨t,th,ty⟩ := cross
    right; intro u uh
    apply strip (location (by omega) free sat bv (parents.trans (pair_comm p y)) (outN_subset uh) (mem_outN.mp uh).2).2
    intro up
    exact free p 4 (by omega) hq
      (.step (outN_subset th) (mem_outN.mp th).2
        (.step (mem_inN.mp yp).1 (mem_outN.mp (mem_filter.mp ty).1).2
          (.step (outN_subset uh) (mem_outN.mp uh).2
            (.step (mem_inN.mp pp).1 (mem_outN.mp (mem_filter.mp up).1).2 (.refl _)))))
  · left; intro t th
    exact strip (location (by omega) free sat bv parents (outN_subset th) (mem_outN.mp th).2).2
      (fun hit=>cross ⟨t,th,hit⟩)

/-- Sum over the actual returns, including repeated use of a head. The
native reverse column law caps the total charge at that head. -/
theorem priced_overlap {q E V U T y} (subU : U⊆V) (subT : T⊆V)
    (w π : ℕ→ℚ) (wn : ∀h∈V,0≤w h) (pn : ∀i∈V,0≤π i) {d : ℚ}
    (cols : ∀h∈V,WeightedSD.col q E V π h=d) :
    let K := T.biUnion (fun t=>bank q E U t y)
    (∑t∈T,(q:ℚ)*π t*mass (bank q E U t y) w)=
        ∑h∈K,(q:ℚ)*w h*mass (T.filter (fun t=>h∈bank q E U t y)) π ∧
    (∑t∈T,(q:ℚ)*π t*mass (bank q E U t y) w)≤∑h∈K,w h*(d-π h) := by
  classical
  intro K
  have subsetK (t) (ht : t∈T) : bank q E U t y⊆K := fun h hb=>mem_biUnion.mpr ⟨t,ht,hb⟩
  have expand (t) (ht : t∈T) : (q:ℚ)*π t*mass (bank q E U t y) w=
      ∑h∈K,if h∈bank q E U t y then (q:ℚ)*w h*π t else 0 := by
    rw [←sum_filter,filter_mem_eq_inter,inter_eq_right.mpr (subsetK t ht)]
    simp only [mass,mul_sum]; apply sum_congr rfl; intros; ring
  have eq : (∑t∈T,(q:ℚ)*π t*mass (bank q E U t y) w)=
        ∑h∈K,(q:ℚ)*w h*mass (T.filter (fun t=>h∈bank q E U t y)) π := by
    rw [sum_congr rfl expand,sum_comm]
    simp only [mass,sum_filter,mul_sum,mul_ite,mul_zero]
  refine ⟨eq,eq.trans_le (sum_le_sum (fun h hk=>?_))⟩
  have hv : h∈V := by
    obtain ⟨t,_,hb⟩ := mem_biUnion.mp hk
    exact subU (outN_subset (mem_filter.mp hb).1)
  have subs : T.filter (fun t=>h∈bank q E U t y)⊆inN E V h := by
    intro t ti
    obtain ⟨tt,hb⟩ := mem_filter.mp ti
    exact mem_inN.mpr ⟨subT tt,(mem_outN.mp (mem_filter.mp hb).1).2⟩
  have bound := mass_mono subs (fun t th=>pn t (mem_inN.mp th).1)
  have law : π h+(q:ℚ)*mass (inN E V h) π=d := by
    simpa only [WeightedSD.col,inW,inN,mass,sum_filter] using cols h hv
  have per := mul_le_mul_of_nonneg_left bound (Nat.cast_nonneg q : (0:ℚ)≤q)
  have per' : (q:ℚ)*mass (T.filter (fun t=>h∈bank q E U t y)) π≤d-π h := by linarith only [law,per]
  linarith only [mul_le_mul_of_nonneg_left per' (wn h hv)]

/-- A strict common lower bill and positive return prices force the
corresponding strict lower bound on this same union's reverse capacity. -/
theorem all_returns {q E V U T y} (subU : U⊆V) (subT : T⊆V) (live : T.Nonempty)
    (w π : ℕ→ℚ) (wn : ∀h∈V,0≤w h) (pos : ∀i∈V,0<π i) {d L : ℚ}
    (cols : ∀h∈V,WeightedSD.col q E V π h=d)
    (lower : ∀t∈T,L<(q:ℚ)*mass (bank q E U t y) w) :
    L*mass T π<∑h∈T.biUnion (fun t=>bank q E U t y),w h*(d-π h) := by
  have step : L*mass T π<(∑t∈T,(q:ℚ)*π t*mass (bank q E U t y) w) := by
    rw [mass,mul_sum]
    apply sum_lt_sum_of_nonempty live
    intro t ht
    linarith only [mul_lt_mul_of_pos_right (lower t ht) (pos t (subT ht))]
  exact step.trans_le (priced_overlap subU subT w π wn (fun i iv=>(pos i iv).le) cols).2

/-- At a head in the union, membership in a bank depends on its parent
only through the single arc t→h. This gives the exact unused column mass. -/
theorem unused_capacity {q E V U T y} (subU : U⊆V) (subT : T⊆V)
    (w π : ℕ→ℚ) (wn : ∀h∈V,0≤w h) (pn : ∀i∈V,0≤π i) {d : ℚ}
    (cols : ∀h∈V,WeightedSD.col q E V π h=d) :
    let K := T.biUnion (fun t=>bank q E U t y)
    (∑t∈T,(q:ℚ)*π t*mass (bank q E U t y) w)=
      ∑h∈K,w h*(d-π h-q*mass (inN E V h \ T) π) := by
  intro K
  rw [(priced_overlap subU subT w π wn pn cols).1]
  apply sum_congr rfl
  intro h hk
  obtain ⟨_,_,hb⟩ := mem_biUnion.mp hk
  obtain ⟨oh,ret⟩ := mem_filter.mp hb
  have hu : h∈U := outN_subset oh
  have owners : T.filter (fun t=>h∈bank q E U t y)=inN E V h∩T := by
    ext t
    simp only [bank,mem_filter,mem_outN,mem_inter,mem_inN,hu,ret,true_and,and_true]
    exact ⟨fun ⟨ht,e⟩=>⟨⟨subT ht,e⟩,ht⟩,fun ⟨⟨_,e⟩,ht⟩=>⟨ht,e⟩⟩
  have split : mass (inN E V h \ T) π+mass (inN E V h∩T) π=mass (inN E V h) π := by
    simp only [mass,←sum_union (disjoint_left.mpr (fun i hi hj=>(mem_sdiff.mp hi).2 (mem_inter.mp hj).2))]
    rw [sdiff_union_inter]
  have law : π h+(q:ℚ)*mass (inN E V h) π=d := by
    simpa only [WeightedSD.col,inW,inN,mass,sum_filter] using cols h (subU hu)
  rw [owners]
  linear_combination w h * law + (q:ℚ)*w h*split

/-- A common retained head exists precisely when the selected returns
send an arc into an old p-head outside the union of all mandatory cuts. -/
theorem common_head_iff {q E U p y} {T : Finset ℕ} :
    (∃t∈T,∃h∈outN E U p,h∈outN E U t \ bank q E U t y) ↔
    ∃h∈outN E U p \ T.biUnion (fun t=>bank q E U t y),∃t∈T,E t h=true := by
  constructor
  · rintro ⟨t,tt,h,hp,ht⟩
    obtain ⟨head,kept⟩ := mem_sdiff.mp ht
    have far : y∉ball E U h (q-2) := fun close=>kept (mem_filter.mpr ⟨head,close⟩)
    refine ⟨h,mem_sdiff.mpr ⟨hp,?_⟩,t,tt,(mem_outN.mp head).2⟩
    rintro inCut
    obtain ⟨_,_,hb⟩ := mem_biUnion.mp inCut
    exact far (mem_filter.mp hb).2
  · rintro ⟨h,good,t,tt,th⟩
    obtain ⟨hp,uncut⟩ := mem_sdiff.mp good
    exact ⟨t,tt,h,hp,mem_sdiff.mpr ⟨mem_outN.mpr ⟨outN_subset hp,th⟩,
      fun hb=>uncut (mem_biUnion.mpr ⟨t,tt,hb⟩)⟩⟩

#print axioms location
#print axioms one_inner_side
#print axioms priced_overlap
#print axioms all_returns
#print axioms unused_capacity
#print axioms common_head_iff

/-- On the native model every nonempty selection of actual returns
has this strict lower bound against its *net* reverse column capacity. -/
theorem native_return_gap {q n b p y w c π d} (X : ShortestCycleWeights.Model q n) (hq : 2≤q)
    (small : SmallerSmallRow q X.V.card) (bv : b∈X.V) (parents : inN X.D X.V b={p,y})
    (backs : ∀i∈inN X.D X.V b,∃j∈region q X.D X.V b,X.D i j=true)
    (wp : ∀i∈X.V,0<w i) (wm : mass X.V w=1) (high : mass X.V w<c)
    (rows : ∀i∈X.V,WeightedSD.row q X.D X.V w i=c)
    (diffuse : ∀i∈X.V,(q:ℚ)^2*w i≤1)
    (pp : ∀i∈X.V,0<π i) (cols : ∀h∈X.V,WeightedSD.col q X.D X.V π h=d)
    {T : Finset ℕ} (within : T⊆outN X.D (region q X.D X.V b) p) (live : T.Nonempty) :
    let K := T.biUnion (fun t=>bank q X.D (X.V.erase b) t y)
    (w b+q*(c-mass X.V w))*mass T π <
      ∑h∈K,w h*(d-π h-q*mass (inN X.D X.V h \ T) π) := by
  intro K
  have sub : T⊆X.V := fun t ht=>BRsub.ballSet_subset (outN_subset (within ht))
  rw [←unused_capacity (erase_subset b X.V) sub w π (fun i iv=>(wp i iv).le)
    (fun i iv=>(pp i iv).le) cols (y:=y)]
  rw [show mass T π=∑t∈T,π t from rfl,mul_sum]
  apply sum_lt_sum_of_nonempty live
  intro t ht
  obtain ⟨tr,pt⟩ := mem_outN.mp (within ht)
  have low := diffuse_bill X hq small bv parents backs tr pt wp wm high rows diffuse
  linarith only [mul_lt_mul_of_pos_right low (pp t (sub ht))]

#print axioms native_return_gap
end LeanCH.BR.Closure.TwoParentReturnCapacity
