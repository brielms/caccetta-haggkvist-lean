import checkpoints.shen_extension.TwoParentReturnPivot
import checkpoints.shen_extension.SingletonSecondNeighbors

namespace LeanCH.BR.Closure.TwoParentOpposedBanks
open Finset BRq2 BRq3 BR45 WeightedSD LabelledLeakageCapacity TwoParentReturnPivot

/-- The cut heads are reached in exactly two steps from p. None is
reachable from y by one or two steps, including when the head itself is y. -/
theorem private_two_step {q E U p t y h} (hq : 2≤q) (free : QFree E U q)
    (tu : t∈U) (pt : E p t=true) (hb : h∈bank q E U t y) :
    Walk E U p h 2 ∧ (∀k,1≤k → k≤2 → ¬Walk E U y h k) := by
  obtain ⟨hh,ret⟩ := mem_filter.mp hb
  obtain ⟨hu,th⟩ := mem_outN.mp hh
  refine ⟨.step tu pt (.step hu th (.refl _)),?_⟩
  obtain ⟨_,l,le,back⟩ := mem_ball.mp ret
  intro k kp kb path
  exact free y _ (by omega) (by omega) (path.append back)

/-- For the attachment's positive two-step relation, the only alternative
to a direct old head of p is a nonadjacent distance-two ordered pair. -/
theorem old_arc_or_P2 {q E U p t y h} (hq : 3≤q) (free : QFree E U q)
    (pu : p∈U) (tu : t∈U) (pt : E p t=true) (hb : h∈bank q E U t y) :
    let hv := outN_subset (mem_filter.mp hb).1
    E p h=true ∨ BalancedSecondNeighborhood.isP2 (SingletonSecondNeighbors.adj E U) ⟨p,pu⟩ ⟨h,hv⟩ := by
  intro hv
  by_cases hit : E p h=true
  · exact Or.inl hit
  right
  have th := (mem_outN.mp (mem_filter.mp hb).1).2
  have path := (private_two_step (by omega : 2≤q) free tu pt hb).1
  have ne : p≠h := fun eq=>free h 2 (by omega) (by omega) (eq ▸ path)
  have no : E h p≠true := fun hp=>free p 3 (by omega) hq (path.snoc pu hp)
  exact ⟨fun eq=>ne (congrArg Subtype.val eq.symm),hit,no,⟨t,tu⟩,pt,th⟩

theorem disjoint_banks {q E U p y t u} (hq : 2≤q) (free : QFree E U q)
    (tu : t∈U) (pt : E p t=true) :
    Disjoint (bank q E U t y) (bank q E U u p) := by
  apply disjoint_left.mpr
  intro h ht hu
  have path := (private_two_step hq free tu pt ht).1
  obtain ⟨_,l,le,back⟩ := mem_ball.mp (mem_filter.mp hu).2
  exact free p _ (by omega) (by omega) (path.append back)

/-- In the diffuse branch the strict bill holds even if every head was
cut. In that case q w(B)=c-w(t) and the two coordinate caps suffice. -/
theorem diffuse_bill {q n b p y t w c} (X : ShortestCycleWeights.Model q n) (hq : 2≤q)
    (small : SmallerSmallRow q X.V.card) (bv : b∈X.V) (parents : inN X.D X.V b={p,y})
    (backs : ∀i∈inN X.D X.V b,∃u∈region q X.D X.V b,X.D i u=true)
    (tr : t∈region q X.D X.V b) (pt : X.D p t=true)
    (wp : ∀i∈X.V,0<w i) (wm : mass X.V w=1) (high : mass X.V w<c)
    (rows : ∀i∈X.V,WeightedSD.row q X.D X.V w i=c)
    (diffuse : ∀i∈X.V,(q:ℚ)^2*w i≤1) :
    w b+q*(c-mass X.V w)<q*mass (bank q X.D (X.V.erase b) t y) w := by
  obtain ⟨_,_,_,_,_,_,low|⟨_,exactCost⟩⟩ := native X hq small bv parents tr pt wp high rows
  · exact low
  rw [exactCost]
  have slack := (ParentReturnDeposit.two_parents X hq small bv parents backs tr pt wp high rows).1
  have tv : t∈X.V := BRsub.ballSet_subset tr
  have two : (2:ℚ)≤q := by exact_mod_cast hq
  have q0 : (0:ℚ)≤q := Nat.cast_nonneg _
  have den : (q:ℚ)+1<(q:ℚ)^2 := by nlinarith only [two,sq_nonneg ((q:ℚ)-2)]
  have caps : w t+(q:ℚ)*w b<1 := by
    by_contra! large
    nlinarith only [mul_le_mul_of_nonneg_left large (sq_nonneg (q:ℚ)),diffuse t tv,
      mul_le_mul_of_nonneg_left (diffuse b bv) q0,den]
  rw [wm] at slack ⊢
  nlinarith only [caps,mul_lt_mul_of_pos_left slack (show 0<(q:ℚ)-1 by linarith)]

/-- Both opposing return banks carry the strict bill on the same
puncture. Their union spends two disjoint sets of original weights. -/
theorem paired {q n b p y t u w c} (X : ShortestCycleWeights.Model q n) (hq : 2≤q)
    (small : SmallerSmallRow q X.V.card) (bv : b∈X.V) (parents : inN X.D X.V b={p,y})
    (backs : ∀i∈inN X.D X.V b,∃j∈region q X.D X.V b,X.D i j=true)
    (tr : t∈region q X.D X.V b) (pt : X.D p t=true)
    (ur : u∈region q X.D X.V b) (yu : X.D y u=true)
    (wp : ∀i∈X.V,0<w i) (wm : mass X.V w=1) (high : mass X.V w<c)
    (rows : ∀i∈X.V,WeightedSD.row q X.D X.V w i=c)
    (diffuse : ∀i∈X.V,(q:ℚ)^2*w i≤1) :
    let U := X.V.erase b
    let B := bank q X.D U t y
    let K := bank q X.D U u p
    Disjoint B K ∧ 2*(w b+q*(c-mass X.V w))<q*mass (B∪K) w := by
  intro U B K
  have tv := BRsub.ballSet_subset tr
  have tu : t∈U := mem_erase.mpr ⟨((saturated_region hq X.free X.sat bv tv).mp tr).1,tv⟩
  have dis : Disjoint B K := disjoint_banks hq (X.free.mono_set (erase_subset b X.V)) tu pt
  have lo := diffuse_bill X hq small bv parents backs tr pt wp wm high rows diffuse
  have rev := diffuse_bill X hq small bv (parents.trans (pair_comm p y)) backs ur yu wp wm high rows diffuse
  have union : mass (B∪K) w=mass B w+mass K w := sum_union dis
  refine ⟨dis,?_⟩
  rw [union]
  change _<(q:ℚ)*mass B w at lo
  change _<(q:ℚ)*mass K w at rev
  linarith only [lo,rev]

#print axioms private_two_step
#print axioms old_arc_or_P2
#print axioms disjoint_banks
#print axioms diffuse_bill
#print axioms paired
end LeanCH.BR.Closure.TwoParentOpposedBanks
