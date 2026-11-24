import checkpoints.shen_extension.NativeReturnAccounts
import checkpoints.shen_extension.TwoParentReverseCharge
import checkpoints.shen_extension.TwoParentOldWeight

namespace LeanCH.BR.Closure.ReturnSponsorMass
open Finset BRq2 BRq3 BR45 WeightedSD LabelledLeakageCapacity TwoParentReturnPivot

/-- The native vertices distinct from p and nonadjacent to it in both directions. -/
def neutral (D : CH.Digraph) (V : Finset ℕ) (p : ℕ) : Finset ℕ :=
  (V.erase p).filter (fun h=>D p h=false ∧ D h p=false)

/-- In the absence of a retained common head, identify the exact part of
the native row that pays through old p-heads in the mandatory bank. -/
theorem partition {q E V b p t y} (hq : 3≤q) (free : QFree E V q)
    (pv : p∈V) (tv : t∈V) (pt : E p t=true) (noB : E t b≠true)
    (none : ¬∃h∈outN E (V.erase b) p,h∈outN E (V.erase b) t \ bank q E (V.erase b) t y) :
    let I := outN E V t∩neutral E V p
    let S := (bank q E (V.erase b) t y).filter (fun h=>E p h=true)
    outN E V t=I∪S ∧ Disjoint I S := by
  intro I S
  constructor
  · ext h
    constructor
    · intro hh
      obtain ⟨hv,th⟩ := mem_outN.mp hh
      have hu : h∈V.erase b := mem_erase.mpr ⟨fun eq=>noB (eq ▸ th),hv⟩
      by_cases ph : E p h=true
      · have ht : h∈outN E (V.erase b) t := mem_outN.mpr ⟨hu,th⟩
        have hp : h∈outN E (V.erase b) p := mem_outN.mpr ⟨hu,ph⟩
        have cut : h∈bank q E (V.erase b) t y := by
          by_contra outside
          exact none ⟨h,hp,mem_sdiff.mpr ⟨ht,outside⟩⟩
        exact mem_union_right _ (mem_filter.mpr ⟨cut,ph⟩)
      · have ne : h≠p := fun eq=>digonfree free (by omega) pv tv pt (eq ▸ th)
        have no : E h p≠true := fun hp=>free p 3 (by omega) hq (.step tv pt (.step hv th (.step pv hp (.refl _))))
        exact mem_union_left _ (mem_inter.mpr ⟨hh,mem_filter.mpr ⟨mem_erase.mpr ⟨ne,hv⟩,
          Bool.eq_false_iff.mpr ph,Bool.eq_false_iff.mpr no⟩⟩)
    · intro hs
      rcases mem_union.mp hs with hi|hb
      · exact (mem_inter.mp hi).1
      · obtain ⟨hit,_⟩ := mem_filter.mp (mem_filter.mp hb).1
        obtain ⟨hu,th⟩ := mem_outN.mp hit
        exact mem_outN.mpr ⟨mem_of_mem_erase hu,th⟩
  · refine disjoint_left.mpr (fun h hi hs=>?_ )
    have miss := (mem_filter.mp (mem_inter.mp hi).2).2.1
    have hit := (mem_filter.mp hs).2
    exact Bool.noConfusion (miss.symm.trans hit)

/-- The alternatives apply to one named native return. A strict row
shortfall above the whole non-neighbour pool forces sponsored mass. -/
theorem alternatives {q E V b p t y w c} (hq : 3≤q) (free : QFree E V q)
    (pv : p∈V) (tv : t∈V) (pt : E p t=true) (noB : E t b≠true)
    (wn : ∀i∈V,0≤w i) (row : WeightedSD.row q E V w t=c) :
    let U := V.erase b
    let B := bank q E U t y
    let S := B.filter (fun h=>E p h=true)
    (∃h∈outN E U p,h∈outN E U t \ B) ∨
      (c=w t+(q:ℚ)*(mass (outN E V t∩neutral E V p) w+mass S w) ∧
       c-w t-(q:ℚ)*mass (neutral E V p) w≤(q:ℚ)*mass S w) := by
  classical
  intro U B S
  by_cases kept : ∃h∈outN E U p,h∈outN E U t \ B
  · exact Or.inl kept
  right
  obtain ⟨cover,dis⟩ := partition hq free pv tv pt noB kept
  rw [WeightedSD.row,outW_eq_mass,cover,mass,Finset.sum_union dis] at row
  have eq : c=w t+(q:ℚ)*(mass (outN E V t∩neutral E V p) w+mass S w) := row.symm
  have bound := sum_le_sum_of_subset_of_nonneg (f:=w)
    (inter_subset_right : outN E V t∩neutral E V p ⊆ neutral E V p)
    (fun h hh _=>wn h (mem_of_mem_erase (mem_filter.mp hh).1))
  refine ⟨eq,?_⟩
  change mass (outN E V t∩neutral E V p) w≤mass (neutral E V p) w at bound
  linarith only [eq,mul_le_mul_of_nonneg_left bound (Nat.cast_nonneg q : (0:ℚ)≤q)]

/-- Either the old-weight withdrawal applies at a named head, or the cost
forced by the missing common head is charged to the very same return bank. -/
theorem native {q n b p y t w c π} (X : ShortestCycleWeights.Model q n) (hq : 3≤q)
    (small : SmallerSmallRow q X.V.card) (bv : b∈X.V) (parents : inN X.D X.V b={p,y})
    (backs : ∀i∈inN X.D X.V b,∃j∈region q X.D X.V b,X.D i j=true)
    (tr : t∈region q X.D X.V b) (pt : X.D p t=true)
    (wp : ∀i∈X.V,0<w i) (wm : mass X.V w=1) (high : mass X.V w<c)
    (rows : ∀i∈X.V,WeightedSD.row q X.D X.V w i=c)
    (diffuse : ∀i∈X.V,(q:ℚ)^2*w i≤1)
    (pp : ∀i∈X.V,0<π i) (cols : ∀h∈X.V,WeightedSD.col q X.D X.V π h=c) :
    let U := X.V.erase b
    let B := bank q X.D U t y
    let neutralMass := mass (neutral X.D X.V p) w
    let base := w b+q*(c-mass X.V w)
    (∃h∈outN X.D U p,h∈outN X.D U t \ B ∧
      base+((q:ℚ)-1)*min (w b) (w t)<q*mass B w) ∨
    ((c-w t-q*neutralMass≤q*mass (B.filter (fun h=>X.D p h=true)) w) ∧
      base*π t+π p*max 0 (c-w t-q*neutralMass)<∑h∈B,w h*(c-π h)) := by
  intro U B neutralMass base
  have two : 2≤q := by omega
  have pv : p∈X.V := (mem_inN.mp (parents ▸ mem_insert_self p ({y}:Finset ℕ))).1
  have tv : t∈X.V := BRsub.ballSet_subset tr
  have tb := ((saturated_region two X.free X.sat bv tv).mp tr).2
  rcases alternatives hq X.free pv tv pt tb (fun i iv=>(wp i iv).le) (rows t tv) with hit|⟨_,lower⟩
  · obtain ⟨h,hp,ht⟩ := hit
    exact Or.inl ⟨h,hp,ht,TwoParentOldWeight.native_withdrawal X two small bv parents tr pt wp high rows ht (mem_outN.mp hp).2⟩
  right
  have sub : ({t}:Finset ℕ)⊆outN X.D (region q X.D X.V b) p :=
    singleton_subset_iff.mpr (mem_outN.mpr ⟨tr,pt⟩)
  have cost := TwoParentReverseCharge.native_sponsor X two small bv parents backs wp wm high rows diffuse pp cols sub (singleton_nonempty t)
  let Z := B.filter (fun h=>X.D p h=true)
  have spec : base*π t+(q:ℚ)*π p*mass Z w<∑h∈B,w h*(c-π h) := by simpa [mass,base,B,U,Z] using cost
  have nonneg : 0≤mass Z w := sum_nonneg (fun h hz=>(wp h
    (mem_of_mem_erase (outN_subset (mem_filter.mp (mem_filter.mp hz).1).1))).le)
  have bound : max 0 (c-w t-q*neutralMass)≤(q:ℚ)*mass Z w :=
    max_le (mul_nonneg (Nat.cast_nonneg _) nonneg) lower
  refine ⟨lower,?_⟩
  linarith only [spec,mul_le_mul_of_nonneg_left bound (pp p pv).le]

#print axioms native

#print axioms partition
#print axioms alternatives
end LeanCH.BR.Closure.ReturnSponsorMass
