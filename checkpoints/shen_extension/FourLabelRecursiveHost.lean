import checkpoints.shen_extension.TwoReplacementNearMiss
import checkpoints.shen_extension.RecursiveHeadTransition

namespace LeanCH.BR.Closure.FourLabelHost
open Finset BRq2 BRq3 DeficitLevels TwoReplacement.NearMiss ClosedHeadIntersection

/-- The conclusion attached to each actual four-label deletion in the capstone. -/
def Child (D : CH.Digraph) (U S : Finset ℕ) (d : ℕ) : Prop :=
  let R := doubleRows D U S
  R.Nonempty ∧ 3*R.card+5 ≤ 4*d ∧ 9 ≤ d ∧ ∀ T ⊆ R, T.Nonempty →
    (∀ x ∈ T, outN D R x ⊆ T) →
    (∀ x ∈ T, 3 ≤ (outN D T x).card) ∧ 10 ≤ T.card ∧ RecursiveHeads.FromHost D T

/-- Every nonempty subset closed under double-loss successors contains a
triangle-free host of internal minimum degree three on its own carrier. -/
theorem native_host {D : CH.Digraph} {U S : Finset ℕ} {d : ℕ}
    (laws : ∀ k<d+1, OrderLaw 3 k (3*k+1)) (size : U.card=3*d+2) (sub : S ⊆ U)
    (four : S.card=4) (safe : QFree D (U \ S) 3) (hd : 2 ≤ d)
    (exactRows : ∀ x ∈ U \ S, (outN D U x).card=d+1)
    (two : ∀ x ∈ U \ S, (outN D S x).card ≤ 2)
    (near : (commonBank D (U \ S) (doubleRows D U S) ∅ d).card+1=d) :
    Child D U S d := by
  unfold Child
  intro R
  have law := laws d (by omega)
  let W := U \ S
  let B := commonBank D W R ∅ d
  have rw' : R ⊆ W := filter_subset _ _
  have wsize : W.card+4=3*d+2 := by
    have h := card_sdiff_add_card_eq_card sub
    dsimp only [W]; omega
  have live : R.Nonempty := by
    by_contra no
    have deg (x) (xw : x ∈ W) : d ≤ (outN D W x).card := by
      have small := two x xw
      have ne : (outN D S x).card ≠ 2 := fun eq => no ⟨x,mem_filter.mpr ⟨xw,eq⟩⟩
      have eq : outN D W x = outN D U x \ outN D S x := by
        ext z; simp only [W,mem_sdiff,mem_outN]; tauto
      have inc : outN D S x ⊆ outN D U x := fun z h =>
        mem_outN.mpr ⟨sub (outN_subset h),(mem_outN.mp h).2⟩
      have count := card_sdiff_add_card_eq_card inc
      rw [← eq,exactRows x xw] at count
      omega
    have := law D W safe deg (card_pos.mp (by omega))
    omega
  have bound : 3*R.card+5 ≤ 4*d := by
    have bs : B ⊆ W \ R := by
      intro x h
      obtain ⟨xw,xr⟩ := mem_sdiff.mp (mem_filter.mp h).1
      exact mem_sdiff.mpr ⟨xw,fun mem => xr (mem_union_right _ mem)⟩
    have bsize : B.card+1=d := near
    let X := (W \ R) \ B
    have split := card_sdiff_add_card_eq_card bs
    change X.card + B.card = (W \ R).card at split
    have parts := card_sdiff_add_card_eq_card rw'
    have paid (b) (hb : b ∈ B) : d-X.card ≤ (outN D B b).card := by
      have need : d ≤ (outN D (W \ R) b).card := by
        simpa [empty_union] using (mem_filter.mp hb).2
      have cover : outN D (W \ R) b ⊆ outN D B b ∪ X := by
        intro z hz
        by_cases zb : z ∈ B
        · exact mem_union_left _ (mem_outN.mpr ⟨zb,(mem_outN.mp hz).2⟩)
        · exact mem_union_right _ (mem_sdiff.mpr ⟨outN_subset hz,zb⟩)
      have bound := (card_le_card cover).trans (card_union_le _ _)
      omega
    have lb := laws (d-X.card) (by omega) D B (safe.mono_set (bs.trans sdiff_subset)) paid
      (card_pos.mp (by omega))
    omega
  suffices allT : ∀ T ⊆ R, T.Nonempty → (∀ x ∈ T, outN D R x ⊆ T) →
      (∀ x ∈ T, 3 ≤ (outN D T x).card) ∧ 10 ≤ T.card ∧ RecursiveHeads.FromHost D T by
    have ten := (allT R Subset.rfl live (fun _ _ => outN_subset)).2.1
    exact ⟨live,bound,by omega,allT⟩
  intro T tr tl closed
  have free := safe.mono_set (tr.trans rw')
  have heads (x) (xt : x ∈ T) : (outN D T x).Nonempty := by
    obtain ⟨z,zh⟩ := native_no_sink law size sub four safe hd exactRows two near x (tr xt)
    exact ⟨z,mem_outN.mpr ⟨closed x xt zh,(mem_outN.mp zh).2⟩⟩
  have pairs : Intersects D T := by
    intro x xt z zt
    obtain ⟨w,h⟩ := native_closed_intersect law size sub four safe exactRows two near.ge x (tr xt) z (tr zt)
    obtain ⟨xw,zw⟩ := mem_inter.mp h
    have left := mem_insert.mp xw
    have right := mem_insert.mp zw
    exact ⟨w,left.elim (fun eq => eq ▸ xt) (fun h => closed x xt h),
      left.imp_right (fun hh => (mem_outN.mp hh).2),right.imp_right (fun hh => (mem_outN.mp hh).2)⟩
  exact ⟨internal_degree free heads pairs,order_ten free heads pairs tl,RecursiveHeads.from_host free heads pairs tl⟩

#print axioms native_host
end LeanCH.BR.Closure.FourLabelHost
