import checkpoints.shen_extension.RotatedPaymentCore
import checkpoints.shen_extension.VacantTargetPayment

namespace LeanCH.BR.TripleBank
open Finset BRq2 BRq3 BR45

/-- Credit a set of shared blockers and either of the two targets, in
addition to the rows that lost a unit in the rotation. -/
theorem rotated_vacant_payment {D : CH.Digraph} {J L W₀ P₀ : Finset ℕ} {a b c d k p q t : ℕ}
    (safe : QFree D (insert k J) 3) (fresh : c ∉ insert k J) (kj : k ∉ J) (dj : d ∈ J)
    (small : J.card+1 ≤ 3*t) (no : BypassRepair.NoHost 3 t)
    (sub : L ⊆ J) (dl : d ∉ L) (pl : p ∈ L) (ql : q ∈ L) (pq : p ≠ q)
    (aj : a ∈ J) (bj : b ∈ J) (ab : a≠b) (ad : a≠d) (bd : b≠d) (al : a∉L) (bl : b∉L)
    (neutral : ∀ l ∈ L, D l a ≠ true ∧ D l b ≠ true)
    (ap : D a p ≠ true) (bq : D b q ≠ true)
    (dp : D d p=true) (dq : D d q=true) (kp : D k p=true) (kq : D k q=true)
    (parents : ∀ v ∈ ({a,b} : Finset ℕ), t ≤ (outN D J v).card+1)
    (old : ∀ v ∈ J, v ≠ a → v ≠ b → v ≠ d → t ≤ (outN D J v).card)
    (released : t ≤ (outN D (rotatedCore J d k) k).card+1)
    (fullP : t+1 ≤ (outN D J p).card) (fullQ : t+1 ≤ (outN D J q).card)
    (spare : ∀ w ∈ (outN D J p \ L) ∪ (outN D J q \ L), t+1 ≤ (outN D J w).card)
    (two : P₀ ⊆ {p,q})
    (budget : ((((outN D J p \ L) ∩ (outN D J q \ L)) \ W₀).card ≤ 2+P₀.card)) :
    let J' := rotatedCore J d k
    let T := rotatedCredits D J a b d k t ∪ W₀ ∪ P₀
    ((J' \ T).filter (fun v => Disjoint (outN D J' v) T)).card < t := by
  classical
  intro J' T
  have pay : rotatedCredits D J a b d k t ⊆ T := (subset_union_left).trans subset_union_left
  have pin : P₀ ⊆ T := subset_union_right
  have wsub : W₀ ⊆ T := (subset_union_right).trans subset_union_left
  have bounds := rotated_floor dj kj parents old released pay
  obtain ⟨pp,wp⟩ := rotated_source_rows safe dj (sub pl) dp kp
  obtain ⟨qq,wq⟩ := rotated_source_rows safe dj (sub ql) dq kq
  have transport (w) (wm : w ∈ (outN D J p \ L) ∪ (outN D J q \ L)) :
      outN D J' w=outN D J w := (mem_union.mp wm).elim
    (fun h => wp w (mem_sdiff.mp h).1) (fun h => wq w (mem_sdiff.mp h).1)
  have inside {v} (vj : v ∈ J) (vd : v ≠ d) : v ∈ J' :=
    mem_insert_of_mem (mem_erase.mpr ⟨vd,vj⟩)
  have count : P₀.card ≤ (if p∈T then 1 else 0)+(if q∈T then 1 else 0) := by
    have incl : P₀ ⊆ ({p,q} : Finset ℕ).filter (fun v => v∈T) := fun v vm =>
      mem_filter.mpr ⟨two vm,pin vm⟩
    have h := card_le_card incl
    by_cases pT : p∈T <;> by_cases qT : q∈T <;> simpa [filter_insert,filter_singleton,pT,qT,pq] using h
  have safe' := safe.mono_set (rotatedCore_subset (J:=J) (d:=d) (k:=k))
  refine vacant_payment_bound safe' (fun m => fresh (rotatedCore_subset m))
    ((by rw [rotatedCore_size dj kj] : J'.card+1=J.card+1) ▸ small) no
    (fun v vm => inside (sub vm) (fun e => dl (e ▸ vm))) pl ql pq (inside aj ad) (inside bj bd)
    ab al bl neutral ap bq bounds.1 bounds.2 (pp ▸ fullP) (qq ▸ fullQ) ?_ ?_ ?_ ?_
  · intro w wm
    rw [pp,qq] at wm
    rw [transport w wm]
    exact spare w wm
  · rw [pp,qq]
    have weak := card_le_card (show ((outN D J p \ L) ∩ (outN D J q \ L)) \ T ⊆
      ((outN D J p \ L) ∩ (outN D J q \ L)) \ W₀ from fun _ wm =>
        mem_sdiff.mpr ⟨(mem_sdiff.mp wm).1,fun h => (mem_sdiff.mp wm).2 (wsub h)⟩)
    omega
  · exact Or.inl (pay (mem_union_left _ (mem_union_left _ (mem_insert_self ..))))
  · exact Or.inl (pay (mem_union_left _ (mem_union_left _ (mem_insert_of_mem (mem_singleton_self _)))))

#print axioms rotated_vacant_payment
end LeanCH.BR.TripleBank
