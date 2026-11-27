import checkpoints.shen_extension.ThreeParentFreePromotion

namespace LeanCH.BR.TripleBank
open Finset BRq2 BRq3 BR45

/-- Replace the removed sink by one released bank label on the vacant core. -/
def rotatedCore (J : Finset ℕ) (d k : ℕ) := insert k (J.erase d)

/-- The two promoting rows are credited explicitly. Another old row needs
credit only if it loses d without gaining k and had no spare arc. -/
def rotatedCredits (D : CH.Digraph) (J : Finset ℕ) (a b d k t : ℕ) :=
  {a,b} ∪ ((inN D J d).filter (fun v => D v k ≠ true ∧ (outN D J v).card ≤ t)) ∪
    (if (outN D (rotatedCore J d k) k).card < t then {k} else ∅)

theorem rotatedCore_subset {J : Finset ℕ} {d k : ℕ} : rotatedCore J d k ⊆ insert k J :=
  insert_subset_insert _ (erase_subset ..)

theorem rotatedCore_size {J : Finset ℕ} {d k : ℕ} (dj : d ∈ J) (kj : k ∉ J) :
    (rotatedCore J d k).card=J.card := by
  rw [rotatedCore,card_insert_of_notMem (fun m => kj (mem_erase.mp m).2),card_erase_add_one dj]

private theorem exchange_row {D : CH.Digraph} {J : Finset ℕ} {d k v : ℕ} (dj : d ∈ J) (kj : k ∉ J) :
    (outN D (rotatedCore J d k) v).card + (if D v d=true then 1 else 0) =
      (outN D J v).card + (if D v k=true then 1 else 0) := by
  classical
  have apart : Disjoint ({k} : Finset ℕ) (J.erase d) := disjoint_singleton_left.mpr
    (fun h => kj (mem_erase.mp h).2)
  have h := card_outN_union (D:=D) apart v
  have er : outN D (J.erase d) v = (outN D J v).erase d := by
    ext w; simp only [mem_outN,mem_erase]; tauto
  rw [singleton_union,er] at h
  have one : (outN D {k} v).card = if D v k=true then 1 else 0 := by
    by_cases e : D v k=true
    · have eq : outN D {k} v = {k} := by ext w; simp only [mem_outN,mem_singleton]; grind
      simp [eq,e]
    · have eq : outN D {k} v = ∅ := by ext w; simp only [mem_outN,mem_singleton,notMem_empty]; grind
      simp [eq,e]
  rw [one] at h
  change (outN D (rotatedCore J d k) v).card = _ + _ at h
  by_cases e : D v d=true
  · have n := card_erase_add_one (mem_outN.mpr ⟨dj,e⟩)
    rw [ite_eq_left e]; omega
  · rw [erase_eq_of_notMem (fun m => e (mem_outN.mp m).2)] at h
    rw [ite_eq_right e]; omega

/-- A common head of d and k, and every one of its successors, has exactly
the same row on both cores. -/
theorem rotated_source_rows {D : CH.Digraph} {J : Finset ℕ} {p d k : ℕ}
    (safe : QFree D (insert k J) 3) (dj : d ∈ J) (pj : p ∈ J)
    (dp : D d p=true) (kp : D k p=true) :
    outN D (rotatedCore J d k) p = outN D J p ∧
    ∀ w ∈ outN D J p, outN D (rotatedCore J d k) w = outN D J w := by
  have vu {v : ℕ} (m : v ∈ J) : v ∈ insert k J := mem_insert_of_mem m
  have ku : k ∈ insert k J := mem_insert_self ..
  have same {v} (nd : D v d ≠ true) (nk : D v k ≠ true) :
      outN D (rotatedCore J d k) v = outN D J v := by
    ext w
    simp only [rotatedCore,mem_outN,mem_insert,mem_erase]
    grind
  refine ⟨same (digonfree safe (by decide) (vu dj) (vu pj) dp)
    (digonfree safe (by decide) ku (vu pj) kp),?_⟩
  intro w wm
  have via {v} (vv : v ∈ insert k J) (vp : D v p=true) : D w v ≠ true := fun wv =>
    safe v 3 (by decide) (by decide) (.step (vu pj) vp (.step (vu (outN_subset wm))
      (mem_outN.mp wm).2 (.step vv wv (.refl _))))
  exact same (via (vu dj) dp) (via ku kp)

/-- After rotation, the two promoted rows can be two short. Every other
row can be at most one short, and the stated credit set covers each loss. -/
theorem rotated_floor {D : CH.Digraph} {J T : Finset ℕ} {a b d k t : ℕ}
    (dj : d ∈ J) (kj : k ∉ J)
    (parents : ∀ v ∈ ({a,b} : Finset ℕ), t ≤ (outN D J v).card+1)
    (old : ∀ v ∈ J, v ≠ a → v ≠ b → v ≠ d → t ≤ (outN D J v).card)
    (released : t ≤ (outN D (rotatedCore J d k) k).card+1)
    (cover : rotatedCredits D J a b d k t ⊆ T) :
    (∀ v ∈ ({a,b} : Finset ℕ), t ≤ (outN D (rotatedCore J d k) v).card+1+(if v∈T then 1 else 0)) ∧
    (∀ v ∈ rotatedCore J d k, v ≠ a → v ≠ b →
      t ≤ (outN D (rotatedCore J d k) v).card+(if v∈T then 1 else 0)) := by
  classical
  constructor
  · intro v vm
    have h := parents v vm
    have m := cover (mem_union_left _ (mem_union_left _ vm))
    have swap := exchange_row (D:=D) (v:=v) dj kj
    rw [ite_eq_left m]
    split at swap <;> split at swap <;> omega
  · intro v vm va vb
    by_cases high : t ≤ (outN D (rotatedCore J d k) v).card
    · omega
    have lt : (outN D (rotatedCore J d k) v).card < t := by omega
    rcases mem_insert.mp vm with vk | ve
    · subst v
      have m := cover (mem_union_right _ (show k ∈ (if (outN D (rotatedCore J d k) k).card < t then {k} else ∅)
        by simp [lt]))
      rw [ite_eq_left m]; exact released
    obtain ⟨vd,vj⟩ := mem_erase.mp ve
    have h := old v vj va vb vd
    have swap := exchange_row (D:=D) (v:=v) dj kj
    have facts : D v d=true ∧ D v k ≠ true ∧ (outN D J v).card=t := by
      split at swap <;> split at swap <;> grind
    have m := cover (mem_union_left _ (mem_union_right _ (mem_filter.mpr
      ⟨mem_inN.mpr ⟨vj,facts.1⟩,facts.2.1,facts.2.2.le⟩)))
    rw [ite_eq_left m]
    rw [ite_eq_left facts.1,ite_eq_right facts.2.1] at swap
    omega

#print axioms rotated_source_rows
#print axioms rotated_floor
end LeanCH.BR.TripleBank
