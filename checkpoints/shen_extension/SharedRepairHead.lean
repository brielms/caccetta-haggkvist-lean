import checkpoints.shen_extension.TripleBankFreeRepair

/-! An exact cut criterion for unit repairs directed to the same surviving head. -/
namespace LeanCH.BR.TripleBank
open Finset BRq2 BRq3 BR45

/-- Keeping z → w obliges w to remove all heads in R. -/
def retainable (D : CH.Digraph) (U R : Finset ℕ) (z t : ℕ) : Finset ℕ :=
  (outN D U z).filter (fun w => t ≤ (outN D U w \ R).card)

/-- Arbitrary cuts can pay the prescribed new arcs if and only if the common
head can keep t successors, each able to remove its arcs to the adding rows. -/
theorem shared_head_iff {D : CH.Digraph} {U R : Finset ℕ} {z t : ℕ}
    (safe : QFree D U 3) (zu : z ∈ U)
    (fresh : ∀ a ∈ R, a ≠ z ∧ D a z ≠ true ∧ D z a ≠ true)
    (room : ∀ a ∈ U, t ≤ (outN D U a).card + (if a ∈ R then 1 else 0)) :
    (∃ C : ℕ → Finset ℕ,
      QFree (patch D (fun a => if a ∈ R then {z} else ∅) C) U 3 ∧
      ∀ a ∈ U, t ≤ (outN (patch D (fun a => if a ∈ R then {z} else ∅) C) U a).card) ↔
    t ≤ (retainable D U R z t).card := by
  classical
  let A (a : ℕ) : Finset ℕ := if a ∈ R then {z} else ∅
  let K := retainable D U R z t
  have zr : z ∉ R := fun h => (fresh z h).1 rfl
  have spec {a b} (new : b ∈ A a) : a ∈ R ∧ b = z := by
    by_cases ar : a ∈ R
    · exact ⟨ar,by simpa [A,ar] using new⟩
    · simp [A,ar] at new
  have outsider {w} (zw : D z w = true) : w ∉ R := fun wr => (fresh w wr).2.2 zw
  constructor
  · rintro ⟨C,ok,floor⟩
    let E := patch D A C
    have old {a b} (ar : a ∉ R) (ed : E a b = true) : D a b = true := by
      have h : b ∈ A a ∨ D a b = true ∧ b ∉ C a := of_decide_eq_true ed
      rcases h with h | h
      · exact False.elim (ar (spec h).1)
      · exact h.1
    apply (floor z zu).trans (card_le_card ?_)
    intro w wm
    change w ∈ outN E U z at wm
    obtain ⟨wu,zw⟩ := mem_outN.mp wm
    have edge := old zr zw
    refine mem_filter.mpr ⟨mem_outN.mpr ⟨wu,edge⟩,(floor w wu).trans (card_le_card ?_)⟩
    intro a am
    change a ∈ outN E U w at am
    obtain ⟨au,wa⟩ := mem_outN.mp am
    refine mem_sdiff.mpr ⟨mem_outN.mpr ⟨au,old (outsider edge) wa⟩,?_⟩
    intro ar
    have az : E a z = true := by
      apply decide_eq_true
      exact Or.inl (by simp [A,ar])
    exact ok a 3 (by decide) (by decide) (.step zu az (.step wu zw (.step au wa (.refl _))))
  · intro enough
    change t ≤ K.card at enough
    let C (a : ℕ) : Finset ℕ :=
      if a = z then outN D U z \ K else if a ∈ K then R else ∅
    have zk : z ∉ K := fun h => loopfree safe (by decide) zu (mem_outN.mp (mem_filter.mp h).1).2
    obtain ⟨ok,rows⟩ := patch_certificate (A := A) (C := C) safe
      (fun a _ _ new => by
        obtain ⟨ar,rfl⟩ := spec new
        exact ⟨zu,(fresh a ar).1.symm,(fresh a ar).2⟩)
      (fun a _ b new w wu zw _ => by
        obtain ⟨ar,bz⟩ := spec new
        subst b
        by_cases wk : w ∈ K
        · have wz : w ≠ z := fun eq => zk (eq ▸ wk)
          exact Or.inr (by simpa [C,wz,wk] using ar)
        · exact Or.inl (by simpa only [C,ite_true] using
            (show w ∈ outN D U z \ K from mem_sdiff.mpr ⟨mem_outN.mpr ⟨wu,zw⟩,wk⟩)))
      (fun _ _ _ new _ next => False.elim (zr ((spec new).2 ▸ (spec next).1)))
    refine ⟨C,ok,?_⟩
    intro a au
    rw [rows a au]
    by_cases az : a = z
    · subst a
      have eq : outN D U z \ C z = K := by
        ext w
        have incl : w ∈ K → w ∈ outN D U z := fun h => (mem_filter.mp h).1
        simp only [C,ite_true,mem_sdiff]
        tauto
      rw [eq]
      omega
    by_cases ak : a ∈ K
    · have pay := (mem_filter.mp ak).2
      rw [show C a = R by simp [C,az,ak]]
      omega
    · rw [show C a = ∅ by simp [C,az,ak],sdiff_empty]
      simpa [A,apply_ite Finset.card] using room a au

#print axioms shared_head_iff
end LeanCH.BR.TripleBank
