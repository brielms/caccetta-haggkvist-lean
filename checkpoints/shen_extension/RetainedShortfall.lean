import checkpoints.shen_extension.RootRegularBridge

namespace LeanCH.BR.RetainedShortfall
open Finset BRq2 BRq3 BypassRepair LoneRow Closure.DeficitLevels

/-- Exact fixed-quota debt after erasing an arbitrary set of labels.
Only deleted heads beyond a surviving row's old spare produce new debt. -/
theorem set_identity {D : CH.Digraph} {U C : Finset ℕ} {t : ℕ} (sub : C⊆U) :
    total t D (U\C)+(∑x∈C,cost t D U x) =
    total t D U+∑u∈U\C,((outN D U u∩C).card-((outN D U u).card-t)) := by
  classical
  have row (u : ℕ) : cost t D (U\C) u=cost t D U u+
      ((outN D U u∩C).card-((outN D U u).card-t)) := by
    have eq : outN D (U\C) u=outN D U u\C := by ext; simp only [mem_outN,mem_sdiff]; tauto
    have partition := card_sdiff_add_card_inter (outN D U u) C
    unfold cost
    rw [eq]
    omega
  have parts := sum_sdiff sub (f:=cost t D U)
  unfold total
  simp only [row,sum_add_distrib]
  omega

/-- The price of erasing one marked column is exactly its surviving
parents that had no spare, after refunding the erased row's own debt. -/
theorem column_identity {D : CH.Digraph} {U : Finset ℕ} {t x : ℕ} (xm : x∈U) :
    total t D (U.erase x)+cost t D U x=total t D U+
      ((U.erase x).filter (fun u=>D u x=true ∧ (outN D U u).card≤t)).card := by
  classical
  have id := set_identity (D:=D) (t:=t) (singleton_subset_iff.mpr xm)
  have cut : U\{x}=U.erase x := by ext; simp [and_comm]
  rw [cut,sum_singleton] at id
  rw [id,card_filter]
  congr 1
  apply sum_congr rfl
  intro u _
  by_cases ux : D u x=true
  · have hit := mem_outN.mpr ⟨xm,ux⟩
    rw [inter_eq_right.mpr (singleton_subset_iff.mpr hit),card_singleton]
    simp only [ux,true_and]
    split <;> omega
  · have miss : x∉outN D U u := fun h=>ux (mem_outN.mp h).2
    have empty : outN D U u∩{x}=∅ := by ext; simp; aesop
    simp [empty,ux]

theorem column_floor {D U q t x} (none : NoHost q t) (near : NoNearHost q t)
    (free : QFree D U q) (xm : x∈U) (live : (U.erase x).Nonempty)
    (room : U.card≤q*t+1) :
    2+cost t D U x≤total t D U+
      ((U.erase x).filter (fun u=>D u x=true ∧ (outN D U u).card≤t)).card := by
  have sizes := card_erase_add_one xm
  have debt := ShortfallBridge.total_ge_two none near (free.mono_set (erase_subset x U)) live (by omega)
  have id := column_identity (D:=D) (t:=t) xm
  omega

#print axioms set_identity
#print axioms column_identity
#print axioms column_floor
end LeanCH.BR.RetainedShortfall
