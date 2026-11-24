import checkpoints.shen_extension.ArrivalParentReserve

namespace LeanCH.BR.LowShellCycleSelection
open Finset BRq2 BRq3 BR45 BRsGen ExteriorPacking PhysicalCycleStock
open scoped Classical

/-- Direct claims of a sparse complete cycle, after reserving high parents.
At most one first-shell key can carry a short representative. The switched
key and the acyclic keys keep separate bills. -/
theorem terminal_direct_budget {D V q r target C} (free : QFree D V q) (reg : OutEq r D V)
    (t : Selection D V q r 3 (3*r)) (policy : ShellBooking t) (ready : RoutingRoom q r V.card target)
    (term : StrongTerminal D V r C) :
    netDebt t C+(highParents D V C 3 (3*r)).card ≤ ((allParents D V C).card:ℚ)+8 := by
  classical
  let E := exterior D V C
  let K := (claims t C).filter (fun Y=>C⊆outN D V (t.rep Y))
  let J := (claims t C\K).erase C
  have keys : K⊆claims t C := filter_subset _ _
  have other : J⊆claims t C := (erase_subset _ _).trans sdiff_subset
  have first Y (ym : Y∈K) := (mem_filter.mp ym).2
  have count := representatives_with_reserve t keys first
  have hq := ready.cycle.1
  have hr := ready.growth.2.1
  have fit := ready.close
  have size := term.size
  have width := term.nextSize
  have all v (vm : v∈C) : exterior D V C⊆outN D V v := fun _ h=>mem_of_mem_erase
    ((complete_row (term.rooted v vm) (reg _ ((term.rooted v vm).sub vm)) width).symm ▸ h)
  have shortKey Y (ym : Y∈K) (low : (ball D V (t.rep Y) 3).card<3*r) : Y=E := by
    have key := (mem_filter.mp (keys ym)).1
    have uv := rep_native t key
    have root := term.rooted
    have len := t.length _ (t.assigned Y key)
    rw [(mem_filter.mp (keys ym)).2] at len
    have shape := short_shapes free reg ready uv low
    have narrow := shape.resolve_right (fun h=>short_large_second_escape free hq reg uv fit len root (first Y ym)
      (by omega) h.1 (by omega))
    have diff := card_sdiff_of_subset (first Y ym)
    rw [reg _ uv] at diff
    have inc := (sparse_gate free (by omega) uv (first Y ym) all
      (fun a (am : a∈outN D V (t.rep Y))=>(reg a (outN_subset am)).ge)
      (fun z zm=>((term.nextRooted z zm).one z zm).le) (by omega)).2
    exact (rep_key t key).symm.trans (eq_of_subset_of_card_le inc (by omega)).symm
  have unit Y (ym : Y∈K.erase E) : shellDebt D V 3 (3*r) Y≤1 := by
    have key := (mem_filter.mp (keys (mem_of_mem_erase ym))).1
    have medium : 3*r≤(ball D V (t.rep Y) 3).card := by
      by_contra! s; exact (mem_erase.mp ym).1 (shortKey Y (mem_of_mem_erase ym) s)
    apply (class_residual (m:=1) _).trans (by decide)
    intro v vm
    have := t.least Y key v vm
    have := (mem_filter.mp (mem_filter.mp vm).1).2
    rw [show (ball D V v 3).card=3*r by omega]; simp [debit]
  have maxBill Y : shellDebt D V 3 (3*r) Y≤4 := by
    apply (class_residual (m:=3) _).trans (by decide)
    intro v vm; unfold debit; split_ifs <;> omega
  have partialBill := sum_le_sum unit
  simp only [sum_const_nat (fun _ _=>rfl),Nat.mul_one] at partialBill
  have kcost : ∑Y∈K,shellDebt D V 3 (3*r) Y≤K.card+3 := by
    by_cases has : E∈K
    · have := sum_erase_add K (fun Y=>shellDebt D V 3 (3*r) Y) has
      have := maxBill E
      have := card_pos.mpr (show K.Nonempty from ⟨E,has⟩)
      rw [card_erase_of_mem has] at partialBill
      omega
    rw [erase_eq_of_notMem has] at partialBill; omega
  have apart : Disjoint K J := disjoint_left.mpr (fun Y ym jm=>(mem_sdiff.mp (mem_of_mem_erase jm)).2 ym)
  have jbill := cohort_unit_bill free reg t ready other (fun Y ym=>by
    by_contra cy
    have mark := (mem_filter.mp (other ym)).2
    have no : Y∉shortSwitches t := fun sw=>(mem_erase.mp ym).1 ((policy.secondary Y sw).symm.trans mark)
    exact (mem_sdiff.mp (mem_of_mem_erase ym)).2
      (mem_filter.mpr ⟨other ym,mark ▸ policy.primary Y (mem_filter.mp (other ym)).1 no cy⟩))
  have bill := split_bill t keys other apart (a:=K.card+3) (by omega) jbill
  have rest : claims t C\(K∪J)⊆{C} := by
    intro Y ym
    have ⟨owner,off⟩ := mem_sdiff.mp ym
    apply mem_singleton.mpr
    by_contra ne
    exact off (mem_union_right _ (mem_erase.mpr ⟨ne,mem_sdiff.mpr ⟨owner,fun k=>off (mem_union_left _ k)⟩⟩))
  have lastNat : (∑Y∈claims t C\(K∪J),shellDebt D V 3 (3*r) Y)≤4 :=
    (sum_le_sum_of_subset rest).trans (by simpa using maxBill C)
  have lastQ : (∑Y∈claims t C\(K∪J),(shellDebt D V 3 (3*r) Y:ℚ))≤4 := by exact_mod_cast lastNat
  have totalQ : (K.card:ℚ)+(highParents D V C 3 (3*r)).card≤(allParents D V C).card := by exact_mod_cast count
  push_cast at bill
  linarith only [bill,lastQ,totalQ]

#print axioms terminal_direct_budget
end LeanCH.BR.LowShellCycleSelection
