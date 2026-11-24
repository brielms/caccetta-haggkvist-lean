import checkpoints.shen_extension.BookedPrimaryArrivals
import checkpoints.shen_extension.SparseBankGate

namespace LeanCH.BR.LowShellCycleSelection
open Finset BRq2 BRq3 BR45 BRsGen ExteriorPacking PhysicalCycleStock
open scoped Classical

/-- Repricing a switched account pins its primary origins to the far side of
the same exterior. At most one minimum-width class can use that account. -/
theorem moved_origin {D V q r C Y} (free : QFree D V q) (reg : OutEq r D V)
    {t : Selection D V q r 3 (3*r)} (room : Room q r) (hr : 4≤r)
    (fit : r≤q+2) (moved : C∈shortSwitches t) (ym : Y∈claims t C) (first : C⊆outN D V (t.rep Y)) :
    Disjoint (outN D V (t.rep Y)) (exterior D V C) ∧
      exterior D V C⊆Y ∧ (Y.card=r-1 → Y=exterior D V C) := by
  classical
  obtain ⟨hq,h₁,h₂,h₃,h₄,_⟩ := room
  have ⟨key,mark⟩ := mem_filter.mp ym
  have uv := rep_native t key
  have floor := (mem_filter.mp (mem_filter.mp (t.represents Y key)).1).2
  have profile := low_third_second free (by omega) reg uv h₁ h₂ h₃ h₄ floor
  have one := card_B1 (free.mono_bound (by omega : 4≤q)) uv
  rw [reg _ uv] at one
  have two := @card_B2 D V (t.rep Y)
  change (ball D V (t.rep Y) 2).card≤2*r+1 at profile
  have width := (mem_filter.mp moved).2.1
  have len := t.length _ (t.assigned Y key)
  rw [mark] at len
  have slots := card_sdiff_of_subset first
  rw [reg _ uv] at slots
  have bank := (switched_shell_paid free reg t (by omega) hr fit moved).1
  have fill v (vm : v∈C) : exterior D V C⊆outN D V v := by
    intro z zm
    exact mem_of_mem_erase ((complete_row (bank.rooted v vm) (reg v ((bank.rooted v vm).sub vm)) bank.width).symm ▸ zm)
  have ew := bank.width
  obtain ⟨off,sub⟩ := sparse_gate free (by omega) uv first fill
    (fun w wm=>(reg w (outN_subset wm)).ge) bank.sparse (by omega)
  rw [rep_key t key] at sub
  exact ⟨off,sub,fun y=>(eq_of_subset_of_card_le sub (by omega)).symm⟩

/-- Both possibilities keep the *same* unpaid physical cycle and its
itemized arrivals. In either case the cycle is proper. -/
structure MixedPayer {D V q r} (t : Selection D V q r 3 (3*r)) (C : Finset ℕ) (δ cap : ℕ)
    (A : Finset (Finset ℕ)) : Prop where
  charges : PrimaryArrivals t C δ cap A
  kept : ∃Y∈claims t C,Y∉shortSwitches t ∧ C⊆outN D V (t.rep Y)
  length : C.card=q+1
  degree : r=q+2
  shape : (C∉shortSwitches t ∧ ProperMark t cap C) ∨
    (C∈shortSwitches t ∧ CompletePayer D V r 1 C ∧
      ∀Y∈claims t C,C⊆outN D V (t.rep Y) →
        Disjoint (outN D V (t.rep Y)) (exterior D V C) ∧ exterior D V C⊆Y ∧
        (Y.card=r-1 → Y=exterior D V C))

theorem mixed_on_booking {D V q r target g mid top cap} (free : QFree D V q) (reg : OutEq r D V)
    (live : V.Nonempty) (t : Selection D V q r 3 (3*r)) (policy : ShellBooking t)
    (room : PrimaryRoom q r V.card target g mid top cap) (reserve : cap+5<3*(r-1)) :
    ∃C A,MixedPayer t C (V.card-((r-1)+top)) cap A := by
  classical
  obtain ⟨C,A,due⟩ := primary_after_routes free reg live t policy room reserve
  obtain ⟨Y,ym,kept,first,cy⟩ := first_is_kept policy due.first
  refine ⟨C,A,?_⟩
  have fit := room.route.close
  have hq := room.route.cycle.1
  have hr := room.route.growth.2.1
  by_cases mv : C∈shortSwitches t
  · have wid := (mem_filter.mp mv).2.1
    have long := t.length _ (t.assigned Y (mem_filter.mp ym).1)
    rw [(mem_filter.mp ym).2] at long
    exact ⟨due,⟨Y,ym,kept,first⟩,by omega,by omega,.inr ⟨mv,(switched_shell_paid free reg t (by omega) hr fit mv).1,
      fun _ m h=>moved_origin free reg room.route.cycle hr fit mv m h⟩⟩
  · have proper : PrimaryShort t cap C := by
      refine ⟨due.bookedHere,due.first,?_,?_⟩
      · intro Z zm cycle
        have id := (mem_filter.mp zm).2
        have notMoved : Z∉shortSwitches t := fun h=>mv (((policy.secondary Z h).symm.trans id) ▸ h)
        exact id ▸ policy.primary Z (mem_filter.mp zm).1 notMoved cycle
      · apply due.due.trans
        apply add_le_add_right
        by_cases terminal : StrongTerminal D V r C
        · rw [ite_eq_left terminal]
          have units := sum_le_sum (fun Z (zm : Z∈A)=>(due.routed Z zm).2.2.2.1)
          simp only [sum_const,nsmul_eq_mul,mul_one] at units
          exact units.trans (by exact_mod_cast due.bounded)
        · have empty : A=∅ := eq_empty_iff_forall_notMem.mpr (fun Z zm=>terminal (due.routed Z zm).2.2.2.2.1)
          simp [empty,terminal]
    have proper' := proper_primary free reg proper room.route
    exact ⟨due,⟨Y,ym,kept,first⟩,proper'.length,proper'.parameters,.inl ⟨mv,proper'⟩⟩

#print axioms moved_origin
#print axioms mixed_on_booking
end LeanCH.BR.LowShellCycleSelection
