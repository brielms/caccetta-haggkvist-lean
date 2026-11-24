import checkpoints.shen_extension.FullPrimaryComplete
import checkpoints.shen_extension.MeasuredCycleBudget

namespace LeanCH.BR.LowShellCycleSelection
open Finset BRq2 BRq3 BR45 BRsGen ExteriorPacking PhysicalCycleStock

/-- The same underfunded cycle misses exactly one named head of a first
representative. The two sizes follow from the girth and the available slots. -/
structure ProperMark {D V q r} (sel : Selection D V q r 3 (3*r)) (cap : ℕ) (C : Finset ℕ) : Prop where
  narrow : NarrowMark sel cap C
  parameters : r=q+2
  length : C.card=q+1
  head : ∀Y∈claims sel C, C⊆outN D V (sel.rep Y) →
    ∃w,w∉C ∧ outN D V (sel.rep Y)=insert w C

theorem proper_primary {D V q r target cap C} (free : QFree D V q) (reg : OutEq r D V)
    {sel : Selection D V q r 3 (3*r)} (short : PrimaryShort sel cap C)
    (ready : RoutingRoom q r V.card target) : ProperMark sel cap C := by
  classical
  have widths := primary_widths free reg short ready
  have smaller : C.card≠r := by
    intro eq
    rcases widths with left|right
    · exact full_at_zero_false free reg short ready eq left
    · exact full_at_one_false free reg short ready eq right
  obtain ⟨Y,ym,sub,_⟩ := short.2.1
  obtain ⟨key,chosen⟩ := mem_filter.mp ym
  have len := sel.length _ (sel.assigned _ key)
  rw [chosen] at len
  have upper := card_le_card sub
  rw [reg _ (rep_native sel key)] at upper
  have fit := ready.close
  refine ⟨⟨short,widths⟩,by omega,by omega,?_⟩
  intro Z zm first
  have degree := reg _ (rep_native sel (mem_filter.mp zm).1)
  have one : ((outN D V (sel.rep Z))\C).card=1 := by
    rw [card_sdiff_of_subset first,degree]; omega
  obtain ⟨w,eq⟩ := card_eq_one.mp one
  have wm : w∈outN D V (sel.rep Z)\C := eq.symm ▸ mem_singleton_self w
  obtain ⟨head,fresh⟩ := mem_sdiff.mp wm
  refine ⟨w,fresh,Subset.antisymm ?_ (insert_subset head first)⟩
  intro a am
  by_cases inside : a∈C
  · exact mem_insert_of_mem inside
  · have left : a∈outN D V (sel.rep Z)\C := mem_sdiff.mpr ⟨am,inside⟩
    rw [eq] at left
    exact mem_insert.mpr (.inl (mem_singleton.mp left))

structure OnProperPrimary (p : CHRuleCatalog.Input) : Prop where
  apply_room : ∀target g mid top cap,PrimaryRoom (CHRuleCatalog.cutoff p) p.s p.n target g mid top cap →
    ∃F,(∀a b,F a b=true → p.D a b=true) ∧ OutEq p.s F (range p.n) ∧
      ∃t : Selection F (range p.n) (CHRuleCatalog.cutoff p) p.s 3 (3*p.s),∃C,ProperMark t cap C

theorem proper_from_input {p : CHRuleCatalog.Input} {target g mid top cap} (bad : CHRuleCatalog.Bad p)
    (room : PrimaryRoom (CHRuleCatalog.cutoff p) p.s p.n target g mid top cap) :
    ∃F,(∀a b,F a b=true → p.D a b=true) ∧ OutEq p.s F (range p.n) ∧
      ∃t : Selection F (range p.n) (CHRuleCatalog.cutoff p) p.s 3 (3*p.s),∃C,ProperMark t cap C := by
  obtain ⟨F,sub,reg,t,C,h⟩ := marked_from_input bad room
  have ff := qfree_sub sub (qfree_of_noShort bad.loopless bad.missing)
  exact ⟨F,sub,reg,t,C,proper_primary ff reg h (by simpa only [card_range] using room.route)⟩

theorem proper_on_bad {p : CHRuleCatalog.Input} (bad : CHRuleCatalog.Bad p) : OnProperPrimary p :=
  ⟨fun _ _ _ _ _ room=>proper_from_input bad room⟩

attribute [aesop safe forward (immediate := [bad]) (rule_sets := [CHGraphFamilies])] proper_on_bad
attribute [aesop safe forward (immediate := [bad,room]) (rule_sets := [CHGraphFamilies])] proper_from_input
attribute [aesop safe forward (immediate := [free,reg,short,ready]) (rule_sets := [CHGraphFamilies])] proper_primary

#print axioms proper_primary
#print axioms proper_on_bad
end LeanCH.BR.LowShellCycleSelection
