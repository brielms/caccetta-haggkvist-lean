import checkpoints.shen_extension.ResidualShellDebt

namespace LeanCH.BR.LowShellCycleSelection
open Finset BRq2 BRq3 BR45 BRsGen PhysicalCycleStock ExteriorPacking
open scoped Classical

/-- Realize a transfer as a selection on the same graph. The values of
the representative and the payer at every retained class are specified. -/
theorem self_booking {D V q r k b} (s : Selection D V q r k b) (M : Finset (Finset ℕ))
    (valid : ∀Y∈M,q<Y.card ∧ (∀v∈Y,Rooted D V v Y) ∧ omissions D V Y r≤r-q) :
    ∃t : Selection D V q r k b,t.rep=s.rep ∧
      ∀Y∈classes D V k b,t.pay Y=if Y∈M then Y else s.pay Y := by
  classical
  apply rebook s (fun Y C=>C=if Y∈M then Y else s.pay Y)
  intro Y ym
  by_cases moved : Y∈M
  · obtain ⟨len,root,loss⟩ := valid _ moved
    exact ⟨Y,Or.inr Subset.rfl,len,root,loss,(ite_eq_left moved).symm⟩
  have cm := s.assigned Y ym
  exact ⟨_,s.located Y ym,s.length _ cm,s.rooted _ cm,s.loss _ cm,(ite_eq_right moved).symm⟩

structure ShellBooking {D V q r} (sel : Selection D V q r 3 (3*r)) : Prop where
  secondary : ∀Y∈shortSwitches sel,sel.pay Y=Y
  primary : ∀Y∈classes D V 3 (3*r),Y∉shortSwitches sel →
    ¬QFree D (outN D V (sel.rep Y)) (outN D V (sel.rep Y)).card → sel.pay Y⊆outN D V (sel.rep Y)
  strong : ∀Y∈classes D V 3 (3*r),NeedsStrong sel Y → StrongChoice sel Y (sel.pay Y)

/-- Under the canonical policy, a primary claimant can never be one of
the short classes already routed to their own second shell. -/
theorem first_is_kept {D V q r C} {sel : Selection D V q r 3 (3*r)} (booking : ShellBooking sel)
    (first : FirstClaim sel C) :
    ∃Y∈claims sel C,Y∉shortSwitches sel ∧ C⊆outN D V (sel.rep Y) ∧
      ¬QFree D (outN D V (sel.rep Y)) (outN D V (sel.rep Y)).card := by
  obtain ⟨Y,ym,sub,cy⟩ := first
  refine ⟨Y,ym,?_,sub,cy⟩
  intro moved
  have hm := sel.assigned Y (mem_filter.mp ym).1
  have len := sel.length _ hm
  obtain ⟨a,am⟩ := card_pos.mp (by omega : 0<(sel.pay Y).card)
  have first := sub ((mem_filter.mp ym).2 ▸ am)
  have sec := (rep_key sel (mem_filter.mp ym).1).symm ▸ (booking.secondary _ moved ▸ am : a∈Y)
  exact (mem_N2.mp sec).2 (X_B1 first)

theorem book_short_shells {D V q r} (free : QFree D V q) (reg : OutEq r D V)
    (s : Selection D V q r 3 (3*r)) (room : Room q r) (hr : 4≤r) (fit : r≤q+2) :
    ∃t : Selection D V q r 3 (3*r),t.rep=s.rep ∧ ShellBooking t := by
  classical
  have hq := room.1
  obtain ⟨initial,orig,policy⟩ := primary_selection free reg s room
  obtain ⟨mid,step⟩ := choose_strong_first free reg initial (by omega) hr fit
  let M := shortSwitches mid
  obtain ⟨t,eq,book⟩ := self_booking mid M (by
    intro Y ym
    have info := (switched_shell_paid free reg mid (by omega) hr fit ym).1
    have key := (mem_filter.mp (show Y∈shortSwitches mid from ym)).1
    have width := (mem_filter.mp (show Y∈shortSwitches mid from ym)).2.1
    have yv : Y⊆V := rep_key mid key ▸ (fun _ m=>N2_subV m)
    have long : q<Y.card := by
      by_contra! small
      obtain ⟨v,vm,sink⟩ := exists_sink (free.mono_set yv) (card_pos.mp (by omega : 0<Y.card)) small
      obtain ⟨a,am⟩ := card_pos.mp (show 0<(outN D Y v).card by rw [(info.rooted v vm).one v vm]; decide)
      exact sink a (outN_subset am) (mem_outN.mp am).2
    exact ⟨long,info.rooted,by simp [omissions,info.width]⟩)
  have keyEq : shortSwitches t=M := by change shortSwitches t=shortSwitches mid; unfold shortSwitches; rw [eq]
  refine ⟨t,eq.trans (step.same.trans orig),?_,?_,?_⟩
  · intro Y ym
    rw [keyEq] at ym
    exact (book _ (mem_filter.mp (show Y∈shortSwitches mid from ym)).1).trans (ite_eq_left ym)
  · intro Y ym away cyclic
    rw [keyEq] at away
    rw [book Y ym,ite_eq_right away,eq]
    by_cases must : NeedsStrong mid Y
    · exact (step.valid Y ym must).1
    · have no : ¬NeedsStrong initial Y := by simpa only [NeedsStrong,step.same] using must
      rw [step.keep Y ym (fun h=>(no h).elim),step.same]
      apply policy Y ym
      simpa only [eq,step.same] using cyclic
  · intro Y ym must
    have need : NeedsStrong mid Y := by simpa only [NeedsStrong,eq] using must
    have untouched : Y∉M := fun h=>(Nat.not_lt_of_ge need.2.2) (mem_filter.mp (show Y∈shortSwitches mid from h)).2.2.2
    simpa only [StrongChoice,book Y ym,ite_eq_right untouched,eq] using step.valid Y ym need

#print axioms self_booking
#print axioms book_short_shells
#print axioms first_is_kept
end LeanCH.BR.LowShellCycleSelection
