import checkpoints.shen_extension.WidePrimaryPayment
import checkpoints.shen_extension.CyclePaymentSchedule

namespace LeanCH.BR.LowShellCycleSelection
open Finset BRq2 BRq3 BR45 BRsGen ExteriorPacking PhysicalCycleStock

theorem primary_widths {D V q r target cap C} (free : QFree D V q) (reg : OutEq r D V)
    {sel : Selection D V q r 3 (3*r)} (short : PrimaryShort sel cap C)
    (ready : RoutingRoom q r V.card target) :
    (exterior D V C).card=r-1 ∨ (exterior D V C).card=r := by
  have hi := paid_wide free reg short ready
  obtain ⟨Y,yc,same⟩ := mem_image.mp short.1
  have n := sel.length _ (sel.assigned Y yc)
  have roots := sel.rooted _ (sel.assigned Y yc)
  rw [same] at n roots
  obtain ⟨x,xm⟩ := card_pos.mp (by omega : 0<C.card)
  have cx := roots x xm
  have row := card_le_card (inter_subset_left : exterior D V C∩outN D V x⊆exterior D V C)
  rw [←row_exterior cx,card_erase_of_mem (outN_mono cx.sub x (successor_mem cx)),reg x (cx.sub xm)] at row
  omega

structure NarrowMark {D V q r} (sel : Selection D V q r 3 (3*r)) (cap : ℕ) (C : Finset ℕ) : Prop where
  short : PrimaryShort sel cap C
  widths : (exterior D V C).card=r-1 ∨ (exterior D V C).card=r

theorem narrow_from_input {p : CHRuleCatalog.Input} {target g mid top cap} (bad : CHRuleCatalog.Bad p)
    (room : PrimaryRoom (CHRuleCatalog.cutoff p) p.s p.n target g mid top cap) :
    ∃F,(∀a b,F a b=true → p.D a b=true) ∧ OutEq p.s F (range p.n) ∧
      ∃t : Selection F (range p.n) (CHRuleCatalog.cutoff p) p.s 3 (3*p.s),∃C,NarrowMark t cap C := by
  obtain ⟨F,sub,reg,t,C,h⟩ := marked_from_input bad room
  have ff := qfree_sub sub (qfree_of_noShort bad.loopless bad.missing)
  exact ⟨F,sub,reg,t,C,h,primary_widths ff reg h (by simpa only [card_range] using room.route)⟩

structure OnNarrowPrimary (p : CHRuleCatalog.Input) : Prop where
  apply_room : ∀target g mid top cap,PrimaryRoom (CHRuleCatalog.cutoff p) p.s p.n target g mid top cap →
    ∃F,(∀a b,F a b=true → p.D a b=true) ∧ OutEq p.s F (range p.n) ∧
      ∃t : Selection F (range p.n) (CHRuleCatalog.cutoff p) p.s 3 (3*p.s),∃C,NarrowMark t cap C

theorem narrow_on_bad {p : CHRuleCatalog.Input} (bad : CHRuleCatalog.Bad p) : OnNarrowPrimary p :=
  ⟨fun _ _ _ _ _ room=>narrow_from_input bad room⟩

attribute [aesop safe forward (immediate := [bad,room]) (rule_sets := [CHGraphFamilies])] narrow_from_input
attribute [aesop safe forward (immediate := [bad]) (rule_sets := [CHGraphFamilies])] narrow_on_bad
attribute [aesop safe forward (immediate := [free,reg,short,ready]) (rule_sets := [CHGraphFamilies])] primary_widths
ch_family_split_result primary_widths

#print axioms primary_widths
#print axioms narrow_on_bad
end LeanCH.BR.LowShellCycleSelection
