import checkpoints.shen_extension.ErasedPowerWitness
import checkpoints.shen_extension.ShortfallBankReplay

namespace LeanCH.BR.FragmentScoreEquality
open Finset BRq2 BRq3 BR45 BRsGen BypassBankReplay

/-- Preserve the deficient row and the retained graph as arguments so the
same test can consume a different erasure or a different marked row. -/
structure OneShortCarrier (D : CH.Digraph) (U : Finset ℕ) (q t x : ℕ) : Prop where
  free : QFree D U q
  marked : x∈U
  other : ∀v∈U,v≠x → t≤(outN D U v).card
  remaining : (U\{x}).Nonempty

@[aesop safe forward (immediate := [cell,lone]) (rule_sets := [CHGraphFamilies])]
theorem carrier_of_lone {q r} {X : ShenMinimumOrder.Source q r} {m : Cell}
    (cell : Marked X m) (lone : LoneBlocked X m) :
    OneShortCarrier X.D (X.V\m.bank) q (r-1) m.x := by
  obtain ⟨y,ym,ne,_⟩ := lone.unpaid
  exact ⟨X.free.mono_set sdiff_subset,cell.xu,lone.paid_elsewhere,
    y,mem_sdiff.mpr ⟨ym,by simpa only [mem_singleton] using ne⟩⟩

def MarkedRootAlternative (D : CH.Digraph) (U : Finset ℕ) (t x : ℕ) : Prop :=
  (∃v∈U,(outN D U v).card+(ball D U v 2).card<U.card) ∨
  (¬ ∃v∈U,(outN D U v).card+(ball D U v 2).card<U.card) ∧
  ∃y∈U,y≠x ∧ D y x=true ∧ (outN D U y).card=t ∧
    ∀z∈outN D U x,D y z≠true → ∃j∈U,j≠x ∧ D y j=true ∧ D j z=true

@[aesop safe forward (immediate := [carrier,cut,room]) (rule_sets := [CHGraphFamilies])]
theorem inspect_short_carrier {D U q t x} (carrier : OneShortCarrier D U q t x)
    (cut : 3≤q) (room : U.card≤3*t) : MarkedRootAlternative D U t x := by
  classical
  by_cases low : ∃v∈U,(outN D U v).card+(ball D U v 2).card<U.card
  · exact Or.inl low
  · exact Or.inr ⟨low,(lone_fork carrier.free cut carrier.marked carrier.other carrier.remaining room).resolve_left low⟩

@[aesop safe forward (immediate := [cell,three]) (rule_sets := [CHGraphFamilies])]
theorem room_of_bank {q r} {X : ShenMinimumOrder.Source q r} {m : Cell}
    (cell : Marked X m) (three : q=3) : (X.V\m.bank).card≤3*(r-1) := by
  subst q
  rw [card_sdiff_of_subset cell.sub,cell.size]
  omega

ch_family_split_predicate MarkedRootAlternative

attribute [aesop safe forward (immediate := [free,cut,sub,live]) (rule_sets := [CHGraphFamilies])] erased_witness

#print axioms carrier_of_lone
#print axioms inspect_short_carrier
#print axioms room_of_bank
end LeanCH.BR.FragmentScoreEquality
