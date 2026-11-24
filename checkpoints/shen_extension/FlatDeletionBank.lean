import checkpoints.shen_extension.ShellDeficitTransfer
import checkpoints.shen_extension.HalfLawSupply

namespace LeanCH.BR.FragmentScoreEquality
open Finset BRq2 BRq3 BR45 BRsGen BypassBankReplay

/-- Saturation of the mixed score identifies the two degrees at every
label. No minimum degree or regularity hypothesis is required. -/
theorem balanced_of_no_cheap {D U q} (free : QFree D U q) (time : 3≤q)
    (none : ¬∃v∈U,(outN D U v).card+(ball D U v 2).card<U.card) :
    ∀v∈U,(inN D U v).card=(outN D U v).card := by
  classical
  have le v (vm : v∈U) : (inN D U v).card≤(outN D U v).card := by
    have low := not_lt.mp (fun h=>none ⟨v,vm,h⟩)
    have := ReachLedger.parent_cap (i:=2) free time vm
    omega
  exact (sum_eq_sum_iff_of_le le).mp (Compose.ThinRigid.sum_out_eq_sum_in D U).symm

/-- Erasing the one marked row: the new small rows are exactly its
parents which were tight. The same labels occur on both sides. -/
theorem erased_low_rows {D U t x} (xu : x∈U)
    (other : ∀v∈U,v≠x → t≤(outN D U v).card) :
    (U.erase x).filter (fun v=>(outN D (U.erase x) v).card<t)=
      (inN D U x).filter (fun v=>v≠x ∧ (outN D U v).card=t) := by
  classical
  ext v
  simp only [mem_filter,mem_erase,mem_inN,outN_erase]
  constructor
  · rintro ⟨⟨ne,vm⟩,low⟩
    have floor := other v vm ne
    have hit : x∈outN D U v := by
      by_contra off
      rw [erase_eq_of_notMem off] at low
      omega
    have := card_erase_add_one hit
    exact ⟨⟨vm,(mem_outN.mp hit).2⟩,ne,by omega⟩
  · rintro ⟨⟨vm,vx⟩,ne,deg⟩
    have := card_erase_add_one (mem_outN.mpr ⟨xu,vx⟩ : x∈outN D U v)
    exact ⟨⟨ne,vm⟩,by omega⟩

/-- A local witness on the erased set suffices; its proof may come
from any tight-row supplier, on these original labels. -/
theorem cheap_of_erased_count {D U q t x} (free : QFree D U q) (cut : 3≤q)
    (xu : x∈U) (other : ∀v∈U,v≠x → t≤(outN D U v).card)
    (many : (outN D U x).card<((U.erase x).filter (fun v=>(outN D (U.erase x) v).card<t)).card) :
    ∃v∈U,(outN D U v).card+(ball D U v 2).card<U.card := by
  by_contra no
  have deg := balanced_of_no_cheap free cut no x xu
  rw [erased_low_rows xu other] at many
  have le := card_le_card (filter_subset (fun v=>v≠x ∧ (outN D U v).card=t) (inN D U x))
  omega

theorem lone_alternative {q r} {X : ShenMinimumOrder.Source q r} {m : Cell}
    (cut : 3≤q) (rank : 3≤r) (cell : Marked X m) (lone : LoneBlocked X m) :
    MarkedRootAlternative X.D (X.V\m.bank) (r-1) m.x := by
  have carrier := carrier_of_lone cell lone
  by_cases eq : q=3
  · exact inspect_short_carrier carrier cut (room_of_bank cell eq)
  · refine Or.inl (cheap_on_positive carrier.free (by omega) ⟨_,cell.xu⟩ ?_)
    intro z zm
    by_cases same : z=m.x
    · subst z
      have := cell.deficit
      omega
    · have := carrier.other z zm same
      omega

/-- In the second orientation both the cutoff and the parent bank
are determined on the original survivor set. -/
structure FlatErasure (D : CH.Digraph) (U : Finset ℕ) (q t x : ℕ) : Prop where
  cutoff_eq : q=3
  balanced : ∀v∈U,(inN D U v).card=(outN D U v).card
  bank : (U.erase x).filter (fun v=>(outN D (U.erase x) v).card<t)=
    (inN D U x).filter (fun v=>v≠x ∧ (outN D U v).card=t)
  cap : ((U.erase x).filter (fun v=>(outN D (U.erase x) v).card<t)).card<t

theorem flat_on_lone {q r} {X : ShenMinimumOrder.Source q r} {m : Cell}
    (cut : 3≤q) (rank : 3≤r) (cell : Marked X m) (lone : LoneBlocked X m)
    (no : ¬∃v∈X.V\m.bank,(outN X.D (X.V\m.bank) v).card+(ball X.D (X.V\m.bank) v 2).card<(X.V\m.bank).card) :
    FlatErasure X.D (X.V\m.bank) q (r-1) m.x := by
  have carr := carrier_of_lone cell lone
  have bal := balanced_of_no_cheap carr.free cut no
  have bank := erased_low_rows cell.xu carr.other
  have cp := not_lt.mp (fun h=>no (cheap_of_erased_count carr.free cut cell.xu carr.other h))
  have deg := cell.deficit
  refine ⟨?_,bal,bank,by omega⟩
  by_contra ne
  apply no
  apply cheap_on_positive carr.free (by omega) ⟨_,cell.xu⟩
  intro v vm
  by_cases eq : v=m.x
  · subst v
    omega
  · have := carr.other v vm eq
    omega

attribute [aesop safe forward (immediate := [cut,rank,cell,lone]) (rule_sets := [CHGraphFamilies])] lone_alternative
attribute [aesop safe forward (immediate := [cut,rank,cell,lone,no]) (rule_sets := [CHGraphFamilies])] flat_on_lone
attribute [aesop safe forward (immediate := [self]) (rule_sets := [CHGraphFamilies])] FlatErasure.cutoff_eq FlatErasure.cap
attribute [aesop safe forward (immediate := [free,cut,xu,other,many]) (rule_sets := [CHGraphFamilies])] cheap_of_erased_count

#print axioms balanced_of_no_cheap
#print axioms erased_low_rows
#print axioms cheap_of_erased_count
#print axioms lone_alternative
#print axioms flat_on_lone
end LeanCH.BR.FragmentScoreEquality
