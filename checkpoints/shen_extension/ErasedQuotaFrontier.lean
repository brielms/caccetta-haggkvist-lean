import checkpoints.shen_extension.ShortRowHeadExit

namespace LeanCH.BR.FragmentScoreEquality
open Finset BRq2 BRq3 BR45 BRsGen BypassBankReplay BypassRepair CHRuleCatalog BypassDegreeDescent

/-- At the flat orientation, puncture at the original exceptional row.
The result violates the local tight-row bound on that actual graph. -/
structure PuncturedQuota (D : CH.Digraph) (U : Finset ℕ) (q t x : ℕ) : Prop where
  order : (U.erase x).card+1=q*t
  quota : ∀v∈U.erase x,t-1≤(outN D (U.erase x) v).card
  scarce : ((U.erase x).filter (fun v=>(outN D (U.erase x) v).card=t-1)).card<t

theorem punctured_quota {D U q t x} (carrier : OneShortCarrier D U q t x)
    (flat : FlatErasure D U q t x) (room : U.card≤3*t) (pos : 0<t)
    (no : ¬∃v∈U,(outN D U v).card+(ball D U v 2).card<U.card) :
    PuncturedQuota D U q t x := by
  have cut := flat.cutoff_eq
  obtain ⟨y,ym,_,bill⟩ := (erased_witness carrier.free (by omega : 3≤q)
    (singleton_subset_iff.mpr carrier.marked) carrier.remaining).resolve_left no
  have paid := carrier.other y (mem_sdiff.mp ym).1 (by simpa only [mem_singleton] using (mem_sdiff.mp ym).2)
  have cap := card_le_card (outN_subset : outN D {x} y⊆{x})
  rw [card_singleton] at cap
  have size : U.card=3*t := by omega
  have count := card_erase_add_one carrier.marked
  refine ⟨by rw [cut]; omega,?_,?_⟩
  · intro v vm
    obtain ⟨ne,vu⟩ := mem_erase.mp vm
    have := carrier.other v vu ne
    rw [outN_erase]
    by_cases hit : x∈outN D U v
    · have := card_erase_add_one hit
      omega
    · rw [erase_eq_of_notMem hit]
      omega
  · have sub : (U.erase x).filter (fun v=>(outN D (U.erase x) v).card=t-1)⊆
        (U.erase x).filter (fun v=>(outN D (U.erase x) v).card<t) := by
      intro v vm
      obtain ⟨live,eq⟩ := mem_filter.mp vm
      exact mem_filter.mpr ⟨live,by omega⟩
    exact lt_of_le_of_lt (card_le_card sub) flat.cap

@[aesop safe forward (immediate := [cell,flat,carrier,no,rank]) (rule_sets := [CHGraphFamilies])]
theorem actual_quota {q r} {X : ShenMinimumOrder.Source q r} {m : Cell}
    (cell : Marked X m) (flat : FlatErasure X.D (X.V\m.bank) q (r-1) m.x)
    (carrier : OneShortCarrier X.D (X.V\m.bank) q (r-1) m.x)
    (no : ¬∃v∈X.V\m.bank,(outN X.D (X.V\m.bank) v).card+(ball X.D (X.V\m.bank) v 2).card<(X.V\m.bank).card)
    (rank : 3≤r) : PuncturedQuota X.D (X.V\m.bank) q (r-1) m.x :=
  punctured_quota carrier flat (room_of_bank cell flat.cutoff_eq) (by omega) no

theorem excluded_tight_law {D U q t x} (free : QFree D U q) (pos : 0<t)
    (packet : PuncturedQuota D U q t x) : ¬TightRow.TightLaw q (t-1) := by
  intro law
  have size := packet.order
  have small := packet.scarce
  have add : t-1+1=t := by omega
  have := law D (U.erase x) (free.mono_set (erase_subset ..)) (by rwa [add]) packet.quota
  omega

@[aesop safe forward (immediate := [carrier,packet,rank]) (rule_sets := [CHGraphFamilies])]
theorem lost_lower_law {D U q r x} (carrier : OneShortCarrier D U q (r-1) x)
    (packet : PuncturedQuota D U q (r-1) x) (rank : 3≤r) : ¬TightRow.TightLaw q (r-2) := by
  have same : r-1-1=r-2 := by omega
  exact same ▸ excluded_tight_law carrier.free (by omega) packet

/-- All tested quotas refer to one physical head bank, including the
endpoint where the exceptional row must itself be a head. -/
structure ParentBankCeiling (D : CH.Digraph) (U : Finset ℕ) (q t x v : ℕ) : Prop where
  at_quota : ∀d,0<d → d≤t → (outN D U v).card≤q*d →
    t+2*(outN D U v).card+2≤U.card+d ∧
    (U.card+d=t+2*(outN D U v).card+2 → x∈outN D U v)

theorem bank_ceiling {D U q t x v} (packet : ShortBankLimit D U q t x v)
    (lower : ∀d,0<d → d≤t → NoHost q d) : ParentBankCeiling D U q t x v := by
  refine ⟨?_⟩
  intro d dp dt fits
  have test := packet.bound d (lower d dp dt) fits
  constructor
  · by_contra too
    have eq := (test (by omega)).2
    omega
  · intro eq
    exact (test (by omega)).1

@[aesop safe forward (immediate := [least,bad,packet]) (rule_sets := [CHGraphFamilies])]
theorem minimal_ceiling {p : Input} {D U x v} (least : MinimalChild p) (bad : Bad p)
    (packet : ShortBankLimit D U (cutoff p) (p.s-1) x v) :
    ParentBankCeiling D U (cutoff p) (p.s-1) x v := by
  have := (remaining_from_run p bad).1
  exact bank_ceiling packet fun d dp dt=>MinimalPowerDescent.lower_host least (by omega) dp (by omega)

attribute [aesop safe forward (immediate := [self]) (rule_sets := [CHGraphFamilies])] PuncturedQuota.order PuncturedQuota.quota PuncturedQuota.scarce
attribute [aesop safe forward (immediate := [packet,lower]) (rule_sets := [CHGraphFamilies])] bank_ceiling

#print axioms punctured_quota
#print axioms actual_quota
#print axioms excluded_tight_law
#print axioms lost_lower_law
#print axioms minimal_ceiling
end LeanCH.BR.FragmentScoreEquality
