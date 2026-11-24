import checkpoints.shen_extension.GuardedProfileBudget

namespace LeanCH.BR.InheritedProfileWindow
open Finset CHRuleCatalog GuardedProfileBudget

/-- Every punctured-graph quota used in the proofs has already been supplied
at this cutoff. The resulting order bound works on any nonempty carrier. -/
theorem carrier_bound {q d h K} (known : ∀t∈K,BypassRepair.NoHost q t)
    (cut : 5≤q) (two : 2≤d) (room : d≤2*q) (cover : Covers q d (2*d) h K)
    (paid : 3*d≤h+2) : GuardedFamilyRules.OrderBound q d (2*d+h-1) := by
  refine ⟨by omega,fun D V free live degree => ?_⟩
  have order := mixed_from_quotas free degree live known cut two room cover paid
  omega

/-- Keeping a smaller quota d allows up to r−d vertices to be discarded. -/
@[ch_numeric_guard] def Fits (n r q : ℕ) (K : Finset ℕ) : Prop :=
  ∃d∈Icc 2 r, Window (n-(r-d)) d q K

instance (n r q : ℕ) (K : Finset ℕ) : Decidable (Fits n r q K) := by
  unfold Fits
  infer_instance

theorem excludes {p : Input} (bad : Bad p) (lib : QuotaLibrary) :
    ¬Fits p.n p.s (cutoff p) lib.ranks := by
  rintro ⟨d,range,window⟩
  obtain ⟨_two,le⟩ := mem_Icc.mp range
  obtain ⟨cut,two,room,cover⟩ := window
  have pay := height_bills (p.n-(p.s-d)) d
  have order := carrier_bound (quotas_from_exclusions bad lib.excluded) cut two room cover pay.1
  exact GuardedFamilyRules.forbidden bad order ⟨le_rfl,le,by omega⟩

theorem verified {p : Input} (bad : Bad p) :
    ¬Fits p.n p.s (cutoff p) verifiedQuotas.ranks := excludes bad _

theorem direct {n r q K} (inside : Window n r q K) : Fits n r q K := by
  exact ⟨r,mem_Icc.mpr ⟨inside.2.1,le_rfl⟩,by simpa using inside⟩

theorem literal {D n r} (hn : 0<n) (hr : 0<r) (loopless : CH.Loopless D n)
    (degree : CH.MinOutdegreeAtLeast D n r)
    (inside : Fits n r (CH.ceilDiv n r) verifiedQuotas.ranks) :
    CH.HasDirectedCycleAtMost D n (CH.ceilDiv n r) := by
  by_contra missing
  exact verified (p:=⟨n,r,D⟩) ⟨hn,hr,loopless,degree,missing⟩ inside

attribute [aesop safe forward (immediate := [bad]) (rule_sets := [CHGraphFamilies])] verified
#print axioms carrier_bound
#print axioms excludes
#print axioms literal
end LeanCH.BR.InheritedProfileWindow
