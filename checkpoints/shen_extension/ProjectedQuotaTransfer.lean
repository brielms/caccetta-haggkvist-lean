import checkpoints.shen_extension.PrimaryContactSearch
import checkpoints.shen_extension.SevenDegreeCapstoneEntry

namespace LeanCH.BR.ProjectedQuotaTransfer
open CHRuleCatalog

/-- A completed degree slice, independent of order and the source family. -/
structure ClosedQuota (d : ℕ) : Prop where
  positive : 0<d
  exclude : ∀p : Input,Bad p → p.s=d → False

theorem verify_projection {d : ℕ} {P : Input → Prop}
    (projection : ∀{p : Input},Bad p → p.s=d → P p) (positive : 0<d)
    (check : ∀p : Input,Bad p → p.s=d → P p → False) : ClosedQuota d :=
  ⟨positive,fun p bad hd => check p bad hd (projection bad hd)⟩

theorem ClosedQuota.literal {d} (cert : ClosedQuota d) {m} {G : CH.Digraph} (hm : 0<m)
    (loop : CH.Loopless G m) (deg : CH.MinOutdegreeAtLeast G m d) :
    CH.HasDirectedCycleAtMost G m (CH.ceilDiv m d) := by
  by_contra missing
  exact cert.exclude ⟨m,d,G⟩ ⟨hm,cert.positive,loop,deg,missing⟩ rfl

/-- Every source can spend its excess degree to reach a solved quota. The
numeric exclusion holds on each repaired input using that input's cutoff. -/
theorem extend_quota {p : Input} {d} (bad : Bad p) (cert : ClosedQuota d) :
    d≤p.s → d*cutoff p+p.s<p.n+d := by
  intro dr
  by_contra! fit
  have qpos : 0<cutoff p := (remaining_from_run p bad).1.trans_lt' (by decide)
  apply bad.missing
  apply SevenDegreeCapstoneEntry.transfer cert.positive qpos _ p.D bad.order dr fit bad.loopless bad.degree
  intro m G hm cap loop deg
  obtain ⟨cycle,ok,len⟩ := cert.literal hm loop deg
  refine ⟨cycle,ok,len.trans ?_⟩
  unfold CH.ceilDiv
  apply Nat.le_of_lt_succ
  apply (Nat.div_lt_iff_lt_mul cert.positive).mpr
  rw [Nat.succ_mul,Nat.mul_comm (cutoff p) d]
  omega

@[ch_numeric_guard] def QuotaWindow (n r q d : ℕ) := d≤r ∧ n+d≤d*q+r
instance {n r q d} : Decidable (QuotaWindow n r q d) := by unfold QuotaWindow; infer_instance

theorem quota_window_missed {p : Input} {d} (bad : Bad p) (cert : ClosedQuota d) :
    ¬QuotaWindow p.n p.s (cutoff p) d :=
  fun fit=>Nat.not_lt_of_ge fit.2 (extend_quota bad cert fit.1)

theorem next_degree {p : Input} {d} (bad : Bad p) (cert : ClosedQuota d) (floor : d≤p.s) :
    d+1≤p.s := by
  have distinct : p.s≠d := cert.exclude p bad
  omega

attribute [aesop safe forward (immediate := [bad,cert,floor]) (rule_sets := [CHGraphFamilies])] next_degree
attribute [aesop safe forward (immediate := [bad,cert]) (rule_sets := [CHGraphFamilies])] quota_window_missed
attribute [aesop safe forward (immediate := [bad,cert]) (rule_sets := [CHGraphFamilies])] extend_quota
#print axioms extend_quota
end LeanCH.BR.ProjectedQuotaTransfer
