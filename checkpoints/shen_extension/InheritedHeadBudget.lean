import checkpoints.shen_extension.FragmentHeadTransfer

namespace LeanCH.BR.FragmentScoreEquality
open Finset BRq2 BRq3 BR45 BRsGen BypassRepair GuardedLayerGrowth GuardedProfileBudget
open CHRuleCatalog ProjectedQuotaTransfer

/-- A lower order only increases the credit available for the very same
ball floor. The proof applies on arbitrary carriers and thins all rows
on that carrier before marking any of their heads. -/
theorem head_order_bound {q d h floor} (known : ∀t,t<floor → NoHost q t)
    (window : HeadWindow (2*h) d q floor) : GuardedFamilyRules.OrderBound q d (2*h) := by
  have half : (2*h+1)/2=h := by omega
  unfold HeadWindow at window
  rw [half] at window
  obtain ⟨cut,rank,room,pressure,space,many,width,heights,tests⟩ := window
  refine ⟨by rcases width with eq|eq <;> omega,?_⟩
  intro D V free live degree
  by_contra! cheap
  obtain ⟨E,sub,reg⟩ := exists_outEq degree
  have safe := qfree_sub sub free
  have tall := head_transfer (k:=q-3) safe reg known tests cut rank room
    (by omega) (by omega) space many cheap width
    (fun x xm=>third safe reg xm (second_floor safe (by omega) reg (by omega) room xm)
      (fun t tm=>known t (mem_range.mp tm)) heights)
  have := card_ge_of_two_balls (i:=3) (j:=3) safe cut tall tall live
  omega

/-- A descendant may spend excess degree on deletion and reuse a
smaller quota's two-radius argument at its own cutoff. -/
@[ch_numeric_guard] def LowerHeadWindow (n r q floor : ℕ) : Prop :=
  ∃d∈Icc 2 (min r (2*q)), ∃h∈Icc (3*d-1) (3*d),
    n+d≤2*h+r ∧ HeadWindow (2*h) d q floor

instance {n r q floor} : Decidable (LowerHeadWindow n r q floor) := by
  unfold LowerHeadWindow; infer_instance

theorem lower_head_window {p : Input} {floor} (bad : Bad p)
    (known : ∀t,t<floor → NoHost (cutoff p) t) : ¬LowerHeadWindow p.n p.s (cutoff p) floor := by
  rintro ⟨d,dm,h,_,width,win⟩
  exact GuardedFamilyRules.forbidden bad (head_order_bound known win)
    ⟨le_rfl,(mem_Icc.mp dm).2.trans (min_le_left ..),width⟩

theorem inherited_at_source {p : Input} (bad : Bad p) :
    ¬LowerHeadWindow p.n p.s (cutoff p) projectionFloor :=
  lower_head_window bad (available_lower_hosts bad)

attribute [aesop safe forward (immediate := [known,window]) (rule_sets := [CHGraphFamilies])] head_order_bound
attribute [aesop safe forward (immediate := [bad,known]) (rule_sets := [CHGraphFamilies])] lower_head_window
attribute [aesop safe forward (immediate := [bad]) (rule_sets := [CHGraphFamilies])] inherited_at_source
#print axioms head_order_bound
#print axioms inherited_at_source
end LeanCH.BR.FragmentScoreEquality