import checkpoints.shen_extension.UniformFragmentFamily
import checkpoints.shen_extension.MinimalPowerDescent

namespace LeanCH.BR.FragmentScoreEquality
open Finset BRq2 BRq3 BR45 CHRuleCatalog BypassDegreeDescent ProjectedQuotaTransfer

/-- Lift the guaranteed second-ball size to the original graph before
building the child. Its rows keep exactly the original two-step labels. -/
theorem physical_power {p : Input} (bad : Bad p) (source : UniformSource p)
    {d : ℕ} (pos : 0<d) (quota : d≤2*p.s)
    (kpos : 0<CH.ceilDiv p.n d) (time : CH.ceilDiv p.n d*2≤cutoff p) :
    ∃c : Input, Child p c ∧ Bad c ∧ c.n=p.n ∧ c.s=d ∧ cutoff c=CH.ceilDiv p.n d ∧
      ∀x∈range p.n,outN c.D (range p.n) x=(ball p.D (range p.n) x 2).erase x := by
  obtain ⟨D,sub,_,_,scores⟩ := source.witness
  have growth x (xm : x∈range p.n) : d+1≤(ball p.D (range p.n) x 2).card := by
    have size := (scores x xm).2
    have lift := card_le_card (ball_sub (W:=range p.n) (u:=x) (k:=2) sub)
    omega
  obtain ⟨edge,rows⟩ := MinimalPowerDescent.power_edge bad pos kpos time growth
  exact ⟨_,edge,bad_child bad edge,rfl,rfl,rfl,rows⟩

@[ch_numeric_guard] def UniformReduction (n r q floor : ℕ) : Prop :=
  UniformWindow n r q floor ∧ 0<2*r ∧ 0<CH.ceilDiv n (2*r) ∧ CH.ceilDiv n (2*r)*2≤q

instance {n r q floor} : Decidable (UniformReduction n r q floor) := by
  unfold UniformReduction; infer_instance

/-- This excludes the minimum-cutoff source from the numerical region.
An arbitrary source there can still have a bad lower-cutoff child. -/
theorem least_exclusion {p : Input} (bad : Bad p) (least : MinimalChild p) :
    ¬UniformReduction p.n p.s (cutoff p) projectionFloor := by
  rintro ⟨win,pos,kpos,time⟩
  obtain ⟨c,edge,_,_,_,cut,_⟩ := physical_power bad (uniform_at_completed bad win) pos le_rfl kpos time
  have back := (least.compare c edge).1
  rw [cut] at back
  omega

theorem original_edge {p : Input} (bad : Bad p)
    (win : UniformReduction p.n p.s (cutoff p) projectionFloor) :
    ∃c : Input,Child p c ∧ Bad c ∧ c.n=p.n ∧ c.s=2*p.s ∧ cutoff c<cutoff p ∧
      ∀x∈range p.n,outN c.D (range p.n) x=(ball p.D (range p.n) x 2).erase x := by
  obtain ⟨src,pos,kpos,time⟩ := win
  obtain ⟨c,edge,bc,order,degree,cut,rows⟩ := physical_power bad
    (uniform_at_completed bad src) pos le_rfl kpos time
  exact ⟨c,edge,bc,order,degree,by omega,rows⟩

attribute [aesop safe forward (immediate := [bad,least]) (rule_sets := [CHGraphFamilies])] least_exclusion
attribute [aesop safe forward (immediate := [bad,win]) (rule_sets := [CHGraphFamilies])] original_edge
ch_family_split_result original_edge
#print axioms physical_power
#print axioms least_exclusion
#print axioms original_edge
end LeanCH.BR.FragmentScoreEquality