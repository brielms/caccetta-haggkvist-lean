import checkpoints.shen_extension.NativePowerBank

namespace LeanCH.BR.FragmentScoreEquality
open Finset BRq2 BRq3 CHRuleCatalog BypassDegreeDescent

/-- The child uses only native incidences, with a bijective record
of which original head each of its labels represents. -/
structure HeadBankChild (p : Input) : Prop where
  witness : ∃y∈range p.n,∃c : Input,∃e : ℕ→ℕ,Child p c ∧ Bad c ∧
    c.n=(outN p.D (range p.n) y).card ∧ c.n<p.n ∧ c.s<p.s ∧ cutoff c≤cutoff p ∧
    (∀i<c.n,e i∈outN p.D (range p.n) y) ∧ (∀v∈outN p.D (range p.n) y,∃i<c.n,e i=v) ∧
    (∀i<c.n,∀j<c.n,e i=e j → i=j) ∧ ∀i<c.n,∀j<c.n,c.D i j=p.D (e i) (e j)

@[ch_numeric_guard] def CanPeel (n r q : ℕ) : Prop :=
  3≤q ∧ n≤3*r ∧ ∃d∈Ico 1 r,d+n≤3*r+2 ∧ r≤q*d

instance {n r q} : Decidable (CanPeel n r q) := by unfold CanPeel; infer_instance

theorem bank_child {p : Input} (bad : Bad p) (inside : CanPeel p.n p.s (cutoff p)) :
    HeadBankChild p := by
  obtain ⟨hq,order,d,dm,quota,fit⟩ := inside
  obtain ⟨pos,less⟩ := mem_Ico.mp dm
  have free := qfree_of_noShort bad.loopless bad.missing
  have native v (vm : v∈range p.n) := Compose.FloorSix.out_card bad.degree (mem_range.mp vm)
  obtain ⟨_,_,y,ym,_,_,low,paid⟩ := native_bank free (nonempty_range_iff.mpr bad.order.ne') native hq
    (by rwa [card_range])
  rw [card_range] at low paid
  let H := outN p.D (range p.n) y
  have floor : p.s≤H.card := native y ym
  have one := ReachLedger.ball_one free (by omega) ym
  change (ball p.D (range p.n) y 1).card=H.card+1 at one
  have growing := card_le_card (ball_mono_radius (D:=p.D) (W:=range p.n) (u:=y) (by decide : 1≤2))
  let t := min (p.s-1) (d+(H.card-p.s))
  have tl : 0<t ∧ t<p.s := by dsimp [t]; omega
  have safe : H.card≤cutoff p*t := by
    have front := Nat.mul_le_mul_right (p.s-1) (show 2≤cutoff p by omega)
    have back := Nat.mul_le_mul_right (H.card-p.s) (show 1≤cutoff p by omega)
    rw [Nat.one_mul] at back
    by_cases le : p.s-1≤d+(H.card-p.s)
    · rw [show t=p.s-1 from min_eq_left le]
      exact le_trans (by omega : H.card≤2*(p.s-1)) front
    · rw [show t=d+(H.card-p.s) from min_eq_right (by omega),Nat.mul_add]
      omega
  have degree z (zm : z∈H) : t≤(outN p.D H z).card := by
    have bill := paid z zm
    change 2*p.s+H.card+2≤p.n+(outN p.D H z).card at bill
    dsimp [t]; omega
  obtain ⟨c,e,edge,rank,n,cut,into,onto,inj,arcs⟩ := host_child p tl.1 (by omega)
    (card_pos.mp (show 0<H.card by omega)) safe (free.mono_set outN_subset) degree
  exact ⟨y,ym,c,e,edge,bad_child bad edge,n,by omega,by omega,cut,into,onto,inj,arcs⟩

theorem least_cannot_peel {p : Input} (bad : Bad p) (least : MinimalChild p) :
    ¬CanPeel p.n p.s (cutoff p) := by
  intro fit
  obtain ⟨_,_,c,_,edge,_,_,_,less,cut,_⟩ := (bank_child bad fit).witness
  obtain ⟨le,rank⟩ := least.compare c edge
  have := rank (le_antisymm le cut)
  omega

attribute [aesop safe forward (immediate := [bad,inside]) (rule_sets := [CHGraphFamilies])] bank_child
attribute [aesop safe forward (immediate := [bad,least]) (rule_sets := [CHGraphFamilies])] least_cannot_peel
attribute [aesop safe forward (immediate := [self]) (rule_sets := [CHGraphFamilies])] HeadBankChild.witness
ch_family_split_result HeadBankChild.witness
#print axioms bank_child
#print axioms least_cannot_peel
end LeanCH.BR.FragmentScoreEquality