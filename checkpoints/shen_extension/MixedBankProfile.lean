import checkpoints.shen_extension.MixedBankScore

namespace LeanCH.BR.MixedBankProfile
open Finset BRq2 BRq3 BR45 BRsGen ExteriorPacking ShellCycleSupply RetainedLayerCapacity GuardedLayerGrowth

/-- Third-ball sizes above the equality profile cannot fit a fourth ball
at the lower floor. Each count is on the same punctured third ball. -/
def Room (r : ℕ) : Prop :=
  ∀a∈Icc (2*r) (3*r+2),
    let m := 3*r+1
    let h := a-1
    m*(m+1)<(m-h)*23+(h-r)*(2*(r+6))+r*(4*r)
instance (r : ℕ) : Decidable (Room r) := by unfold Room; infer_instance

theorem uniform {D V q r} (free : QFree D V q) (reg : OutEq r D V) (hq : 7≤q)
    (hr : 7≤r) (fit : r≤q+1) (bounds : FourthRoom r) (cap : MixedBankScore.Capacity r)
    (room : Room r) (host : V.card≤7*r) :
    ∀u∈V,2*r+1≤(ball D V u 2).card ∧ (ball D V u 3).card=3*r+1 ∧ (ball D V u 4).card=4*r := by
  have near v (vm : v∈V) := second_floor free (by omega : 4≤q) reg (by omega : 0<r) (by omega) vm
  have third v (vm : v∈V) := diagonal_third (k:=q-2) free vm reg hq (by omega) fit (by omega) (by omega) bounds.1
  have fourth v (vm : v∈V) := diagonal_fourth free hq (by omega) fit bounds reg vm
  let score := fun u=>(ball D V u 3).card+(ball D V u 4).card
  have floor := MixedBankScore.low_score_floor free reg hq hr fit bounds cap host
  have totals := ConsecutiveShellBanks.remote_capacity free (show 3+4≤q by omega)
  have exactScores : (∑_v∈V,(7*r+1))=∑v∈V,score v := by
    apply le_antisymm (sum_le_sum floor)
    rw [sum_const_nat (fun _ _=>rfl)]
    exact (Nat.le_add_left _ _).trans (totals.trans (Nat.mul_le_mul_left _ (by omega)))
  have flat v (vm : v∈V) : (ball D V v 3).card+(ball D V v 4).card=7*r+1 :=
    ((sum_eq_sum_iff_of_le floor).mp exactScores v vm).symm
  have upper v (vm : v∈V) : (ball D V v 3).card≤3*r+1 := by
    have sum := flat v vm
    have min4 := fourth v vm
    have min2 := near v vm
    have sub := card_le_card (ball_mono_radius (D:=D) (W:=V) (u:=v) (by decide : 2≤3))
    by_contra! hi
    have mid : (ball D V v 3).card=3*r+2 := by omega
    have test := room (ball D V v 2).card (mem_Icc.mpr ⟨min2,by omega⟩)
    have nx := CycleLayerTransport.fourth (d:=3) (target:=4*r) free hq reg vm (.inr rfl)
      (by omega) (by omega) (by omega) near (by simp only [mid,Nat.reduceEqDiff,ite_false,Nat.reduceMul,Nat.reduceAdd]; simpa using test)
    omega
  have second u (uv : u∈V) : 2*r+1≤(ball D V u 2).card := by
    have lo := near u uv
    have one := card_B1 (free.mono_bound (by omega : 4≤q)) uv
    rw [reg u uv] at one
    have two := @card_B2 D V u
    by_contra! low
    obtain ⟨v,vm⟩ := card_pos.mp (show 0<(outN D V u).card by rw [reg u uv]; omega)
    have grow := (narrow_supply free (by omega) reg uv fit (by omega) v vm).2 2 (by omega)
    simp only [Nat.reduceAdd] at grow
    have maxV := upper v (outN_subset vm)
    have min4 := fourth u uv
    omega
  intro u uv
  have lo := third u uv
  have hi := upper u uv
  have sum := flat u uv
  have top : (ball D V u 3).card=3*r+1 := by
    by_contra! off
    have min2 := second u uv
    have max2 := ShellProfileCapacity.short_second free hq (by omega) fit reg uv (by omega)
    have one := card_B1 (free.mono_bound (by omega : 4≤q)) uv
    rw [reg u uv] at one
    have two := @card_B2 D V u
    have three := @card_B3 D V u
    obtain ⟨s,sm,narrow,_⟩|high := equal_rows free (by omega) (by omega) fit reg uv (by omega) (by omega)
    · have := second s (outN_subset sm)
      omega
    obtain ⟨v,vm⟩ := card_pos.mp (show 0<(outN D V u).card by rw [reg u uv]; omega)
    have := (high v vm).2
    have := upper v (outN_subset vm)
    omega
  exact ⟨second u uv,top,by omega⟩


/-- The profile is retained for every exact-degree thinning of this bad
graph, including a thinning selected later using labelled side conditions. -/
structure OnFamily (p : CHRuleCatalog.Input) : Prop where
  on_graph : ∀{q},q≤CHRuleCatalog.cutoff p → 7≤q → 7≤p.s → p.s≤q+1 →
    FourthRoom p.s → MixedBankScore.Capacity p.s → Room p.s → p.n≤7*p.s →
    ∀F, (∀u v,F u v=true → p.D u v=true) → OutEq p.s F (range p.n) →
      ∀u∈range p.n,2*p.s+1≤(ball F (range p.n) u 2).card ∧
        (ball F (range p.n) u 3).card=3*p.s+1 ∧ (ball F (range p.n) u 4).card=4*p.s

theorem native (p : CHRuleCatalog.Input) (bad : CHRuleCatalog.Bad p) : OnFamily p := by
  constructor
  intro q within hq hr fit bounds cap room host F sub reg
  have free := (qfree_of_noShort bad.loopless bad.missing).mono_bound within
  exact uniform (qfree_sub sub free) reg hq hr fit bounds cap room (by simpa using host)

attribute [aesop safe forward (immediate := [free,reg,hq,hr,fit,bounds,cap,host])
  (rule_sets := [CHGraphFamilies])] MixedBankScore.low_score_floor
attribute [aesop safe forward (immediate := [free,reg,hq,hr,fit,bounds,cap,room,host])
  (rule_sets := [CHGraphFamilies])] uniform
attribute [aesop safe forward (immediate := [bad]) (rule_sets := [CHGraphFamilies])] native
attribute [aesop safe forward (immediate := [free,hq,time,degree,room,score,actual,sv,ordinary,belongs,cycles,sub,strictly_paid])
  (rule_sets := [CHGraphFamilies])] MixedBankPayments.balance
attribute [aesop safe forward (immediate := [free,hq,cut,time,degree,room,score,actual,groups,profit,supplier])
  (rule_sets := [CHGraphFamilies])] MixedBankPayments.no_low
attribute [aesop safe forward (immediate := [free,hq,hr,fit,reg,uv,ys,zs,cr,time])
  (rule_sets := [CHGraphFamilies])] CycleLayerTransport.transfer
#print axioms native

#print axioms uniform
end LeanCH.BR.MixedBankProfile


