import checkpoints.shen_extension.RenewedFragmentBudget

namespace LeanCH.BR.FragmentScoreEquality
open Finset BRq2 BRq3 BR45 BRsGen BypassRepair ParentBankPeel CHRuleCatalog ProjectedQuotaTransfer

/-- A proposed number e of available fourth-layer slots must meet this
bill for at least one possible two-ball size. The floors use inclusive
ball sizes s and t. -/
def ShellTest (n r q s t d e : ℕ) : Prop :=
  6≤q ∧ 0<d ∧ d+e≤r ∧ 1<s-e ∧ s-e≤q*d+1 ∧
  n+1≤s+(t+e+1) ∧ t+e+2<2*s ∧
  ∀a∈Icc (s-1) (t-1),
    (t-1)*t<2*((t-1-a)*(floorTable q d 3+1)+(a-r)*(s-e+1)+r*(t-e))

instance {n r q s t d e} : Decidable (ShellTest n r q s t d e) := by unfold ShellTest; infer_instance

theorem outside_fourth {D V q r s t d e} (free : QFree D V q) (reg : OutEq r D V)
    (live : V.Nonempty) (known : ∀j,j≤d → NoHost q j)
    (two : ∀x∈V,s≤(ball D V x 2).card) (three : ∀x∈V,(ball D V x 3).card=t)
    (paid : ShellTest V.card r q s t d e) : False := by
  obtain ⟨cut,pos,cost,seed,room,global,apart,excess⟩ := paid
  have four v (vm : v∈V) : t+e+1≤(ball D V v 4).card := by
    by_contra! small
    have threeV := three v vm
    have bill := renewed_three_bill free vm reg cut pos known two
      (fun x xm=>(three x xm).ge) (show (ball D V v 4).card≤(ball D V v 3).card+e by omega)
      cost seed room
    dsimp only at bill
    rw [threeV] at bill
    have increasing := card_le_card (ball_mono_radius (D:=D) (W:=V) (u:=v) (by decide : 2≤3))
    have twoV := two v vm
    have expensive := excess ((ball D V v 2).card-1) (mem_Icc.mpr ⟨by omega,by omega⟩)
    have positive : 0<t := by omega
    rw [Nat.sub_add_cancel positive] at bill
    exact expensive.not_ge bill
  have same := MixedFragmentEscape.score_equality free (by omega : 2+4≤q)
    (fun _=>s+(t+e+1)) (fun x xm=>Nat.add_le_add (two x xm) (four x xm))
    (by simpa only [sum_const_nat (fun _ _=>rfl)] using Nat.mul_le_mul_left V.card global)
  obtain ⟨v,vm,twice,_⟩ := power_receiver (k:=2) free live (by omega)
  change 2*(ball D V v 2).card≤(ball D V v 4).card+1 at twice
  have eq := same v vm
  have low := two v vm
  omega

@[ch_numeric_guard] def FourthWindow (n r q floor : ℕ) : Prop :=
  UniformWindow n r q floor ∧ ∃d∈range floor,∃e∈range r,
    ShellTest n r q (2*r+1) (3*r) d e

instance {n r q floor} : Decidable (FourthWindow n r q floor) := by unfold FourthWindow; infer_instance

theorem uniform_exit {p : Input} {floor} (bad : Bad p)
    (known : ∀t,t<floor → NoHost (cutoff p) t) : ¬FourthWindow p.n p.s (cutoff p) floor := by
  rintro ⟨win,d,dm,e,_,test⟩
  obtain ⟨D,_,free,reg,profile⟩ := (uniform_on_bad bad known win).witness
  exact outside_fourth free reg (nonempty_range_iff.mpr bad.order.ne')
    (fun j small=>known j (small.trans_lt (mem_range.mp dm)))
    (fun x xm=>(profile x xm).2) (fun x xm=>(profile x xm).1) (by rwa [card_range])

theorem original_exit {p : Input} (bad : Bad p) :
    ¬FourthWindow p.n p.s (cutoff p) projectionFloor := uniform_exit bad (available_lower_hosts bad)

attribute [aesop safe forward (immediate := [bad,known]) (rule_sets := [CHGraphFamilies])] uniform_exit
attribute [aesop safe forward (immediate := [bad]) (rule_sets := [CHGraphFamilies])] original_exit
#print axioms outside_fourth
#print axioms original_exit
end LeanCH.BR.FragmentScoreEquality