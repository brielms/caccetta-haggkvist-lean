import checkpoints.shen_extension.InheritedHeadBudget

namespace LeanCH.BR.FragmentScoreEquality
open Finset BRq2 BRq3 BR45 BRsGen BypassRepair GuardedLayerGrowth GuardedProfileBudget
open CHRuleCatalog ProjectedQuotaTransfer

/-- A single additional ambient label changes the same ledger into
rigidity. Every row has the same three-ball, and no row can have
the minimal two-ball: its physical one-head bank would be too tall. -/
theorem odd_profile {D V q r floor k} (free : QFree D V q) (reg : OutEq r D V)
    (known : ∀d,d<floor → NoHost q d) (tests : ProfileTests q r (3*r-1) floor)
    (cut : 3+3≤q) (rank : 2≤r) (room : r≤2*q) (time : k+3≤q)
    (pressure : r≤q+k+1) (space : 2*r≤3*q+1) (many : 3≤2*q+2-r)
    (size : V.card+1=2*(3*r)) (lower : ∀v∈V,3*r-1≤(ball D V v 3).card) :
    ∀v∈V,(ball D V v 3).card=3*r ∧ 2*r<(ball D V v 2).card := by
  have paid := MixedBankSupply.paid (i:=3) (j:=3) (base:=2*(3*r)) free (by omega)
    reg rank time pressure space cut size.le many (fun x xm=>by have := lower x xm; omega) (by
      intro x xm low
      have eq : (ball D V x 3).card=3*r-1 := by have := lower x xm; omega
      have two := floor_root_two free reg xm (by omega) (by omega) room known tests eq
      have y := @card_B2 D V x
      rw [card_B1 (free.mono_bound (by omega : 4≤q)) xm,reg x xm] at y
      have z := @card_B3 D V x
      exact ⟨by omega,Or.inl (by omega)⟩) (fun x xm _ score=>by omega)
  have eq := MixedFragmentEscape.score_equality free cut _ paid
    (by simpa only [sum_const_nat (fun _ _=>rfl)] using Nat.mul_le_mul_left V.card size.le)
  have atThree v (vm : v∈V) : (ball D V v 3).card=3*r := by have := eq v vm; omega
  intro v vm
  refine ⟨atThree v vm,?_⟩
  have low := second_floor free (by omega) reg (by omega) room vm
  by_contra! small
  have y := @card_B2 D V v
  rw [card_B1 (free.mono_bound (by omega : 4≤q)) vm,reg v vm] at y
  have z := @card_B3 D V v
  have t := atThree v vm
  have tally := MixedBankSupply.marked_rows free (by omega) vm reg rank time pressure
    (by omega) (Or.inr (by omega)) space
  let X := outN D V v
  let F := X.filter (fun w=>(outN D X w).card=1)
  change 2*q+2≤r+F.card ∧ ∀w∈F,_ at tally
  obtain ⟨w,wm⟩ := card_pos.mp (show 0<F.card by have := tally.1; omega)
  have score := (tally.2 w wm).2
  have := atThree w (outN_subset (mem_filter.mp wm).1)
  omega

/-- This package selects the exact-degree graph once so that subsequent
rules can use its labelled balls together. -/
structure UniformSource (p : Input) : Prop where
  witness : ∃D : CH.Digraph,(∀u v,D u v=true → p.D u v=true) ∧
    QFree D (range p.n) (cutoff p) ∧ OutEq p.s D (range p.n) ∧
    ∀v∈range p.n,(ball D (range p.n) v 3).card=3*p.s ∧ 2*p.s<(ball D (range p.n) v 2).card

@[ch_numeric_guard] def UniformWindow (n r q floor : ℕ) : Prop :=
  6≤q ∧ 2≤r ∧ r≤2*q ∧ r≤2*q-2 ∧ 2*r≤3*q+1 ∧ 3≤2*q+2-r ∧
  n+1=2*(3*r) ∧ Covers q r (2*r) (3*r-1) (range floor) ∧ ProfileTests q r (3*r-1) floor

instance {n r q floor} : Decidable (UniformWindow n r q floor) := by unfold UniformWindow; infer_instance

theorem uniform_on_bad {p : Input} {floor} (bad : Bad p)
    (known : ∀t,t<floor → NoHost (cutoff p) t) (win : UniformWindow p.n p.s (cutoff p) floor) :
    UniformSource p := by
  obtain ⟨cut,rank,room,pressure,space,many,size,heights,tests⟩ := win
  obtain ⟨D,sub,reg⟩ := exists_outEq (fun v (vm : v∈range p.n)=>Compose.FloorSix.out_card bad.degree (mem_range.mp vm))
  have free := qfree_sub sub (qfree_of_noShort bad.loopless bad.missing)
  exact ⟨D,sub,free,reg,odd_profile (k:=cutoff p-3) free reg known tests cut rank room
    (by omega) (by omega) space many (by simpa only [card_range] using size)
    (fun x xm=>third free reg xm (second_floor free (by omega) reg (by omega) room xm)
      (fun t tm=>known t (mem_range.mp tm)) heights)⟩

theorem uniform_at_completed {p : Input} (bad : Bad p) :
    UniformWindow p.n p.s (cutoff p) projectionFloor → UniformSource p :=
  uniform_on_bad bad (available_lower_hosts bad)

attribute [aesop safe forward (immediate := [bad,known,win]) (rule_sets := [CHGraphFamilies])] uniform_on_bad
attribute [aesop safe forward (immediate := [bad]) (rule_sets := [CHGraphFamilies])] uniform_at_completed
#print axioms odd_profile
#print axioms uniform_on_bad
end LeanCH.BR.FragmentScoreEquality