import checkpoints.shen_extension.ReachCompletionCatalog
import checkpoints.shen_extension.RootRegularBridge
import checkpoints.shen_extension.QuotaBankPromotion
import checkpoints.shen_extension.PowerReceiverBudget

namespace LeanCH.BR.SharedBankOrderTransfer
open Finset BRq2 BRq3 CHRuleCatalog BypassRepair GuardedFamilyRules ProjectedQuotaTransfer

/-- If the doubled-radius floor would be too small at a Seymour witness,
equality in the complementary-ball count is impossible. All three
pointwise floors refer to the same digraph and carrier. -/
theorem strict_order {D V q k j u a b} (free : QFree D V q) (live : V.Nonempty)
    (time : 2*k+j≤q) (first : ∀x∈V, u≤(ball D V x k).card)
    (double : ∀x∈V, a≤(ball D V x (2*k)).card)
    (other : ∀x∈V, b≤(ball D V x j).card) (gain : a+2≤2*u) : a+b≤V.card := by
  have weak := card_ge_of_two_balls free time double other live
  by_contra! small
  obtain ⟨x,hx,large,_⟩ := FragmentScoreEquality.power_receiver (k:=k) free live (by omega)
  have fixed := (two_balls_boundary_cards free time double other (by omega)) x hx
  have := first x hx
  omega

/-- A shared-head exclusion at one carrier size gives a transferable order
bound. Padding proves the bound at smaller orders without assuming that
the quadratic budget itself is monotone. -/
theorem order_bound {q t d m} (cut : 4≤q) (rank : 2≤t) (within : t≤q)
    (shape : d=q*t+1) (regular : Closure.BoundaryHub.QBoundaryInRegular q t)
    (lower : NoHost q t) (above : NoHost q (t+1)) (live : 0<m)
    (bill : m*(m+1)+2 < 2*(t*d)+2*m+m*((2*d+1-t)+(2*d+1-t)))
    (short : m+1≤2*(2*d+2-t)) : OrderBound q d m := by
  refine ⟨live,fun D V free ne degree => ?_⟩
  by_contra! small
  apply ParentBankPeel.pad_regime (q:=q) (r:=d) (n:=m) _ free degree rfl ⟨card_pos.mpr ne,small⟩
  intro E W sz ef ed
  obtain ⟨F,sub,exactRows⟩ := exists_outEq ed
  have safe := qfree_sub sub ef
  have enough : t≤d := by
    have := Nat.le_mul_of_pos_left t (by omega : 0<q)
    omega
  have twoFloor := SharedHeadSuppliers.floor_by_budget (a:=2*d+1-t) lower above regular safe
    cut (by omega) within exactRows sz shape (by omega) bill
  have oneFloor (x) (hx : x∈W) : d+1≤(ball F W x 1).card := by
    rw [ReachLedger.ball_one safe (by omega) hx, exactRows x hx]
  have total := strict_order (k:=1) (j:=2) safe (card_pos.mp (by omega : 0<W.card))
    (by omega) oneFloor twoFloor twoFloor (by omega)
  omega

/-- Spend the excess degree on vertex deletion and test the shared-bank
budget at the actual required order. -/
@[ch_numeric_guard] def Window (n r q quotaLimit : ℕ) : Prop :=
  4≤q ∧ ∃ t∈Icc 2 q, t+1<quotaLimit ∧ ¬WeightedSD.NativePressureRegion q t ∧
    let d := q*t+1
    let m := max 1 (n-(r-d))
    m+1≤2*(2*d+2-t) ∧ m*(m+1)+2 < 2*(t*d)+2*m+m*((2*d+1-t)+(2*d+1-t)) ∧
      Fits n r q q d m

instance {n r q quotaLimit} : Decidable (Window n r q quotaLimit) := by
  unfold Window WeightedSD.NativePressureRegion
  infer_instance

theorem excluded {p : Input} {quotaLimit} (bad : Bad p)
    (known : ∀k,k<quotaLimit → NoHost (cutoff p) k) : ¬Window p.n p.s (cutoff p) quotaLimit := by
  rintro ⟨cut,t,tm,room,reg,short,bill,fits⟩
  obtain ⟨two,within⟩ := mem_Icc.mp tm
  have regular := RootRegularBridge.inRegular_of_boundaryRegular (by omega : 1≤cutoff p)
    (WeightedSD.boundary_regular_outside_pressure_region (by omega) two reg)
  apply forbidden bad _ fits
  exact order_bound cut (by omega) within rfl regular (known t (by omega)) (known _ room)
    (by omega) bill short

theorem from_prefix {p : Input} (bad : Bad p) : ¬Window p.n p.s (cutoff p) projectionFloor :=
  excluded bad (available_lower_hosts bad)

attribute [aesop safe forward (immediate := [bad,known]) (rule_sets := [CHGraphFamilies])] excluded
attribute [aesop safe forward (immediate := [bad]) (rule_sets := [CHGraphFamilies])] from_prefix
attribute [aesop safe forward (immediate := [free,live,time,first,double,other,gain])
  (rule_sets := [CHGraphFamilies])] strict_order

#print axioms strict_order
#print axioms order_bound
#print axioms excluded
#print axioms from_prefix
end LeanCH.BR.SharedBankOrderTransfer
