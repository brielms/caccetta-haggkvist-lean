import checkpoints.shen_extension.SharedBankOrderTransfer
import checkpoints.shen_extension.OddShellOrder

namespace LeanCH.BR.RecursivePrefixBudget
open Finset BRq2 BRq3 BypassRepair MixedRadiusCompletion CHRuleCatalog ProjectedQuotaTransfer
open DotTwoPassShellTransport (layer shell)

/-- A comparison quota and its inclusive floors at complementary radii. -/
structure Comparison where
  degree : ℕ
  left : ℕ
  right : ℕ
  deriving DecidableEq, Repr

def Valid (q : ℕ) (b : Comparison) : Prop :=
  Floor q b.degree (q/2) b.left ∧ Floor q b.degree (q-q/2) b.right

/-- A different smaller degree may pay for each possible labelled prefix profile. -/
def CanRaise (q r p lo F : ℕ) (bank : List Comparison) : Prop :=
  ∀ x∈Icc lo F, ∀ c∈range (x-p+1), bank.any (fun b =>
    decide (Pass x c F r b.degree (q*b.degree+1) (b.left+b.right))) = true

instance {q r p lo F bank} : Decidable (CanRaise q r p lo F bank) := by
  unfold CanRaise
  infer_instance

theorem advance {q r k p lo F bank}
    (inner : Floor q r k p) (outer : Floor q r (k+1) lo)
    (time : k+2≤q) (narrow : F<lo+r)
    (sound : ∀b∈bank, Valid q b ∧ b.degree≤r ∧ NoHost q b.degree)
    (check : CanRaise q r p lo F bank) : Floor q r (k+2) (F+1) := by
  intro D V free deg u hu
  by_contra! small
  have prev := inner D V free deg u hu
  have start := outer D V free deg u hu
  have inc := card_le_card (ball_mono_radius (D:=D) (W:=V) (u:=u) (Nat.le_succ (k+1)))
  have lay : (layer D V (k+1) u).card+(ball D V u k).card=(ball D V u (k+1)).card := by
    simpa only [layer,Nat.add_sub_cancel] using card_sdiff_add_card_eq_card
      (ball_mono_radius (D:=D) (W:=V) (u:=u) (Nat.le_succ k))
  have sh : (shell D V (k+1) u).card+(ball D V u (k+1)).card=(ball D V u (k+2)).card :=
    card_sdiff_add_card_eq_card (ball_mono_radius (Nat.le_succ (k+1)))
  obtain ⟨b,hb,pass⟩ := List.any_eq_true.mp (check (ball D V u (k+1)).card (mem_Icc.mpr ⟨start,by omega⟩)
    (layer D V (k+1) u).card (mem_range.mpr (by omega)))
  obtain ⟨⟨left,right⟩,fit,lower⟩ := sound b hb
  obtain ⟨G,Q,hG,_,hL,quad,cap⟩ := prefix_completion (by omega : q/2+(q-q/2)≤q)
    (order_of_noHost lower) left right fit free deg hu time (by omega)
  exact pass_false (F:=F) (card_erase_add_one (self_mem_ball hu)) (by omega) hG hL quad cap
    (of_decide_eq_true pass)

private def climb (q r p lo : ℕ) (bank : List Comparison) (value fuel : ℕ) : ℕ :=
  match fuel with
  | 0 => value
  | fuel+1 => if CanRaise q r p lo value bank then climb q r p lo bank (value+1) fuel else value

private theorem climb_sound {q r k p lo bank} (inner : Floor q r k p) (outer : Floor q r (k+1) lo)
    (time : k+2≤q) (sound : ∀b∈bank, Valid q b ∧ b.degree≤r ∧ NoHost q b.degree)
    (fuel value : ℕ) (start : Floor q r (k+2) value) (budget : value+fuel≤lo+r) :
    Floor q r (k+2) (climb q r p lo bank value fuel) := by
  induction fuel generalizing value with
  | zero => exact start
  | succ n ih =>
    simp only [climb]
    split
    next check => exact ih _ (advance inner outer time (by omega) sound check) (by omega)
    next => exact start

/-- Two successive radius floors. Only confirmed increments advance the bound. -/
def layers (q r : ℕ) (bank : List Comparison) : ℕ → ℕ × ℕ
  | 0 => (1,r+1)
  | k+1 =>
    let (p,lo) := layers q r bank k
    (lo, climb q r p lo bank lo r)

theorem layers_sound {q r bank} (hq : 1≤q)
    (sound : ∀b∈bank, Valid q b ∧ b.degree≤r ∧ NoHost q b.degree) (k : ℕ) (time : k+1≤q) :
    Floor q r k (layers q r bank k).1 ∧ Floor q r (k+1) (layers q r bank k).2 := by
  induction k with
  | zero =>
    constructor
    · intro D V _ _ u hu
      exact card_pos.mpr ⟨u,self_mem_ball hu⟩
    · intro D V free deg u hu
      change r+1≤(ball D V u 1).card
      rw [ReachLedger.ball_one free hq hu]
      have := deg u hu
      omega
  | succ k ih =>
    obtain ⟨inner,outer⟩ := ih (by omega)
    exact ⟨outer,climb_sound inner outer time sound _ _ (fun D V free deg u hu =>
      (outer D V free deg u hu).trans (card_le_card (ball_mono_radius (Nat.le_succ (k+1))))) (by omega)⟩

def middle (q r : ℕ) (bank : List Comparison) : Comparison :=
  let (left,next) := layers q r bank (q/2)
  ⟨r,left,if q-q/2=q/2 then left else next⟩

theorem middle_valid {q r bank} (hq : 2≤q)
    (sound : ∀b∈bank, Valid q b ∧ b.degree≤r ∧ NoHost q b.degree) :
    Valid q (middle q r bank) := by
  obtain ⟨a,b⟩ := layers_sound (by omega : 1≤q) sound (q/2) (by omega)
  refine ⟨a,?_⟩
  change Floor q r (q-q/2) (if q-q/2=q/2 then _ else _)
  split
  next e => simpa only [e] using a
  next e => simpa only [show q-q/2=q/2+1 by omega] using b

/-- The odd-shell proof supplies pointwise floors on the carrier of a completion. -/
private def shellMiddle (q r : ℕ) (bank : List Comparison) : Comparison :=
  let b := middle q r bank
  if 4≤q/2 ∧ 5≤q-q/2 ∧ OddShellOrder.Capacity q r (q/2) (q-q/2) then
    ⟨r,max b.left (4*r+1),max b.right (5*r)⟩
  else b

private theorem shellMiddle_degree (q r : ℕ) (bank : List Comparison) :
    (shellMiddle q r bank).degree=r := by unfold shellMiddle; split <;> rfl

private theorem shellMiddle_valid {q r bank} (hq : 2≤q)
    (sound : ∀b∈bank, Valid q b ∧ b.degree≤r ∧ NoHost q b.degree) :
    Valid q (shellMiddle q r bank) := by
  have ordinary := middle_valid hq sound
  unfold shellMiddle
  split
  next h =>
    have floors {D V} (free : QFree D V q) (deg : ∀u∈V,r≤(outN D V u).card) (u) (hu : u∈V) :=
      (OddShellOrder.order_and_balls free ⟨u,hu⟩ deg h.2.2).1 u hu
    constructor
    · intro D V free deg u hu
      exact max_le (ordinary.1 D V free deg u hu)
        ((floors free deg u hu).1.trans (card_le_card (ball_mono_radius h.1)))
    · intro D V free deg u hu
      exact max_le (ordinary.2 D V free deg u hu)
        ((floors free deg u hu).2.trans (card_le_card (ball_mono_radius h.2.1)))
  next => exact ordinary

/-- Build the comparison library in increasing degree, once per degree. -/
def library (q : ℕ) : ℕ → List Comparison
  | 0 => []
  | d+1 => let prev := library q d; shellMiddle q (d+1) prev :: prev

theorem library_sound {q} (hq : 2≤q) (d : ℕ) (known : ∀t,t<d → NoHost q t) :
    ∀b∈library q d, Valid q b ∧ b.degree≤d := by
  induction d with
  | zero => simp [library]
  | succ d ih =>
    have prev := ih (fun t ht=>known t (by omega))
    intro b hb
    rcases List.mem_cons.mp hb with rfl|old
    · exact ⟨shellMiddle_valid hq (fun c hc=>⟨(prev c hc).1,by have := (prev c hc).2; omega,
        known _ (by have := (prev c hc).2; omega)⟩),(shellMiddle_degree ..).le⟩
    · exact ⟨(prev b old).1,(prev b old).2.trans (Nat.le_succ d)⟩

def result (q d : ℕ) := middle q d (library q (d-1))

theorem result_valid {q d} (hq : 2≤q) (hd : 0<d) (known : ∀t,t<d → NoHost q t) :
    Valid q (result q d) := by
  have prev := library_sound hq (d-1) (fun t ht=>known t (by omega))
  exact middle_valid hq (fun c hc=>⟨(prev c hc).1,by have := (prev c hc).2; omega,
    known _ (by have := (prev c hc).2; omega)⟩)

private def strictGain (q d : ℕ) (b : Comparison) : Prop :=
  2*(q/2/2)=q/2 ∧ b.left+2≤2*(layers q d (library q (d-1)) (q/2/2)).1
private instance {q d b} : Decidable (strictGain q d b) := by unfold strictGain; infer_instance

/-- If the left radius doubles an earlier one, test its Seymour witness at equality. -/
def bound (q d : ℕ) : ℕ :=
  let b := result q d
  b.left+b.right+(if strictGain q d b then 1 else 0)-2

theorem bound_sound {q d} (hq : 2≤q) (hd : 0<d) (known : ∀t,t<d → NoHost q t)
    {D V} (free : QFree D V q) (ne : V.Nonempty) (deg : ∀v∈V,d≤(outN D V v).card) :
    bound q d<V.card := by
  let b := result q d
  obtain ⟨left,right⟩ := result_valid hq hd known
  change Floor q d (q/2) b.left at left
  change Floor q d (q-q/2) b.right at right
  change b.left+b.right+(if strictGain q d b then 1 else 0)-2<V.card
  have pos := card_pos.mpr ne
  split
  next gain =>
    obtain ⟨eq,more⟩ := gain
    have prev := library_sound hq (d-1) (fun t ht=>known t (by omega))
    have bank := layers_sound (by omega : 1≤q) (r:=d) (bank:=library q (d-1))
      (fun c hc=>⟨(prev c hc).1,by have := (prev c hc).2; omega,known _ (by have := (prev c hc).2; omega)⟩)
      (q/2/2) (by omega)
    have size := SharedBankOrderTransfer.strict_order (k:=q/2/2) free ne
      (by omega : 2*(q/2/2)+(q-q/2)≤q) (bank.1 D V free deg)
      (eq.symm ▸ left D V free deg) (right D V free deg) more
    omega
  next =>
    have size := order_of_floors (by omega : q/2+(q-q/2)≤q) left right D V free deg ne
    omega

@[ch_numeric_guard] def Window (n r q limit : ℕ) : Prop :=
  let d := min r limit
  2≤q ∧ 0<d ∧ 0<bound q d ∧ n+d≤bound q d+r

instance {n r q limit} : Decidable (Window n r q limit) := by unfold Window; infer_instance

theorem excluded {p : Input} {limit} (bad : Bad p) (known : ∀t,t<limit → NoHost (cutoff p) t) :
    ¬Window p.n p.s (cutoff p) limit := by
  rintro ⟨cut,pos,live,paid⟩
  have certificate : GuardedFamilyRules.OrderBound (cutoff p) (min p.s limit) (bound (cutoff p) (min p.s limit)) :=
    ⟨live, fun _ _ free ne deg => bound_sound cut pos
      (fun t ht => known t (ht.trans_le (min_le_right ..))) free ne deg⟩
  exact GuardedFamilyRules.forbidden bad certificate ⟨le_rfl,min_le_left ..,paid⟩

theorem at_completed {p : Input} (bad : Bad p) :
    ¬Window p.n p.s (cutoff p) projectionFloor := excluded bad (available_lower_hosts bad)

attribute [aesop safe forward (immediate := [inner,outer,time,narrow,sound,check]) (rule_sets := [CHGraphFamilies])] advance
attribute [aesop safe forward (immediate := [bad,known]) (rule_sets := [CHGraphFamilies])] excluded
attribute [aesop safe forward (immediate := [bad]) (rule_sets := [CHGraphFamilies])] at_completed
#print axioms advance
#print axioms result_valid
#print axioms at_completed
end LeanCH.BR.RecursivePrefixBudget
