import checkpoints.shen_extension.GuardedMixedOrder
import checkpoints.shen_extension.ReachDescentCatalog
import checkpoints.shen_extension.VerifiedDegreeFrontier

namespace LeanCH.BR.GuardedProfileBudget
open Finset BRq2 BRq3 BR45 BRsGen OneSpareGrowth GuardedLayerGrowth
open BypassRepair ParentBankPeel

/-- Three independent contradictions for a proposed inclusive second-ball size.
The quota set K can contain any degrees for which smaller hosts are excluded. -/
def Obstructs (q r h b : ℕ) (K : Finset ℕ) : Prop :=
  (4≤q ∧ 2≤r ∧ r≤2*q ∧ b=2*r ∧ r<2*(q-2)+3 ∧ h+1≤b+r) ∨
  (4≤q ∧ r≤2*q ∧ ∃t∈Icc 2 q, t+h≤r+b+1 ∧
    (b-1)*b < 2*(r*(r+t)+(b-1-r)*(2*t+1))) ∨
  (3≤q ∧ ∃d∈K, 1<b ∧ b≤q*d+1 ∧ h+d≤b+r+1)

instance (q r h b : ℕ) (K : Finset ℕ) : Decidable (Obstructs q r h b K) := by
  unfold Obstructs
  infer_instance

def Covers (q r b₀ h : ℕ) (K : Finset ℕ) : Prop := ∀b∈Ico b₀ h,Obstructs q r h b K

instance (q r b₀ h : ℕ) (K : Finset ℕ) : Decidable (Covers q r b₀ h K) := by
  unfold Covers
  infer_instance

/-- A size supplied by any earlier rule is tested on this root. No integer profile
is enumerated in the proof. The tight-shell and fragment tests use the actual row. -/
theorem third {D V q r a b₀ h K} (free : QFree D V q) (reg : OutEq r D V) (av : a∈V)
    (base : b₀≤(ball D V a 2).card) (known : ∀t∈K,NoHost q t)
    (profiles : Covers q r b₀ h K) : h≤(ball D V a 3).card := by
  by_contra! small
  let b := (ball D V a 2).card
  have weak : b≤(ball D V a 3).card :=
    card_le_card (ball_mono_radius (D:=D) (W:=V) (u:=a) (by decide : 2≤3))
  have split : b+(N3 D V a).card=(ball D V a 3).card := (card_B3 ..).symm
  rcases profiles b (mem_Ico.mpr ⟨base,by omega⟩) with tight|fragment|child
  · obtain ⟨cut,two,room,size,pressure,target⟩ := tight
    have layer : (N2 D V a).card+1=r := by
      have first := @card_B2 D V a
      rw [card_B1 (free.mono_bound cut) av,reg a av] at first
      change (ball D V a 2).card=2*r at size
      omega
    have grow := guarded_third (k:=q-2) free cut av reg two layer (by omega) room pressure
    omega
  · obtain ⟨cut,room,t,tm,fit,pressure⟩ := fragment
    obtain ⟨two,rank⟩ := mem_Icc.mp tm
    have bill := fragment_budget free cut av reg room two rank (by omega)
    dsimp only at bill
    rw [card_erase_of_mem (self_mem_ball av)] at bill
    change 2*(r*(r+t)+(b-1-r)*(2*t+1))≤(b-1)*(b-1+1) at bill
    have pos : 1≤b := card_pos.mpr ⟨a,self_mem_ball av⟩
    rw [Nat.sub_add_cancel pos] at bill
    exact pressure.not_ge bill
  · obtain ⟨cut,d,dm,big,fit,paid⟩ := child
    have step := PrefixDegreeGrowth.step (j:=2) (d:=d) free av (by omega)
      (fun v vm=>(reg v vm).ge) (fun _ ne size safe deg=>known d dm D _ ne size safe deg) big fit
    change b+r<(ball D V a 3).card+d at step
    omega

/-- Any certified punctured-ball floor, obtained at any positive radius, can
be iterated from the same label. The seed may differ from root to root. -/
theorem advance {D V q r a j b} (free : QFree D V q)
    (degree : ∀v∈V,r≤(outN D V v).card) (known : ∀t,t<r→NoHost q t)
    (hq : 1≤q) (hr : 1≤r) (av : a∈V) (start : 1≤j)
    (seed : b+1≤(ball D V a j).card) :
    ∀k,j+k≤q → (growthFloor q r)^[k] b+1≤(ball D V a (j+k)).card := by
  intro k
  induction k with
  | zero => simpa using fun (_ : j≤q)=>seed
  | succ k ih =>
    intro time
    have prev := ih (by omega)
    have next := floor_step free degree known hq hr av (by omega : 1≤j+k) time
    rw [Function.iterate_succ_apply'] 
    exact (Nat.add_le_add_right (growthFloor_mono hq (by omega : (growthFloor q r)^[k] b ≤
      (ball D V a (j+k)).card-1)) 1).trans next

/-- Every compatible pair of radii can spend the improved seed from radius
three. No NoHost law is inferred from arithmetic. It is supplied by descent. -/
def OrderBudget (q r n : ℕ) : Prop :=
  ∀h, 4≤q → 2≤r → r≤2*q → Covers q r (2*r) h (range r) →
    (5≤q → 3*r≤h+2 → 2*r+h≤n) ∧
    ∀i j,3+i+(3+j)≤q → (growthFloor q r)^[i] (h-1)+(growthFloor q r)^[j] (h-1)<n

theorem order_budget {D V q r} (free : QFree D V q)
    (degree : ∀v∈V,r≤(outN D V v).card) (live : V.Nonempty)
    (known : ∀t,t<r→NoHost q t) : OrderBudget q r V.card := by
  intro h cut two room profiles
  obtain ⟨E,sub,reg⟩ := exists_outEq degree
  have safe := qfree_sub sub free
  have thirdFloor v (vm : v∈V) := third safe reg vm (second_floor safe cut reg (by omega) room vm)
    (fun t tm=>known t (mem_range.mp tm)) profiles
  constructor
  · intro enough paid
    exact mixed_order safe enough live reg two room thirdFloor paid
  · intro i j time
    have deep (k : ℕ) (ok : 3+k≤q) (v) (vm : v∈V) :
        (growthFloor q r)^[k] (h-1)+1≤(ball E V v (3+k)).card := by
      apply advance safe (fun x xm=>(reg x xm).ge) known (by omega) (by omega) vm (by decide) _ k ok
      have lower := thirdFloor v vm
      have pos : 0<(ball E V v 3).card := card_pos.mpr ⟨v,self_mem_ball vm⟩
      omega
    have total := card_ge_of_two_balls safe time (deep i (by omega)) (deep j (by omega)) live
    omega

theorem least_order {p : CHRuleCatalog.Input} (bad : CHRuleCatalog.Bad p)
    (least : BypassDegreeDescent.MinimalChild p) : OrderBudget (CHRuleCatalog.cutoff p) p.s p.n := by
  have free := qfree_of_noShort bad.loopless bad.missing
  have deg (v) (vm : v∈range p.n) := Compose.FloorSix.out_card bad.degree (mem_range.mp vm)
  simpa only [card_range] using order_budget free deg (nonempty_range_iff.mpr bad.order.ne')
    (ReachDescentCatalog.lower_from_bad bad least)

attribute [aesop safe forward (immediate := [free,reg,av,base,known,profiles]) (rule_sets := [CHGraphFamilies])] third
attribute [aesop safe forward (immediate := [free,degree,live,known]) (rule_sets := [CHGraphFamilies])] order_budget
attribute [aesop safe forward (immediate := [bad,least]) (rule_sets := [CHGraphFamilies])] least_order

/-- Any globally excluded set of positive quotas can be reused on any original
bad input. The host-child theorem keeps the physical enumeration and cycle pullback. -/
theorem quotas_from_exclusions {p : CHRuleCatalog.Input} (bad : CHRuleCatalog.Bad p)
    {K : Finset ℕ} (excluded : ∀c : CHRuleCatalog.Input,CHRuleCatalog.Bad c → c.s∉K) :
    ∀t∈K,NoHost (CHRuleCatalog.cutoff p) t := by
  intro t tk D V live size free degree
  by_cases zero : t=0
  · subst t
    simp only [Nat.mul_zero] at size
    have := card_pos.mpr live
    omega
  have qpos := (CHRuleCatalog.remaining_from_run p bad).1
  obtain ⟨c,_,edge,rank,_⟩ := BypassDegreeDescent.host_child p (by omega : 0<t)
    (by omega) live size free degree
  exact excluded c (CHRuleCatalog.bad_child bad edge) (rank ▸ tk)

/-- The mixed-order consequence requires only the quotas actually used in
the profile inequalities. It applies before choosing a minimal descendant. -/
theorem mixed_from_quotas {D V q r h K} (free : QFree D V q)
    (degree : ∀v∈V,r≤(outN D V v).card) (live : V.Nonempty)
    (known : ∀t∈K,NoHost q t) (cut : 5≤q) (two : 2≤r) (room : r≤2*q)
    (profiles : Covers q r (2*r) h K) (paid : 3*r≤h+2) : 2*r+h≤V.card := by
  obtain ⟨E,sub,reg⟩ := exists_outEq degree
  have safe := qfree_sub sub free
  exact mixed_order safe cut live reg two room (fun v vm=>third safe reg vm
    (second_floor safe (by omega) reg (by omega) room vm) known profiles) paid

/-- The obstruction at any raw input ranges over every library of proven
quotas. The degree, order and cutoff are taken from the input itself. -/
def RawBudget (q r n : ℕ) : Prop :=
  ∀K:Finset ℕ,(∀c : CHRuleCatalog.Input,CHRuleCatalog.Bad c → c.s∉K) →
    ∀h,5≤q → 2≤r → r≤2*q → Covers q r (2*r) h K → 3*r≤h+2 → 2*r+h≤n

theorem raw_budget {p : CHRuleCatalog.Input} (bad : CHRuleCatalog.Bad p) :
    RawBudget (CHRuleCatalog.cutoff p) p.s p.n := by
  intro K excluded h cut rank room cover paid
  have free := qfree_of_noShort bad.loopless bad.missing
  have deg (v) (vm : v∈range p.n) := Compose.FloorSix.out_card bad.degree (mem_range.mp vm)
  simpa only [card_range] using mixed_from_quotas free deg (nonempty_range_iff.mpr bad.order.ne')
    (quotas_from_exclusions bad excluded) cut rank room cover paid

theorem raw_exit {q r n h K} (law : RawBudget q r n)
    (excluded : ∀c : CHRuleCatalog.Input,CHRuleCatalog.Bad c → c.s∉K)
    (cut : 5≤q) (two : 2≤r) (room : r≤2*q) (cover : Covers q r (2*r) h K)
    (paid : 3*r≤h+2) (small : n<2*r+h) : False :=
  (Nat.not_lt_of_ge (law K excluded h cut two room cover paid)) small

theorem literal_profile {q r n h K} {D : CH.Digraph}
    (hn : 0<n) (rank : 2≤r) (cutoff : CH.ceilDiv n r=q)
    (loopless : CH.Loopless D n) (degree : CH.MinOutdegreeAtLeast D n r)
    (excluded : ∀c : CHRuleCatalog.Input,CHRuleCatalog.Bad c → c.s∉K)
    (cut : 5≤q) (room : r≤2*q) (cover : Covers q r (2*r) h K) (paid : 3*r≤h+2)
    (small : n<2*r+h) : CH.HasDirectedCycleAtMost D n (CH.ceilDiv n r) := by
  by_contra missing
  have bad : CHRuleCatalog.Bad ⟨n,r,D⟩ := ⟨hn,by change 0<r; omega,loopless,degree,missing⟩
  have law := raw_budget bad
  change RawBudget (CH.ceilDiv n r) r n at law
  exact raw_exit (cutoff ▸ law) excluded cut rank room cover paid small

attribute [aesop safe forward (immediate := [bad]) (rule_sets := [CHGraphFamilies])] raw_budget
attribute [aesop safe forward (immediate := [bad,excluded]) (rule_sets := [CHGraphFamilies])] quotas_from_exclusions
attribute [aesop safe forward (immediate := [law,excluded,cut,two,room,cover,paid,small]) (rule_sets := [CHGraphFamilies])] raw_exit
/-- The smallest requested height that makes the mixed-order estimate pay. -/
def neededHeight (n r : ℕ) := max (3*r-2) (n+1-2*r)

@[ch_numeric_guard] def Window (n r q : ℕ) (K : Finset ℕ) : Prop :=
  5≤q ∧ 2≤r ∧ r≤2*q ∧ Covers q r (2*r) (neededHeight n r) K

instance (n r q : ℕ) (K : Finset ℕ) : Decidable (Window n r q K) := by
  unfold Window
  infer_instance

theorem height_bills (n r : ℕ) : 3*r≤neededHeight n r+2 ∧ n<2*r+neededHeight n r := by
  unfold neededHeight
  omega

/-- Any successful requested height also certifies the smallest one. -/
theorem covers_mono {q r b₀ h h' K} (cover : Covers q r b₀ h K) (le : h'≤h) : Covers q r b₀ h' K := by
  intro b bm
  obtain ⟨lb,top⟩ := mem_Ico.mp bm
  rcases cover b (mem_Ico.mpr ⟨lb,by omega⟩) with tight|fragment|child
  · obtain ⟨cut,two,room,eq,pressure,paid⟩ := tight
    exact .inl ⟨cut,two,room,eq,pressure,by omega⟩
  · obtain ⟨cut,room,t,tm,fit,pressure⟩ := fragment
    exact .inr (.inl ⟨cut,room,t,tm,by omega,pressure⟩)
  · obtain ⟨cut,d,dm,big,fit,paid⟩ := child
    exact .inr (.inr ⟨cut,d,dm,big,fit,by omega⟩)

theorem window_iff {q r n K} (cut : 5≤q) (two : 2≤r) (room : r≤2*q) :
    Window n r q K ↔ ∃h,Covers q r (2*r) h K ∧ 3*r≤h+2 ∧ n<2*r+h := by
  constructor
  · intro test
    exact ⟨neededHeight n r,test.2.2.2,height_bills n r⟩
  · rintro ⟨h,cover,paid,small⟩
    refine ⟨cut,two,room,covers_mono cover ?_⟩
    unfold neededHeight
    omega

theorem raw_window {q r n K} (law : RawBudget q r n)
    (excluded : ∀c : CHRuleCatalog.Input,CHRuleCatalog.Bad c → c.s∉K) :
    ¬Window n r q K := by
  rintro ⟨cut,two,room,cert⟩
  exact raw_exit law excluded cut two room cert (height_bills n r).1 (height_bills n r).2

theorem least_window {q r n} (law : OrderBudget q r n) : ¬Window n r q (range r) := by
  rintro ⟨cut,two,room,cert⟩
  have order := (law _ (by omega) two room cert).1 cut (height_bills n r).1
  exact (Nat.not_lt_of_ge order) (height_bills n r).2

attribute [aesop safe forward (immediate := [law,excluded]) (rule_sets := [CHGraphFamilies])] raw_window
attribute [aesop safe forward (immediate := [law]) (rule_sets := [CHGraphFamilies])] least_window
/-- A proof for a previously verified range of degrees can be reused as a set
of excluded quotas. Its endpoint is inferred from the imported theorem. -/
structure QuotaLibrary where
  ranks : Finset ℕ
  excluded : ∀c : CHRuleCatalog.Input,CHRuleCatalog.Bad c → c.s∉ranks

def library_from_floor {k : ℕ}
    (floor : ∀{n r q},VerifiedDegreeFrontier.Remaining n r q → k≤r) : QuotaLibrary :=
  ⟨range k,fun c bad=>by
    obtain short|bounds := VerifiedDegreeFrontier.cycle_or_remaining c.D bad.order
      (CHRuleCatalog.remaining_from_run c bad).2.1 bad.loopless bad.degree
    · exact (bad.missing short).elim
    · exact fun mem=>Nat.not_lt_of_ge (floor bounds) (mem_range.mp mem)⟩

def verifiedQuotas : QuotaLibrary := library_from_floor VerifiedDegreeFrontier.Remaining.floor

theorem verified_window {q r n} (law : RawBudget q r n) : ¬Window n r q verifiedQuotas.ranks :=
  raw_window law verifiedQuotas.excluded

/-- Full literal CH everywhere the decidable profile inequalities hold. No
minimal-descendant assumption or unproved smaller degree is required. -/
theorem literal_window {n r} {D : CH.Digraph} (hn : 0<n) (hr : 0<r)
    (loopless : CH.Loopless D n) (degree : CH.MinOutdegreeAtLeast D n r)
    (region : Window n r (CH.ceilDiv n r) verifiedQuotas.ranks) :
    CH.HasDirectedCycleAtMost D n (CH.ceilDiv n r) := by
  by_contra missing
  exact verified_window (raw_budget (p:=⟨n,r,D⟩) ⟨hn,hr,loopless,degree,missing⟩) region

attribute [aesop safe forward (immediate := [law]) (rule_sets := [CHGraphFamilies])] verified_window
#print axioms literal_window

#print axioms window_iff
#print axioms least_window

#print axioms raw_budget
#print axioms literal_profile

#print axioms third
#print axioms advance
#print axioms order_budget
#print axioms least_order
end LeanCH.BR.GuardedProfileBudget
