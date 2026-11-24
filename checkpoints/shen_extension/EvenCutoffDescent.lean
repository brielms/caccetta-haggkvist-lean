import checkpoints.shen_extension.CHRuleCatalog
import LeanCH.BR.BRFiveCutoff

namespace LeanCH.BR.SATBoundaryPilot
open Finset BRq2 BRq3 BR45 CHRuleCatalog ShenReachTransition

private theorem child_cutoff {n s t k : ℕ} (hn : 0<n) (hs : 0<s) (ht : 0<t)
    (parent : CH.ceilDiv n s=t*k) : CH.ceilDiv n (t*s)=k := by
  unfold CH.ceilDiv at *
  have old := (Nat.div_eq_iff hs).mp parent
  apply (Nat.div_eq_iff (Nat.mul_pos ht hs)).mpr
  have exchange : t*k*s=k*(t*s) := by ring
  rw [exchange] at old
  have big : s≤t*s := by simpa using Nat.mul_le_mul_right s ht
  omega

/-- When k times the radius fits inside the old cutoff, zero potential admits
every off-diagonal reach entry. This is the existing catalog's child graph. -/
theorem power_out {D : CH.Digraph} {V : Finset ℕ} {q t k x : ℕ}
    (xv : x∈V) (budget : k*t≤q) :
    outN (nextGraph D V q k (fun _=>t) (fun _=>0)) V x = (ball D V x t).erase x := by
  classical
  ext y
  constructor
  · intro head
    obtain ⟨_,edge⟩ := mem_outN.mp head
    obtain ⟨_,ne,ball,_⟩ := of_decide_eq_true edge
    exact mem_erase.mpr ⟨ne.symm,ball⟩
  · intro entry
    obtain ⟨ne,ball⟩ := mem_erase.mp entry
    have cap : ShenLabelledReach.cost D V q (fun _=>t) x y ≤ t := by
      simp only [ShenLabelledReach.cost]
      split <;> first | exact min_le_left _ _ | exact le_rfl
    exact mem_outN.mpr ⟨ball_subset ball,decide_eq_true
      ⟨xv,ne.symm,ball,(Nat.mul_le_mul_left k cap).trans budget⟩⟩

/-- A full set of sufficiently growing radius-t balls funds a literal edge of
the real recursive catalog. The child's cutoff is its own ceil(n/degree). -/
theorem powered_child {p : Input} (b : Bad p) {k t : ℕ} (kt : 0<k) (tt : 0<t)
    (cut : cutoff p=t*k) (growth : ∀x∈range p.n, t*p.s+1≤(ball p.D (range p.n) x t).card) :
    ∃c : Input, Child p c ∧ c.n=p.n ∧ c.s=t*p.s ∧ cutoff c=k := by
  let E := nextGraph p.D (range p.n) (cutoff p) k (fun _=>t) (fun _=>0)
  have eq := child_cutoff b.order b.degree_pos tt cut
  have ktle : k*t≤cutoff p := by rw [cut,Nat.mul_comm]
  have bound : t≤cutoff p := by rw [cut]; simpa using Nat.mul_le_mul_left t kt
  have deg : CH.MinOutdegreeAtLeast E p.n (t*p.s) := by
    intro x inside
    have xv := mem_range.mpr inside
    have old := growth x xv
    have sz := card_erase_add_one (self_mem_ball (D:=p.D) (k:=t) xv)
    have enough : t*p.s≤(outN E (range p.n) x).card := by
      rw [show outN E (range p.n) x=(ball p.D (range p.n) x t).erase x from power_out xv ktle]
      omega
    obtain ⟨H,sub,size⟩ := exists_subset_card_eq enough
    refine ⟨H.toList,by simpa using size,H.nodup_toList,?_⟩
    intro y hy
    obtain ⟨yv,xy⟩ := mem_outN.mp (sub (mem_toList.mp hy))
    exact ⟨mem_range.mp yv,xy⟩
  exact ⟨⟨p.n,t*p.s,E⟩, reach_child b _ _ _ _ (Nat.mul_pos tt b.degree_pos) kt eq
      (fun _ _=>bound) deg, rfl,rfl,eq⟩

/-- Any even cutoff at least the minimum degree descends on the same vertices.
This supplies the degree guard of the existing recursive catalog rule. -/
theorem even_bad_descends {p : Input} (b : Bad p) {k : ℕ}
    (cut : cutoff p=2*k) (large : p.s≤cutoff p) (two : 2≤p.s) :
    ∃c : Input, Child p c ∧ Bad c ∧ c.n=p.n ∧ c.s=2*p.s ∧ cutoff c=k ∧ cutoff c<cutoff p := by
  have kt : 0<k := by omega
  have free := (qfree_of_noShort b.loopless b.missing).mono_bound large
  have degree (x) (hx : x∈range p.n) : p.s≤(outN p.D (range p.n) x).card :=
    Compose.FloorSix.out_card b.degree (mem_range.mp hx)
  obtain ⟨c,edge,order,deg,cc⟩ := powered_child b kt (by decide : 0<2) cut
    (fun x hx=>BRsGen.card_ball_two_ge_twice two free degree hx)
  exact ⟨c,edge,bad_child b edge,order,deg,cc,by omega⟩

/-- The literal CH goal follows from the odd-or-low portion of the lower
region. In particular, the six even boundary orders need no independent
supplier if the induction parameter is the actual cutoff across all degrees. -/
theorem ch_of_odd_or_low (remaining : ∀p : Input, RemainingOrders p →
    cutoff p≤2*p.s-7 → (cutoff p%2=1 ∨ cutoff p<p.s) → ¬Bad p) :
    CH.CaccettaHaggkvistConjecture := by
  have exclude (q : ℕ) : ∀p : Input,cutoff p=q → ¬Bad p := by
    induction q using Nat.strong_induction_on with
    | h q ih =>
      intro p eq bad
      have orders := remaining_from_run p bad
      obtain ⟨three,six,branch⟩ := orders
      by_cases good : cutoff p%2=1 ∨ cutoff p<p.s
      · have low : cutoff p≤2*p.s-7 := by
          obtain ⟨bd,seven,_,_⟩|⟨bd,_⟩ := branch
          · omega
          · exact bd
        exact remaining p (remaining_from_run p bad) low good bad
      · have even : cutoff p=2*(cutoff p/2) := by omega
        obtain ⟨c,_,child,_,_,_,smaller⟩ := even_bad_descends bad even (by omega) (by omega)
        exact ih (cutoff c) (by omega) c rfl child
  intro n s D hn hs loop deg
  by_contra no
  let p : Input := ⟨n,s,D⟩
  exact exclude (cutoff p) p rfl ⟨hn,hs,loop,deg,no⟩

#print axioms powered_child
#print axioms even_bad_descends
#print axioms ch_of_odd_or_low
end LeanCH.BR.SATBoundaryPilot
