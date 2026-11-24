import checkpoints.shen_extension.EvenCutoffDescent

namespace LeanCH.BR.OneLossCutoffDescent
open Finset BRq2 BRq3 BR45 CHRuleCatalog ShenReachTransition

/-- At order at most 2q the induced first neighbourhood has a row with
at most one internal head. Its other heads all belong to the second layer. -/
theorem radius_two {D : CH.Digraph} {V : Finset ℕ} {q s u : ℕ}
    (two : 2≤q) (pos : 0<s) (room : s≤2*q) (free : QFree D V q)
    (degree : ∀x∈V,s≤(outN D V x).card) (hu : u∈V) : 2*s≤(ball D V u 2).card := by
  obtain ⟨F,sub,reg⟩ := exists_outEq degree
  have safe := qfree_sub sub free
  let A := outN F V u
  have ac : A.card=s := reg u hu
  obtain ⟨y,ya,low⟩ : ∃y∈A,(outN F A y).card≤1 := by
    by_contra! allRows
    have h := corB (by omega : 1≤q) (safe.mono_set (outN_subset : A⊆V))
      (fun i hi=>allRows i hi) (card_pos.mp (ac ▸ pos))
    change 2*q+1≤A.card at h
    omega
  let H := outN F V y
  have hc : H.card=s := reg y (outN_subset ya)
  have meet : A∩H=outN F A y := by
    ext j
    simp only [mem_inter,mem_outN,H]
    exact ⟨fun h=>⟨h.1,h.2.2⟩,fun h=>⟨h.1,outN_subset h.1,h.2⟩⟩
  have inside : insert u (A∪H) ⊆ ball F V u 2 := by
    intro j hj
    rcases mem_insert.mp hj with rfl | hj
    · exact self_mem_ball hu
    rcases mem_union.mp hj with ja | jh
    · exact ball_mono_radius (by decide : 1≤2) (mem_ball_one_of_out ja)
    · exact ball_step (mem_ball_one_of_out ya) (outN_subset jh) (mem_outN.mp jh).2
  have outside : u∉A∪H := by
    rintro hit
    rcases mem_union.mp hit with a | h
    · exact loopfree safe (by omega) hu (mem_outN.mp a).2
    · exact digonfree safe two hu (outN_subset ya) (mem_outN.mp ya).2 (mem_outN.mp h).2
  have total := card_le_card (inside.trans (ball_sub (W:=V) (u:=u) (k:=2) sub))
  rw [card_insert_of_notMem outside] at total
  have count := card_union_add_card_inter A H
  rw [meet] at count
  omega

/-- Parameter pairs this transition sends to a strictly smaller cutoff. -/
def Window (n s q : ℕ) : Prop := s≤2*q ∧ n≤(q/2)*(2*s-1)

theorem descends {p : Input} (bad : Bad p) (two : 2≤cutoff p)
    (window : Window p.n p.s (cutoff p)) :
    ∃c : Input, Child p c ∧ Bad c ∧ c.n=p.n ∧ c.s=2*p.s-1 ∧ cutoff c≤cutoff p/2 := by
  let d := 2*p.s-1
  let k := CH.ceilDiv p.n d
  have dp : 0<d := by dsimp [d]; have := bad.degree_pos; omega
  have hn := bad.order
  have kp : 0<k := by
    dsimp [k,CH.ceilDiv]
    exact Nat.div_pos (by omega) dp
  obtain ⟨room,fit⟩ := window
  have cap : k≤cutoff p/2 := by
    have h : p.n+d-1<(cutoff p/2+1)*d := by rw [Nat.add_mul,Nat.one_mul]; change p.n≤cutoff p/2*d at fit; omega
    have := (Nat.div_lt_iff_lt_mul dp).mpr h
    dsimp [k,CH.ceilDiv]; omega
  let E := nextGraph p.D (range p.n) (cutoff p) k (fun _=>2) (fun _=>0)
  have growth (x : ℕ) (hx : x∈range p.n) := radius_two (u:=x) two bad.degree_pos room (qfree_of_noShort bad.loopless bad.missing)
    (fun y hy=>Compose.FloorSix.out_card bad.degree (mem_range.mp hy)) hx
  have degree : CH.MinOutdegreeAtLeast E p.n d := by
    intro x hx
    have xv := mem_range.mpr hx
    have g := growth x xv
    have eq := card_erase_add_one (self_mem_ball (D:=p.D) (k:=2) xv)
    have fund : d≤(outN E (range p.n) x).card := by
      rw [SATBoundaryPilot.power_out xv (by omega : k*2≤cutoff p)]
      dsimp [d]; omega
    obtain ⟨T,sub,sz⟩ := exists_subset_card_eq fund
    refine ⟨T.toList,by simpa using sz,T.nodup_toList,?_⟩
    intro y hy
    obtain ⟨yv,edge⟩ := mem_outN.mp (sub (mem_toList.mp hy))
    exact ⟨mem_range.mp yv,edge⟩
  have child := reach_child bad d k (fun _=>2) (fun _=>0) dp kp rfl (fun _ _=>two) degree
  exact ⟨_,child,bad_child bad child,rfl,rfl,cap⟩

theorem cutoff_four {p : Input} (q4 : cutoff p=4) (win : Window p.n p.s (cutoff p)) : ¬Bad p := by
  intro bad
  obtain ⟨c,_,bc,_,_,cc⟩ := descends bad (by omega) win
  have low := (remaining_from_run c bc).1
  omega

/-- Some degree-doubled children at cutoff three already meet the root
catalog's numerical triangle exclusion. This closes their original parents. -/
theorem cutoff_six {p : Input} (q6 : cutoff p=6) (win : Window p.n p.s (cutoff p))
    (ratio : 3*(p.n-1)*(p.n-1)≤6*(p.n-1)*(2*p.s-1)+7*(2*p.s-1)*(2*p.s-1)) : ¬Bad p := by
  intro bad
  obtain ⟨c,_,bc,cn,cs,cc⟩ := descends bad (by omega) win
  have low := (remaining_from_run c bc).1
  have three : cutoff c=3 := by omega
  exact exclusion_from_run c bc .nonedgeRatio ⟨three,by simpa only [cn,cs] using ratio⟩

/-- In the previously reduced region this step removes exactly an even
cutoff and a minimum amount of order slack. -/
theorem window_iff {n s q : ℕ} (hs : 0<s) (ceiling : q*s<n+s)
    (parity : q%2=1 ∨ q<s) :
    Window n s q ↔ ∃k,q=2*k ∧ q<s ∧ s≤2*q ∧ n+k≤q*s := by
  have amount (k : ℕ) : k*(2*s-1)+k=(2*k)*s := by
    have z : 2*s-1+1=2*s := by omega
    calc
      k*(2*s-1)+k=k*(2*s-1+1) := by ring
      _=(2*k)*s := by rw [z]; ring
  constructor
  · rintro ⟨band,fit⟩
    let k := q/2
    have split : q=2*k ∨ q=2*k+1 := by dsimp [k]; omega
    rcases split with even | odd
    · exact ⟨k,even,by omega,band,by rw [even]; have := amount k; change n≤k*(2*s-1) at fit; omega⟩
    · rw [odd,Nat.add_mul,Nat.one_mul] at ceiling
      change n≤k*(2*s-1) at fit
      have := amount k
      omega
  · rintro ⟨k,rfl,_,band,fit⟩
    refine ⟨band,?_⟩
    have half : 2*k/2=k := by omega
    rw [half]
    have := amount k
    omega

/-- Reuse all earlier exclusions and recur on the child's own cutoff. -/
theorem reduce (remaining : ∀p : Input, RemainingOrders p → cutoff p≤2*p.s-7 →
    (cutoff p%2=1 ∨ cutoff p<p.s) → ¬Window p.n p.s (cutoff p) → ¬Bad p) :
    CH.CaccettaHaggkvistConjecture := by
  have exclude (q : ℕ) : ∀p : Input,cutoff p=q → ¬Bad p := by
    induction q using Nat.strong_induction_on with
    | h q ih =>
      intro p eq bad
      have ord := remaining_from_run p bad
      obtain ⟨three,six,branch⟩ := ord
      by_cases win : Window p.n p.s (cutoff p)
      · by_cases four : cutoff p=4
        · exact cutoff_four four win bad
        by_cases sixPaid : cutoff p=6 ∧ 3*(p.n-1)*(p.n-1)≤6*(p.n-1)*(2*p.s-1)+7*(2*p.s-1)*(2*p.s-1)
        · exact cutoff_six sixPaid.1 win sixPaid.2 bad
        obtain ⟨c,_,bc,_,_,cc⟩ := descends bad (by omega) win
        exact ih (cutoff c) (by omega) c rfl bc
      by_cases good : cutoff p%2=1 ∨ cutoff p<p.s
      · have low : cutoff p≤2*p.s-7 := by
          obtain ⟨bd,seven,_,_⟩|⟨bd,_⟩ := branch
          · omega
          · exact bd
        exact remaining p (remaining_from_run p bad) low good win bad
      · have even : cutoff p=2*(cutoff p/2) := by omega
        obtain ⟨c,_,bc,_,_,_,less⟩ := SATBoundaryPilot.even_bad_descends bad even (by omega) (by omega)
        exact ih (cutoff c) (by omega) c rfl bc
  intro n s D hn hs loop deg
  by_contra no
  let p : Input := ⟨n,s,D⟩
  exact exclude (cutoff p) p rfl ⟨hn,hs,loop,deg,no⟩

#print axioms radius_two
#print axioms descends
#print axioms cutoff_six
#print axioms window_iff
#print axioms cutoff_four
#print axioms reduce
end LeanCH.BR.OneLossCutoffDescent
