import checkpoints.pair_tilt_20261119.DeadExitInterval

namespace LeanCH.BR.Closure.PortParentInvariant
open Finset BRq2 BRq3 BR45 WeightedSD

/-- Below the return length, deleting the root and any one of its parents
preserves the native heads and their whole forward ball. -/
theorem same_ball {q d E V a b} (free : QFree E V q) (av : a∈V) (bv : b∈V)
    (ba : E b a=true) (room : d+2≤q) :
    let U := (V.erase a).erase b
    outN E U a=outN E V a ∧
    BRsub.ballSet E U (outN E U a) d=BRsub.ballSet E V (outN E V a) d := by
  classical
  intro U
  let H := outN E V a
  let B := BRsub.ballSet E V H d
  have avoid : ∀r∈B,r≠a ∧ r≠b := by
    intro r rr
    obtain ⟨h,hh,hit⟩ := BRsub.mem_ballSet.mp rr
    obtain ⟨_,k,le,p⟩ := mem_ball.mp hit
    have path := Walk.step (mem_outN.mp hh).1 (mem_outN.mp hh).2 p
    constructor
    · rintro rfl; exact free _ _ (by omega) (by omega) path
    · rintro rfl; exact free _ _ (by omega) (by omega) (path.snoc av ba)
  have hsub : H⊆U := by
    intro h hh
    have hv := (mem_outN.mp hh).1
    obtain ⟨ha,hb⟩ := avoid h (BRsub.mem_ballSet.mpr ⟨h,hh,self_mem_ball hv⟩)
    exact mem_erase.mpr ⟨hb,mem_erase.mpr ⟨ha,hv⟩⟩
  have heads : outN E U a=H := by
    ext h
    exact ⟨fun h₁=>mem_outN.mpr ⟨(mem_erase.mp (mem_erase.mp (mem_outN.mp h₁).1).2).2,
      (mem_outN.mp h₁).2⟩,fun h₂=>mem_outN.mpr ⟨hsub h₂,(mem_outN.mp h₂).2⟩⟩
  have del : ({a,b}:Finset ℕ)⊆V\B := by
    intro x hx
    simp only [mem_insert,mem_singleton] at hx
    rcases hx with rfl|rfl
    · exact mem_sdiff.mpr ⟨av,fun h=>(avoid _ h).1 rfl⟩
    · exact mem_sdiff.mpr ⟨bv,fun h=>(avoid _ h).2 rfl⟩
  have carrier : U=V\{a,b} := by ext x; simp [U]; tauto
  exact ⟨heads,by rw [heads,carrier]; exact RankedMerge.ball_delete del⟩

/-- On the native parent-independent ball, a near row has no outgoing leakage. -/
theorem near_closed {q E V a} (hq : 3≤q)
    {r} (near : r∈BRsub.ballSet E V (outN E V a) (q-3)) :
    (V\BRsub.ballSet E V (outN E V a) (q-2)).filter (fun v=>E r v=true)=∅ := by
  apply eq_empty_of_forall_notMem
  intro x hx
  simpa using DeadExit.near_leak (V:=V) hq near hx

/-- A single native witness works simultaneously for every choice of deleted parent.
Its leakage into the exterior meets the cut-at-zero bill. It is on the outer layer. -/
theorem common_leaking_row {q E V a} (hq : 3≤q) (free : QFree E V q)
    (av : a∈V) (parents : ∃b∈V,E b a=true) (heads : (outN E V a).Nonempty)
    (small : SmallerSmallRow q V.card) (w : ℕ→ℚ) (pos : ∀v∈V,0<w v)
    {c : ℚ} (high : mass V w<c) (flat : ∀i∈V,WeightedSD.row q E V w i=c) :
    let R := BRsub.ballSet E V (outN E V a) (q-2)
    ∃r∈R,r∉BRsub.ballSet E V (outN E V a) (q-3) ∧
      ∀b∈V,E b a=true →
        let U := (V.erase a).erase b
        let B := BRsub.ballSet E U (outN E U a) (q-2)
        r∈B ∧ c-mass B w≤q*mass ((V\B).filter (fun x=>E r x=true)) w := by
  intro R
  obtain ⟨b,bv,ba⟩ := parents
  have eq := (same_ball (d:=q-2) free av bv ba (by omega)).2
  have rs : R⊆V := BRsub.ballSet_subset
  have proper : R≠V := by
    intro all
    have ar : a∈R := all ▸ av
    change a∈BRsub.ballSet E V (outN E V a) (q-2) at ar
    rw [←eq] at ar
    exact (mem_erase.mp (mem_erase.mp (BRsub.ballSet_subset ar)).2).1 rfl
  obtain ⟨h,hh⟩ := heads
  have live : R.Nonempty := ⟨h,BRsub.mem_ballSet.mpr ⟨h,hh,self_mem_ball (mem_outN.mp hh).1⟩⟩
  obtain ⟨r,rr,low⟩ := small.induced free R rs proper w (fun i hi=>(pos i (rs hi)).le) live
  have rows := DeadExit.native_rows rs flat r rr
  have bill : c-mass R w≤q*mass ((V\R).filter (fun x=>E r x=true)) w := by linarith
  have cap : mass R w≤mass V w := sum_le_sum_of_subset_of_nonneg rs (fun i hi _=>(pos i hi).le)
  refine ⟨r,rr,?_,?_⟩
  · intro near
    rw [show (V\R).filter (fun x=>E r x=true)=∅ from near_closed hq near] at bill
    simp [mass] at bill
    exact (not_le_of_gt (cap.trans_lt high)) bill
  · intro b' bv' ba' U B
    have same : B=R := (same_ball free av bv' ba' (by omega)).2
    exact same.symm ▸ And.intro rr bill

/-- Any nonempty collection of exterior vertices with no arc back into R
contributes its total mass to the lower bound on the native slack. -/
theorem collective_slack {q E V R Z} (free : QFree E V q) (small : SmallerSmallRow q V.card)
    (alive : Z.Nonempty) (outside : Z⊆V\R) (proper : Z≠V)
    (dead : ∀z∈Z,∀r∈R,E z r=false)
    (w : ℕ→ℚ) (pos : ∀v∈V,0≤w v) {c : ℚ} (flat : ∀i∈V,WeightedSD.row q E V w i=c) :
    (q:ℚ)*(c-mass V w)+((q:ℚ)-1)*mass Z w≤q*(c-mass V w+mass (V\R) w)-c := by
  have sub : Z⊆V := outside.trans sdiff_subset
  obtain ⟨z,zz,low⟩ := small.induced free Z sub proper w (fun i hi=>pos i (sub hi)) alive
  have eq := DeadExit.native_rows sub flat z zz
  have caps : (V\Z).filter (fun v=>E z v=true)⊆(V\R)\Z := by
    intro v hv
    obtain ⟨vd,e⟩ := mem_filter.mp hv
    obtain ⟨vv,vz⟩ := mem_sdiff.mp vd
    exact mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨vv,fun vr=>Bool.noConfusion ((dead z zz v vr).symm.trans e)⟩,vz⟩
  have le : mass _ w≤mass _ w := sum_le_sum_of_subset_of_nonneg caps
    (fun v hv _=>pos v (mem_sdiff.mp (mem_sdiff.mp hv).1).1)
  have split : mass ((V\R)\Z) w+mass Z w=mass (V\R) w := sum_sdiff outside
  nlinarith [mul_le_mul_of_nonneg_left le (Nat.cast_nonneg q : (0:ℚ)≤q),
    congrArg (fun t : ℚ=>(q:ℚ)*t) split]

#print axioms same_ball
#print axioms common_leaking_row
#print axioms collective_slack
end LeanCH.BR.Closure.PortParentInvariant
