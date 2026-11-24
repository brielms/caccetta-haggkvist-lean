import checkpoints.shen_extension.LabelledLeakageControl

namespace LeanCH.BR.Closure.SoleExitWeightGap
open Finset BRq2 BRq3 BR45 WeightedSD LabelledLeakageCapacity

/-- If an inner row meets its bill with one exit, that exit is a parent of
the root and carries the full cut bill. -/
def PaidSole (q : ℕ) (E : CH.Digraph) (V : Finset ℕ) (w : ℕ→ℚ) (c : ℚ) (a j : ℕ) : Prop :=
  ∃i∈region q E V a,outN E (V\region q E V a) i={j} ∧
    c-mass (region q E V a) w≤q*mass (outN E (V\region q E V a) i) w

theorem parent_bill {q E V w c a j} (hq : 2≤q) (free : QFree E V q)
    (sat : BRsub.Sat q E V) (av : a∈V) (paid : PaidSole q E V w c a j) :
    j∈inN E V a ∧ c-mass V w+w a+mass ((inN E V a).erase j) w≤((q:ℚ)-1)*w j := by
  classical
  obtain ⟨i,ir,one,le⟩ := paid
  let R := region q E V a
  have rs : R⊆V := BRsub.ballSet_subset
  have hit := mem_outN.mp (one ▸ mem_singleton_self j)
  obtain ⟨jv,off⟩ := mem_sdiff.mp hit.1
  have eligible : a∈V.filter (fun x=>i∈region q E V x ∧ j∉region q E V x) :=
    mem_filter.mpr ⟨av,ir,off⟩
  rw [crossing hq free sat (rs ir) jv hit.2] at eligible
  have ja : j∈inN E V a := mem_inN.mpr ⟨jv,(mem_outN.mp (mem_sdiff.mp eligible).1).2⟩
  have complement : V\R=insert a (inN E V a) := by
    ext x
    by_cases xv : x∈V
    · simp only [mem_sdiff,xv,true_and,R,saturated_region hq free sat av xv,mem_insert,mem_inN]
      tauto
    · simp only [mem_sdiff,xv,false_and,mem_insert,mem_inN,or_false]
      have ne : x≠a := fun eq=>xv (eq ▸ av)
      simp [ne]
  have noLoop : a∉inN E V a := fun h=>loopfree free (by omega) av (mem_inN.mp h).2
  have split : mass (V\R) w+mass R w=mass V w := sum_sdiff rs
  rw [complement] at split
  unfold mass at split
  rw [sum_insert noLoop,←sum_erase_add (inN E V a) w ja] at split
  rw [one] at le
  simp only [mass,sum_singleton] at le
  refine ⟨ja,?_⟩
  change c-mass V w+w a+(∑k∈(inN E V a).erase j,w k)≤_
  unfold mass
  dsimp [R] at split
  linarith

/-- Across every set of at most q roots, some root can only use a sole exit
outside the set. Its price must clear the native margin and that root's weight. -/
theorem small_set {q E V w c} (hq : 2≤q) (free : QFree E V q) (sat : BRsub.Sat q E V)
    (pos : ∀v∈V,0≤w v) {S : Finset ℕ} (sv : S⊆V) (live : S.Nonempty) (size : S.card≤q) :
    ∃a∈S,∀j,PaidSole q E V w c a j →
      j∈V\S ∧ c-mass V w+w a≤((q:ℚ)-1)*w j := by
  obtain ⟨s,ss⟩ := live
  obtain ⟨a,as,source,_⟩ := reach_sink_of_card ((free.mono_set sv).reverse) size ss
  refine ⟨a,as,?_⟩
  intro j paid
  obtain ⟨ja,price⟩ := parent_bill hq free sat (sv as) paid
  have jp := mem_inN.mp ja
  have nn : 0≤mass ((inN E V a).erase j) w :=
    mass_nonneg (fun v hv=>pos v (mem_inN.mp (mem_of_mem_erase hv)).1)
  exact ⟨mem_sdiff.mpr ⟨jp.1,fun js=>source j js jp.2⟩,by linarith⟩

theorem gap_forces_multiple {q E V w c} (hq : 2≤q) (free : QFree E V q) (sat : BRsub.Sat q E V)
    (pos : ∀v∈V,0≤w v) {S : Finset ℕ} (sv : S⊆V) (live : S.Nonempty) (size : S.card≤q)
    (gap : ∀a∈S,∀j∈V\S,((q:ℚ)-1)*w j<c-mass V w+w a) :
    ∃a∈S,∀j,¬PaidSole q E V w c a j := by
  obtain ⟨a,ha,all⟩ := small_set (c:=c) hq free sat pos sv live size
  exact ⟨a,ha,fun j paid=>let ⟨out,bill⟩:=all j paid; (gap a ha j out).not_ge bill⟩

#print axioms parent_bill
#print axioms small_set
#print axioms gap_forces_multiple

/-- If every root pays through one head, the root-weighted mean of those head
weights has a lower bound determined by the native surplus and second moment. -/
theorem weighted_bill {q E V w c} (hq : 2≤q) (free : QFree E V q) (sat : BRsub.Sat q E V)
    (pos : ∀a∈V,0≤w a) (norm : mass V w=1)
    (flat : ∀a∈V,WeightedSD.row q E V w a=c)
    (j : ℕ→ℕ) (all : ∀a∈V,PaidSole q E V w c a (j a)) :
    (q:ℚ)*(c-1)+c+((q:ℚ)-1)*(∑a∈V,w a^2)≤(q:ℚ)^2*(∑a∈V,w a*w (j a)) := by
  have per (a) (av : a∈V) :
      (q:ℚ)*(c-1)+WeightedSD.col q E V w a+((q:ℚ)-1)*w a≤(q:ℚ)^2*w (j a) := by
    obtain ⟨ja,bd⟩ := parent_bill hq free sat av (all a av)
    have ins : mass ((inN E V a).erase (j a)) w+w (j a)=mass (inN E V a) w := sum_erase_add _ w ja
    have eq : mass (inN E V a) w=inW E V w a := by simp [mass,inN,inW,sum_filter]
    rw [eq] at ins
    rw [norm] at bd
    unfold WeightedSD.col
    have b : c-1+w a+inW E V w a≤(q:ℚ)*w (j a) := by linarith
    nlinarith only [mul_le_mul_of_nonneg_left b (Nat.cast_nonneg q : (0:ℚ)≤q)]
  have sum := sum_le_sum (s:=V) (fun a av=>mul_le_mul_of_nonneg_left (per a av) (pos a av))
  have sm : ∑a∈V,w a=1 := norm
  have balance := row_col_balance q E V w
  have e : (∑a∈V,w a*WeightedSD.row q E V w a)=c := by
    calc _ = ∑a∈V,w a*c := sum_congr rfl (fun a av=>by rw [flat a av])
         _ = c := by rw [←sum_mul,sm,one_mul]
  simp only [mul_add,Finset.sum_add_distrib] at sum
  have scale (t : ℚ) (f : ℕ→ℚ) : (∑a∈V,w a*(t*f a))=t*∑a∈V,w a*f a := by
    rw [mul_sum]; exact sum_congr rfl (fun _ _=>by ring)
  rw [scale,scale,←sum_mul,sm,one_mul,←balance,e] at sum
  rw [scale ((q:ℚ)^2) (fun a=>w (j a))] at sum
  simpa only [sq] using sum

/-- If no vertex carries more than 1/q² of the mass, a strict native source
has a root that cannot pay its bill through a sole exit. -/
theorem diffuse_forces_multiple {q E V w c} (hq : 2≤q) (free : QFree E V q) (sat : BRsub.Sat q E V)
    (pos : ∀a∈V,0≤w a) (norm : mass V w=1) (high : 1<c)
    (flat : ∀a∈V,WeightedSD.row q E V w a=c)
    (cap : ∀a∈V,(q:ℚ)^2*w a≤1) : ∃a∈V,∀j,¬PaidSole q E V w c a j := by
  classical
  by_contra! alt
  let j a := if av : a∈V then (alt a av).choose else a
  have all (a) (av : a∈V) : PaidSole q E V w c a (j a) := by
    simpa [j,av] using (alt a av).choose_spec
  have bill := weighted_bill hq free sat pos norm flat j all
  have upper : (q:ℚ)^2*(∑a∈V,w a*w (j a))≤mass V w := by
    rw [mul_sum]
    apply sum_le_sum
    intro a av
    have jp := (parent_bill hq free sat av (all a av)).1
    have small := mul_le_mul_of_nonneg_left (cap _ (mem_inN.mp jp).1) (pos _ av)
    linarith only [small]
  have lo : (2:ℚ)≤q := by exact_mod_cast hq
  have squares : 0≤∑a∈V,w a^2 := sum_nonneg (fun _ _=>sq_nonneg _)
  rw [norm] at upper
  linarith [mul_nonneg (by linarith : (0:ℚ)≤(q:ℚ)-1) squares,
    mul_nonneg (Nat.cast_nonneg q : (0:ℚ)≤q) (sub_nonneg.mpr high.le)]

/-- The three heavy labels in the seven-vertex control illustrate the gap.
At root 4, only row 6 meets the bill, through four distinct heads. -/
theorem control_four :
    let V := LabelledLeakageControl.V
    let E := LabelledLeakageControl.E
    let w := LabelledLeakageControl.w
    let R := region 3 E V 4
    R.filter (fun i=>1-mass R w≤3*mass (outN E (V\R) i) w)={6} ∧
      outN E (V\R) 6=range 4 := by
  intro V E w R
  have eq : R=V.filter (fun i=>i≠4 ∧ E i 4≠true) := by
    ext i
    by_cases iv : i∈V
    · simpa [iv] using saturated_region (by decide : 2≤3) LabelledLeakageControl.free
        LabelledLeakageControl.sat (a:=4) (by decide) iv
    · have off : i∉R := fun h=>iv (BRsub.ballSet_subset h)
      simp [iv,off]
  rw [eq]
  decide +kernel

#print axioms weighted_bill
#print axioms diffuse_forces_multiple
#print axioms control_four

/-- A concrete two-head witness on the same saturated graph and prices.
The two heads leave the inner ball of a single root. -/
theorem diffuse_witness {q E V w p c} (hq : 3≤q) (free : QFree E V q)
    (sat : BRsub.Sat q E V) (small : SmallerSmallRow q V.card)
    (wp : ∀a∈V,0<w a) (pp : ∀a∈V,0<p a) (wm : mass V w=1) (pm : mass V p=1)
    (high : 1<c) (flat : ∀a∈V,WeightedSD.row q E V w a=c)
    (cols : ∀a∈V,WeightedSD.col q E V p a=c) (cap : ∀a∈V,(q:ℚ)^2*w a≤1) :
    ∃a∈V,(∀j,¬PaidSole q E V w c a j) ∧ ∃i∈region q E V a,
      let O := outN E (V\region q E V a) i
      c-mass (region q E V a) w≤q*mass O w ∧ 2≤O.card := by
  classical
  obtain ⟨a,av,no⟩ := diffuse_forces_multiple (by omega) free sat (fun i iv=>(wp i iv).le)
    wm high flat cap
  have live {G t} (tp : ∀i∈V,0<t i) (tm : mass V t=1) (row : WeightedSD.row q G V t a=c) :
      (outN G V a).Nonempty := by
    by_contra! empty
    rw [WeightedSD.row,outW_eq_mass,empty] at row
    have le : t a≤mass V t := single_le_sum (fun i iv=>(tp i iv).le) av
    simp [mass] at row
    linarith
  obtain ⟨b,bh⟩ := live (G:=fun i j=>E j i) pp pm (cols a av)
  obtain ⟨bv,ba⟩ := mem_outN.mp bh
  obtain ⟨i,ir,_,all⟩ := PortParentInvariant.common_leaking_row hq free av ⟨b,bv,ba⟩
    (live wp wm (flat a av)) small w wp (wm ▸ high) flat
  obtain ⟨_,bill⟩ := all b bv ba
  rw [(PortParentInvariant.same_ball (d:=q-2) free av bv ba (by omega)).2] at bill
  change c-mass (region q E V a) w≤q*mass (outN E (V\region q E V a) i) w at bill
  refine ⟨a,av,no,i,ir,bill,?_⟩
  let O := outN E (V\region q E V a) i
  change 2≤O.card
  have liveO : O.Nonempty := by
    by_contra! empty
    change c-mass (region q E V a) w≤q*mass O w at bill
    rw [empty] at bill
    have sub : region q E V a⊆V := BRsub.ballSet_subset
    have le := mass_mono sub (fun x xv=>(wp x xv).le)
    simp only [mass,sum_empty,mul_zero] at bill
    change c-mass (region q E V a) w≤0 at bill
    linarith
  have positive := card_pos.mpr liveO
  by_contra! low
  obtain ⟨j,one⟩ := card_eq_one.mp (show O.card=1 by omega)
  exact no j ⟨i,ir,one,bill⟩

#print axioms diffuse_witness
end LeanCH.BR.Closure.SoleExitWeightGap
