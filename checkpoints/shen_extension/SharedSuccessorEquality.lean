import checkpoints.shen_extension.OneSpareBankPacking

namespace LeanCH.BR.OneSpareGrowth
open Finset BRq2 BRq3 BR45 DotClonePairCompletion

/-- At an even order twice a uniform inclusive ball floor, short roots map
to tall labels. If common images certify missing reach in both directions,
the entire excess and missing-pair count is determined. -/
theorem shared_successor_equality {D V q k b} (free : QFree D V q) (distance : k+k≤q)
    (order : V.card=2*b) (floor : ∀v∈V,b≤(ball D V v k).card) (f : ℕ→ℕ)
    (tall : ∀v∈V,(ball D V v k).card=b → f v∈V ∧ b<(ball D V (f v) k).card)
    (miss : ∀u∈V,∀v∈V,(ball D V u k).card=b → (ball D V v k).card=b →
      u≠v → f u=f v → v∉ball D V u k) :
    let S := V.filter (fun v=>(ball D V v k).card=b)
    S.card=b ∧ (V\S).card=b ∧ (orderedIncomparable D V k)=∅ ∧
      ∀v∈V\S,(ball D V v k).card=b+1 := by
  classical
  intro S
  let T := V\S
  let score := fun v=>(ball D V v k).card
  have short {v} (h : v∈S) : score v=b := (mem_filter.mp h).2
  have high (v) (h : v∈T) : b+1≤score v := by
    obtain ⟨vm,off⟩ := mem_sdiff.mp h
    have ge := floor v vm
    exact Nat.lt_of_le_of_ne ge (fun eq=>off (mem_filter.mpr ⟨vm,eq.symm⟩))
  have land : S.image f⊆T := by
    intro w hw
    obtain ⟨v,vs,rfl⟩ := mem_image.mp hw
    obtain ⟨live,ht⟩ := tall v (mem_filter.mp vs).1 (short vs)
    exact mem_sdiff.mpr ⟨live,fun fs=>(Nat.ne_of_gt ht) (short fs)⟩
  have inc : S.offDiag.filter (fun e=>f e.1=f e.2) ⊆ orderedIncomparable D V k := by
    intro e h
    obtain ⟨od,eq⟩ := mem_filter.mp h
    obtain ⟨us,vs,ne⟩ := mem_offDiag.mp od
    have uv := (mem_filter.mp us).1
    have vv := (mem_filter.mp vs).1
    exact mem_filter.mpr ⟨mem_offDiag.mpr ⟨uv,vv,ne⟩, miss _ uv _ vv (short us) (short vs) ne eq,
      miss _ vv _ uv (short vs) (short us) ne.symm eq.symm⟩
  have slots := collision_budget f S
  have used := card_le_card inc
  have targets := card_le_card land
  have part : T.card+S.card=V.card := card_sdiff_add_card_eq_card (filter_subset _ _)
  have spl : (∑v∈T,score v)+(∑v∈S,score v)=∑v∈V,score v := sum_sdiff (f:=score) (filter_subset _ _)
  have lowSum : (∑v∈S,score v)=S.card*b := (sum_congr rfl (fun _ h=>short h)).trans (sum_const_nat (fun _ _=>rfl))
  have hiSum := sum_le_sum high
  rw [sum_const_nat (fun _ _=>rfl)] at hiSum
  have capacity := incomparable_reach_identity free distance
  change (orderedIncomparable D V k).card+2*(∑v∈V,score v)=_ at capacity
  rw [←spl,lowSum] at capacity
  have prod := congrArg (fun n=>n*b) part
  change (T.card+S.card)*b=V.card*b at prod
  rw [add_mul] at prod
  rw [Nat.mul_add,Nat.mul_one] at hiSum
  have spare : (orderedIncomparable D V k).card+2*T.card≤V.card := by nlinarith
  have counts : S.card=b ∧ T.card=b ∧ (orderedIncomparable D V k).card=0 := by omega
  have exactSum : (∑_v∈T,(b+1))=(∑v∈T,score v) := by
    rw [sum_const_nat (fun _ _=>rfl)]
    obtain ⟨s,t,zero⟩ := counts
    rw [zero,s,order] at capacity
    rw [t]
    nlinarith
  exact ⟨counts.1,counts.2.1,card_eq_zero.mp counts.2.2,fun v vm=>((sum_eq_sum_iff_of_le high).mp exactSum v vm).symm⟩

#print axioms shared_successor_equality
end LeanCH.BR.OneSpareGrowth
