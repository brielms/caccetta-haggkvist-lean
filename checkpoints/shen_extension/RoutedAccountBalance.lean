import checkpoints.shen_extension.GlobalCycleDeficit

namespace LeanCH.BR.LowShellCycleSelection
open Finset
open scoped Classical

/-- On one fixed accounting, route small unpaid accounts to actual destinations.
Each destination uses its own total incoming debt. An outstanding priority
account is either short locally or receives a particular incoming load.
All balances and the reciprocal inequality are on this same allocation. -/
theorem routed_balance {α : Type*} [DecidableEq α] (F : Finset α) (live : F.Nonempty)
    (debt : α→ℚ) (stock : Finset α→α→ℚ) (priority strong : α→Prop)
    (chooseDest : α→α)
    (dest : ∀a∈F,¬priority a → ¬strong a → stock F a≤debt a → strong (chooseDest a))
    (unpaid : ∀K : Finset α,(∀z∈K,strong z) → ∑z∈F∪K,stock (F∪K) z≤∑a∈F,debt a)
    (stable : ∀K : Finset α,(∀z∈K,strong z) → ∀a∈F,stock (F∪K) a=stock F a)
    (nonneg : ∀K : Finset α,(∀z∈K,strong z) → ∀a∈F∪K,0≤stock (F∪K) a) :
    let P := F.filter (fun a=>¬priority a ∧ ¬strong a ∧ stock F a≤debt a)
    let K := P.image chooseDest
    let incoming := fun z=>∑a∈P.filter (fun a=>chooseDest a=z),debt a
    ∃z∈(F∪K)\P,(z∈F ∧ (priority z ∨ strong z) ∨ z∈K) ∧
      stock (F∪K) z≤(if z∈F then debt z else 0)+incoming z := by
  classical
  dsimp only
  let P := F.filter (fun a=>¬priority a ∧ ¬strong a ∧ stock F a≤debt a)
  let K := P.image chooseDest
  let U := (F∪K)\P
  let cost := fun z=>∑a∈P.filter (fun a=>chooseDest a=z),debt a
  change ∃z∈U,(z∈F ∧ (priority z ∨ strong z) ∨ z∈K) ∧ stock (F∪K) z≤(if z∈F then debt z else 0)+cost z
  have pf : P⊆F := filter_subset _ _
  have strongK z (zm : z∈K) : strong z := by
    obtain ⟨a,am,rfl⟩ := mem_image.mp zm
    obtain ⟨af,p,t,b⟩ := mem_filter.mp am
    exact dest a af p t b
  have ku : K⊆U := fun z zm=>mem_sdiff.mpr ⟨mem_union_right _ zm,fun x=>(mem_filter.mp x).2.2.1 (strongK z zm)⟩
  have emptyCost z (off : z∉K) : cost z=0 := by
    apply sum_eq_zero
    intro a am
    exact (off ((mem_filter.mp am).2 ▸ mem_image_of_mem chooseDest (mem_filter.mp am).1)).elim
  have hU : U.Nonempty := by
    obtain ⟨a,af⟩ := live
    by_cases paid : a∈P
    · exact ⟨_,ku (mem_image_of_mem _ paid)⟩
    exact ⟨a,mem_sdiff.mpr ⟨mem_union_left _ af,paid⟩⟩
  by_contra! no
  have under z (zu : z∈U) : (if z∈F then debt z else 0)+cost z<stock (F∪K) z := by
    by_cases overlap : z∈K
    · exact no z zu (.inr overlap)
    have zf := (mem_union.mp (mem_sdiff.mp zu).1).resolve_right overlap
    by_cases key : priority z
    · exact no z zu (.inl ⟨zf,.inl key⟩)
    by_cases t : strong z
    · exact no z zu (.inl ⟨zf,.inr t⟩)
    rw [ite_eq_left zf,emptyCost z overlap,add_zero,stable K strongK z zf]
    by_contra! short
    exact (mem_sdiff.mp zu).2 (mem_filter.mpr ⟨zf,key,t,short⟩)
  have sums := sum_lt_sum (fun z zm=>(under z zm).le) (hU.imp (fun z zm=>⟨zm,under z zm⟩))
  rw [sum_add_distrib,←sum_filter] at sums
  have uf : U.filter (fun a=>a∈F)=F\P := by ext; simp [U]; tauto
  have billed : ∑z∈U,cost z=∑a∈P,debt a := by
    refine (sum_fiberwise_of_maps_to (fun a (am : a∈P)=>ku (mem_image_of_mem chooseDest am)) debt)
  rw [uf,billed,sum_sdiff pf] at sums
  have all := sum_le_sum_of_subset_of_nonneg (sdiff_subset : U⊆F∪K)
    (fun a am _=>nonneg K strongK a am)
  exact (not_lt_of_ge (unpaid K strongK)) (sums.trans_le all)

#print axioms routed_balance
end LeanCH.BR.LowShellCycleSelection
