import checkpoints.shen_extension.dot_tensor_research.DotDegreeSevenQ6Order42Budget_20261121

namespace LeanCH.BR.DotDegreeSevenLow
open Finset BRq2 BRq3 BR45 BRsGen DotClonePairCompletion
open scoped BigOperators

/-- The order-28 closure given the two native guarded marks per bank
and their shared-row payment. Missing pairs are accounted on the one
original host, not by declaring separate capacities for the groups. -/
theorem order28_guarded_bank_budget {ι : Type*} [DecidableEq ι]
    {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V 4) (ho : OutEq 7 D V) (hn : V.card=28)
    (K : Finset ι) (roots escorts : ι→Finset ℕ)
    (partition : V.filter (fun v => (ball D V v 2).card=14) = K.biUnion roots)
    (dis : (↑K : Set ι).PairwiseDisjoint roots)
    (esub : ∀ B∈K, escorts B⊆V) (e2 : ∀ B∈K, (escorts B).card=2)
    (miss : ∀ g∈K, ∀ v∈roots g,
      (roots g).erase v⊆V \ (ball D V v 2 ∪ reverseBall D V v 2))
    (pay : ∀ v∈V, 14+(K.filter (fun B => v∈escorts B)).card ≤
      (ball D V v 2).card) : False := by
  classical
  let L := V.filter (fun v => (ball D V v 2).card=14)
  let N := V.filter (fun v => 14<(ball D V v 2).card)
  let E (v : ℕ) := (ball D V v 2).card-14
  have floor (v) (hv : v∈V) : 14≤(ball D V v 2).card :=
    floor_two14 (by decide) hf (fun x hx => (ho x hx).ge) hv
  have mb := incomparable_reach_identity hf (by decide : 2+2≤4)
  have summ :
      (∑ v∈V,(ball D V v 2).card)=14*V.card+∑ v∈V,E v := by
    rw [Nat.mul_comm 14,←Finset.sum_const_nat (s:=V) (fun _ _ => rfl),←sum_add_distrib]
    apply sum_congr rfl
    intro v hv
    have a := floor v hv
    change (ball D V v 2).card=14+((ball D V v 2).card-14)
    omega
  rw [summ,hn] at mb
  have es : (orderedIncomparable D V 2).card+2*(∑ v∈V,E v)=28 := by omega
  have nel : N.card≤∑ v∈V,E v := by
    have h : (∑ v∈N,(1:ℕ))≤∑ v∈N,E v := by
      apply sum_le_sum
      intro v hv
      have n := (mem_filter.mp hv).2
      change 1≤(ball D V v 2).card-14
      omega
    rw [Finset.sum_const_nat (fun _ _ => rfl),Nat.mul_one] at h
    exact h.trans (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => Nat.zero_le _))
  have CN : N=V\L := by
    ext v
    simp only [N,L,mem_filter,mem_sdiff]
    constructor
    · rintro ⟨hv,gt⟩
      exact ⟨hv,fun h => (Nat.ne_of_gt gt) h.2⟩
    · rintro ⟨hv,neq⟩
      exact ⟨hv,by have a:=floor v hv; by_contra! n; exact neq ⟨hv,by omega⟩⟩
  have split : N.card+L.card=28 := by
    rw [CN,←hn]
    exact card_sdiff_add_card_eq_card (filter_subset _ _)
  have tax : (∑ v∈V,(K.filter (fun B => v∈escorts B)).card)=2*K.card := by
    calc
      _ = ∑ v∈V, ∑ B∈K, (if v∈escorts B then (1 : ℕ) else 0) := by
        apply sum_congr rfl
        intro v hv
        rw [←sum_filter]
        simp
      _ = ∑ B∈K, ∑ v∈V, (if v∈escorts B then (1 : ℕ) else 0) := sum_comm
      _ = ∑ B∈K,(2 : ℕ) := by
        apply sum_congr rfl
        intro B hB
        simp [sum_ite_mem, inter_eq_right.mpr (esub B hB),e2 B hB]
      _ = 2*K.card := by rw [Finset.sum_const_nat (fun _ _ => rfl),Nat.mul_comm]
  have total := sum_le_sum pay
  rw [sum_add_distrib,tax,Finset.sum_const_nat (fun _ _ => rfl),summ,Nat.mul_comm V.card 14] at total
  have ll : L.card=∑ g∈K,(roots g).card := by
    rw [show L=K.biUnion roots from partition,card_biUnion dis]
  have ml :
      (∑ g∈K,(roots g).card*((roots g).card-1))≤(orderedIncomparable D V 2).card := by
    rw [incomparable_card_rows]
    calc
      _ = ∑ g∈K,∑ _v∈roots g,((roots g).card-1) := by
        simp only [Finset.sum_const_nat (fun _ _ => rfl)]
      _ ≤ ∑ g∈K,∑ v∈roots g,(V\(ball D V v 2∪reverseBall D V v 2)).card := by
        apply sum_le_sum
        intro g hg
        apply sum_le_sum
        intro v hv
        simpa only [card_erase_of_mem hv] using card_le_card (miss g hg v hv)
      _ = ∑ v∈L,(V\(ball D V v 2∪reverseBall D V v 2)).card := by
        rw [show L=K.biUnion roots from partition,sum_biUnion dis]
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => Nat.zero_le _)
  have group (g : ι) (_ : g∈K) :
      2*(roots g).card≤(roots g).card*((roots g).card-1)+2 := by
    let t := (roots g).card
    change 2*t≤t*(t-1)+2
    cases t with
    | zero => decide
    | succ a =>
      cases a with
      | zero => decide
      | succ b => simp [Nat.add_mul,Nat.mul_add,Nat.mul_comm]; omega
  have ag := sum_le_sum group
  rw [←mul_sum,←ll,sum_add_distrib,Finset.sum_const_nat (fun _ _ => rfl)] at ag
  have pos : 0<K.card := by
    by_contra! h
    have z : K=∅ := card_eq_zero.mp (by omega)
    simp [z] at ll
    omega
  omega

#print axioms order28_guarded_bank_budget
end LeanCH.BR.DotDegreeSevenLow
