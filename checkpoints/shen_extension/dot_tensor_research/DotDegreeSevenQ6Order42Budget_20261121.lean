import checkpoints.shen_extension.dot_tensor_research.DotDegreeSevenQ6Order41Profile_20261121

namespace LeanCH.BR.DotDegreeSevenQ6
open Finset BRq2 BRq3 BR45 BRsGen DotClonePairCompletion
open scoped BigOperators

/-- The order-42 contradiction at precisely the paired-bank interface.
J indexes root groups by bank and type; banks with two types are charged
once for their seven tall labels and separately for intra-type holes. -/
theorem order42_bank_budget {ι : Type*} [DecidableEq ι] {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V 6) (ho : OutEq 7 D V) (ne : V.Nonempty) (hn : V.card≤42)
    (J : Finset ι) (roots : ι→Finset ℕ) (H : Finset ℕ) (k : ℕ)
    (jc : J.card≤2*k) (hc : H.card=7*k)
    (partition : V.filter (fun v => (ball D V v 3).card=21) = J.biUnion roots)
    (rsub : ∀ g∈J, roots g⊆V)
    (dis : (↑J : Set ι).PairwiseDisjoint roots)
    (htall : H⊆V.filter (fun v => 21<(ball D V v 3).card))
    (miss : ∀ g∈J, ∀ v∈roots g,
      (roots g).erase v⊆V \ (ball D V v 3 ∪ reverseBall D V v 3)) : False := by
  classical
  let L := V.filter (fun v => (ball D V v 3).card=21)
  let N := V.filter (fun v => 21<(ball D V v 3).card)
  let E (v : ℕ) := (ball D V v 3).card-21
  have floor (v) (hv : v∈V) : 21≤(ball D V v 3).card :=
    floor_three21 hf (fun x hx => (ho x hx).ge) hv
  have mb := incomparable_reach_identity hf (by decide : 3+3≤6)
  have summ :
      (∑ v∈V,(ball D V v 3).card)=21*V.card+∑ v∈V,E v := by
    rw [Nat.mul_comm 21,←Finset.sum_const_nat (s:=V) (fun _ _ => rfl),←sum_add_distrib]
    apply sum_congr rfl
    intro v hv
    have a := floor v hv
    change (ball D V v 3).card=21+((ball D V v 3).card-21)
    omega
  rw [summ] at mb
  have nprod : V.card*(V.card+1)≤V.card*43 :=
    Nat.mul_le_mul_left _ (by omega)
  have es : (orderedIncomparable D V 3).card+2*(∑ v∈V,E v)≤V.card := by omega
  have nel : N.card≤∑ v∈V,E v := by
    have h : (∑ v∈N,(1:ℕ))≤∑ v∈N,E v := by
      apply sum_le_sum
      intro v hv
      have n := (mem_filter.mp hv).2
      change 1≤(ball D V v 3).card-21
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
  have split : N.card+L.card=V.card := by
    rw [CN]
    exact card_sdiff_add_card_eq_card (filter_subset _ _)
  have tl : 7*k≤∑ v∈V,E v := by
    exact hc ▸ (card_le_card htall).trans nel
  have ll : L.card=∑ g∈J,(roots g).card := by
    rw [show L=J.biUnion roots from partition,card_biUnion dis]
  have ml :
      (∑ g∈J,(roots g).card*((roots g).card-1))≤(orderedIncomparable D V 3).card := by
    rw [incomparable_card_rows]
    calc
      _ = ∑ g∈J,∑ _v∈roots g,((roots g).card-1) := by
        simp only [Finset.sum_const_nat (fun _ _ => rfl)]
      _ ≤ ∑ g∈J,∑ v∈roots g,(V\(ball D V v 3∪reverseBall D V v 3)).card := by
        apply sum_le_sum
        intro g hg
        apply sum_le_sum
        intro v hv
        simpa only [card_erase_of_mem hv] using card_le_card (miss g hg v hv)
      _ = ∑ v∈L,(V\(ball D V v 3∪reverseBall D V v 3)).card := by
        rw [show L=J.biUnion roots from partition,sum_biUnion dis]
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => Nat.zero_le _)
  have group (g : ι) (_ : g∈J) :
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
  have nn := card_pos.mpr ne
  omega

#print axioms order42_bank_budget
end LeanCH.BR.DotDegreeSevenQ6
