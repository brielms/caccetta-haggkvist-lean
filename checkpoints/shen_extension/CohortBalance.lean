import checkpoints.shen_extension.MixedPayerEntry

namespace LeanCH.BR.LowShellCycleSelection
open Finset BRq2 BRq3 BR45 BRsGen ExteriorPacking PhysicalCycleStock
open scoped Classical

/-- Only credits whose two physical representatives both belong to the cohort. -/
noncomputable def credits {D V q r k b} (s : Selection D V q r k b) (K : Finset (Finset ℕ)) :=
  (K.image s.rep).offDiag ∩ DotClonePairCompletion.orderedIncomparable D V k

theorem separate_credits {D V q r k b C} (s : Selection D V q r k b) {K J : Finset (Finset ℕ)}
    (keys : K⊆claims s C) (other : J⊆claims s C) (apart : Disjoint K J) :
    (credits s K).card+(credits s J).card≤(receipts s C).card := by
  classical
  have sub H (h : H⊆claims s C) : credits s H⊆receipts s C := by
    intro e em
    obtain ⟨edge,missing⟩ := mem_inter.mp em
    obtain ⟨a,b,ne⟩ := mem_offDiag.mp edge
    exact mem_inter.mpr ⟨mem_offDiag.mpr ⟨image_subset_image h a,image_subset_image h b,ne⟩,missing⟩
  have sep : Disjoint (credits s K) (credits s J) := by
    apply disjoint_left.mpr
    intro e em fm
    obtain ⟨Y,ym,hy⟩ := mem_image.mp (mem_offDiag.mp (mem_inter.mp em).1).1
    obtain ⟨Z,zm,hz⟩ := mem_image.mp (mem_offDiag.mp (mem_inter.mp fm).1).1
    have eq := (rep_key s (mem_filter.mp (keys ym)).1).symm.trans
      ((congrArg (N2 D V) (hy.trans hz.symm)).trans (rep_key s (mem_filter.mp (other zm)).1))
    exact disjoint_left.mp apart ym (eq.symm ▸ zm)
  have union := card_le_card (union_subset (sub K keys) (sub J other))
  rwa [card_union_of_disjoint sep] at union

theorem cohort_unit_bill {D V q r target C} (free : QFree D V q) (reg : OutEq r D V)
    (s : Selection D V q r 3 (3*r)) (room : RoutingRoom q r V.card target)
    {J : Finset (Finset ℕ)} (keys : J⊆claims s C)
    (dag : ∀Y∈J,QFree D (outN D V (s.rep Y)) (outN D V (s.rep Y)).card) :
    (∑Y∈J,shellDebt D V 3 (3*r) Y)≤(credits s J).card+1 := by
  classical
  have hr := room.growth.2.1
  have key Y (ym : Y∈J) := (mem_filter.mp (keys ym)).1
  have data Y (ym : Y∈J) : ClaimData D V Y C q r (s.rep Y) target :=
    (mem_filter.mp (keys ym)).2 ▸ claim_data free reg (by omega) s (key Y ym) room.cycle (dag Y ym)
      room.close room.space room.distance room.score
  let R := J.image s.rep
  have holes : R.offDiag ⊆ credits s J := by
    intro e em
    obtain ⟨am,bm,ne⟩ := mem_offDiag.mp em
    obtain ⟨Y,y,hy⟩ := mem_image.mp am
    obtain ⟨Z,z,hz⟩ := mem_image.mp bm
    have unequal : Y≠Z := fun eq=>ne (hy.symm.trans ((congrArg s.rep eq).trans hz))
    have no i (im : i∈J) j (jm : j∈J) (ij : i≠j) := separate_claims free
      (by have := room.cycle.1; omega) reg (by omega) (rep_native s (key i im)) (rep_native s (key j jm))
      (rep_key s (key i im)) (rep_key s (key j jm)) ij (data i im) (data j jm)
    exact mem_inter.mpr ⟨em,mem_filter.mpr ⟨mem_offDiag.mpr ⟨hy ▸ rep_native s (key Y y),
      hz ▸ rep_native s (key Z z),ne⟩,hy ▸ hz ▸ no Y y Z z unequal,hy ▸ hz ▸ no Z z Y y unequal.symm⟩⟩
  have count : R.card=J.card := card_image_of_injOn (fun a am b bm eq=>
    (rep_key s (key a am)).symm.trans ((congrArg (N2 D V) eq).trans (rep_key s (key b bm))))
  have num := card_le_card holes
  rw [offDiag_card,count] at num
  have cost := sum_le_sum (fun Y (ym : Y∈J)=>(acyclic_class_debit free reg (by omega) s (key _ ym) room.cycle
    (dag Y ym) (by have := room.close; have := room.space; omega) room.distance).2)
  simp only [sum_const_nat (fun _ _=>rfl),Nat.mul_one] at cost
  by_cases small : J.card≤1
  · omega
  have := Nat.mul_le_mul_left J.card (show 2≤J.card by omega)
  omega

/-- Split any physical group's account into two disjoint lists of classes.
The outside cost is literal. Internal receipts of the two lists cannot coincide. -/
theorem split_bill {D V q r k b C} (s : Selection D V q r k b) {K J : Finset (Finset ℕ)}
    (keys : K⊆claims s C) (other : J⊆claims s C) (apart : Disjoint K J)
    {a b' : ℕ} (costK : ∑Y∈K,shellDebt D V k b Y≤(credits s K).card+a)
    (costJ : ∑Y∈J,shellDebt D V k b Y≤(credits s J).card+b') :
    netDebt s C≤(a:ℚ)+b'+∑Y∈claims s C\(K∪J),(shellDebt D V k b Y:ℚ) := by
  classical
  have cap := separate_credits s keys other apart
  have aggregate : (∑Y∈K,shellDebt D V k b Y)+(∑Y∈J,shellDebt D V k b Y)≤(receipts s C).card+a+b' := by omega
  have bound : (∑Y∈K,(shellDebt D V k b Y:ℚ))+(∑Y∈J,(shellDebt D V k b Y:ℚ))≤(receipts s C).card+(a:ℚ)+b' := by exact_mod_cast aggregate
  have split := sum_sdiff (union_subset keys other) (f:=fun Y=>(shellDebt D V k b Y:ℚ))
  rw [sum_union apart] at split
  unfold netDebt
  linarith only [bound,split]

#print axioms separate_credits
#print axioms cohort_unit_bill
#print axioms split_bill
end LeanCH.BR.LowShellCycleSelection
