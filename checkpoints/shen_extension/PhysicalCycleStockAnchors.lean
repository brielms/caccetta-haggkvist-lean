import checkpoints.shen_extension.PhysicalCycleStockReplay

namespace LeanCH.BR.PhysicalCycleStock
open Finset BRq2 BRq3 BR45 BRsGen RetainedRadiusLayers RetainedMixedCapacity

/-- At minimum degree four, the two growth steps from a heavy first row
give a reusable third-ball bill. Both steps use the literal punctured
prefix of that row. -/
theorem rank_four_full_third {D V q r x} (free : QFree D V q) (hq : 5 ≤ q)
    (hx : x ∈ V) (reg : ∀ v ∈ V, 4 ≤ (outN D V v).card)
    (full : r ≤ (outN D V x).card) (positive : 1 ≤ r)
    (two : r+4 ≤ 2*q+1) (three : r+6 ≤ 3*q+1) :
    r+7 ≤ (ball D V x 3).card := by
  have first : r+1 ≤ (ball D V x 1).card := by
    rw [card_B1 (free.mono_bound (by omega : 4≤q)) hx]
    omega
  have second := PrefixDegreeGrowth.raise_floor (j := 1) (target := r+4) free hx (by omega)
    reg hq first (by omega) (by
      intro m lo hi
      exact ⟨2, by decide, by decide, by omega, by omega⟩)
  change r+4 ≤ (ball D V x 2).card at second
  have third := PrefixDegreeGrowth.raise_floor (j := 2) (target := r+7) free hx (by omega)
    reg hq second (by omega) (by
      intro m lo hi
      by_cases small : m ≤ 2*q+1
      · exact ⟨2, by decide, by decide, by omega, by omega⟩
      · exact ⟨3, by decide, by decide, by omega, by omega⟩)
  exact third

/-- A punctured fourth ball preserves the first-layer rows' entire native
third balls, the second-layer rows' native second balls, and the remaining
third-layer rows' native degree. The first-layer bill can include any
proved increment on a selected subset of those same physical rows. -/
theorem fifth_prefix_budget {D V q u r d base full near first} (free : QFree D V q) (hq : 6 ≤ q)
    (hu : u ∈ V) (degree : ∀x∈V, r ≤ (outN D V x).card)
    (loss : d+(ball D V u 5 \ ball D V u 4).card ≤ r)
    (nearby : ∀x∈(ball D V u 2).erase u, near ≤ (ball D V x 2).card)
    (firstBill : first ≤ ∑ x ∈ (ball D V u 1).erase u, 2*(ball D V x 3).card)
    (scores : ∀W : Finset ℕ, QFree D W q → (∀x∈W,d ≤ (outN D W x).card) →
      ∀x∈W, base ≤ 2*(ball D W x 3).card ∧
        (r ≤ (outN D W x).card → full ≤ 2*(ball D W x 3).card)) :
    let W := (ball D V u 4).erase u
    let A := (ball D V u 3).erase u
    let B := (ball D V u 2).erase u
    let C := (ball D V u 1).erase u
    (W.card-A.card)*base+(A.card-B.card)*full+(B.card-C.card)*(2*near)+first ≤ W.card*(W.card+1) := by
  dsimp only
  let W := (ball D V u 4).erase u
  let A := (ball D V u 3).erase u
  let B := (ball D V u 2).erase u
  let C := (ball D V u 1).erase u
  let score := fun x => (ball D W x 3).card+(ball D W x 3).card
  have aw : A ⊆ W := erase_subset_erase u (ball_mono_radius (by decide : 3≤4))
  have ba : B ⊆ A := erase_subset_erase u (ball_mono_radius (by decide : 2≤3))
  have cb : C ⊆ B := erase_subset_erase u (ball_mono_radius (by decide : 1≤2))
  have ff : QFree D W q := free.mono_set ((erase_subset _ _).trans ball_subset)
  have part := scores W ff (minOut_prefix_erase free hu (by omega) degree loss)
  have minimum x (hx : x∈W) : base ≤ score x := by
    have bound := (part x hx).1
    simpa only [score, two_mul] using bound
  have fullRow x (hx : x∈A) : full ≤ score x := by
    have sub := outN_prefix_erase_root free hu (by omega : 3+1≤q) (mem_of_mem_erase hx)
    have rank := (degree x (ball_subset (mem_of_mem_erase hx))).trans (card_le_card sub)
    have bound := (part x (aw hx)).2 rank
    simpa only [score, two_mul] using bound
  have nearRow x (hx : x∈B) : 2*near ≤ score x := by
    exact (Nat.mul_le_mul_left 2 (nearby x hx)).trans
      (two_scores free hu hx (by decide : 2+2≤4) (by omega) (by decide : 2≤3) (by decide : 2≤3))
  have firstRow x (hx : x∈C) : 2*(ball D V x 3).card ≤ score x :=
    two_scores free hu hx (by decide : 1+3≤4) (by omega) le_rfl le_rfl
  have h0 := sum_le_sum (s := W\A) (fun x hx => minimum x (mem_sdiff.mp hx).1)
  have h1 := sum_le_sum (s := A\B) (fun x hx => fullRow x (mem_sdiff.mp hx).1)
  have h2 := sum_le_sum (s := B\C) (fun x hx => nearRow x (mem_sdiff.mp hx).1)
  have h3 : first ≤ ∑ x ∈ C, score x := firstBill.trans (sum_le_sum firstRow)
  rw [sum_const_nat (fun _ _ => rfl), card_sdiff_of_subset aw] at h0
  rw [sum_const_nat (fun _ _ => rfl), card_sdiff_of_subset ba] at h1
  rw [sum_const_nat (fun _ _ => rfl), card_sdiff_of_subset cb] at h2
  have s0 := sum_sdiff aw (f := score)
  have s1 := sum_sdiff ba (f := score)
  have s2 := sum_sdiff cb (f := score)
  have bound := weighted_rows ff (by omega : 3+3≤q) (score := score) (fun _ _ => le_rfl)
  change (W.card-A.card)*base+(A.card-B.card)*full+(B.card-C.card)*(2*near)+first ≤ W.card*(W.card+1)
  omega

#print axioms rank_four_full_third
#print axioms fifth_prefix_budget
end LeanCH.BR.PhysicalCycleStock
