import checkpoints.shen_extension.dot_tensor_research.DotDegreeSevenQ5Order34_20261121

namespace LeanCH.BR.DotDegreeSevenLow
open Finset BRq2 BRq3 BR45 BRsGen
open scoped BigOperators

noncomputable def missingMixed (D : CH.Digraph) (V : Finset ℕ) (u : ℕ) :=
  V \ (ball D V u 2 ∪ reverseBall D V u 3)

noncomputable def mixedScore (D : CH.Digraph) (V : Finset ℕ) (u : ℕ) :=
  (ball D V u 2).card + (ball D V u 3).card

/-- The exact leftover of the radius-two / reverse-three partition. -/
theorem mixedScore_with_missing {D : CH.Digraph} {V : Finset ℕ}
    (hf : QFree D V 5) :
    (∑ u∈V, (missingMixed D V u).card) + (∑ u∈V, mixedScore D V u) =
      V.card*(V.card+1) := by
  classical
  have local_eq (x : ℕ) (hx : x∈V) :
      (missingMixed D V x).card +
        ((ball D V x 2).card + (reverseBall D V x 3).card) = V.card+1 := by
    let F := ball D V x 2
    let I := reverseBall D V x 3
    have hI : I⊆(V \ F) ∪ {x} := reverseBall_subset_complement hf (by decide : 2+3≤5)
    have hmeet : F∩I={x} := by
      ext y
      constructor
      · intro m
        obtain ⟨f,g⟩ := mem_inter.mp m
        rcases mem_union.mp (hI g) with h | h
        · exact ((mem_sdiff.mp h).2 f).elim
        · exact h
      · intro m
        obtain rfl := mem_singleton.mp m
        exact mem_inter.mpr ⟨self_mem_ball hx,mem_filter.mpr ⟨hx,self_mem_ball hx⟩⟩
    have hsub : F∪I ⊆ V := union_subset ball_subset (filter_subset _ _)
    have h1 := card_sdiff_add_card_eq_card hsub
    have h2 := card_union_add_card_inter F I
    rw [hmeet,card_singleton] at h2
    change (V \ (F∪I)).card+(F.card+I.card)=V.card+1
    omega
  have eq := sum_congr (s₁:=V) rfl local_eq
  rw [sum_add_distrib,sum_add_distrib,sum_reverseBall_eq_sum_ball,Finset.sum_const_nat (fun _ _ => rfl)] at eq
  unfold mixedScore
  rw [sum_add_distrib]
  exact eq

/-- Final accounting: if the geometric input supplies four escorts per
actual short bank at the row's full multiplicity, short banks are impossible.
The hypotheses retain the actual groups and missing-pair witnesses. -/
theorem no_short_banks_of_escort_certificate
    {D : CH.Digraph} {V : Finset ℕ} {K : Finset (Finset ℕ)}
    (hf : QFree D V 5) (hn : V.card=35)
    (L : Finset ℕ) (roots escorts : Finset ℕ → Finset ℕ)
    (hL : L = K.biUnion roots)
    (rsub : ∀ B∈K, roots B⊆V) (hne : ∀ B∈K, (roots B).Nonempty)
    (ed : (↑K : Set (Finset ℕ)).PairwiseDisjoint roots)
    (esub : ∀ B∈K, escorts B⊆V) (e4 : ∀ B∈K, (escorts B).card=4)
    (miss : ∀ B∈K, ∀ u∈roots B, (roots B).erase u ⊆ missingMixed D V u)
    (pay : ∀ v∈V, 36+(K.filter (fun B => v∈escorts B)).card ≤
      mixedScore D V v + (if v∈L then 2 else 0)) :
    K=∅ := by
  classical
  have lv : L⊆V := hL ▸ biUnion_subset.mpr rsub
  have tax : (∑ v∈V,(K.filter (fun B => v∈escorts B)).card)=4*K.card := by
    calc
      _ = ∑ v∈V, ∑ B∈K, (if v∈escorts B then (1 : ℕ) else 0) := by
        apply sum_congr rfl
        intro v hv
        rw [←sum_filter]
        simp
      _ = ∑ B∈K, ∑ v∈V, (if v∈escorts B then (1 : ℕ) else 0) := sum_comm
      _ = ∑ B∈K,(4 : ℕ) := by
        apply sum_congr rfl
        intro B hB
        simp [sum_ite_mem, inter_eq_right.mpr (esub B hB),e4 B hB]
      _ = 4*K.card := by rw [Finset.sum_const_nat (fun _ _ => rfl),Nat.mul_comm]
  have sumPay := sum_le_sum pay
  have cL : (∑ v∈V, if v∈L then (2 : ℕ) else 0)=2*L.card := by
    simp [sum_ite_mem, inter_eq_right.mpr lv,Nat.mul_comm]
  rw [sum_add_distrib,sum_add_distrib,tax,cL,
    Finset.sum_const_nat (fun _ _ => rfl),hn] at sumPay
  have budget := mixedScore_with_missing hf
  rw [hn] at budget
  have missL :
      (∑ B∈K, (roots B).card*((roots B).card-1)) ≤ ∑ v∈V,(missingMixed D V v).card := by
    calc
      _ = ∑ B∈K, ∑ v∈roots B, ((roots B).card-1) := by
        simp only [Finset.sum_const_nat (fun _ _ => rfl)]
      _ ≤ ∑ B∈K, ∑ v∈roots B, (missingMixed D V v).card := by
        apply sum_le_sum
        intro B hB
        apply sum_le_sum
        intro v hv
        simpa only [card_erase_of_mem hv] using card_le_card (miss B hB v hv)
      _ = ∑ v∈L,(missingMixed D V v).card := by rw [hL,sum_biUnion ed]
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg lv (fun _ _ _ => Nat.zero_le _)
  have cardL : L.card=∑ B∈K,(roots B).card := by rw [hL,card_biUnion ed]
  have gain (B : Finset ℕ) (hB : B∈K) :
      2*(roots B).card+2≤(roots B).card*((roots B).card-1)+4 := by
    have g : 0<(roots B).card := card_pos.mpr (hne B hB)
    let k := (roots B).card
    change 2*k+2≤k*(k-1)+4
    cases k with
    | zero => simp
    | succ i =>
      cases i with
      | zero => decide
      | succ j => simp [Nat.add_mul, Nat.mul_add, Nat.mul_comm]; omega
  have g := sum_le_sum gain
  rw [sum_add_distrib,sum_add_distrib,←mul_sum,←cardL,
    Finset.sum_const_nat (fun _ _ => rfl),Finset.sum_const_nat (fun _ _ => rfl)] at g
  have cn : K.card=0 := by omega
  exact card_eq_zero.mp cn

#print axioms mixedScore_with_missing
#print axioms no_short_banks_of_escort_certificate
end LeanCH.BR.DotDegreeSevenLow

