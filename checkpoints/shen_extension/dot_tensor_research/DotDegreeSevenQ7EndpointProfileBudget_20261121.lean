import checkpoints.shen_extension.dot_tensor_research.DotDegreeSevenQ7EndpointProfileBasins_20261121

namespace LeanCH.BR.DotDegreeSevenQ7
open Finset BRq2 BRq3 BR45

/-- A long-distance recipient pays not only its own place but also all the
strictly shorter suffix labels of its actual sink path. -/
theorem long_basin_budget {D : CH.Digraph} {A P R : Finset ℕ} {s x r : ℕ}
    (hf : QFree D A 7) (ac : A.card≤7) (sub : R⊆P) (ss : IsSinkOn D A s)
    (p : ShortestSinkPath D A x) (ends : p.vertex p.len=s) (len : r≤p.len)
    (inside : ∀ i, i≤p.len → p.vertex i∈P)
    (low : ∀ y∈R, ∀ m, Walk D A y s m → r≤m) :
    R.card+r≤P.card := by
  classical
  let f := fun i => p.vertex (p.len-r+1+i)
  let Q := (range r).image f
  have QP : Q⊆P := by
    intro y hy
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hy
    exact inside _ (by have := mem_range.mp hi; omega)
  have inj : Set.InjOn f (range r) := by
    intro i hi j hj eq
    have hi : i<r := mem_range.mp hi
    have hj : j<r := mem_range.mp hj
    have e := p.injective hf ac
      (show p.len-r+1+i ∈ range (p.len+1) from mem_range.mpr (by omega))
      (show p.len-r+1+j ∈ range (p.len+1) from mem_range.mpr (by omega)) eq
    omega
  have disj : Disjoint R Q := disjoint_left.mpr (by
    intro y hy hr
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hr
    have hi : i<r := mem_range.mp hi
    have w := p.walk (show p.len-r+1+i≤p.len by omega) le_rfl
    rw [ends] at w
    have hh := low (f i) hy _ w
    omega)
  have c := card_le_card (union_subset sub QP)
  rw [card_union_of_disjoint disj] at c
  have qc : Q.card=r := by
    change ((range r).image f).card=r
    rw [card_image_of_injOn inj,card_range]
  omega

/-- Three active basins cannot accommodate pairwise return-distance budgets at
degree seven. This is only the numerical consumer of path-disjointness. -/
theorem three_basin_budget {A P Q R : Finset ℕ} {i j k : ℕ}
    (ac : A.card≤7) (hP : P⊆A) (hQ : Q⊆A) (hR : R⊆A)
    (p : i+1≤P.card) (q : j+1≤Q.card) (r : k+1≤R.card)
    (dpq : Disjoint P Q) (dpr : Disjoint P R) (dqr : Disjoint Q R)
    (ij : 4≤i+j) (ik : 4≤i+k) (jk : 4≤j+k) : False := by
  have d : Disjoint (P∪Q) R := disjoint_left.mpr (by
    intro x h hR
    rcases mem_union.mp h with hP|hQ
    · exact disjoint_left.mp dpr hP hR
    · exact disjoint_left.mp dqr hQ hR)
  have c := card_le_card (union_subset (union_subset hP hQ) hR)
  rw [card_union_of_disjoint d,card_union_of_disjoint dpq] at c
  omega

#print axioms long_basin_budget
#print axioms three_basin_budget
end LeanCH.BR.DotDegreeSevenQ7
