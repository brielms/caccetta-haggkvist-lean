import checkpoints.shen_extension.dot_tensor_research.DotDegreeSevenQ5SameBank_20261121

namespace LeanCH.BR.DotDegreeSevenLow
open Finset BRq2 BRq3 BR45 BRsGen

/-- Distinct roots with the same bank cannot reach in two steps,
independently of whether the bank has a return to the first layer. -/
theorem same_bank_no_two_q4 {D : CH.Digraph} {V : Finset ℕ} {u v : ℕ}
    (hf : QFree D V 4) (ho : OutEq 7 D V) (hu : u∈V) (hv : v∈V) (ne : u≠v)
    (eq : SecondBank D V u=SecondBank D V v) :
    v∉ball D V u 2 := by
  have no1 : v∉ball D V u 1 := by
    intro m
    have uv : D u v=true := (mem_outN.mp
      ((erase_ball_one_eq_outN hf (by decide : 1≤4) hu) ▸
        (mem_erase.mpr ⟨ne.symm,m⟩ : v∈(ball D V u 1).erase u))).2
    have sub : outN D V v ⊆ outN D V u := by
      intro x hx
      obtain ⟨xv,vx⟩ := mem_outN.mp hx
      have x2 : x∈ball D V u 2 := ball_step m xv vx
      have x1 : x∈ball D V u 1 := by
        by_contra n
        have xb : x∈SecondBank D V u := mem_sdiff.mpr ⟨x2,n⟩
        rw [eq] at xb
        exact (mem_sdiff.mp xb).2 ((mem_ball_one hv).mpr (Or.inr hx))
      have xx : x≠u := by
        intro e
        subst x
        exact hf u 2 (by decide) (by decide)
          (.step hv uv (.step hu vx (.refl u)))
      rw [←erase_ball_one_eq_outN hf (by decide : 1≤4) hu]
      exact mem_erase.mpr ⟨xx,x1⟩
    have equal : outN D V v=outN D V u :=
      eq_of_subset_of_card_le sub (by rw [ho u hu,ho v hv])
    have self : v∈outN D V v := equal ▸ mem_outN.mpr ⟨hv,uv⟩
    exact hf v 1 (by decide) (by decide) (.step hv (mem_outN.mp self).2 (.refl v))
  have no2 : v∉ball D V u 2 := by
    intro vv
    have b : v∈SecondBank D V u := mem_sdiff.mpr ⟨vv,no1⟩
    rw [eq] at b
    exact (mem_sdiff.mp b).2 (self_mem_ball hv)
  exact no2
#print axioms same_bank_no_two_q4
end LeanCH.BR.DotDegreeSevenLow
