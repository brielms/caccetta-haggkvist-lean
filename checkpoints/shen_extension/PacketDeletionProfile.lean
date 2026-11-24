import checkpoints.shen_extension.SharedArcStrictParent
import checkpoints.shen_extension.SharedArcComponentExchange

namespace LeanCH.BR.Closure.SharedArcStrictParent
open Finset Matrix BRq2 BRq3 BR45 WeightedSD ShenCycleSuccessor ShortestCycleWeights FirstPacketBarrier
open MarkedCyclePeeling SharedArcExpansion SharedArcBarrier SharedArcComponentExchange FiniteCutInverse
open scoped Matrix

/-- A two-head minimum has a strict certificate after at least one single deletion.
With three or more heads every single deletion has such a certificate. -/
theorem deletion_profile {q n} (X : Model q n) (hq : 2 ≤ q) (small : SmallerSmallRow q X.V.card)
    {F B} (step : Boundary X F B)
    (least : ∀ M, Boundary X F M → (targets X.D X.V F B).card ≤ (targets X.D X.V F M).card)
    {H : Matrix X.V X.V ℝ} (inv : CommonInverse (realMatrix q (graph X.D (insert B F)) X.V) H)
    (charge : ∀ a b : X.V, (a:ℕ)∈B → (b:ℕ)∈B → X.D a b=true → graph X.D F a b=false →
      1 ≤ (q:ℝ)*H b a)
    (multi : 1 < (targets X.D X.V F B).card) :
    let P := added X.D F B
    let strict := fun e : ℕ × ℕ => ∃ p : X.V → ℝ, (∀ k, 0 ≤ p k) ∧ (∑ k, p k) = 1 ∧
      ∀ k, (p ᵥ* realMatrix q (eraseArc (graph X.D (insert B F)) e.1 e.2) X.V) k < 1
    (∃ e ∈ P, strict e) ∧ (3 ≤ P.card → ∀ e ∈ P, strict e) := by
  classical
  intro P strict
  have cyc : Cycle X.D X.V q B := (mem_filter.mp step.1).2
  have enough : 1 < P.card := by simpa only [P,count cyc] using multi
  have resolve {e f : ℕ × ℕ} (he : e∈P) (hf : f∈P) (ne : e ≠ f) (cross : f.1 ≠ e.2) :
      strict e := by
    obtain ⟨ab,bb,ed,off⟩ := mem_added.mp he
    obtain ⟨ib,jb,ij,miss⟩ := mem_added.mp hf
    have heads : f.2 ≠ e.2 := fun eq => ne (matching cyc he hf (Or.inr eq.symm))
    exact punctured X hq small step least inv charge ⟨_,cyc.sub ab⟩ ⟨_,cyc.sub bb⟩
      ⟨_,cyc.sub ib⟩ ⟨_,cyc.sub jb⟩ ab bb ed off ib jb ij miss heads
      (fun eq => cross (congrArg Subtype.val eq))
  constructor
  · obtain ⟨e,he,f,hf,ne⟩ := Finset.one_lt_card.mp enough
    by_cases cross : f.1 = e.2
    · refine ⟨f,hf,resolve hf he ne.symm ?_⟩
      intro reverse
      obtain ⟨ab,bb,ed,_⟩ := mem_added.mp he
      have de := (mem_added.mp hf).2.2.1
      rw [cross,←reverse] at de
      exact no_back_arc X.free (cyc.sub ab)
        (mem_ball.mpr ⟨cyc.sub bb,1,le_rfl,.step (cyc.sub bb) ed (.refl _)⟩) hq de
    · exact ⟨e,he,resolve he hf ne cross⟩
  · intro three e he
    have rem : 1 < (P.erase e).card := by rw [card_erase_of_mem he]; omega
    obtain ⟨f,hf,g,hg,fg⟩ := Finset.one_lt_card.mp rem
    obtain ⟨fe,fp⟩ := mem_erase.mp hf
    obtain ⟨ge,gp⟩ := mem_erase.mp hg
    by_cases cross : f.1 = e.2
    · exact resolve he gp ge.symm (fun eq => fg (matching cyc fp gp (Or.inl (cross.trans eq.symm))))
    · exact resolve he fp fe.symm cross

end LeanCH.BR.Closure.SharedArcStrictParent

#print axioms LeanCH.BR.Closure.SharedArcStrictParent.deletion_profile

