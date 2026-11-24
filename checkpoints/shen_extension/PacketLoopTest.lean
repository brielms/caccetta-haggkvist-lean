import checkpoints.shen_extension.PacketLoopElimination

namespace LeanCH.BR.PacketCompression
open Finset Matrix
universe u

private noncomputable def remainder {I : Type u} [Fintype I] [DecidableEq I] (K : Matrix I I ℝ) (b : I) :
    Matrix ((univ : Finset I).erase b) ((univ : Finset I).erase b) ℝ :=
  fun i j => K i j + K i b * (K b j / (1 - K b b))

/-- Each pass either detects a loop of mass at least one or eliminates one
head. The finite choice fixes a pivot order independent of the weights. -/
noncomputable def loopTest : (fuel : ℕ) → {I : Type u} → [Fintype I] → [DecidableEq I] →
    Matrix I I ℝ → Prop
  | 0, _, _, _, _ => False
  | fuel+1, I, _, _, K => by
    classical
    exact if h : Nonempty I then
      let b := Classical.choice h
      1 ≤ K b b ∨ (K b b < 1 ∧ loopTest fuel (remainder K b))
    else False

theorem loopTest_iff (fuel : ℕ) : ∀ {I : Type u} [Fintype I] [DecidableEq I]
    (K : Matrix I I ℝ), (∀ i j, 0 ≤ K i j) → Fintype.card I ≤ fuel →
    (loopTest fuel K ↔ Feasible K) := by
  induction fuel with
  | zero =>
    intro I _ _ K _ size
    constructor
    · exact False.elim
    · rintro ⟨_,⟨_,b,_⟩,_⟩
      have pos := Fintype.card_pos_iff.mpr (⟨b⟩ : Nonempty I)
      omega
  | succ n ih =>
    intro I _ _ K nn size
    classical
    rw [loopTest]
    split
    · rename_i h
      let b := Classical.choice h
      change (1 ≤ K b b ∨ (K b b < 1 ∧ loopTest n (remainder K b))) ↔ Feasible K
      by_cases big : 1 ≤ K b b
      · exact ⟨fun _ => pivot_pays nn b big, fun _ => Or.inl big⟩
      · have low := lt_of_not_ge big
        obtain ⟨next,eq⟩ := eliminate nn b low
        have smaller : Fintype.card ((univ : Finset I).erase b) ≤ n := by
          rw [Fintype.card_coe,card_erase_of_mem (mem_univ b),card_univ]
          omega
        have reduced := ih (remainder K b) next smaller
        exact ⟨fun paid => eq.mpr (reduced.mp ((paid.resolve_left big).2)),
          fun paid => Or.inr ⟨low,reduced.mpr (eq.mp paid)⟩⟩
    · rename_i empty
      exact ⟨False.elim,fun ⟨_,⟨_,b,_⟩,_⟩ => empty ⟨b⟩⟩

end LeanCH.BR.PacketCompression

#print axioms LeanCH.BR.PacketCompression.loopTest_iff

