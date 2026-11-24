import LeanCH.BR.BRsubSat

/-! Forced out-regularity for an entire boundary class implies saturation. -/

namespace LeanCH.BR.BRsGen
open BRq2 BRq3 BRsub

theorem sat_of_forced_out_regular {D : CH.Digraph} {V : Finset ℕ} {q s : ℕ}
    (hforced : ∀ E : CH.Digraph, QFree E V q →
      (∀ v ∈ V, s ≤ (outN E V v).card) → OutEq s E V)
    (hf : QFree D V q) (hmin : ∀ v ∈ V, s ≤ (outN D V v).card) : Sat q D V := by
  classical
  intro v hv w hw hnot
  by_contra hn
  let E : CH.Digraph := fun a b => if a = w ∧ b = v then true else D a b
  have hsub : ∀ a b, D a b = true → E a b = true := by
    intro a b hab
    simp only [E]
    split
    · rfl
    · exact hab
  have hEfree : QFree E V q := qfree_insertQ hf hw (by
    intro a b hab
    simp only [E] at hab
    split at hab
    · right; assumption
    · left; exact hab) hn
  have hminE : ∀ a ∈ V, s ≤ (outN E V a).card := by
    intro a ha
    apply (hmin a ha).trans (Finset.card_le_card ?_)
    intro b hb
    exact mem_outN.mpr ⟨(mem_outN.mp hb).1, hsub a b (mem_outN.mp hb).2⟩
  have hrow : outN E V w = insert v (outN D V w) := by
    ext b
    simp only [mem_outN, Finset.mem_insert]
    by_cases hb : b = v <;> simp [E, hb, hv]
  have hmissing : v ∉ outN D V w := fun h => hnot (mem_outN.mp h).2
  have hnew := hforced E hEfree hminE w hw
  rw [hrow, Finset.card_insert_of_notMem hmissing] at hnew
  have hold := hmin w hw
  omega

end LeanCH.BR.BRsGen
