import checkpoints.shen_extension.TripleBankMenu

namespace LeanCH.BR.TripleBank
open Finset BRq2 BRq3

/-- Maximum size of the common out-neighborhood of three distinct rows. -/
def TripleCap (D : CH.Digraph) (V : Finset ℕ) (m : ℕ) : Prop :=
  ∀ (i j k : ℕ), i ∈ V → j ∈ V → k ∈ V → i ≠ j → i ≠ k → j ≠ k →
    ((outN D V i ∩ outN D V j) ∩ outN D V k).card ≤ m

namespace GlobalTripleChoice

/-- Retain the global common-head bound on the exact triple selected for repair. -/
theorem top_repair_frontier {D : CH.Digraph} {V : Finset ℕ} {s : ℕ}
    (safe : QFree D V 3) (reg : OutEq s D V) (hs : 7 ≤ s) (room : V.card = 3*s)
    (none : BypassRepair.NoHost 3 (s-1)) :
    ∃ P ⊆ V, 2 ≤ P.card ∧ TripleCap D V P.card ∧ ∃ B ⊆ V, B.card = 3 ∧ (∀ b ∈ B, P ⊆ outN D V b) ∧
      let U := V \ B
      let S := U.filter (fun c => 2 ≤ (outN D B c).card)
      (∀ c ∈ S, ∃ z ∈ P, D c z ≠ true) ∧
      (∀ c ∈ S, ∃ E : CH.Digraph, QFree E U 3 ∧
        (outN E U c).card = (outN D U c).card + (rowMenu D U P c).card ∧
        ∀ a ∈ U, a ≠ c → min (s-1) (outN E U a).card = min (s-1) (outN D U a).card) ∧
      (2 ≤ S.card ∨ ∃ c, S = {c} ∧ (outN D B c).card = 3 ∧ (rowMenu D U P c).card = 1) := by
  classical
  obtain ⟨P,pv,pc,maximum,B,bv,bc,common,miss⟩ := top_triple_maximum safe reg hs room
  have cap : TripleCap D V P.card := by
    intro i j k iv jv kv ij ik jk
    let Q := (outN D V i ∩ outN D V j) ∩ outN D V k
    have qi : Q ⊆ outN D V i := inter_subset_left.trans inter_subset_left
    have qj : Q ⊆ outN D V j := inter_subset_left.trans inter_subset_right
    have qk : Q ⊆ outN D V k := inter_subset_right
    have rows : ({i,j,k} : Finset ℕ) ⊆ V.filter (fun a => Q ⊆ outN D V a) :=
      insert_subset_iff.mpr ⟨mem_filter.mpr ⟨iv,qi⟩,insert_subset_iff.mpr
        ⟨mem_filter.mpr ⟨jv,qj⟩,singleton_subset_iff.mpr (mem_filter.mpr ⟨kv,qk⟩)⟩⟩
    have three : ({i,j,k} : Finset ℕ).card = 3 := by simp [ij,ik,jk]
    exact maximum Q (qi.trans outN_subset) (three ▸ card_le_card rows)
  exact ⟨P,pv,pc,cap,B,bv,bc,common,repair_on_triple safe reg hs room none pv bv bc common miss⟩

#print axioms top_repair_frontier
end GlobalTripleChoice
end LeanCH.BR.TripleBank
