import LeanCH.BR.BRCommonParentTransferGeometry

/-! An actual edited one-vertex extension: retain old core edges, give the
fresh vertex heads O and parents I. Safety keeps length-zero paths explicit. -/
namespace LeanCH.BR.WeightedSD
open Finset BRq2 BRq3 BR45 BRsub

def coreOutgoingExtension (D : CH.Digraph) (S O : Finset ℕ) (v : ℕ) : CH.Digraph :=
  fun a b => decide (b ∈ S ∧ ((a ∈ S ∧ D a b = true) ∨ (a=v ∧ b ∈ O)))

def coreTwoSidedExtension (D : CH.Digraph) (S I O : Finset ℕ) (v : ℕ) : CH.Digraph :=
  fun a b => decide (coreOutgoingExtension D S O v a b = true ∨ (a ∈ I ∧ b=v))

theorem coreOutgoingExtension_walk {D : CH.Digraph} {S O : Finset ℕ} {v : ℕ}
    (hv : v ∉ S) {a b k : ℕ} (w : Walk (coreOutgoingExtension D S O v) (insert v S) a b k) :
    a ∈ S → Walk D S a b k := by
  induction w with
  | refl a => exact fun _ => .refl a
  | @step a c b k hc hac rest ih =>
    intro ha
    have he := of_decide_eq_true hac
    have hcS : c ∈ S := he.1
    have haD : D a c = true := by
      rcases he.2 with h | ⟨rfl,_⟩
      · exact h.2
      · exact (hv ha).elim
    exact .step hcS haD (ih hcS)

theorem coreOutgoingExtension_qfree {D : CH.Digraph} {S O : Finset ℕ} {v q : ℕ}
    (hv : v ∉ S) (hf : QFree D S q) : QFree (coreOutgoingExtension D S O v) (insert v S) q := by
  intro a l hpos hle w
  cases l with
  | zero => omega
  | succ k =>
    obtain ⟨y,_,_,hya⟩ := w.unsnoc
    have ha : a ∈ S := (of_decide_eq_true hya).1
    exact hf a (k+1) hpos hle (coreOutgoingExtension_walk hv w ha)

theorem coreTwoSidedExtension_qfree {D : CH.Digraph} {S I O : Finset ℕ} {v q : ℕ}
    (hv : v ∉ S) (hIS : I ⊆ S) (hf : QFree D S q)
    (hshort : ∀ o ∈ O, ∀ i ∈ I, ∀ k, k ≤ q-2 → ¬ Walk D S o i k) :
    QFree (coreTwoSidedExtension D S I O v) (insert v S) q := by
  apply qfree_common_head_additions (P := fun x => x ∈ I) (coreOutgoingExtension_qfree hv hf)
    (fun x hx => mem_insert_of_mem (hIS hx))
    (fun a b hab => of_decide_eq_true hab)
  intro i hi hball
  obtain ⟨_,k,hk,w⟩ := mem_ball.mp hball
  cases w with
  | refl => exact hv (hIS hi)
  | @step a c b k hc hac rest =>
    have he := of_decide_eq_true hac
    have hcO : c ∈ O := by
      rcases he.2 with h | h
      · exact (hv h.1).elim
      · exact h.2
    exact hshort c hcO i hi k (by omega) (coreOutgoingExtension_walk hv rest he.1)

end LeanCH.BR.WeightedSD
