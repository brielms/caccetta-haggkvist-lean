import checkpoints.shen_extension.TripleBankFreeRepair
import checkpoints.shen_extension.SignatureRestoration

namespace LeanCH.BR.ReturnSignature
open Finset BRq2 BRq3 BR45 TripleBank

/-- Reverse a family of donor-to-short-row arcs at once. Each donor pays for
its own reversals. Distinct rows may choose the same donor if it has room. -/
theorem reverse_donors {H : CH.Digraph} {U S : Finset ℕ} {t : ℕ} (f : ℕ → ℕ)
    (safe : QFree H U 3) (inside : S⊆U)
    (donor : ∀ x∈S, f x∈U\S ∧ H (f x) x=true)
    (bare : ∀ x∈S, ∀ m∈U, H (f x) m=true → H m x≠true)
    (short : ∀ x∈S, t≤(outN H U x).card+1)
    (capacity : ∀ a∈U, a∉S → t+(S.filter (fun x=>f x=a)).card≤(outN H U a).card) :
    ∃ E : CH.Digraph, QFree E U 3 ∧ (∀ x∈S, E x (f x)=true) ∧ ∀ a∈U, t≤(outN E U a).card := by
  classical
  let C (a : ℕ) := S.filter (fun x => f x=a)
  let F : CH.Digraph := fun a b => decide (H a b=true ∧ b∉C a)
  have old {a b} (edge : F a b=true) := (show H a b=true from (of_decide_eq_true edge).1)
  have clean : QFree F U 3 := SignatureRestoration.free_sub safe (fun _ _ h => old h)
  have row (a : ℕ) : outN F U a=outN H U a \ C a := by
    ext b
    simp only [mem_outN,mem_sdiff,F,decide_eq_true_eq]
    tauto
  have sub (a : ℕ) : C a⊆outN H U a := by
    intro x h
    obtain ⟨xs,e⟩ := mem_filter.mp h
    exact mem_outN.mpr ⟨inside xs,e ▸ (donor x xs).2⟩
  have none {x} (xs : x∈S) : C x=∅ := eq_empty_iff_forall_notMem.mpr (fun a h => by
    obtain ⟨am,e⟩ := mem_filter.mp h
    exact (mem_sdiff.mp (donor a am).1).2 (e ▸ xs))
  let A (x : ℕ) : Finset ℕ := if x∈S then {f x} else ∅
  have spec {a b} (m : b∈A a) : a∈S ∧ b=f a := by
    by_cases am : a∈S
    · exact ⟨am,by simpa [A,am] using m⟩
    · simp [A,am] at m
  obtain ⟨ok,rows⟩ := patch_certificate (A:=A) (C:=fun _ => ∅) clean
    (fun x xu b m => by
      obtain ⟨xs,rfl⟩ := spec m
      obtain ⟨pos,arc⟩ := donor x xs
      obtain ⟨fv,fs⟩ := mem_sdiff.mp pos
      refine ⟨fv,fun same => fs (same.symm ▸ xs),fun ed => digonfree safe (by decide) fv xu arc (old ed),?_⟩
      intro ed
      exact (of_decide_eq_true ed).2 (mem_filter.mpr ⟨xs,rfl⟩))
    (fun x _ b h m mu bm mx => by
      obtain ⟨xs,rfl⟩ := spec h
      exact (bare x xs m mu (old bm) (old mx)).elim)
    (fun a _ b ab _ bc => by
      obtain ⟨am,rfl⟩ := spec ab
      exact ((mem_sdiff.mp (donor a am).1).2 (spec bc).1).elim)
  refine ⟨_,ok,fun x xs => decide_eq_true (Or.inl (by simp [A,xs])),?_⟩
  intro a au
  rw [rows a au,row a]
  by_cases am : a∈S
  · simpa [none am,A,am] using short a am
  · have cap := capacity a au am
    have fit := card_le_card (sub a)
    have count := card_sdiff_of_subset (sub a)
    change t+(C a).card ≤ _ at cap
    simp only [sdiff_empty,A,ite_eq_right am,card_empty,Nat.add_zero]
    omega

#print axioms reverse_donors
end LeanCH.BR.ReturnSignature
