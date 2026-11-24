module

public import LeanCH.CompromiseArcLoss

set_option linter.style.header false

/-! Deleting the only incoming arc makes its head a source. Its weighted
compromise certificate already follows from vertex deletion, so that
part of weighted arc minimality supplies no independent constraint. -/

open Finset CH.CompromiseGame CH.CompromiseSeven CH.CompromiseWeighted
open CH.CompromiseFair CH.CompromiseDeletion CH.CompromiseCritical
public section

namespace CH.CompromiseSourceArc

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (adj : V → V → Prop) [DecidableRel adj]

theorem source_extension (j : V) (source : ∀ v, ¬ adj v j)
    (p : V → ℝ) (hp : FairOn adj (univ.erase j) p) : Fair adj p := by
  apply (extension_iff adj _ p hp).mpr
  intro u hu
  have he : u = j := by simpa using hu
  subst u
  have hi : inN adj j = ∅ := by ext v; simp [source v]
  rw [hi]
  have ho := weight_nonneg p hp.1 (outN adj j)
  have hs := weight_nonneg p hp.1 (secondIn adj j)
  simpa only [mass, sum_empty, mul_zero] using add_nonneg ho hs

theorem fairOn_erase_arc (i j : V) (p : V → ℝ)
    (hp : FairOn adj (univ.erase j) p) :
    FairOn (CH.ArcMinimal.eraseArc adj i j) (univ.erase j) p := by
  refine ⟨hp.1, hp.2.1, hp.2.2.1, ?_⟩
  intro u hu
  have uj : u ≠ j := (mem_erase.mp hu).1
  have hi : inN (CH.ArcMinimal.eraseArc adj i j) u ∩ univ.erase j =
      inN adj u ∩ univ.erase j := by
    ext v
    simp [CH.ArcMinimal.eraseArc, uj]
  have ho : outN (CH.ArcMinimal.eraseArc adj i j) u ∩ univ.erase j =
      outN adj u ∩ univ.erase j := by
    ext v
    simp only [mem_inter, mem_outN, CH.ArcMinimal.eraseArc,
      mem_erase, mem_univ, and_true]
    tauto
  have hs : restrictedSecondIn (CH.ArcMinimal.eraseArc adj i j) (univ.erase j) u =
      restrictedSecondIn adj (univ.erase j) u := by
    ext v
    simp only [restrictedSecondIn, mem_filter, mem_erase, mem_univ, and_true,
      CH.ArcMinimal.eraseArc, uj, and_false, not_false_eq_true, and_true]
    constructor
    · rintro ⟨hv, hne, hnon, a, ha, hva, hau⟩
      exact ⟨hv, hne, hnon, a, ha, hva.1, hau⟩
    · rintro ⟨hv, hne, hnon, a, ha, hva, hau⟩
      exact ⟨hv, hne, hnon, a, ha, ⟨hva, fun h => ha h.2⟩, hau⟩
  rw [hi, ho, hs]
  exact hp.2.2.2 u hu

/-- This conclusion does not assume weighted arc minimality. -/
theorem unique_parent_fair (deleted : DeletedFair adj) (i j : V)
    (unique : ∀ v, adj v j → v = i) :
    ∃ p, Fair (CH.ArcMinimal.eraseArc adj i j) p := by
  obtain ⟨p, hp⟩ := deleted j
  refine ⟨p, source_extension _ j ?_ p (fairOn_erase_arc adj i j p hp)⟩
  intro v h
  exact h.2 ⟨unique v h.1, rfl⟩

theorem unique_parent_compromise (deleted : DeletedFair adj) (i j : V)
    (unique : ∀ v, adj v j → v = i) (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) :
    ∃ v, 0 ≤ surplus (CH.ArcMinimal.eraseArc adj i j) w v := by
  obtain ⟨p, hp⟩ := unique_parent_fair adj deleted i j unique
  obtain ⟨v, _, hv⟩ := compromise_of_fair _ p w hp hw
  refine ⟨v, ?_⟩
  dsimp [surplus]
  linarith

end CH.CompromiseSourceArc

#print axioms CH.CompromiseSourceArc.source_extension
#print axioms CH.CompromiseSourceArc.unique_parent_fair
#print axioms CH.CompromiseSourceArc.unique_parent_compromise
