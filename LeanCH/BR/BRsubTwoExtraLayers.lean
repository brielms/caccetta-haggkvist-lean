import LeanCH.BR.BRsubExtraLayers
import LeanCH.BR.BRTwoExtraCyclic

/-! The proved uniform excess-two exclusion and its BFS consequences. -/

namespace LeanCH.BR.BRsub

open BRq2 BRq3 BR45 BRsGen

variable {E : CH.Digraph} {V : Finset ℕ} {u s : ℕ}

/-- Conditional BFS bridge retained for explicit dependency inspection. -/
theorem two_extra_layers_false_of (htwo : TwoExtraTripleImpossible)
    (hs : 6 ≤ s) (hf : QFree E V (s - 1))
    (hu : u ∈ V) (hmin : ∀ v ∈ V, s ≤ (outN E V v).card)
    (h1 : (outN E V u).card = s)
    (h2 : (ball E V u 2 \ ball E V u 1).card = s)
    (h3 : (ball E V u 3 \ ball E V u 2).card = s + 2)
    (h4 : (ball E V u 4 \ ball E V u 3).card ≤ s - 3) : False := by
  classical
  let X := outN E V u
  let Y := ball E V u 2 \ ball E V u 1
  let Z := ball E V u 3 \ ball E V u 2
  let K := ball E V u 4 \ ball E V u 3
  have hXV : X ⊆ V := outN_subset
  have hYV : Y ⊆ V := fun _ hy => ball_subset (Finset.mem_sdiff.mp hy).1
  have hZV : Z ⊆ V := fun _ hz => ball_subset (Finset.mem_sdiff.mp hz).1
  have hXV1 : X ⊆ ball E V u 1 := fun _ hx => (mem_ball_one hu).mpr (Or.inr hx)
  have hXY : Disjoint X Y := Finset.disjoint_left.mpr
    (fun x hx hy => (Finset.mem_sdiff.mp hy).2 (hXV1 hx))
  have hXY2 : X ∪ Y ⊆ ball E V u 2 := Finset.union_subset
    (hXV1.trans (ball_mono_radius (by decide : 1 ≤ 2))) Finset.sdiff_subset
  have houter : Disjoint (X ∪ Y) Z := Finset.disjoint_left.mpr
    (fun v hv hz => (Finset.mem_sdiff.mp hz).2 (hXY2 hv))
  have hsplit2 : ∀ v ∈ ball E V u 2, v ≠ u → v ∈ X ∪ Y := by
    intro v hv hvu
    by_cases hv1 : v ∈ ball E V u 1
    · rcases (mem_ball_one hu).mp hv1 with h | h
      · exact (hvu h).elim
      · exact Finset.mem_union_left _ h
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hv, hv1⟩)
  have hsplit3 : ∀ v ∈ ball E V u 3, v ≠ u → v ∈ X ∪ Y ∪ Z := by
    intro v hv hvu
    by_cases hv2 : v ∈ ball E V u 2
    · exact Finset.mem_union_left _ (hsplit2 v hv2 hvu)
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hv, hv2⟩)
  have hhighX : ∀ x ∈ X, s ≤ (outN E (X ∪ Y) x).card := by
    intro x hx
    have hsub : outN E V x ⊆ outN E (X ∪ Y) x := by
      intro v hv
      obtain ⟨hvV, hxv⟩ := mem_outN.mp hv
      refine mem_outN.mpr ⟨hsplit2 v (ball_step (hXV1 hx) hvV hxv) ?_, hxv⟩
      intro hvu
      exact no_back_arc hf hu (hXV1 hx) (by omega) (hvu ▸ hxv)
    exact (hmin x (hXV hx)).trans (Finset.card_le_card hsub)
  have hhighY : ∀ y ∈ Y, s ≤ (outN E (X ∪ Y ∪ Z) y).card := by
    intro y hy
    have hsub : outN E V y ⊆ outN E (X ∪ Y ∪ Z) y := by
      intro v hv
      obtain ⟨hvV, hyv⟩ := mem_outN.mp hv
      refine mem_outN.mpr ⟨hsplit3 v (ball_step (Finset.mem_sdiff.mp hy).1 hvV hyv) ?_, hyv⟩
      intro hvu
      exact no_back_arc hf hu (Finset.mem_sdiff.mp hy).1 (by omega) (hvu ▸ hyv)
    exact (hmin y (hYV hy)).trans (Finset.card_le_card hsub)
  have hlowZ : ∀ z ∈ Z, 3 ≤ (outN E (X ∪ Y ∪ Z) z).card := by
    intro z hz
    have hsub : outN E V z ⊆ outN E (X ∪ Y ∪ Z) z ∪ K := by
      intro v hv
      obtain ⟨hvV, hzv⟩ := mem_outN.mp hv
      by_cases hv3 : v ∈ ball E V u 3
      · refine Finset.mem_union_left _ (mem_outN.mpr ⟨hsplit3 v hv3 ?_, hzv⟩)
        intro hvu
        exact no_back_arc hf hu (Finset.mem_sdiff.mp hz).1 (by omega) (hvu ▸ hzv)
      · exact Finset.mem_union_right _
          (Finset.mem_sdiff.mpr ⟨ball_step (Finset.mem_sdiff.mp hz).1 hvV hzv, hv3⟩)
    have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    have hh := hmin z (hZV hz)
    change K.card ≤ s - 3 at h4
    omega
  have hparents : ∀ z ∈ Z, ∃ y ∈ Y, E y z = true := by
    intro z hz
    obtain ⟨y, hy, hyz⟩ := ball_succ_pred hu (Finset.mem_sdiff.mp hz).1 (Finset.mem_sdiff.mp hz).2
    have hy1 : y ∉ ball E V u 1 := by
      intro hy1
      exact (Finset.mem_sdiff.mp hz).2 (ball_step hy1 (hZV hz) hyz)
    exact ⟨y, Finset.mem_sdiff.mpr ⟨hy, hy1⟩, hyz⟩
  exact htwo s E X Y Z hs (hf.mono_set (Finset.union_subset (Finset.union_subset hXV hYV) hZV))
    hXY houter h1 h2 h3 hhighX hhighY hlowZ hparents

/-- Conditional bridge for the degree-six profile. -/
theorem no_six_six_eight_three_of_two_extra (htwo : TwoExtraTripleImpossible)
    (hf : QFree E V 5) (hu : u ∈ V) (hmin : ∀ v ∈ V, 6 ≤ (outN E V v).card)
    (h1 : (outN E V u).card = 6)
    (h2 : (ball E V u 2 \ ball E V u 1).card = 6)
    (h3 : (ball E V u 3 \ ball E V u 2).card = 8)
    (h4 : (ball E V u 4 \ ball E V u 3).card = 3) : False :=
  two_extra_layers_false_of htwo (by decide : 6 ≤ 6) hf hu hmin h1 h2 h3 (by omega)

/-- The full uniform excess-two layer exclusion now has its structural proof supplied. -/
theorem two_extra_layers_false (hs : 6 ≤ s)
    (hf : QFree E V (s - 1)) (hu : u ∈ V)
    (hmin : ∀ v ∈ V, s ≤ (outN E V v).card)
    (h1 : (outN E V u).card = s)
    (h2 : (ball E V u 2 \ ball E V u 1).card = s)
    (h3 : (ball E V u 3 \ ball E V u 2).card = s + 2)
    (h4 : (ball E V u 4 \ ball E V u 3).card ≤ s - 3) : False :=
  two_extra_layers_false_of two_extra_triple_impossible hs hf hu hmin h1 h2 h3 h4

theorem no_six_six_eight_three
    (hf : QFree E V 5) (hu : u ∈ V) (hmin : ∀ v ∈ V, 6 ≤ (outN E V v).card)
    (h1 : (outN E V u).card = 6)
    (h2 : (ball E V u 2 \ ball E V u 1).card = 6)
    (h3 : (ball E V u 3 \ ball E V u 2).card = 8)
    (h4 : (ball E V u 4 \ ball E V u 3).card = 3) : False :=
  no_six_six_eight_three_of_two_extra two_extra_triple_impossible hf hu hmin h1 h2 h3 h4

end LeanCH.BR.BRsub
