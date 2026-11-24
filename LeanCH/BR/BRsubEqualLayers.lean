import LeanCH.BR.BREqualPair
import LeanCH.BR.BRsubSetBall

/-! Equal-layer exclusion, with a uniform local theorem and its (5,6) application. -/

namespace LeanCH.BR.BRsub

open BRq2 BRq3 BR45 BRsGen

variable {E : CH.Digraph} {V : Finset ℕ} {u s : ℕ}

/-- Equal first and second layers cannot send a back arc when the third layer is smaller. -/
theorem equal_first_layers_no_back (hs : 5 ≤ s) (hf : QFree E V (s - 1))
    (hu : u ∈ V) (hmin : ∀ v ∈ V, s ≤ (outN E V v).card)
    (h1 : (outN E V u).card = s)
    (h2 : (ball E V u 2 \ ball E V u 1).card = s)
    (h3 : (ball E V u 3 \ ball E V u 2).card ≤ s - 1) :
    ∀ y ∈ ball E V u 2 \ ball E V u 1, ∀ x ∈ outN E V u, ¬ E y x = true := by
  classical
  let X := outN E V u
  let Y := ball E V u 2 \ ball E V u 1
  let Z := ball E V u 3 \ ball E V u 2
  have hXV : X ⊆ V := outN_subset
  have hYV : Y ⊆ V := fun _ hy => ball_subset (Finset.mem_sdiff.mp hy).1
  have hXV1 : X ⊆ ball E V u 1 := fun _ hx => (mem_ball_one hu).mpr (Or.inr hx)
  have hXY : Disjoint X Y := Finset.disjoint_left.mpr
    (fun x hx hy => (Finset.mem_sdiff.mp hy).2 (hXV1 hx))
  have hsplit2 : ∀ z ∈ ball E V u 2, z ≠ u → z ∈ X ∪ Y := by
    intro z hz hzu
    by_cases hz1 : z ∈ ball E V u 1
    · rcases (mem_ball_one hu).mp hz1 with h | h
      · exact (hzu h).elim
      · exact Finset.mem_union_left _ h
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hz, hz1⟩)
  have hhigh : ∀ x ∈ X, s ≤ (outN E (X ∪ Y) x).card := by
    intro x hx
    have hsub : outN E V x ⊆ outN E (X ∪ Y) x := by
      intro z hz
      obtain ⟨hzV, hxz⟩ := mem_outN.mp hz
      refine mem_outN.mpr ⟨hsplit2 z (ball_step (hXV1 hx) hzV hxz) ?_, hxz⟩
      intro hzu
      exact no_back_arc hf hu (hXV1 hx) (by omega) (hzu ▸ hxz)
    exact (hmin x (hXV hx)).trans (Finset.card_le_card hsub)
  have hlow : ∀ y ∈ Y, 1 ≤ (outN E (X ∪ Y) y).card := by
    intro y hy
    have hsub : outN E V y ⊆ outN E (X ∪ Y) y ∪ Z := by
      intro z hz
      obtain ⟨hzV, hyz⟩ := mem_outN.mp hz
      by_cases hz2 : z ∈ ball E V u 2
      · refine Finset.mem_union_left _ (mem_outN.mpr ⟨hsplit2 z hz2 ?_, hyz⟩)
        intro hzu
        exact no_back_arc hf hu (Finset.mem_sdiff.mp hy).1 (by omega) (hzu ▸ hyz)
      · exact Finset.mem_union_right _
          (Finset.mem_sdiff.mpr ⟨ball_step (Finset.mem_sdiff.mp hy).1 hzV hyz, hz2⟩)
    have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    have hh := hmin y (hYV hy)
    change Z.card ≤ s - 1 at h3
    omega
  exact equal_pair_no_back hs (hf.mono_set (Finset.union_subset hXV hYV)) hXY h1 h2 hhigh hlow

/-- All profiles beginning `(6,6,<=5)` are excluded at the saturated (5,6) boundary. -/
theorem no_first_layers_six_six_small (hf : QFree E V 5) (hsat : Sat 5 E V)
    (hV : V.card = 31) (hmin : ∀ v ∈ V, 6 ≤ (outN E V v).card) (hu : u ∈ V)
    (h1 : (outN E V u).card = 6)
    (h2 : (ball E V u 2 \ ball E V u 1).card = 6)
    (h3 : (ball E V u 3 \ ball E V u 2).card ≤ 5) : False := by
  classical
  let Y := ball E V u 2 \ ball E V u 1
  let Z := ball E V u 3 \ ball E V u 2
  have hYV : Y ⊆ V := fun _ hy => ball_subset (Finset.mem_sdiff.mp hy).1
  have hn := equal_first_layers_no_back (by decide : 5 ≤ 6) hf hu hmin h1 h2 h3
  have hbound : ∀ y ∈ Y, 6 ≤ (outN E Y y).card + Z.card := by
    intro y hy
    have hsub : outN E V y ⊆ outN E Y y ∪ Z := by
      intro z hz
      obtain ⟨hzV, hyz⟩ := mem_outN.mp hz
      by_cases hz2 : z ∈ ball E V u 2
      · have hz1 : z ∉ ball E V u 1 := by
          intro hz1
          rcases (mem_ball_one hu).mp hz1 with hzu | hzX
          · exact no_back_arc hf hu (Finset.mem_sdiff.mp hy).1 (by decide) (hzu ▸ hyz)
          · exact hn y hy z hzX hyz
        exact Finset.mem_union_left _ (mem_outN.mpr ⟨Finset.mem_sdiff.mpr ⟨hz2, hz1⟩, hyz⟩)
      · exact Finset.mem_union_right _
          (Finset.mem_sdiff.mpr ⟨ball_step (Finset.mem_sdiff.mp hy).1 hzV hyz, hz2⟩)
    exact (hmin y (hYV hy)).trans ((Finset.card_le_card hsub).trans (Finset.card_union_le _ _))
  have hlow : ∀ y ∈ Y, 1 ≤ (outN E Y y).card := by
    intro y hy
    have := hbound y hy
    change Z.card ≤ 5 at h3
    omega
  have hreg := (dt_reg (by decide) (ball_q_one 5 (by decide)) (hf.mono_set hYV) hlow h2).1
  obtain ⟨y, hy⟩ := Finset.card_pos.mp (by change 0 < Y.card; change Y.card = 6 at h2; omega)
  have hz5 : Z.card = 5 := by
    have hh := hbound y hy
    rw [hreg y hy] at hh
    change Z.card ≤ 5 at h3
    omega
  obtain ⟨y, hy, x, hx, hyx⟩ := depth_two_back_arc hf hsat hV hmin hu h1 h2 hz5
  exact hn y hy x hx hyx

end LeanCH.BR.BRsub
