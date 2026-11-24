import LeanCH.BR.BRWideAcyclicPair
import LeanCH.BR.BRsubCycleReturn

/-! First-layer acyclicity and the forced return in a small surviving profile. -/

namespace LeanCH.BR.BRsub
open BRq2 BRq3 BR45 BRsGen

/-- The acyclic wide-pair theorem transports to BFS layers at every s >= 6. -/
theorem acyclic_wide_layers_no_back {D : CH.Digraph} {V : Finset ℕ} {u s : ℕ}
    (hs : 6 ≤ s) (hf : QFree D V (s - 1)) (hu : u ∈ V)
    (hm : ∀ v ∈ V, s ≤ (outN D V v).card)
    (h1 : (outN D V u).card = s + 1)
    (h2 : (ball D V u 2 \ ball D V u 1).card = s)
    (h3 : (ball D V u 3 \ ball D V u 2).card ≤ s - 1)
    (hacy : QFree D (outN D V u) (s + 1)) :
    ∀ y ∈ ball D V u 2 \ ball D V u 1, ∀ x ∈ outN D V u, ¬ D y x = true := by
  classical
  let X := outN D V u
  let Y := ball D V u 2 \ ball D V u 1
  let Z := ball D V u 3 \ ball D V u 2
  have hXV : X ⊆ V := outN_subset
  have hYV : Y ⊆ V := Finset.sdiff_subset.trans ball_subset
  have hX1 : X ⊆ ball D V u 1 := fun _ hx => (mem_ball_one hu).mpr (Or.inr hx)
  have hXY : Disjoint X Y := Finset.disjoint_left.mpr
    (fun x hx hy => (Finset.mem_sdiff.mp hy).2 (hX1 hx))
  have hU2 : (ball D V u 2).erase u = X ∪ Y := by
    rw [show 2 = 1 + 1 by decide, erase_ball_succ_eq_union hu,
      erase_ball_one_eq_outN hf (by omega) hu]
  have hhigh : ∀ x ∈ X, s ≤ (outN D (X ∪ Y) x).card := by
    intro x hx
    have hh := outN_prefix_erase_root hf hu (by omega : 1 + 1 ≤ s - 1) (hX1 hx)
    rw [hU2] at hh
    exact (hm x (hXV hx)).trans (Finset.card_le_card hh)
  have hlow : ∀ y ∈ Y, 1 ≤ (outN D (X ∪ Y) y).card := by
    intro y hy
    have hsub : outN D V y ⊆ outN D (X ∪ Y) y ∪ Z := by
      intro z hz
      have hz3 := outN_prefix_erase_root hf hu (by omega : 2 + 1 ≤ s - 1)
        (Finset.mem_sdiff.mp hy).1 hz
      obtain ⟨hzu, hzB3⟩ := Finset.mem_erase.mp (mem_outN.mp hz3).1
      by_cases hzB2 : z ∈ ball D V u 2
      · exact Finset.mem_union_left _ (mem_outN.mpr
          ⟨hU2 ▸ Finset.mem_erase.mpr ⟨hzu, hzB2⟩, (mem_outN.mp hz).2⟩)
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hzB3, hzB2⟩)
    have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    have hh := hm y (hYV hy)
    change Z.card ≤ s - 1 at h3
    omega
  exact acyclic_wide_pair_no_back hs (hf.mono_set (Finset.union_subset hXV hYV))
    hacy hXY h1 h2 hhigh hlow

/-- The six-vertex second layer of the small profile is acyclic. -/
theorem small_profile_six_second_acyclic {D : CH.Digraph} {V : Finset ℕ} {u : ℕ}
    (hf : QFree D V 5) (hsat : Sat 5 D V) (hu : u ∈ V) (hV : V.card = 31)
    (hm : ∀ v ∈ V, 6 ≤ (outN D V v).card) (hp : RemainingSixProfile D V u)
    (hsmall : (ball D V u 4).card ≤ 23)
    (hY : (ball D V u 2 \ ball D V u 1).card = 6) :
    QFree D (ball D V u 2 \ ball D V u 1) 6 := by
  obtain ⟨y, hy, hsink⟩ := small_profile_six_second_has_sink hf hsat hu hV hm hp hsmall hY
  apply qfree_succ_of_sink (hf.mono_set (Finset.sdiff_subset.trans ball_subset)) hY hy
  intro z hz hyz
  have hh := mem_outN.mpr ⟨hz, hyz⟩
  rw [hsink] at hh
  exact Finset.notMem_empty z hh

/-- A return forced by layer two rules out acyclicity of the seven-vertex
first layer. This does not yet rule out its six- and seven-cycles. -/
theorem small_profile_seven_first_not_acyclic {D : CH.Digraph} {V : Finset ℕ} {u : ℕ}
    (hf : QFree D V 5) (hsat : Sat 5 D V) (hu : u ∈ V) (hV : V.card = 31)
    (hm : ∀ v ∈ V, 6 ≤ (outN D V v).card) (hp : RemainingSixProfile D V u)
    (hsmall : (ball D V u 4).card ≤ 23)
    (hY : (ball D V u 2 \ ball D V u 1).card = 6) :
    ¬ QFree D (outN D V u) 7 := by
  intro hacy
  obtain ⟨hB2, h3, _, _, _⟩ := remaining_six_small_ball_cards hf hu hp hsmall
  have hU2 : (ball D V u 2).erase u = outN D V u ∪ (ball D V u 2 \ ball D V u 1) := by
    rw [show 2 = 1 + 1 by decide, erase_ball_succ_eq_union hu,
      erase_ball_one_eq_outN hf (by decide) hu]
  have hdisj : Disjoint (outN D V u) (ball D V u 2 \ ball D V u 1) :=
    Finset.disjoint_left.mpr (fun x hx hy =>
      (Finset.mem_sdiff.mp hy).2 ((mem_ball_one hu).mpr (Or.inr hx)))
  have hcard := congrArg Finset.card hU2
  rw [Finset.card_erase_of_mem (self_mem_ball hu), Finset.card_union_of_disjoint hdisj,
    hB2, hY] at hcard
  have hn := acyclic_wide_layers_no_back (by decide : 6 ≤ 6) hf hu hm
    (by omega : (outN D V u).card = 6 + 1) hY h3.le hacy
  obtain ⟨y, hy, _, x, hx, hyx⟩ :=
    small_profile_six_second_sink_returns hf hsat hu hV hm hp hsmall hY
  exact hn y hy x hx hyx

end LeanCH.BR.BRsub
