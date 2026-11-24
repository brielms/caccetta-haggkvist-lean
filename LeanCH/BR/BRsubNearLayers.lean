import LeanCH.BR.BRNearCycle
import LeanCH.BR.BRNarrowPair
import LeanCH.BR.BRsubSetBall21

/-! A first layer of size s+1 followed by layers of sizes s-1 and s. -/

namespace LeanCH.BR.BRsub

open BRq2 BRq3 BR45 BRsGen

variable {E : CH.Digraph} {V : Finset ℕ} {u s : ℕ}

/-- The first-layer near-cycle funnel inside the ambient graph. -/
theorem wide_first_funnel (hs : 4 ≤ s) (hf : QFree E V (s - 1))
    (hu : u ∈ V) (hmin : ∀ v ∈ V, s ≤ (outN E V v).card)
    (h1 : (outN E V u).card = s + 1)
    (h2 : (ball E V u 2 \ ball E V u 1).card = s - 1) :
    ∀ x ∈ outN E V u, ∀ y ∈ ball E V u 2 \ ball E V u 1,
      ∃ m, 1 ≤ m ∧ m ≤ 3 ∧ Walk E V x y m := by
  classical
  let X := outN E V u
  let Y := ball E V u 2 \ ball E V u 1
  have hXV : X ⊆ V := outN_subset
  have hYV : Y ⊆ V := fun _ hy => ball_subset (Finset.mem_sdiff.mp hy).1
  have hXV1 : X ⊆ ball E V u 1 := fun _ hx => (mem_ball_one hu).mpr (Or.inr hx)
  have hXY : Disjoint X Y := Finset.disjoint_left.mpr
    (fun x hx hy => (Finset.mem_sdiff.mp hy).2 (hXV1 hx))
  have hhigh : ∀ x ∈ X, s ≤ (outN E (X ∪ Y) x).card := by
    intro x hx
    have hsub : outN E V x ⊆ outN E (X ∪ Y) x := by
      intro z hz
      obtain ⟨hzV, hxz⟩ := mem_outN.mp hz
      have hz2 := ball_step (hXV1 hx) hzV hxz
      refine mem_outN.mpr ⟨?_, hxz⟩
      by_cases hz1 : z ∈ ball E V u 1
      · rcases (mem_ball_one hu).mp hz1 with hzu | hzX
        · exact (no_back_arc hf hu (hXV1 hx) (by omega) (hzu ▸ hxz)).elim
        · exact Finset.mem_union_left _ hzX
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hz2, hz1⟩)
    exact (hmin x (hXV hx)).trans (Finset.card_le_card hsub)
  have hfun := near_cycle_funnel hs (hf.mono_set (Finset.union_subset hXV hYV)) hXY h1 h2 hhigh
  intro x hx y hy
  obtain ⟨m, hm, hm3, w⟩ := hfun x hx y hy
  exact ⟨m, hm, hm3, w.mono (Finset.union_subset hXV hYV)⟩

/-- The near-cycle funnel excludes third-layer return arcs in the `(s+1,s-1,s)` shape. -/
theorem wide_first_layers_no_back (hs : 6 ≤ s) (hf : QFree E V (s - 1))
    (hu : u ∈ V) (hmin : ∀ v ∈ V, s ≤ (outN E V v).card)
    (h1 : (outN E V u).card = s + 1)
    (h2 : (ball E V u 2 \ ball E V u 1).card = s - 1)
    (h3 : (ball E V u 3 \ ball E V u 2).card = s)
    (h4 : (ball E V u 4 \ ball E V u 3).card ≤ s - 1) :
    ∀ z ∈ ball E V u 3 \ ball E V u 2, ∀ v ∈ ball E V u 2, ¬ E z v = true := by
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
  have hYZ : Disjoint Y Z := Finset.disjoint_left.mpr
    (fun y hy hz => (Finset.mem_sdiff.mp hz).2 (Finset.mem_sdiff.mp hy).1)
  have hsplit2 : ∀ v ∈ ball E V u 2, v ≠ u → v ∈ X ∪ Y := by
    intro v hv hvu
    by_cases hv1 : v ∈ ball E V u 1
    · rcases (mem_ball_one hu).mp hv1 with h | h
      · exact (hvu h).elim
      · exact Finset.mem_union_left _ h
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hv, hv1⟩)
  have hhighX : ∀ x ∈ X, s ≤ (outN E (X ∪ Y) x).card := by
    intro x hx
    have hsub : outN E V x ⊆ outN E (X ∪ Y) x := by
      intro v hv
      obtain ⟨hvV, hxv⟩ := mem_outN.mp hv
      refine mem_outN.mpr ⟨hsplit2 v (ball_step (hXV1 hx) hvV hxv) ?_, hxv⟩
      intro hvu
      exact no_back_arc hf hu (hXV1 hx) (by omega) (hvu ▸ hxv)
    exact (hmin x (hXV hx)).trans (Finset.card_le_card hsub)
  have hfunnel := near_cycle_funnel (by omega : 4 ≤ s)
    (hf.mono_set (Finset.union_subset hXV hYV)) hXY h1 h2 hhighX
  have hnoYX : ∀ y ∈ Y, ∀ x ∈ X, ¬ E y x = true := by
    intro y hy x hx hyx
    obtain ⟨m, hm, hm3, w⟩ := hfunnel x hx y hy
    exact hf x (m + 1) (by omega) (by omega)
      ((w.mono (Finset.union_subset hXV hYV)).snoc (hXV hx) hyx)
  have hnoZX : ∀ z ∈ Z, ∀ x ∈ X, ¬ E z x = true := by
    intro z hz x hx hzx
    obtain ⟨y, hy, hyz⟩ := ball_succ_pred hu (Finset.mem_sdiff.mp hz).1 (Finset.mem_sdiff.mp hz).2
    have hy1 : y ∉ ball E V u 1 := by
      intro hy1
      exact (Finset.mem_sdiff.mp hz).2 (ball_step hy1 (hZV hz) hyz)
    have hyY : y ∈ Y := Finset.mem_sdiff.mpr ⟨hy, hy1⟩
    obtain ⟨m, hm, hm3, w⟩ := hfunnel x hx y hyY
    exact hf x (m + 1 + 1) (by omega) (by omega)
      (((w.mono (Finset.union_subset hXV hYV)).snoc (hZV hz) hyz).snoc (hXV hx) hzx)
  have hsplit3 : ∀ v ∈ ball E V u 3, v ≠ u → v ∉ X → v ∈ Y ∪ Z := by
    intro v hv hvu hvX
    by_cases hv2 : v ∈ ball E V u 2
    · rcases Finset.mem_union.mp (hsplit2 v hv2 hvu) with hx | hy
      · exact (hvX hx).elim
      · exact Finset.mem_union_left _ hy
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hv, hv2⟩)
  have hhighY : ∀ y ∈ Y, s ≤ (outN E (Y ∪ Z) y).card := by
    intro y hy
    have hsub : outN E V y ⊆ outN E (Y ∪ Z) y := by
      intro v hv
      obtain ⟨hvV, hyv⟩ := mem_outN.mp hv
      refine mem_outN.mpr ⟨hsplit3 v (ball_step (Finset.mem_sdiff.mp hy).1 hvV hyv) ?_ ?_, hyv⟩
      · intro hvu
        exact no_back_arc hf hu (Finset.mem_sdiff.mp hy).1 (by omega) (hvu ▸ hyv)
      · intro hvX
        exact hnoYX y hy v hvX hyv
    exact (hmin y (hYV hy)).trans (Finset.card_le_card hsub)
  have hlowZ : ∀ z ∈ Z, 1 ≤ (outN E (Y ∪ Z) z).card := by
    intro z hz
    have hsub : outN E V z ⊆ outN E (Y ∪ Z) z ∪ K := by
      intro v hv
      obtain ⟨hvV, hzv⟩ := mem_outN.mp hv
      by_cases hv3 : v ∈ ball E V u 3
      · refine Finset.mem_union_left _ (mem_outN.mpr ⟨hsplit3 v hv3 ?_ ?_, hzv⟩)
        · intro hvu
          exact no_back_arc hf hu (Finset.mem_sdiff.mp hz).1 (by omega) (hvu ▸ hzv)
        · intro hvX
          exact hnoZX z hz v hvX hzv
      · exact Finset.mem_union_right _
          (Finset.mem_sdiff.mpr ⟨ball_step (Finset.mem_sdiff.mp hz).1 hvV hzv, hv3⟩)
    have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    have hh := hmin z (hZV hz)
    change K.card ≤ s - 1 at h4
    omega
  have hnoZY := narrow_pair_no_back (by omega : 4 ≤ s)
    (hf.mono_set (Finset.union_subset hYV hZV)) hYZ h2 h3 hhighY hlowZ
  intro z hz v hv hzv
  by_cases hvu : v = u
  · exact no_back_arc hf hu (Finset.mem_sdiff.mp hz).1 (by omega) (hvu ▸ hzv)
  · rcases Finset.mem_union.mp (hsplit2 v hv hvu) with hvX | hvY
    · exact hnoZX z hz v hvX hzv
    · exact hnoZY z hz v hvY hzv

/-- The strengthened module cap excludes every `(7,5,6,<=5)` initial profile. -/
theorem no_first_layers_seven_five_six_small (hf : QFree E V 5) (hsat : Sat 5 E V)
    (hV : V.card = 31) (hmin : ∀ v ∈ V, 6 ≤ (outN E V v).card) (hu : u ∈ V)
    (h1 : (outN E V u).card = 7)
    (h2 : (ball E V u 2 \ ball E V u 1).card = 5)
    (h3 : (ball E V u 3 \ ball E V u 2).card = 6)
    (h4 : (ball E V u 4 \ ball E V u 3).card ≤ 5) : False := by
  classical
  let P := ball E V u 2 \ ball E V u 1
  let M := ball E V u 3 \ ball E V u 2
  let Y := ball E V u 4 \ ball E V u 3
  have hPV : P ⊆ V := fun _ hp => ball_subset (Finset.mem_sdiff.mp hp).1
  have hMV : M ⊆ V := fun _ hm => ball_subset (Finset.mem_sdiff.mp hm).1
  have hYV : Y ⊆ V := fun _ hy => ball_subset (Finset.mem_sdiff.mp hy).1
  have hn := wide_first_layers_no_back (by decide : 6 ≤ 6) hf hu hmin h1 h2 h3 h4
  have hMY : Disjoint M Y := Finset.disjoint_left.mpr
    (fun x hx hy => (Finset.mem_sdiff.mp hy).2 (Finset.mem_sdiff.mp hx).1)
  have hout : ∀ x ∈ M, (outN E V x).card = (outN E M x).card + (outN E Y x).card := by
    intro x hx
    have heq : outN E V x = outN E (M ∪ Y) x := by
      apply Finset.Subset.antisymm _ (outN_mono (Finset.union_subset hMV hYV) x)
      intro z hz
      obtain ⟨hzV, hxz⟩ := mem_outN.mp hz
      refine mem_outN.mpr ⟨?_, hxz⟩
      have hz4 := ball_step (Finset.mem_sdiff.mp hx).1 hzV hxz
      by_cases hz3 : z ∈ ball E V u 3
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hz3, fun hz2 => hn x hx z hz2 hxz⟩)
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hz4, hz3⟩)
    rw [heq, card_outN_union hMY]
  have hminM : ∀ x ∈ M, 1 ≤ (outN E M x).card := by
    intro x hx
    have hh := hmin x (hMV hx)
    rw [hout x hx] at hh
    have hc := Finset.card_le_card (outN_subset (D := E) (W := Y) (y := x))
    change Y.card ≤ 5 at h4
    omega
  have hreg := (dt_reg (by decide) (ball_q_one 5 (by decide)) (hf.mono_set hMV) hminM h3).1
  have hfull : ∀ x ∈ M, outN E Y x = Y := by
    intro x hx
    apply Finset.eq_of_subset_of_card_le outN_subset
    have hh := hmin x (hMV hx)
    rw [hout x hx, hreg x hx] at hh
    change Y.card ≤ 5 at h4
    omega
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (by change M.card = 6 at h3; omega : 0 < M.card)
  have hY5 : Y.card = 5 := by
    have hh := hmin x (hMV hx)
    rw [hout x hx, hreg x hx, hfull x hx] at hh
    change Y.card ≤ 5 at h4
    omega
  have hhead : ∀ x ∈ M, ∀ y ∈ Y, E x y = true := fun x hx y hy =>
    (mem_outN.mp ((hfull x hx).symm ▸ hy)).2
  have hdeg : ∀ x ∈ M, (outN E V x).card = 6 := by
    intro x hx
    rw [hout x hx, hreg x hx, hfull x hx, hY5]
  have hcap := tightModule_WM_le_four hf hV hmin hMV hYV h3 hY5 hhead
  have hsub : P ⊆ WM E V M Y 5 := by
    intro p hp
    obtain ⟨x, hx, hpx⟩ := exists_depth_three_head (by decide) hf hsat hu
      (Finset.mem_sdiff.mp hp).1 (Finset.mem_sdiff.mp hp).2
    have hin : p ∈ inN E V x := mem_inN.mpr ⟨hPV hp, hpx⟩
    rw [lemmaM (by decide : 5 + 1 = 6) (by decide) hf hsat hMV hYV hY5 hhead hdeg hreg hx] at hin
    rcases Finset.mem_union.mp hin with hinM | hinW
    · exact ((Finset.mem_sdiff.mp (mem_inN.mp hinM).1).2 (Finset.mem_sdiff.mp hp).1).elim
    · exact hinW
  have hc := Finset.card_le_card hsub
  change P.card = 5 at h2
  omega

/-- The whole `(7,5)` first-two-layer branch satisfies the strict non-tight cap. -/
theorem wide_first_ball_four_ge_twenty_five (hf : QFree E V 5) (hsat : Sat 5 E V)
    (hV : V.card = 31) (hmin : ∀ v ∈ V, 6 ≤ (outN E V v).card) (hu : u ∈ V)
    (h1 : (outN E V u).card = 7)
    (h2 : (ball E V u 2 \ ball E V u 1).card = 5) :
    25 ≤ (ball E V u 4).card := by
  classical
  let Y := ball E V u 2 \ ball E V u 1
  have hYV : Y ⊆ V := fun _ hy => ball_subset (Finset.mem_sdiff.mp hy).1
  have hfunnel := wide_first_funnel (by decide : 4 ≤ 6) hf hu hmin h1 h2
  have h17 := card_ballSet_two_ge_seventeen hf hsat hV hmin hYV h2
  have hsub : ballSet E V Y 2 ⊆ ball E V u 4 := by
    intro z hz
    obtain ⟨y, hy, hyz⟩ := mem_ballSet.mp hz
    obtain ⟨_, m, hm, wm⟩ := mem_ball.mp (Finset.mem_sdiff.mp hy).1
    obtain ⟨hzV, n, hn, wn⟩ := mem_ball.mp hyz
    exact mem_ball.mpr ⟨hzV, m + n, by omega, wm.append wn⟩
  have hdisj : Disjoint (ball E V u 1) (ballSet E V Y 2) := by
    apply Finset.disjoint_left.mpr
    intro z hz1 hzY
    obtain ⟨y, hy, hyz⟩ := mem_ballSet.mp hzY
    obtain ⟨_, n, hn, wn⟩ := mem_ball.mp hyz
    rcases (mem_ball_one hu).mp hz1 with hzu | hzX
    · obtain ⟨_, m, hm, wm⟩ := mem_ball.mp (Finset.mem_sdiff.mp hy).1
      have hmpos : 1 ≤ m := by
        by_contra hm0
        have heq : m = 0 := by omega
        subst m
        cases wm
        exact (Finset.mem_sdiff.mp hy).2 (self_mem_ball hu)
      have wn' : Walk E V y u n := hzu ▸ wn
      exact hf u (m + n) (by omega) (by omega) (wm.append wn')
    · obtain ⟨m, hm, hm3, wm⟩ := hfunnel z hzX y hy
      exact hf z (m + n) (by omega) (by omega) (wm.append wn)
  have hle := Finset.card_le_card
    (Finset.union_subset (ball_mono_radius (by decide : 1 ≤ 4)) hsub)
  rw [Finset.card_union_of_disjoint hdisj] at hle
  have hB1 : (ball E V u 1).card = 8 := by
    have heq : ball E V u 1 = insert u (outN E V u) := by
      ext z
      simp only [mem_ball_one hu, Finset.mem_insert]
    have huO : u ∉ outN E V u := fun h => loopfree hf (by decide) hu (mem_outN.mp h).2
    rw [heq, Finset.card_insert_of_notMem huO, h1]
  omega

end LeanCH.BR.BRsub
