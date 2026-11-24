import LeanCH.BR.BRsubM

/-!
# Set balls and tight modules at `(q,s) = (5,6)`

The set-ball bound uses the smaller-degree deletion tests on two consecutive
balls. The tight-module bound then follows from the disjoint sets in Lemma M.
-/

namespace LeanCH.BR.BRsub

open BRq2 BRq3 BR45

variable {E : CH.Digraph} {V Y : Finset ℕ}

theorem ballSet_subset {k : ℕ} : ballSet E V Y k ⊆ V := by
  intro v hv
  obtain ⟨_, _, hw⟩ := mem_ballSet.mp hv
  exact ball_subset hw

theorem subset_ballSet {k : ℕ} (hY : Y ⊆ V) : Y ⊆ ballSet E V Y k :=
  fun y hy => mem_ballSet.mpr ⟨y, hy, self_mem_ball (hY hy)⟩

theorem ballSet_mono {i j : ℕ} (h : i ≤ j) : ballSet E V Y i ⊆ ballSet E V Y j := by
  intro v hv
  obtain ⟨y, hy, hw⟩ := mem_ballSet.mp hv
  exact mem_ballSet.mpr ⟨y, hy, ball_mono_radius h hw⟩

theorem outN_subset_ballSet_succ {k x : ℕ} (hx : x ∈ ballSet E V Y k) :
    outN E V x ⊆ ballSet E V Y (k + 1) := by
  intro z hz
  obtain ⟨y, hy, hxy⟩ := mem_ballSet.mp hx
  obtain ⟨hzV, hxz⟩ := mem_outN.mp hz
  exact mem_ballSet.mpr ⟨y, hy, ball_step hxy hzV hxz⟩

theorem ball_five_small {c : ℕ} (hc : 1 ≤ c) (hc4 : c ≤ 4) : Ball 5 c := by
  rcases (show c = 1 ∨ c = 2 ∨ c = 3 ∨ c = 4 by omega) with rfl | rfl | rfl | rfl
  · exact ball_q_one 5 (by decide)
  · intro D W hf hout u hu
    exact ball_growth 5 (by decide) D W hf (fun v hv => (hout v hv).ge) u hu 4 (by decide)
  · exact ball_all 5 (by decide)
  · exact BRq4.ball_all4 5 (by decide)

theorem ballSet_deletion {k c : ℕ} (hc : 1 ≤ c) (hc4 : c ≤ 4)
    (hfree : QFree E V 5) (hYV : Y ⊆ V) (hYne : Y.Nonempty)
    (hout : ∀ x ∈ ballSet E V Y (k + 1), 6 ≤ (outN E V x).card)
    (hnext : c + (ballSet E V Y (k + 2) \ ballSet E V Y (k + 1)).card ≤ 6) :
    5 * c + 2 ≤ (ballSet E V Y (k + 1)).card := by
  let A := ballSet E V Y (k + 1)
  let B := ballSet E V Y (k + 2) \ A
  have hAB : Disjoint A B := Finset.disjoint_sdiff
  have hAfree : QFree E A 5 := fun a l h1 h5 w => hfree a l h1 h5 (w.mono ballSet_subset)
  have hmin : ∀ x ∈ A, c ≤ (outN E A x).card := by
    intro x hx
    have hsub : outN E V x ⊆ outN E (A ∪ B) x := by
      intro z hz
      obtain ⟨hzV, hxz⟩ := mem_outN.mp hz
      have hz' := outN_subset_ballSet_succ hx hz
      exact mem_outN.mpr ⟨Finset.mem_union.mpr (or_iff_not_imp_left.mpr
        (fun hzA => Finset.mem_sdiff.mpr ⟨hz', hzA⟩)), hxz⟩
    have hle := Finset.card_le_card hsub
    rw [card_outN_union hAB] at hle
    have hB := Finset.card_le_card (outN_subset (D := E) (W := B) (y := x))
    have h6 := hout x hx
    change c + B.card ≤ 6 at hnext
    omega
  obtain ⟨y, hy⟩ := hYne
  have hyA : y ∈ A := subset_ballSet hYV hy
  have hne : A.Nonempty := ⟨y, hyA⟩
  have hb := ball_five_small hc hc4
  have hsize := dt_size (by decide) hb hAfree hmin hne
  suffices A.card ≠ 5 * c + 1 by
    change 5 * c + 2 ≤ A.card
    omega
  intro heq
  have hreg := (dt_reg (by decide) hb hAfree hmin heq).1 y hyA
  have hsub : outN E V y ⊆ outN E A y := by
    intro z hz
    exact mem_outN.mpr ⟨outN_subset_ballSet_succ (subset_ballSet (k := k) hYV hy) hz,
      (mem_outN.mp hz).2⟩
  have hle := Finset.card_le_card hsub
  have h6 := hout y hyA
  omega

/-- Five starting vertices with out-degree at least six through radius two
reach at least twenty vertices within three steps in a 5-free digraph. -/
theorem card_ballSet_three_ge_twenty (hfree : QFree E V 5) (hYV : Y ⊆ V)
    (hY : Y.card = 5) (hout : ∀ x ∈ ballSet E V Y 2, 6 ≤ (outN E V x).card) :
    20 ≤ (ballSet E V Y 3).card := by
  have hYne : Y.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨y, hy, hsink⟩ := exists_sink
    (fun a l h1 h5 w => hfree a l h1 h5 (w.mono hYV)) hYne (by omega : Y.card ≤ 5)
  have hstart : 6 ≤ (ballSet E V Y 1 \ Y).card :=
    (hout y (subset_ballSet hYV hy)).trans (Finset.card_le_card (by
      intro z hz
      obtain ⟨hzV, hyz⟩ := mem_outN.mp hz
      exact Finset.mem_sdiff.mpr ⟨mem_ballSet.mpr ⟨y, hy, ball_of_adj hzV hyz⟩,
        fun hzY => hsink z hzY hyz⟩))
  let b (k : ℕ) := (ballSet E V Y k).card
  let l (k : ℕ) := (ballSet E V Y (k + 1) \ ballSet E V Y k).card
  have h1 : 11 ≤ b 1 := by
    have h := Finset.card_sdiff_add_card_eq_card (subset_ballSet (k := 1) (E := E) hYV)
    dsimp [b]
    omega
  have h2 : l 1 + b 1 = b 2 := Finset.card_sdiff_add_card_eq_card (ballSet_mono (by decide))
  have h3 : l 2 + b 2 = b 3 := Finset.card_sdiff_add_card_eq_card (ballSet_mono (by decide))
  have htest₁ (c : ℕ) (hc : 1 ≤ c) (hc4 : c ≤ 4) (h : c + l 1 ≤ 6) : 5 * c + 2 ≤ b 1 :=
    ballSet_deletion (k := 0) hc hc4 hfree hYV hYne
      (fun x hx => hout x (ballSet_mono (by decide : 1 ≤ 2) hx)) h
  have htest₂ (c : ℕ) (hc : 1 ≤ c) (hc4 : c ≤ 4) (h : c + l 2 ≤ 6) : 5 * c + 2 ≤ b 2 :=
    ballSet_deletion (k := 1) hc hc4 hfree hYV hYne hout h
  have h11 : l 1 ≤ 5 → 7 ≤ b 1 := fun h => htest₁ 1 (by decide) (by decide) (by omega)
  have h12 : l 1 ≤ 4 → 12 ≤ b 1 := fun h => htest₁ 2 (by decide) (by decide) (by omega)
  have h13 : l 1 ≤ 3 → 17 ≤ b 1 := fun h => htest₁ 3 (by decide) (by decide) (by omega)
  have h14 : l 1 ≤ 2 → 22 ≤ b 1 := fun h => htest₁ 4 (by decide) (by decide) (by omega)
  have h21 : l 2 ≤ 5 → 7 ≤ b 2 := fun h => htest₂ 1 (by decide) (by decide) (by omega)
  have h22 : l 2 ≤ 4 → 12 ≤ b 2 := fun h => htest₂ 2 (by decide) (by decide) (by omega)
  have h23 : l 2 ≤ 3 → 17 ≤ b 2 := fun h => htest₂ 3 (by decide) (by decide) (by omega)
  have h24 : l 2 ≤ 2 → 22 ≤ b 2 := fun h => htest₂ 4 (by decide) (by decide) (by omega)
  change 20 ≤ b 3
  omega

/-- At boundary order 31, at most five outside vertices can head a tight
six-vertex module with five common exterior heads. -/
theorem tightModule_WM_le_five {M : Finset ℕ} (hfree : QFree E V 5) (hV : V.card = 31)
    (hmin : ∀ x ∈ V, 6 ≤ (outN E V x).card) (hMV : M ⊆ V) (hYV : Y ⊆ V)
    (hM : M.card = 6) (hY : Y.card = 5) (hhead : ∀ x ∈ M, ∀ y ∈ Y, E x y = true) :
    (WM E V M Y 5).card ≤ 5 := by
  have hball := card_ballSet_three_ge_twenty hfree hYV hY
    (fun x hx => hmin x (ballSet_subset hx))
  have hd : Disjoint M (ballSet E V Y 3) := (lemmaM_a (by decide) hfree hMV hYV hhead).1
  have hsum := Finset.card_sdiff_add_card_eq_card
    (Finset.union_subset hMV (ballSet_subset (E := E) (Y := Y) (k := 3)))
  rw [Finset.card_union_of_disjoint hd, hV, hM] at hsum
  change (WM E V M Y 5).card + (6 + (ballSet E V Y 3).card) = 31 at hsum
  omega

/-- A member of a tight six-vertex module cannot be a deficient vertex in a
saturated `(5,6)` boundary graph. -/
theorem tightModule_in_le_six {M : Finset ℕ} (hfree : QFree E V 5) (hsat : Sat 5 E V)
    (hV : V.card = 31) (hmin : ∀ x ∈ V, 6 ≤ (outN E V x).card)
    (hMV : M ⊆ V) (hYV : Y ⊆ V) (hM : M.card = 6) (hY : Y.card = 5)
    (hhead : ∀ x ∈ M, ∀ y ∈ Y, E x y = true) (hout : ∀ x ∈ M, (outN E V x).card = 6)
    (hcyc : ∀ x ∈ M, (outN E M x).card = 1 ∧ (inN E M x).card = 1)
    {x : ℕ} (hx : x ∈ M) : (inN E V x).card ≤ 6 := by
  rw [lemmaM_card (by decide : 5 + 1 = 6) (by decide) hfree hsat hMV hYV hY hhead hout hcyc hx]
  have hw := tightModule_WM_le_five hfree hV hmin hMV hYV hM hY hhead
  omega

/-- A depth-two vertex in a saturated graph has an exact return of length
`q - 1`. Every vertex before the final return lies at its forward layer. -/
theorem depth_two_return {q u y : ℕ} (hq : 3 ≤ q)
    (hfree : QFree E V q) (hsat : Sat q E V) (hu : u ∈ V)
    (hy : y ∈ ball E V u 2) (hy1 : y ∉ ball E V u 1) :
    ∃ m, m + 1 = q ∧ Walk E V y u m ∧
      ∀ (i j z : ℕ), i + j = m → 0 < j →
        Walk E V y z i → Walk E V z u j →
          z ∈ ball E V u (i + 2) \ ball E V u (i + 1) := by
  have huy : ¬ E u y = true :=
    fun h => hy1 (ball_of_adj (ball_subset hy) h)
  obtain ⟨_, m, hm, ret⟩ := mem_ball.mp (hsat y (ball_subset hy) u hu huy)
  obtain ⟨_, k, hk, toY⟩ := mem_ball.mp hy
  have hk2 : k = 2 := by
    by_contra hn
    exact hy1 (mem_ball_of_walk toY (by omega) (ball_subset hy))
  have hmq : m + 1 = q := by
    by_contra hn
    exact hfree u (k + m) (by omega) (by omega) (toY.append ret)
  refine ⟨m, hmq, ret, ?_⟩
  intro i j z hij hj toZ fromZ
  have hzV : z ∈ V := by
    rcases toZ.end_mem_or with h | h
    · exact h ▸ ball_subset hy
    · exact h
  refine Finset.mem_sdiff.mpr ⟨mem_ball_of_walk (toY.append toZ) (by omega) hzV, ?_⟩
  intro hz
  obtain ⟨_, l, hl, short⟩ := mem_ball.mp hz
  exact hfree u (l + j) (by omega) (by omega) (short.append fromZ)

/-- In a saturated graph a depth-two vertex has a head at depth three. -/
theorem exists_depth_three_head {q u y : ℕ} (hq : 3 ≤ q)
    (hfree : QFree E V q) (hsat : Sat q E V) (hu : u ∈ V)
    (hy : y ∈ ball E V u 2) (hy1 : y ∉ ball E V u 1) :
    ∃ z ∈ ball E V u 3 \ ball E V u 2, E y z = true := by
  obtain ⟨m, hmq, ret, hlayers⟩ := depth_two_return hq hfree hsat hu hy hy1
  cases ret with
  | refl => omega
  | @step _ z _ k hz hyz rest =>
    have hfirst : Walk E V y z 1 := .step hz hyz (.refl z)
    exact ⟨z, hlayers 1 k z (by omega) (by omega) hfirst rest, hyz⟩

/-- A six-vertex layer followed by five vertices must send a back arc
if at least six earlier vertices have heads in the layer. -/
theorem layer_back_arc {u k : ℕ} {P : Finset ℕ} (hfree : QFree E V 5) (hsat : Sat 5 E V)
    (hV : V.card = 31) (hmin : ∀ x ∈ V, 6 ≤ (outN E V x).card)
    (hP : P ⊆ ball E V u k) (hP6 : 6 ≤ P.card)
    (hheads : ∀ y ∈ P, ∃ x ∈ ball E V u (k + 1) \ ball E V u k, E y x = true)
    (hM : (ball E V u (k + 1) \ ball E V u k).card = 6)
    (hY : (ball E V u (k + 2) \ ball E V u (k + 1)).card = 5) :
    ∃ x ∈ ball E V u (k + 1) \ ball E V u k, ∃ z ∈ ball E V u k, E x z = true := by
  let M := ball E V u (k + 1) \ ball E V u k
  let Y := ball E V u (k + 2) \ ball E V u (k + 1)
  have hMV : M ⊆ V := fun x hx => ball_subset (Finset.mem_sdiff.mp hx).1
  have hYV : Y ⊆ V := fun x hx => ball_subset (Finset.mem_sdiff.mp hx).1
  by_contra hn
  push Not at hn
  have hMY : Disjoint M Y := Finset.disjoint_left.mpr
    (fun _ hx hy => (Finset.mem_sdiff.mp hy).2 (Finset.mem_sdiff.mp hx).1)
  have hout (x : ℕ) (hx : x ∈ M) : (outN E V x).card = (outN E M x).card + (outN E Y x).card := by
    have hEq : outN E V x = outN E (M ∪ Y) x := by
      apply Finset.Subset.antisymm _ (outN_mono (Finset.union_subset hMV hYV) x)
      intro z hz
      obtain ⟨hzV, hxz⟩ := mem_outN.mp hz
      have hzNext := ball_step (Finset.mem_sdiff.mp hx).1 hzV hxz
      refine mem_outN.mpr ⟨Finset.mem_union.mpr ?_, hxz⟩
      by_cases hzHere : z ∈ ball E V u (k + 1)
      · exact Or.inl (Finset.mem_sdiff.mpr ⟨hzHere, fun hzPast => hn x hx z hzPast hxz⟩)
      · exact Or.inr (Finset.mem_sdiff.mpr ⟨hzNext, hzHere⟩)
    rw [hEq, card_outN_union hMY]
  have hminM (x : ℕ) (hx : x ∈ M) : 1 ≤ (outN E M x).card := by
    have hle := Finset.card_le_card (outN_subset (D := E) (W := Y) (y := x))
    have h6 := hmin x (hMV hx)
    change Y.card = 5 at hY
    rw [hout x hx] at h6
    omega
  have hreg := (dt_reg (by decide) (ball_q_one 5 (by decide))
    (fun a l h1 h5 w => hfree a l h1 h5 (w.mono hMV)) hminM hM).1
  have hYeq (x : ℕ) (hx : x ∈ M) : outN E Y x = Y := by
    apply Finset.eq_of_subset_of_card_le outN_subset
    have h6 := hmin x (hMV hx)
    rw [hout x hx, hreg x hx] at h6
    change Y.card = 5 at hY
    omega
  have hhead (x : ℕ) (hx : x ∈ M) (y : ℕ) (hy : y ∈ Y) : E x y = true := by
    rw [← hYeq x hx] at hy
    exact (mem_outN.mp hy).2
  have hdeg (x : ℕ) (hx : x ∈ M) : (outN E V x).card = 6 := by
    rw [hout x hx, hreg x hx, hYeq x hx, hY]
  have hcap := tightModule_WM_le_five hfree hV hmin hMV hYV hM hY hhead
  have hsub : P ⊆ WM E V M Y 5 := by
    intro y hy
    obtain ⟨x, hx, hyx⟩ := hheads y hy
    have hin : y ∈ inN E V x := mem_inN.mpr ⟨ball_subset (hP hy), hyx⟩
    rw [lemmaM (by decide : 5 + 1 = 6) (by decide) hfree hsat hMV hYV hY hhead hdeg hreg hx] at hin
    rcases Finset.mem_union.mp hin with hinM | hinW
    · exact ((Finset.mem_sdiff.mp (mem_inN.mp hinM).1).2 (hP hy)).elim
    · exact hinW
  have hle := Finset.card_le_card hsub
  omega

/-- A six-vertex depth-three layer with five vertices at depth four
must send an arc back into the radius-two ball. -/
theorem depth_three_back_arc {u : ℕ} (hfree : QFree E V 5) (hsat : Sat 5 E V)
    (hV : V.card = 31) (hmin : ∀ x ∈ V, 6 ≤ (outN E V x).card) (hu : u ∈ V)
    (h2 : 6 ≤ (ball E V u 2 \ ball E V u 1).card)
    (h3 : (ball E V u 3 \ ball E V u 2).card = 6)
    (h4 : (ball E V u 4 \ ball E V u 3).card = 5) :
    ∃ x ∈ ball E V u 3 \ ball E V u 2, ∃ z ∈ ball E V u 2, E x z = true :=
  layer_back_arc (k := 2) hfree hsat hV hmin Finset.sdiff_subset h2
    (fun y hy => exists_depth_three_head (by decide) hfree hsat hu
      (Finset.mem_sdiff.mp hy).1 (Finset.mem_sdiff.mp hy).2) h3 h4

/-- If the first three layers have sizes `(6,6,5)`, the second
layer must send a back arc into the first. -/
theorem depth_two_back_arc {u : ℕ} (hfree : QFree E V 5) (hsat : Sat 5 E V)
    (hV : V.card = 31) (hmin : ∀ x ∈ V, 6 ≤ (outN E V x).card) (hu : u ∈ V)
    (h1 : (outN E V u).card = 6)
    (h2 : (ball E V u 2 \ ball E V u 1).card = 6)
    (h3 : (ball E V u 3 \ ball E V u 2).card = 5) :
    ∃ x ∈ ball E V u 2 \ ball E V u 1, ∃ z ∈ outN E V u, E x z = true := by
  have hp : outN E V u ⊆ ball E V u 1 := fun _ hy => (mem_ball_one hu).mpr (Or.inr hy)
  have hheads (y : ℕ) (hy : y ∈ outN E V u) :
      ∃ x ∈ ball E V u 2 \ ball E V u 1, E y x = true := by
    by_contra hn
    push Not at hn
    have hyV := (mem_outN.mp hy).1
    have hsub : outN E V y ⊆ (outN E V u).erase y := by
      intro x hx
      obtain ⟨hxV, hyx⟩ := mem_outN.mp hx
      have hx2 := ball_step (hp hy) hxV hyx
      have hx1 : x ∈ ball E V u 1 := by
        by_contra hx1
        exact hn x (Finset.mem_sdiff.mpr ⟨hx2, hx1⟩) hyx
      refine Finset.mem_erase.mpr ⟨fun h => loopfree hfree (by decide) hyV (h ▸ hyx), ?_⟩
      rcases (mem_ball_one hu).mp hx1 with rfl | h
      · exact (no_back_arc hfree hu (hp hy) (by decide) hyx).elim
      · exact h
    have hle := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem hy, h1] at hle
    have h6 := hmin y hyV
    omega
  obtain ⟨x, hx, z, hz, hxz⟩ :=
    layer_back_arc (k := 1) hfree hsat hV hmin hp h1.ge hheads h2 h3
  refine ⟨x, hx, z, ?_, hxz⟩
  rcases (mem_ball_one hu).mp hz with rfl | h
  · exact (no_back_arc hfree hu (Finset.mem_sdiff.mp hx).1 (by decide) hxz).elim
  · exact h

end LeanCH.BR.BRsub
