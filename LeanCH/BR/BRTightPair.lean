import LeanCH.BR.BRTightChain

/-! Two-layer access improves the forbidden-return budget for arbitrary tight prefixes. -/

namespace LeanCH.BR.BRsGen
open BRq2 BRq3 BR45

/-- Local degree descent reaches a prescribed target set whose size covers the missing heads. -/
theorem small_first_reaches_target_set {D : CH.Digraph} {V X Y P : Finset ℕ}
    {q d s : ℕ} (hq : 2 ≤ q) (hb : Ball q d) (hf : QFree D V q)
    (hm : ∀ v ∈ V, d ≤ (outN D V v).card)
    (hXV : X ⊆ V) (hYV : Y ⊆ V) (hXY : Disjoint X Y)
    (hX : X.card ≤ d * (q - 1)) (hPY : P ⊆ Y)
    (hbudget : d + Y.card ≤ s + P.card)
    (hhigh : ∀ x ∈ X, s ≤ (outN D (X ∪ Y) x).card) :
    ∀ x ∈ X, ∃ p ∈ P, ∃ m, 1 ≤ m ∧ m ≤ q - 1 ∧ Walk D V x p m := by
  intro x hx
  obtain ⟨b, hbX, hlow, m, hm, w⟩ := local_degree_drop_reachable hq hb hf hm hXV hX hx
  obtain ⟨p, hpP, hbp⟩ : ∃ p ∈ P, D b p = true := by
    by_contra hn
    have hsub : outN D Y b ⊆ Y \ P := by
      intro p hp
      exact Finset.mem_sdiff.mpr ⟨(mem_outN.mp hp).1,
        fun hpP => hn ⟨p, hpP, (mem_outN.mp hp).2⟩⟩
    have hcount := Finset.card_le_card hsub
    have hpart := Finset.card_sdiff_add_card_eq_card hPY
    have hh := hhigh b hbX
    rw [card_outN_union hXY] at hh
    omega
  exact ⟨p, hpP, m + 1, by omega, by omega, (w.mono hXV).snoc (hYV (hPY hpP)) hbp⟩

/-- Two consecutive sink removals give a two-element subset closed under internal heads. -/
theorem exists_closed_pair {D : CH.Digraph} {Y : Finset ℕ} {q : ℕ}
    (hf : QFree D Y q) (hY : 2 ≤ Y.card) (hYq : Y.card ≤ q) :
    ∃ P : Finset ℕ, P ⊆ Y ∧ P.card = 2 ∧
      ∀ p ∈ P, ∀ y ∈ Y, D p y = true → y ∈ P := by
  classical
  obtain ⟨a, ha, hsa⟩ := exists_sink hf (Finset.card_pos.mp (by omega)) hYq
  have he : (Y.erase a).card = Y.card - 1 := Finset.card_erase_of_mem ha
  obtain ⟨b, hb, hsb⟩ := exists_sink (hf.mono_set (Finset.erase_subset a Y))
    (Finset.card_pos.mp (by omega : 0 < (Y.erase a).card)) (by omega)
  have hba : b ≠ a := (Finset.mem_erase.mp hb).1
  refine ⟨{a, b}, ?_, by simp [Ne.symm hba], ?_⟩
  · intro y hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact ha
    · rcases Finset.mem_singleton.mp hy with rfl
      exact (Finset.mem_erase.mp hb).2
  · intro p hp y hy hpy
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact (hsa y hy hpy).elim
    · have hpb : p = b := Finset.mem_singleton.mp hp
      subst p
      by_cases hya : y = a
      · simp [hya]
      · exact (hsb y (Finset.mem_erase.mpr ⟨hya, hy⟩) hpy).elim

/-- Two tight layers reach every third-layer vertex within ceil(s/2)+2 steps. -/
theorem two_layer_pair_funnel {D : CH.Digraph} {V X Y Z : Finset ℕ} {s q : ℕ}
    (hs : 2 ≤ s) (hq : s + 1 ≤ q) (hf : QFree D V q)
    (hm : ∀ v ∈ V, 2 ≤ (outN D V v).card)
    (hXV : X ⊆ V) (hYV : Y ⊆ V) (hZV : Z ⊆ V)
    (hXY : Disjoint X Y) (hYZ : Disjoint Y Z)
    (hX : X.card = s) (hY : Y.card = s) (hZ : Z.card = s)
    (hhighX : ∀ x ∈ X, s ≤ (outN D (X ∪ Y) x).card)
    (hhighY : ∀ y ∈ Y, s ≤ (outN D (Y ∪ Z) y).card) :
    ∀ x ∈ X, ∀ z ∈ Z, ∃ m, 1 ≤ m ∧ m ≤ (s + 1) / 2 + 2 ∧ Walk D V x z m := by
  obtain ⟨P, hPY, hP, hclosed⟩ := exists_closed_pair (hf.mono_set hYV) (by omega) (by omega)
  let L := (s + 1) / 2 + 1
  have hL : 2 ≤ L := by dsimp [L]; omega
  have hLq : L ≤ q := by dsimp [L]; omega
  have hb : Ball L 2 := by
    intro G W hG hOut u hu
    exact ball_growth L (by omega) G W hG (fun v hv => (hOut v hv).ge) u hu (L - 1) (by omega)
  have hhighP : ∀ p ∈ P, s ≤ (outN D (P ∪ Z) p).card := by
    intro p hp
    apply (hhighY p (hPY hp)).trans
    apply Finset.card_le_card
    intro z hz
    obtain ⟨hzU, hpz⟩ := mem_outN.mp hz
    refine mem_outN.mpr ⟨?_, hpz⟩
    rcases Finset.mem_union.mp hzU with hzY | hzZ
    · exact Finset.mem_union_left _ (hclosed p hp z hzY hpz)
    · exact Finset.mem_union_right _ hzZ
  have hPZ : Disjoint P Z := Finset.disjoint_left.mpr
    (fun p hp hz => Finset.disjoint_left.mp hYZ (hPY hp) hz)
  intro x hx z hz
  obtain ⟨p, hp, a, ha, haL, wa⟩ := small_first_reaches_target_set hL hb
    (hf.mono_bound hLq) hm hXV hYV hXY
    (by dsimp [L]; omega) hPY (by omega) hhighX x hx
  obtain ⟨b, hbpos, hb2, wb⟩ := small_first_funnel_of_ball (by decide : 2 ≤ 3)
    (ball_q_one 3 (by decide)) (hf.mono_bound (by omega))
    (fun v hv => by have hh := hm v hv; omega) (hPY.trans hYV) hZV hPZ
    (by omega) (by omega) hhighP p hp z hz
  exact ⟨a + b, by omega, by dsimp [L] at haL; omega, wa.append wb⟩

/-- Pair access excludes all earlier-layer returns at the improved cutoff. -/
theorem tight_prefix_no_back_pair {s k q : ℕ} (hs : 2 ≤ s) (_hk : 2 ≤ k)
    (hnear : s + 1 ≤ q) (hfar : (s + 1) / 2 + k ≤ q)
    {D : CH.Digraph} {V : Finset ℕ} {u : ℕ}
    (hf : QFree D V q) (hm : ∀ v ∈ V, s ≤ (outN D V v).card) (hu : u ∈ V)
    (htight : ∀ i, 1 ≤ i → i ≤ k → (ball D V u i \ ball D V u (i - 1)).card = s) :
    ∀ j, 1 ≤ j → j ≤ k → ∀ y ∈ ball D V u j \ ball D V u (j - 1),
      ∀ x ∈ ball D V u (j - 1), ¬ D y x = true := by
  have hreturn : k + 1 ≤ q := by omega
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
    intro hj hjk y hy x hx hyx
    by_cases hxu : x = u
    · subst x
      exact no_back_arc hf hu (Finset.mem_sdiff.mp hy).1 (by omega) hyx
    obtain ⟨i, hi, hij, hxi⟩ := ball_mem_positive_layer hx hxu
    have hib : i < j := by omega
    have hnoback := ih i hib hi (by omega)
    let X := ball D V u i \ ball D V u (i - 1)
    let Y := ball D V u (i + 1) \ ball D V u i
    have hXV : X ⊆ V := fun _ hv => ball_subset (Finset.mem_sdiff.mp hv).1
    have hYV : Y ⊆ V := fun _ hv => ball_subset (Finset.mem_sdiff.mp hv).1
    have hXY : Disjoint X Y := Finset.disjoint_left.mpr (fun v hv hw =>
      (Finset.mem_sdiff.mp hw).2 (Finset.mem_sdiff.mp hv).1)
    have hXc : X.card = s := htight i hi (by omega)
    have hYc : Y.card = s := by
      simpa only [Nat.add_sub_cancel] using htight (i + 1) (by omega) (by omega)
    have hhighX : ∀ v ∈ X, s ≤ (outN D (X ∪ Y) v).card := by
      intro v hv
      exact (hm v (hXV hv)).trans (Finset.card_le_card (layer_rows_of_no_back hnoback hv))
    by_cases hadj : j = i + 1
    · have hyY : y ∈ Y := by simpa [hadj, Y] using hy
      obtain ⟨m, hmpos, hms, w⟩ := small_first_funnel_of_ball (by omega : 2 ≤ s + 1)
        (ball_q_one (s + 1) (by omega)) (hf.mono_bound hnear)
        (fun v hv => by have hh := hm v hv; omega) hXV hYV hXY
        (by simp [hXc]) (by omega) hhighX x hxi y hyY
      exact hf x (m + 1) (by omega) (by omega) (w.snoc (ball_subset hx) hyx)
    have hgap : i + 2 ≤ j := by omega
    let Z := ball D V u (i + 2) \ ball D V u (i + 1)
    have hZV : Z ⊆ V := fun _ hv => ball_subset (Finset.mem_sdiff.mp hv).1
    have hYZ : Disjoint Y Z := Finset.disjoint_left.mpr (fun v hv hw =>
      (Finset.mem_sdiff.mp hw).2 (Finset.mem_sdiff.mp hv).1)
    have hZc : Z.card = s := by
      simpa only [show i + 2 - 1 = i + 1 by omega] using
        htight (i + 2) (by omega) (by omega)
    have hnoY := ih (i + 1) (by omega) (by omega) (by omega)
    have hhighY : ∀ v ∈ Y, s ≤ (outN D (Y ∪ Z) v).card := by
      intro v hv
      have hvY : v ∈ ball D V u (i + 1) \ ball D V u (i + 1 - 1) := by
        simpa only [Nat.add_sub_cancel] using hv
      have hh := layer_rows_of_no_back hnoY hvY
      have hc := (hm v (hYV hv)).trans (Finset.card_le_card hh)
      simpa only [Nat.add_sub_cancel, show i + 1 + 1 = i + 2 by omega] using hc
    obtain ⟨z, hz, wz⟩ := layer_geodesic_ancestor hu (by omega : 1 ≤ i + 2) hgap hy
    have hzZ : z ∈ Z := by simpa only [show i + 2 - 1 = i + 1 by omega] using hz
    obtain ⟨m, hmpos, hms, w⟩ := two_layer_pair_funnel hs hnear hf
      (fun v hv => by have hh := hm v hv; omega) hXV hYV hZV hXY hYZ
      hXc hYc hZc hhighX hhighY x hxi z hzZ
    exact hf x (m + (j - (i + 2)) + 1) (by omega) (by omega)
      ((w.append wz).snoc (ball_subset hx) hyx)

/-- Tight-prefix expansion with separate adjacent and nonadjacent return budgets. -/
theorem tight_layers_expand_pair {s k q : ℕ} (hs : 2 ≤ s) (hk : 2 ≤ k)
    (hnear : s + 1 ≤ q) (hfar : (s + 1) / 2 + k ≤ q)
    {D : CH.Digraph} {V : Finset ℕ} {u : ℕ}
    (hf : QFree D V q) (hm : ∀ v ∈ V, s ≤ (outN D V v).card) (hu : u ∈ V)
    (htight : ∀ i, 1 ≤ i → i ≤ k → (ball D V u i \ ball D V u (i - 1)).card = s) :
    s ≤ (ball D V u (k + 1) \ ball D V u k).card := by
  let X := ball D V u k \ ball D V u (k - 1)
  let Y := ball D V u (k + 1) \ ball D V u k
  have hXV : X ⊆ V := fun _ hx => ball_subset (Finset.mem_sdiff.mp hx).1
  have hXc : X.card = s := htight k (by omega) le_rfl
  obtain ⟨x, hx, hsink⟩ := exists_sink (hf.mono_set hXV)
    (Finset.card_pos.mp (by omega : 0 < X.card)) (by omega)
  have hkeep := layer_rows_of_no_back
    (tight_prefix_no_back_pair hs hk hnear hfar hf hm hu htight k (by omega) le_rfl) hx
  have hsub : outN D V x ⊆ Y := by
    intro y hy
    obtain ⟨hyU, hxy⟩ := mem_outN.mp (hkeep hy)
    rcases Finset.mem_union.mp hyU with hyX | hyY
    · exact (hsink y hyX hxy).elim
    · exact hyY
  exact (hm x (hXV hx)).trans (Finset.card_le_card hsub)

end LeanCH.BR.BRsGen
