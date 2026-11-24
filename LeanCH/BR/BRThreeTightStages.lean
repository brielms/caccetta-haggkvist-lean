import LeanCH.BR.BRLocalDegreeDrop
import LeanCH.BR.BRPrefixRetention

/-! Three tight acyclic stages expand when two additional return lengths are forbidden. -/

namespace LeanCH.BR.BRsGen
open BRq2 BRq3 BR45

theorem three_stage_funnel_expansion_of_first_cap
    {D : CH.Digraph} {V X Y Z T : Finset ℕ} {s m : ℕ}
    (hs : 1 ≤ s) (hsm : s ≤ m) (hf : QFree D V (m + 2))
    (hmin : ∀ v ∈ V, 1 ≤ (outN D V v).card)
    (hXV : X ⊆ V) (hYV : Y ⊆ V) (hZV : Z ⊆ V)
    (hXY : Disjoint X Y) (hYZ : Disjoint Y Z)
    (hX : X.card ≤ m) (hY : Y.card = s) (hZ : Z.card = s)
    (hhighX : ∀ x ∈ X, s ≤ (outN D (X ∪ Y) x).card)
    (hhighY : ∀ y ∈ Y, s ≤ (outN D (X ∪ Y ∪ Z) y).card)
    (hhighZ : ∀ z ∈ Z, s ≤ (outN D (X ∪ Y ∪ Z ∪ T) z).card) : s ≤ T.card := by
  classical
  have hlowfree := hf.mono_bound (by omega : m + 1 ≤ m + 2)
  have hb := ball_q_one (m + 1) (by omega)
  have hXYreach := small_first_funnel_of_ball (by omega : 2 ≤ m + 1) hb hlowfree
    hmin hXV hYV hXY (by simpa using hX) (by omega) hhighX
  have hnoYX := small_first_no_back_of_ball (by omega : 2 ≤ m + 1) hb hlowfree
    hmin hXV hYV hXY (by simpa using hX) (by omega) hhighX
  have hkeepY : ∀ y ∈ Y, outN D (X ∪ Y ∪ Z) y ⊆ outN D (Y ∪ Z) y := by
    intro y hy z hz
    obtain ⟨hzU, hyz⟩ := mem_outN.mp hz
    refine mem_outN.mpr ⟨?_, hyz⟩
    rcases Finset.mem_union.mp hzU with hzXY | hzZ
    · rcases Finset.mem_union.mp hzXY with hzX | hzY
      · exact (hnoYX y hy z hzX hyz).elim
      · exact Finset.mem_union_left _ hzY
    · exact Finset.mem_union_right _ hzZ
  have hYout : ∀ y ∈ Y, s ≤ (outN D (Y ∪ Z) y).card :=
    fun y hy => (hhighY y hy).trans (Finset.card_le_card (hkeepY y hy))
  have hnoZY := small_first_no_back_of_ball (by omega : 2 ≤ m + 1) hb hlowfree
    hmin hYV hZV hYZ (by simpa [hY] using hsm) (by omega) hYout
  obtain ⟨y, hy, hysink⟩ := exists_sink (hf.mono_set hYV)
    (Finset.card_pos.mp (by omega : 0 < Y.card)) (by omega)
  have hfullY : ∀ z ∈ Z, D y z = true := by
    have hsub : outN D (Y ∪ Z) y ⊆ Z := by
      intro z hz
      rcases Finset.mem_union.mp (mem_outN.mp hz).1 with hzY | hzZ
      · exact (hysink z hzY (mem_outN.mp hz).2).elim
      · exact hzZ
    have heq : outN D (Y ∪ Z) y = Z :=
      Finset.eq_of_subset_of_card_le hsub (by have hh := hYout y hy; omega)
    intro z hz
    exact (mem_outN.mp (heq.symm ▸ hz)).2
  have hnoZX : ∀ z ∈ Z, ∀ x ∈ X, ¬ D z x = true := by
    intro z hz x hx hzx
    obtain ⟨m, hm, hms, w⟩ := hXYreach x hx y hy
    exact hf x (m + 1 + 1) (by omega) (by omega)
      (((w.snoc (hZV hz) (hfullY z hz))).snoc (hXV hx) hzx)
  obtain ⟨z, hz, hzsink⟩ := exists_sink (hf.mono_set hZV)
    (Finset.card_pos.mp (by omega : 0 < Z.card)) (by omega)
  have hsub : outN D (X ∪ Y ∪ Z ∪ T) z ⊆ T := by
    intro w hw
    obtain ⟨hwU, hzw⟩ := mem_outN.mp hw
    rcases Finset.mem_union.mp hwU with hwXYZ | hwT
    · rcases Finset.mem_union.mp hwXYZ with hwXY | hwZ
      · rcases Finset.mem_union.mp hwXY with hwX | hwY
        · exact (hnoZX z hz w hwX hzw).elim
        · exact (hnoZY z hz w hwY hzw).elim
      · exact (hzsink w hwZ hzw).elim
    · exact hwT
  exact (hhighZ z hz).trans (Finset.card_le_card hsub)

theorem three_stage_funnel_expansion {D : CH.Digraph} {V X Y Z T : Finset ℕ} {s : ℕ}
    (hs : 1 ≤ s) (hf : QFree D V (s + 2))
    (hmin : ∀ v ∈ V, 1 ≤ (outN D V v).card)
    (hXV : X ⊆ V) (hYV : Y ⊆ V) (hZV : Z ⊆ V)
    (hXY : Disjoint X Y) (hYZ : Disjoint Y Z)
    (hX : X.card ≤ s) (hY : Y.card = s) (hZ : Z.card = s)
    (hhighX : ∀ x ∈ X, s ≤ (outN D (X ∪ Y) x).card)
    (hhighY : ∀ y ∈ Y, s ≤ (outN D (X ∪ Y ∪ Z) y).card)
    (hhighZ : ∀ z ∈ Z, s ≤ (outN D (X ∪ Y ∪ Z ∪ T) z).card) : s ≤ T.card :=
  three_stage_funnel_expansion_of_first_cap hs le_rfl hf hmin hXV hYV hZV
    hXY hYZ hX hY hZ hhighX hhighY hhighZ

theorem fourth_layer_of_two_tight_layers_of_first_cap
    {D : CH.Digraph} {V : Finset ℕ} {u s m : ℕ}
    (hs : 2 ≤ s) (hsm : s ≤ m) (hf : QFree D V (m + 2))
    (hm : ∀ v ∈ V, s ≤ (outN D V v).card) (hu : u ∈ V)
    (hfirst : (outN D V u).card ≤ m)
    (h2 : (ball D V u 2 \ ball D V u 1).card = s)
    (h3 : (ball D V u 3 \ ball D V u 2).card = s) :
    s ≤ (ball D V u 4 \ ball D V u 3).card := by
  classical
  let X := outN D V u
  let Y := ball D V u 2 \ ball D V u 1
  let Z := ball D V u 3 \ ball D V u 2
  let T := ball D V u 4 \ ball D V u 3
  have he2 : (ball D V u 2).erase u = X ∪ Y := by
    rw [erase_ball_succ_eq_union hu, erase_ball_one_eq_outN hf (by omega) hu]
  have he3 : (ball D V u 3).erase u = X ∪ Y ∪ Z := by
    rw [erase_ball_succ_eq_union hu, he2]
  have he4 : (ball D V u 4).erase u = X ∪ Y ∪ Z ∪ T := by
    rw [erase_ball_succ_eq_union hu, he3]
  have hXV : X ⊆ V := outN_subset
  have hYV : Y ⊆ V := fun _ hy => ball_subset (Finset.mem_sdiff.mp hy).1
  have hZV : Z ⊆ V := fun _ hz => ball_subset (Finset.mem_sdiff.mp hz).1
  have hXY : Disjoint X Y := Finset.disjoint_left.mpr (fun x hx hy =>
    (Finset.mem_sdiff.mp hy).2 ((mem_ball_one hu).mpr (Or.inr hx)))
  have hYZ : Disjoint Y Z := Finset.disjoint_left.mpr (fun y hy hz =>
    (Finset.mem_sdiff.mp hz).2 (Finset.mem_sdiff.mp hy).1)
  apply three_stage_funnel_expansion_of_first_cap (by omega) hsm hf
    (fun v hv => by have hh := hm v hv; omega) hXV hYV hZV hXY hYZ hfirst h2 h3
  · intro x hx
    have hc := Finset.card_le_card (outN_prefix_erase_root hf hu (by omega : 1 + 1 ≤ m + 2)
      ((mem_ball_one hu).mpr (Or.inr hx)))
    rw [he2] at hc
    exact (hm x (hXV hx)).trans hc
  · intro y hy
    have hc := Finset.card_le_card (outN_prefix_erase_root hf hu (by omega : 2 + 1 ≤ m + 2)
      (Finset.mem_sdiff.mp hy).1)
    rw [he3] at hc
    exact (hm y (hYV hy)).trans hc
  · intro z hz
    have hc := Finset.card_le_card (outN_prefix_erase_root hf hu (by omega : 3 + 1 ≤ m + 2)
      (Finset.mem_sdiff.mp hz).1)
    rw [he4] at hc
    exact (hm z (hZV hz)).trans hc

theorem fourth_layer_of_two_tight_layers {D : CH.Digraph} {V : Finset ℕ} {u s : ℕ}
    (hs : 2 ≤ s) (hf : QFree D V (s + 2)) (ho : OutEq s D V) (hu : u ∈ V)
    (h2 : (ball D V u 2 \ ball D V u 1).card = s)
    (h3 : (ball D V u 3 \ ball D V u 2).card = s) :
    s ≤ (ball D V u 4 \ ball D V u 3).card :=
  fourth_layer_of_two_tight_layers_of_first_cap hs le_rfl hf
    (fun v hv => (ho v hv).ge) hu (ho u hu).le h2 h3

end LeanCH.BR.BRsGen
