import LeanCH.BR.BR45Base
import LeanCH.BR.BRFiniteWalk

/-! Rows with a parent in a graph at most two vertices above its girth cutoff. -/

namespace LeanCH.BR.BRq2

variable {D : CH.Digraph} {W : Finset ℕ}

theorem Walk.reverse_of_mem {a b m : ℕ} (w : Walk D W a b m) (ha : a ∈ W) :
    Walk (fun x y => D y x) W b a m := by
  induction w with
  | refl a => exact .refl a
  | step hb hab _ ih => exact (ih hb).snoc ha hab

theorem QFree.reverse {q : ℕ} (hf : QFree D W q) :
    QFree (fun x y => D y x) W q := by
  intro a m hm hmq w
  cases m with
  | zero => omega
  | succ m =>
    obtain ⟨_, _, ha, _⟩ := w.unsnoc
    exact hf a (m + 1) hm hmq (w.reverse_of_mem ha)

end LeanCH.BR.BRq2

namespace LeanCH.BR.BRsGen

open BRq2 BRq3 BR45

variable {D : CH.Digraph} {W : Finset ℕ} {q a b : ℕ}

/-- At order at most q+2 and minimum out-degree one, a row with a parent has at most two heads. -/
theorem near_boundary_parent_row_cap (hq : 2 ≤ q) (hf : QFree D W q)
    (hc : W.card ≤ q + 2) (hmin : ∀ x ∈ W, 1 ≤ (outN D W x).card)
    (ha : a ∈ W) (hb : b ∈ W) (hba : D b a = true) :
    (outN D W a).card ≤ 2 := by
  classical
  by_cases hmore : QFree D W (q + 1)
  · have hsize := dt_size (by omega : 1 ≤ q + 1) (ball_q_one _ (by omega))
      hmore hmin ⟨a, ha⟩
    have heq : W.card = (q + 1) * 1 + 1 := by omega
    have hreg := (dt_reg (by omega) (ball_q_one _ (by omega)) hmore hmin heq).1 a ha
    omega
  · unfold QFree at hmore
    push Not at hmore
    obtain ⟨v, m, hm, hmq, w⟩ := hmore
    have hmeq : m = q + 1 := by
      by_contra hn
      exact hf v m hm (by omega) w
    subst m
    obtain ⟨M, hMW, hMc, hminM⟩ := boundary_closed_walk_support hf w
    have hfM := hf.mono_set hMW
    have hreg := dt_reg (by omega : 1 ≤ q) (ball_q_one _ (by omega)) hfM hminM
      (by omega : M.card = q * 1 + 1)
    have hEc : (W \ M).card ≤ 1 := by
      rw [Finset.card_sdiff_of_subset hMW]
      omega
    by_cases haM : a ∈ M
    · have hsub : outN D W a ⊆ outN D M a ∪ (W \ M) := by
        intro x hx
        obtain ⟨hxW, hax⟩ := mem_outN.mp hx
        by_cases hxM : x ∈ M
        · exact Finset.mem_union_left _ (mem_outN.mpr ⟨hxM, hax⟩)
        · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hxW, hxM⟩)
      have := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
      have := hreg.1 a haM
      omega
    · have hsplit : ∀ x ∈ W, x ∈ M ∨ x = a := by
        intro x hx
        by_cases hxM : x ∈ M
        · exact Or.inl hxM
        · exact Or.inr (Finset.card_le_one.mp hEc x (Finset.mem_sdiff.mpr ⟨hx, hxM⟩)
            a (Finset.mem_sdiff.mpr ⟨ha, haM⟩))
      have hbM : b ∈ M := by
        rcases hsplit b hb with h | rfl
        · exact h
        · exact (loopfree hf (by omega) ha hba).elim
      let R := ball (fun x y => D y x) M b (q - 2)
      have hrev : ∀ x ∈ M, 1 ≤ (outN (fun x y => D y x) M x).card := by
        intro x hx
        change 1 ≤ (inN D M x).card
        rw [hreg.2 x hx]
      have hRc : q - 1 ≤ R.card := by
        have := ball_one_growth hfM.reverse hrev hbM (q - 2) (by omega)
        change q - 1 ≤ (ball (fun x y => D y x) M b (q - 2)).card
        omega
      have hsub : outN D W a ⊆ M \ R := by
        intro x hx
        obtain ⟨hxW, hax⟩ := mem_outN.mp hx
        have hxM : x ∈ M := by
          rcases hsplit x hxW with h | rfl
          · exact h
          · exact (loopfree hf (by omega) ha hax).elim
        refine Finset.mem_sdiff.mpr ⟨hxM, ?_⟩
        intro hxR
        obtain ⟨_, k, hk, wk⟩ := mem_ball.mp hxR
        have wxb : Walk D W x b k := (wk.reverse_of_mem hbM).mono hMW
        exact hf a (k + 1 + 1) (by omega) (by omega)
          (.step (hMW hxM) hax (wxb.snoc ha hba))
      have := Finset.card_le_card hsub
      rw [Finset.card_sdiff_of_subset (show R ⊆ M from ball_subset), hMc] at this
      omega

/-- A small acyclic set cannot escape through at most two vertices with these return floors. -/
theorem two_escape_high_return_false {R E : Finset ℕ} {s : ℕ}
    (hs : 6 ≤ s) (hf : QFree D (R ∪ E) (s - 1)) (hdisj : Disjoint R E)
    (hRlo : s - 3 ≤ R.card) (hRhi : R.card ≤ s - 1) (hE : E.card ≤ 2)
    (hminR : ∀ r ∈ R, 1 ≤ (outN D (R ∪ E) r).card)
    (hhigh : ∀ e ∈ E, (∃ r ∈ R, D r e = true) → R.card - 2 ≤ (outN D R e).card) :
    False := by
  classical
  let F := E.filter (fun e => ∃ r ∈ R, D r e = true)
  have hFE : F ⊆ E := Finset.filter_subset _ _
  have hFc : F.card ≤ 2 := (Finset.card_le_card hFE).trans hE
  have hRF : Disjoint R F := hdisj.mono_right hFE
  have hf' := hf.mono_set (Finset.union_subset_union_right hFE)
  have hret : ∀ r ∈ R, 1 ≤ (outN D (R ∪ F) r).card := by
    intro r hr
    apply (hminR r hr).trans
    apply Finset.card_le_card
    intro v hv
    obtain ⟨hvU, hrv⟩ := mem_outN.mp hv
    refine mem_outN.mpr ⟨?_, hrv⟩
    rcases Finset.mem_union.mp hvU with hvR | hvE
    · exact Finset.mem_union_left _ hvR
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hvE, r, hr, hrv⟩)
  have hhighF : ∀ e ∈ F, R.card - 2 ≤ (outN D R e).card := by
    intro e he
    exact hhigh e (Finset.mem_filter.mp he).1 (Finset.mem_filter.mp he).2
  have hmin : ∀ v ∈ R ∪ F, 1 ≤ (outN D (R ∪ F) v).card := by
    intro v hv
    rcases Finset.mem_union.mp hv with hvR | hvF
    · exact hret v hvR
    · have hh : R.card - 2 ≤ (outN D (R ∪ F) v).card := (hhighF v hvF).trans
        (Finset.card_le_card (outN_mono Finset.subset_union_left v))
      omega
  obtain ⟨r, hr, hrs⟩ := exists_sink (hf.mono_set Finset.subset_union_left)
    (Finset.card_pos.mp (by omega : 0 < R.card)) hRhi
  obtain ⟨e, he⟩ := Finset.card_pos.mp (hret r hr)
  obtain ⟨heU, hre⟩ := mem_outN.mp he
  have heF : e ∈ F := by
    rcases Finset.mem_union.mp heU with heR | heF
    · exact (hrs e heR hre).elim
    · exact heF
  have hcard : (R ∪ F).card = R.card + F.card := Finset.card_union_of_disjoint hRF
  have hdeg : R.card - 2 ≤ (outN D (R ∪ F) e).card := (hhighF e heF).trans
    (Finset.card_le_card (outN_mono Finset.subset_union_left e))
  by_cases hsmall : R.card ≤ s - 2
  · have hsize := dt_size (by omega : 1 ≤ s - 1) (ball_q_one _ (by omega))
      hf' hmin ⟨r, Finset.mem_union_left _ hr⟩
    have horder : (R ∪ F).card = (s - 1) * 1 + 1 := by omega
    have heq := (dt_reg (by omega) (ball_q_one _ (by omega)) hf' hmin horder).1 e heU
    omega
  · have hcap := near_boundary_parent_row_cap (by omega : 2 ≤ s - 1) hf'
      (by omega) hmin heU (Finset.mem_union_left _ hr) hre
    omega

end LeanCH.BR.BRsGen
