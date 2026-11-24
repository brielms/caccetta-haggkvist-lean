import LeanCH.BR.BRsubSat

/-!
# Lemma M: a saturated tight `C_s`-module is a full module (Lean 4.35.0)

Paper: `checkpoints/boundary_20261111/BRsubdiag_attempt_subagent.md` §1 (Lemma M (a), (b)).

Setting: `E` is `q`-free and saturated on `V` (`Sat q E V`), `q + 1 = s`, `q ≥ 2`. `M ⊆ V` induces a digraph in which
every vertex has exactly one head and one tail (`D[M] = C_s` when `|M| = s`), every `x ∈ M` heads every vertex of
`Y ⊆ V`, `|Y| = s - 1`, and `out(x) = s`. Put `B := B_{q-2}(Y) = ⋃_{y ∈ Y} B_{q-2}(y)` and `W_M := V ∖ (M ∪ B)`.

* `lemmaM_a` (**Lemma M(a)**): `M ∩ B = ∅`, and no vertex of `B` heads a vertex of `M`.
* `out_sub`: `O(x) ⊆ M ∪ Y` for `x ∈ M`.
* `ball_sub_MY`: `B_k(x) ⊆ M ∪ B_{k-1}(Y)` for `x ∈ M` (`k ≥ 1`).
* `lemmaM` (**Lemma M(b)**): for every `x ∈ M`, `I(x) = I_M(x) ∪ W_M`, where `I_M(x) = {x⁻}` has one element and
  `W_M` does not depend on `x`; `lemmaM_card`: `in(x) = 1 + |W_M|`.

(The size `|M| = s` is not needed for (a), (b): only one head and one tail inside `M`, `|Y| = s - 1`, `out = s`.)
-/

set_option linter.style.longLine false

namespace LeanCH.BR.BRsub

open LeanCH.BR.BRq2 LeanCH.BR.BRq3 LeanCH.BR.BR45 CH Compose.Boundary Compose.FloorSix

variable {E : CH.Digraph} {V : Finset ℕ}

/-- `B_k(Y) = ⋃_{y ∈ Y} B_k(y)`. -/
noncomputable def ballSet (E : CH.Digraph) (V : Finset ℕ) (Y : Finset ℕ) (k : ℕ) : Finset ℕ :=
  open Classical in Y.biUnion (fun y => ball E V y k)

theorem mem_ballSet {Y : Finset ℕ} {k v : ℕ} : v ∈ ballSet E V Y k ↔ ∃ y ∈ Y, v ∈ ball E V y k := by
  classical
  unfold ballSet
  exact Finset.mem_biUnion

/-- The common in-set `W_M = V ∖ (M ∪ B_{q-2}(Y))`. -/
noncomputable def WM (E : CH.Digraph) (V M Y : Finset ℕ) (q : ℕ) : Finset ℕ :=
  open Classical in V \ (M ∪ ballSet E V Y (q - 2))

theorem mem_WM {M Y : Finset ℕ} {q v : ℕ} :
    v ∈ WM E V M Y q ↔ v ∈ V ∧ v ∉ M ∧ v ∉ ballSet E V Y (q - 2) := by
  classical
  unfold WM
  rw [Finset.mem_sdiff, Finset.mem_union]
  tauto

/-- **Lemma M(a).** `M ∩ B_{q-2}(Y) = ∅`, and no vertex of `B_{q-2}(Y)` heads `M`. -/
theorem lemmaM_a {q : ℕ} (hq : 2 ≤ q) (hfree : QFree E V q) {M Y : Finset ℕ} (hMV : M ⊆ V) (hYV : Y ⊆ V)
    (hhead : ∀ x ∈ M, ∀ y ∈ Y, E x y = true) :
    Disjoint M (ballSet E V Y (q - 2)) ∧ ∀ b ∈ ballSet E V Y (q - 2), ∀ x ∈ M, ¬ E b x = true := by
  refine ⟨Finset.disjoint_left.mpr (fun x hx hb => ?_), fun b hb x hx hbx => ?_⟩
  · obtain ⟨y, hy, hxy⟩ := mem_ballSet.mp hb
    exact no_back_arc hfree (hYV hy) hxy (by omega) (hhead x hx y hy)
  · obtain ⟨y, hy, hby⟩ := mem_ballSet.mp hb
    have h := ball_trans (ball_of_adj (hYV hy) (hhead x hx y hy)) hby
    exact no_back_arc hfree (hMV hx) h (by omega) hbx

/-- `O(x) ⊆ M ∪ Y` for `x ∈ M`: one head in `M`, all `s - 1` vertices of `Y`, and `out(x) = s`. -/
theorem out_sub {q s : ℕ} (hq : q + 1 = s) (hq2 : 2 ≤ q) (hfree : QFree E V q) {M Y : Finset ℕ}
    (hMV : M ⊆ V) (hYV : Y ⊆ V) (hY : Y.card = s - 1)
    (hhead : ∀ x ∈ M, ∀ y ∈ Y, E x y = true) (hout : ∀ x ∈ M, (outN E V x).card = s)
    (hcyc : ∀ x ∈ M, (outN E M x).card = 1) {x z : ℕ} (hx : x ∈ M) (hz : z ∈ V) (hxz : E x z = true) :
    z ∈ M ∨ z ∈ Y := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨hzM, hzY⟩ := hcon
  have hdMY : Disjoint (outN E M x) Y := by
    rw [Finset.disjoint_left]
    intro y hyM hyY
    have hyM' := (mem_outN.mp hyM).1
    exact loopfree hfree (by omega) (hMV hyM') (hhead y hyM' y hyY)
  have hznot : z ∉ outN E M x ∪ Y := by
    rw [Finset.mem_union]
    rintro (h | h)
    · exact hzM (mem_outN.mp h).1
    · exact hzY h
  have hsub : insert z (outN E M x ∪ Y) ⊆ outN E V x := by
    intro w hw
    rcases Finset.mem_insert.mp hw with h | h
    · rw [h]
      exact mem_outN.mpr ⟨hz, hxz⟩
    · rcases Finset.mem_union.mp h with h | h
      · exact outN_mono hMV x h
      · exact mem_outN.mpr ⟨hYV h, hhead x hx w h⟩
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem hznot, Finset.card_union_of_disjoint hdMY, hcyc x hx, hY, hout x hx] at h1
  omega

/-- `B_k(x) ⊆ M ∪ B_{k-1}(Y)` for `x ∈ M`, given `O(m) ⊆ M ∪ Y` on `M`. -/
theorem ball_sub_MY {M Y : Finset ℕ} (hMV : M ⊆ V)
    (hO : ∀ m ∈ M, ∀ z ∈ V, E m z = true → z ∈ M ∨ z ∈ Y) {x : ℕ} (hx : x ∈ M) :
    ∀ k v, v ∈ ball E V x k → v ∈ M ∨ ∃ y ∈ Y, ∃ j, j + 1 ≤ k ∧ v ∈ ball E V y j := by
  intro k
  induction k with
  | zero =>
    intro v hv
    left
    rw [eq_of_mem_ball_zero hv]
    exact hx
  | succ k ih =>
    intro v hv
    by_cases hvk : v ∈ ball E V x k
    · rcases ih v hvk with h | ⟨y, hy, j, hj, hvy⟩
      · exact Or.inl h
      · exact Or.inr ⟨y, hy, j, by omega, hvy⟩
    · obtain ⟨p, hp, hpv⟩ := ball_succ_pred (hMV hx) hv hvk
      have hvV : v ∈ V := ball_subset hv
      rcases ih p hp with h | ⟨y, hy, j, hj, hpy⟩
      · rcases hO p h v hvV hpv with h' | h'
        · exact Or.inl h'
        · exact Or.inr ⟨v, h', 0, by omega, self_mem_ball hvV⟩
      · exact Or.inr ⟨y, hy, j + 1, by omega, ball_step hpy hvV hpv⟩

/-- **Lemma M(b).** For every `x ∈ M`, `I(x) = I_M(x) ∪ W_M` with `W_M = V ∖ (M ∪ B_{q-2}(Y))` independent of `x`. -/
theorem lemmaM {q s : ℕ} (hq : q + 1 = s) (hq2 : 2 ≤ q) (hfree : QFree E V q) (hsat : Sat q E V)
    {M Y : Finset ℕ} (hMV : M ⊆ V) (hYV : Y ⊆ V) (hY : Y.card = s - 1)
    (hhead : ∀ x ∈ M, ∀ y ∈ Y, E x y = true) (hout : ∀ x ∈ M, (outN E V x).card = s)
    (hcyc : ∀ x ∈ M, (outN E M x).card = 1) {x : ℕ} (hx : x ∈ M) :
    inN E V x = inN E M x ∪ WM E V M Y q := by
  classical
  have hO : ∀ m ∈ M, ∀ z ∈ V, E m z = true → z ∈ M ∨ z ∈ Y :=
    fun m hm z hz hmz => out_sub hq hq2 hfree hMV hYV hY hhead hout hcyc hm hz hmz
  have hxV := hMV hx
  ext p
  rw [Finset.mem_union, mem_WM, mem_inN, mem_inN]
  constructor
  · rintro ⟨hpV, hpx⟩
    by_cases hpM : p ∈ M
    · exact Or.inl ⟨hpM, hpx⟩
    · exact Or.inr ⟨hpV, hpM, fun hb => (lemmaM_a hq2 hfree hMV hYV hhead).2 p hb x hx hpx⟩
  · rintro (⟨hpM, hpx⟩ | ⟨hpV, hpM, hpB⟩)
    · exact ⟨hMV hpM, hpx⟩
    · refine ⟨hpV, by_contra (fun hpx => ?_)⟩
      have hb := hsat x hxV p hpV hpx
      rcases ball_sub_MY hMV hO hx (q - 1) p hb with h | ⟨y, hy, j, hj, hpy⟩
      · exact hpM h
      · exact hpB (mem_ballSet.mpr ⟨y, hy, ball_mono_radius (by omega) hpy⟩)

/-- **Lemma M(b), counting form.** `in(x) = 1 + |W_M|` for every `x ∈ M` (given one tail inside `M`). -/
theorem lemmaM_card {q s : ℕ} (hq : q + 1 = s) (hq2 : 2 ≤ q) (hfree : QFree E V q) (hsat : Sat q E V)
    {M Y : Finset ℕ} (hMV : M ⊆ V) (hYV : Y ⊆ V) (hY : Y.card = s - 1)
    (hhead : ∀ x ∈ M, ∀ y ∈ Y, E x y = true) (hout : ∀ x ∈ M, (outN E V x).card = s)
    (hcyc : ∀ x ∈ M, (outN E M x).card = 1 ∧ (inN E M x).card = 1) {x : ℕ} (hx : x ∈ M) :
    (inN E V x).card = 1 + (WM E V M Y q).card := by
  classical
  rw [lemmaM hq hq2 hfree hsat hMV hYV hY hhead hout (fun m hm => (hcyc m hm).1) hx]
  have hd : Disjoint (inN E M x) (WM E V M Y q) := by
    rw [Finset.disjoint_left]
    intro p hp hw
    exact (mem_WM.mp hw).2.1 (mem_inN.mp hp).1
  rw [Finset.card_union_of_disjoint hd, (hcyc x hx).2]

end LeanCH.BR.BRsub
