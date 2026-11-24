import LeanCH.BR.BRsGen2Twin
import LeanCH.BR.BRq4Reach

/-!
# General `s` and excess `e`: Lemma 14 and Corollary 15 (1)–(3) (Lean 4.35.0)

Paper: `BallQ4b_attempt_subagent.md` §2 (Lemma 14, Corollary 15), `BallQ5_attempt_subagent.md` §3 (Q4) and §6
(Proposition T, hypothesis (Good_e)). The `s = 4`, `e = 2` versions are `BRq4Reach.lean`. No existing file is changed.

Level `k = j + 3`. Both the out-degree `s` and the excess `e` are parameters.

* `GSet D W u j s e` (the paper's `(S_k)` at excess `e`): `BallSmall(k,s)`, `D` `(k+2)`-free and out-`s`,
  `b_{k+1} = sk+2+e`, `sk+1 ≤ b_k ≤ sk+1+e`. Hence `|V♮| = sk+1+e` and `1 ≤ |K| ≤ e+1` (`GSet.hV`, `GSet.hK`).
* `GoodT p z`: `M_z ∖ {p} ⊆ B_{k-1}` (the part of (R2)/(R0) that Lemma 14 uses). `AllGood`: every π-target of every
  `p ∈ P` that does not head `K` is `GoodT`. This is the paper's (Good_e) without the depth clause.
* `reach_g` (**Lemma 14 (c), (d)**, any `s`, any `e`): from `GoodT p z` alone.
* `C15 D W u j s e`: `GSet` + `AllGood` + `|K| < s` + the `P_0` bound `n_k ≤ k+2 ∨ n_k < 2(s-|K|)+1`.
* `target_out_g`, `no_inP_g`, `no_target_P_g`, `disj_target_g` (**Corollary 15 (1)–(3)**, any `s`, any `e`).
  The `P_0` step uses `exists_sink` (`n_k ≤ k+2`) or the tournament count `digon_bound` (`n_k < 2(s-|K|)+1`), since
  `D[P_0]` has min out `≥ s - |K|`.
-/

set_option linter.style.longLine false

namespace LeanCH.BR.BRsGen

open LeanCH.BR.BRq2 LeanCH.BR.BRq3 LeanCH.BR.BRq4

/-- The setting `(S_k)` at out-degree `s` and excess `e`, level `k = j + 3`. -/
structure GSet (D : CH.Digraph) (W : Finset ℕ) (u j s e : ℕ) : Prop where
  hS : BallSmall (j + 3) s
  hfree : QFree D W (j + 5)
  hout : OutEq s D W
  hu : u ∈ W
  hb : (ball D W u (j + 4)).card = s * (j + 3) + 2 + e
  hbk : s * (j + 3) + 1 ≤ (ball D W u (j + 3)).card
  hb3 : (ball D W u (j + 3)).card ≤ s * (j + 3) + 1 + e

/-- `M_z ∖ {p} ⊆ B_{k-1}`. -/
def GoodT (D : CH.Digraph) (W : Finset ℕ) (u j p z : ℕ) : Prop :=
  ∀ x ∈ VV D W u j, x ∉ BB D W u j z → x ≠ p → x ∈ ball D W u (j + 2)

/-- (Good_e) without the depth clause: every π-target of a `P`-vertex that does not head `K` is `GoodT`. -/
def AllGood (D : CH.Digraph) (W : Finset ℕ) (u j : ℕ) : Prop :=
  ∀ p ∈ PP D W u j, ∀ z ∈ W, D p z = true → z ∉ KK D W u j → (¬ ∃ c ∈ KK D W u j, D z c = true) →
    GoodT D W u j p z

variable {D : CH.Digraph} {W : Finset ℕ} {u j s e : ℕ}

namespace GSet

variable (H : GSet D W u j s e)
include H

theorem hV : (VV D W u j).card = s * (j + 3) + 1 + e := by
  rw [Finset.card_erase_of_mem (self_mem_ball H.hu), H.hb]; omega

theorem hK : 1 ≤ (KK D W u j).card ∧ (KK D W u j).card ≤ e + 1 := by
  have e' := Finset.card_sdiff_add_card_eq_card (ball_mono_radius (D := D) (W := W) (u := u) (by omega : j + 3 ≤ j + 4))
  have := H.hb; have := H.hbk; have := H.hb3
  simp only [KK]
  omega

end GSet

/-- **Lemma 14 (c), (d)**, any `s` and `e`: for a π-target `z ∉ P` of `p` with `M_z ∖ {p} ⊆ B_{k-1}`, no vertex of
`N_k ∪ K` points to `p`, and `p` is the only in-neighbour of `z` in `N_k ∪ K`. -/
theorem reach_g (hfree : QFree D W (j + 5)) (hu : u ∈ W) {p z : ℕ} (hp : p ∈ ball D W u (j + 3))
    (hp1 : p ∉ ball D W u (j + 2)) (hpz : D p z = true) (hzW : z ∈ W) (hzK : z ∉ KK D W u j)
    (hM : GoodT D W u j p z) :
    (∀ x ∈ ball D W u (j + 4), x ∉ ball D W u (j + 2) → ¬ D x p = true) ∧
      (∀ x ∈ ball D W u (j + 4), x ∉ ball D W u (j + 2) → x ≠ p → ¬ D x z = true) := by
  -- (b) and Claim 0
  have hreach : ∀ x ∈ ball D W u (j + 4), x ∉ ball D W u (j + 2) → x ≠ p → ∃ m ≤ j + 3, Walk D W z x m := by
    intro x hx hx2 hxp
    have hxV : x ∈ VV D W u j := memV_of hu hx hx2
    have hxB : x ∈ BB D W u j z := by by_contra h; exact hx2 (hM x hxV h hxp)
    obtain ⟨_, m, hm, w⟩ := mem_ball.mp hxB
    rcases fold_walk hzK w with h | ⟨c, hc, m1, m2, hsum, h1, w1, w2⟩
    · exact ⟨m, hm, h⟩
    · exact absurd (mem_ball_of_walk w2 (by omega) (VV_sub hxV)) hx2
  refine ⟨fun x hx hx2 hxp => ?_, fun x hx hx2 hxp' hxz => ?_⟩
  · -- (c)
    have hxp' : x ≠ p := by rintro rfl; exact loopfree hfree (by omega) (ball_subset hp) hxp
    obtain ⟨m, hm, w⟩ := hreach x hx hx2 hxp'
    exact hfree z (m + 1 + 1) (by omega) (by omega) ((w.snoc (ball_subset hp) hxp).snoc hzW hpz)
  · -- (d)
    obtain ⟨m, hm, w⟩ := hreach x hx hx2 hxp'
    exact hfree z (m + 1) (by omega) (by omega) (w.snoc hzW hxz)

/-- The hypotheses of Corollary 15 at out-degree `s` and excess `e`. -/
structure C15 (D : CH.Digraph) (W : Finset ℕ) (u j s e : ℕ) : Prop where
  set : GSet D W u j s e
  good : AllGood D W u j
  sK : (KK D W u j).card < s
  nk : (ball D W u (j + 3) \ ball D W u (j + 2)).card ≤ j + 5 ∨
    (ball D W u (j + 3) \ ball D W u (j + 2)).card < 2 * (s - (KK D W u j).card) + 1

/-- **Corollary 15, the `P_0` step**, any `s` and `e`. Every `p ∈ P` has a π-target outside `P`. -/
theorem target_out_g (C : C15 D W u j s e) {p : ℕ} (hp : p ∈ PP D W u j) :
    ∃ z ∈ W, D p z = true ∧ z ∉ KK D W u j ∧ ¬ ∃ c ∈ KK D W u j, D z c = true := by
  classical
  have H := C.set
  by_contra hcon
  set P0 := (PP D W u j).filter (fun t => ∀ z ∈ outN D W t, z ∉ KK D W u j → ∃ c ∈ KK D W u j, D z c = true)
    with hP0
  have hmem0 : ∀ t ∈ PP D W u j, (∀ z ∈ W, D t z = true → z ∉ KK D W u j → ∃ c ∈ KK D W u j, D z c = true) →
      t ∈ P0 := fun t ht h => Finset.mem_filter.mpr ⟨ht, fun z hz hzK => h z (mem_outN.mp hz).1 (mem_outN.mp hz).2 hzK⟩
  have hpP0 : p ∈ P0 := hmem0 p hp (fun z hzW hpz hzK => by
    by_contra h; exact hcon ⟨z, hzW, hpz, hzK, h⟩)
  have hP0W : P0 ⊆ W := (Finset.filter_subset _ _).trans PP_W
  -- every out-neighbour of `t ∈ P_0` outside `K` lies in `P_0`
  have hstep : ∀ t ∈ P0, outN D W t \ KK D W u j ⊆ outN D P0 t := by
    intro t ht z hz
    obtain ⟨hz1, hzK⟩ := Finset.mem_sdiff.mp hz
    obtain ⟨hzW, htz⟩ := mem_outN.mp hz1
    obtain ⟨htP, hall⟩ := Finset.mem_filter.mp ht
    obtain ⟨ht3, ht2, -⟩ := mem_PP.mp htP
    have hzc := hall z hz1 hzK
    have hzP := memPP_of (toV H.hfree H.hu ht3 htz hzW) hzK hzc
    refine mem_outN.mpr ⟨hmem0 z hzP (fun z' hz'W hzz' hz'K => ?_), htz⟩
    by_contra h
    obtain ⟨hz3, hz2, -⟩ := mem_PP.mp hzP
    exact (reach_g H.hfree H.hu hz3 hz2 hzz' hz'W hz'K (C.good z hzP z' hz'W hzz' hz'K h)).1 t
      (ball_mono_radius (by omega) ht3) ht2 htz
  have hmin : ∀ t ∈ P0, s - (KK D W u j).card ≤ (outN D P0 t).card := by
    intro t ht
    have h1 := Finset.le_card_sdiff (KK D W u j) (outN D W t)
    rw [H.hout t (hP0W ht)] at h1
    have := Finset.card_le_card (hstep t ht)
    omega
  have hcard : P0.card ≤ (ball D W u (j + 3) \ ball D W u (j + 2)).card :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans (Finset.card_le_card PP_sub)
  have hsK := C.sK
  rcases C.nk with hnk | hnk
  · obtain ⟨t, ht, hsink⟩ := exists_sink ((H.hfree).mono_set hP0W) ⟨p, hpP0⟩ (hcard.trans hnk)
    obtain ⟨z, hz⟩ : (outN D P0 t).Nonempty := by
      rw [← Finset.card_pos]; have := hmin t ht; omega
    exact hsink z (mem_outN.mp hz).1 (mem_outN.mp hz).2
  · have := digon_bound ((H.hfree.mono_bound (by omega)).mono_set hP0W) hmin ⟨p, hpP0⟩
    omega

/-- **Corollary 15 (2)**, any `s` and `e`. No vertex of `N_k ∪ K` points into `P`. -/
theorem no_inP_g (C : C15 D W u j s e) {p : ℕ} (hp : p ∈ PP D W u j) :
    ∀ x ∈ ball D W u (j + 4), x ∉ ball D W u (j + 2) → ¬ D x p = true := by
  obtain ⟨z, hzW, hpz, hzK, hzP⟩ := target_out_g C hp
  obtain ⟨hp3, hp2, -⟩ := mem_PP.mp hp
  exact (reach_g C.set.hfree C.set.hu hp3 hp2 hpz hzW hzK (C.good p hp z hzW hpz hzK hzP)).1

/-- **Corollary 15 (1)**, any `s` and `e`. No π-target of a `P`-vertex lies in `P`. -/
theorem no_target_P_g (C : C15 D W u j s e) {p z : ℕ} (hp : p ∈ PP D W u j) (hpz : D p z = true)
    (hzW : z ∈ W) (hzK : z ∉ KK D W u j) : ¬ ∃ c ∈ KK D W u j, D z c = true := by
  intro h
  obtain ⟨hp3, hp2, -⟩ := mem_PP.mp hp
  have hzP := memPP_of (toV C.set.hfree C.set.hu hp3 hpz hzW) hzK h
  exact no_inP_g C hzP p (ball_mono_radius (by omega) hp3) hp2 hpz

/-- **Corollary 15 (3)**, any `s` and `e`. Distinct `P`-vertices have disjoint π-targets. -/
theorem disj_target_g (C : C15 D W u j s e) {p p' z : ℕ} (hp : p ∈ PP D W u j) (hp' : p' ∈ PP D W u j)
    (hzW : z ∈ W) (hzK : z ∉ KK D W u j) (hpz : D p z = true) (hp'z : D p' z = true) : p = p' := by
  by_contra hne
  obtain ⟨hp3, hp2, -⟩ := mem_PP.mp hp
  obtain ⟨hp'3, hp'2, -⟩ := mem_PP.mp hp'
  have hzP := no_target_P_g C hp hpz hzW hzK
  exact (reach_g C.set.hfree C.set.hu hp3 hp2 hpz hzW hzK (C.good p hp z hzW hpz hzK hzP)).2 p'
    (ball_mono_radius (by omega) hp'3) hp'2 (Ne.symm hne) hp'z

end LeanCH.BR.BRsGen
