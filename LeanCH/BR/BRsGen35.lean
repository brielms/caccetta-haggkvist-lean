import LeanCH.BR.BRsGen35Reg
import LeanCH.BR.BRq4Fold
import LeanCH.BR.BRsGenBBall

/-!
# BBall(3,5): Lemma B1 (Lean 4.35.0)

Paper: `checkpoints/boundary_20261111/BallQ5b_attempt_subagent.md` §2 (Lemma B1, steps 1–8). No existing file is
changed.

**Lemma B1.** A `3`-free out-`5` digraph on at most `16` vertices has `|B_2(y)| ≥ 11` at every vertex.

Notation at a vertex `y` with `|B_2(y)| ≤ 10`: `X = O(y)`, `Y = N_2(y)`, `R = W ∖ B_2(y)`, `e(X) = Σ_{x∈X} |O(x) ∩ X|`.

* Step 0 (`card_ge_16`, `in_eq_five`): `|W| = 16` and every in-degree is `5` (`BR35.br_five`).
* Step 1: `O(x) ⊆ X ∪ Y`; `D[X]` has min out `≥ 1`; `|Y| = 4` (`ch2_set` at `q = 3`), so `|R| = 6`.
* Step 2 (`five_shape_W`): `e(X) ≤ 8`, and at `e(X) = 8` a source `e` with every other `c ∈ X` heading all of `Y`.
* Step 3: `Y ↛ X`. A `z₀ → v` caps the `X`-parents of `z₀` at `2`; then `e(X,Y) = 25 - e(X) ≤ 17` forces `e(X) = 8`,
  and the shape gives `z₀` four `X`-parents.
* Step 4 (in-degree 5): `e(R,X) = 20 - e(X)` and `e(Y) + e(R,Y) = e(X) - 5`.
* Step 5: a sink of `D[Y]` sends all five arcs into `R' = O(Y) ∩ R`, so `|R'| ≥ 5`.
* Step 6: `r ∈ R'` with parent `z ∈ Y` has `|O(r) ∩ X| + |I(z) ∩ X| ≤ 5` (no triangle `r → x → z → r`).
* Steps 7–8: the count. If every `z` has `≥ 4` `X`-parents, `Σ_{R'} |O(r) ∩ X| ≤ |R'|` is too small. Otherwise
  `e(X) = 7`, one `z*` has `3` `X`-parents and the others `5`; `D[Y]` has `≥ 2` sinks, so a sink `z' ≠ z*`; if
  `|R'| = 6` the cap `2` per row is too small, if `|R'| = 5` the sink `z'` heads all of `R'` and kills every row.

* `ball_two_ge` (the lemma), `bball35 : BallSmall 3 5`, `bball35_boundary : BBall 3 5`.
-/

set_option linter.style.longLine false

namespace LeanCH.BR.BRsGen35

open LeanCH.BR.BRq2 LeanCH.BR.BRq3 LeanCH.BR.BRq4 LeanCH.BR.BRsGen
open LeanCH.BR.BR35 (oc ic oc_le ic_le oc_union ic_union oc_mono ic_mono ic_insert all_of_oc ic_full swap
  sum_le_card_mul card_mul_le_sum sum_add_one_le oc_le_of_sub)

variable {D : CH.Digraph} {W : Finset ℕ}

/-- **Lemma B1.** -/
theorem ball_two_ge (hfree : QFree D W 3) (hout : OutEq 5 D W) (hcard : W.card ≤ 16) {y : ℕ} (hy : y ∈ W) :
    11 ≤ (ball D W y 2).card := by
  classical
  -- Step 0
  have hW16 : W.card = 16 := le_antisymm hcard (card_ge_16 hfree hout ⟨y, hy⟩)
  have hin := in_eq_five hfree hout hW16
  have hoc : ∀ v ∈ W, oc D W v = 5 := fun v hv => hout v hv
  have tri : ∀ {a b c : ℕ}, a ∈ W → b ∈ W → c ∈ W → D a b = true → D b c = true → D c a = true → False :=
    fun {a b c} ha hb hc h1 h2 h3 => hfree a 3 (by omega) le_rfl (.step hb h1 (.step hc h2 (.step ha h3 (.refl a))))
  set X := outN D W y with hXdef
  set Y := ball D W y 2 \ ball D W y 1 with hYdef
  set R := W \ ball D W y 2 with hRdef
  have hX5 : X.card = 5 := hout y hy
  have hyX : y ∉ X := fun h => loopfree hfree (by omega) hy (mem_outN.mp h).2
  have hb1eq : ball D W y 1 = insert y X := by ext v; rw [mem_ball_one hy, Finset.mem_insert]
  have hb1 : (ball D W y 1).card = 6 := by rw [hb1eq, Finset.card_insert_of_notMem hyX, hX5]
  have hsub12 : ball D W y 1 ⊆ ball D W y 2 := ball_mono_radius (by omega)
  have hYc : Y.card + (ball D W y 1).card = (ball D W y 2).card := Finset.card_sdiff_add_card_eq_card hsub12
  have hb2W := Finset.card_le_card (ball_subset (D := D) (W := W) (u := y) (k := 2))
  have hRc : R.card = W.card - (ball D W y 2).card := Finset.card_sdiff_of_subset ball_subset
  have hXW : X ⊆ W := outN_subset
  have hYW : Y ⊆ W := fun x hx => ball_subset (Finset.mem_sdiff.mp hx).1
  have hRW : R ⊆ W := Finset.sdiff_subset
  have hdXY : Disjoint X Y := Finset.disjoint_left.mpr fun _ hx hxY =>
    (Finset.mem_sdiff.mp hxY).2 (mem_ball_one_of_out hx)
  have hdXR : Disjoint X R := Finset.disjoint_left.mpr fun _ hx hxR =>
    (Finset.mem_sdiff.mp hxR).2 (hsub12 (mem_ball_one_of_out hx))
  have hdYR : Disjoint Y R := Finset.disjoint_left.mpr fun _ hx hxR =>
    (Finset.mem_sdiff.mp hxR).2 (Finset.mem_sdiff.mp hx).1
  have hyY : y ∉ Y := fun h => (Finset.mem_sdiff.mp h).2 (self_mem_ball hy)
  have hyR : y ∉ R := fun h => (Finset.mem_sdiff.mp h).2 (self_mem_ball hy)
  have hyXYR : y ∉ X ∪ (Y ∪ R) := by
    simp only [Finset.mem_union, not_or]
    exact ⟨hyX, hyY, hyR⟩
  have hdXYR : Disjoint X (Y ∪ R) := Finset.disjoint_union_right.mpr ⟨hdXY, hdXR⟩
  have hsplit : ∀ b ∈ W, b = y ∨ b ∈ X ∨ b ∈ Y ∨ b ∈ R := by
    intro b hb
    by_cases h2 : b ∈ ball D W y 2
    · by_cases h1 : b ∈ ball D W y 1
      · rcases (mem_ball_one hy).mp h1 with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl (Finset.mem_sdiff.mpr ⟨h2, h1⟩)))
    · exact Or.inr (Or.inr (Or.inr (Finset.mem_sdiff.mpr ⟨hb, h2⟩)))
  have hWeq : W = insert y (X ∪ (Y ∪ R)) := by
    ext b
    simp only [Finset.mem_insert, Finset.mem_union]
    constructor
    · intro hb; exact hsplit b hb
    · rintro (rfl | h | h | h)
      · exact hy
      · exact hXW h
      · exact hYW h
      · exact hRW h
  have icW : ∀ v, ic D W v = (if D y v = true then 1 else 0) + (ic D X v + (ic D Y v + ic D R v)) := by
    intro v
    rw [hWeq, ic_insert hyXYR, ic_union hdXYR, ic_union hdYR]
  -- every vertex of `Y` has a parent in `X`
  have hpar : ∀ z ∈ Y, ∃ x ∈ X, D x z = true := by
    intro z hz
    obtain ⟨hz2, hz1⟩ := Finset.mem_sdiff.mp hz
    obtain ⟨p, hp, hpz⟩ := ball_succ_pred (k := 1) hy hz2 hz1
    rcases (mem_ball_one hy).mp hp with rfl | hpX
    · exact absurd (ball_of_adj (hYW hz) hpz) hz1
    · exact ⟨p, hpX, hpz⟩
  have hYy : ∀ z ∈ Y, ¬ D z y = true := by
    intro z hz hzy
    obtain ⟨x, hx, hxz⟩ := hpar z hz
    exact tri hy (hXW hx) (hYW hz) (mem_outN.mp hx).2 hxz hzy
  -- Step 1
  have hXout : ∀ x ∈ X, ∀ b ∈ W, D x b = true → b ∈ X ∨ b ∈ Y := by
    intro x hx b hb hxb
    rcases hsplit b hb with rfl | h | h | h
    · exact absurd hxb (fun h' => digonfree hfree (by omega) hb (hXW hx) (mem_outN.mp hx).2 h')
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd (ball_step (k := 1) (mem_ball_one_of_out hx) hb hxb) (Finset.mem_sdiff.mp h).2
  have hrowX : ∀ x ∈ X, oc D X x + oc D Y x = 5 := by
    intro x hx
    have h1 : oc D W x ≤ oc D X x + oc D Y x := out_split (hXout x hx)
    have h2 := oc_mono (G := D) (Finset.union_subset hXW hYW) x
    rw [oc_union hdXY] at h2
    have := hoc x (hXW hx)
    omega
  by_contra hlt
  have hY4 : Y.card ≤ 4 := by omega
  have hi1 : ∀ x ∈ X, 1 ≤ oc D X x := fun x hx => by
    have := hrowX x hx; have := oc_le (G := D) Y x; omega
  have hY4' : Y.card = 4 := by
    by_contra hne
    have hmin : ∀ x ∈ X, 2 ≤ (outN D X x).card := fun x hx => by
      have := hrowX x hx; have := oc_le (G := D) Y x
      change 2 ≤ oc D X x; omega
    have := ch2_set (q := 3) (by omega) (hfree.mono_set hXW) hmin (Finset.card_pos.mp (by omega))
    omega
  have hR6 : R.card = 6 := by omega
  -- Step 2
  obtain ⟨hle8, hshape⟩ := five_shape_W hfree hXW hX5 hi1
  have hfull8 : 8 ≤ ∑ x ∈ X, oc D X x → ∀ z ∈ Y, 4 ≤ ic D X z := by
    intro h8 z hz
    obtain ⟨e, he, hc⟩ := hshape h8
    have hall : ∀ c ∈ X.erase e, D c z = true := by
      intro c hc'
      obtain ⟨hce, hcX⟩ := Finset.mem_erase.mp hc'
      have h1 := (hc c hcX hce).2
      have := hrowX c hcX
      exact all_of_oc (G := D) (A := Y) (w := c) (by omega) z hz
    have h1 := ic_full (G := D) hall
    have h2 := ic_mono (G := D) (Finset.erase_subset e X) z
    rw [Finset.card_erase_of_mem he, hX5] at h1
    omega
  have hXrow : ∑ x ∈ X, oc D X x + ∑ x ∈ X, oc D Y x = 25 := by
    have h : ∑ x ∈ X, (oc D X x + oc D Y x) = ∑ _x ∈ X, 5 := Finset.sum_congr rfl hrowX
    rw [Finset.sum_add_distrib, Finset.sum_const, hX5, smul_eq_mul] at h
    omega
  have hXY : ∑ x ∈ X, oc D Y x = ∑ z ∈ Y, ic D X z := swap D X Y
  -- Step 3: `Y ↛ X`
  have hYX : ∀ z ∈ Y, ∀ v ∈ X, ¬ D z v = true := by
    intro z0 hz0 v hv hzv
    have hOv : outN D W v ⊆ X ∪ Y := fun b hb =>
      Finset.mem_union.mpr (hXout v hv b (mem_outN.mp hb).1 (mem_outN.mp hb).2)
    have hvO : v ∉ outN D W v := fun h => loopfree hfree (by omega) (hXW hv) (mem_outN.mp h).2
    have hz0O : z0 ∉ outN D W v := fun h =>
      digonfree hfree (by omega) (hXW hv) (hYW hz0) (mem_outN.mp h).2 hzv
    have hsubP : X.filter (fun a => D a z0 = true) ⊆ (((X ∪ Y) \ outN D W v).erase v).erase z0 := by
      intro a ha
      obtain ⟨haX, haz⟩ := Finset.mem_filter.mp ha
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_erase.mpr ⟨?_, Finset.mem_sdiff.mpr ⟨Finset.mem_union_left _ haX, ?_⟩⟩⟩
      · rintro rfl; exact loopfree hfree (by omega) (hYW hz0) haz
      · rintro rfl; exact digonfree hfree (by omega) (hXW haX) (hYW hz0) haz hzv
      · intro h; exact tri (hXW hv) (hXW haX) (hYW hz0) (mem_outN.mp h).2 haz hzv
    have hvmem : v ∈ (X ∪ Y) \ outN D W v := Finset.mem_sdiff.mpr ⟨Finset.mem_union_left _ hv, hvO⟩
    have hz0mem : z0 ∈ ((X ∪ Y) \ outN D W v).erase v :=
      Finset.mem_erase.mpr ⟨fun h => Finset.disjoint_left.mp hdXY (show z0 ∈ X from h ▸ hv) hz0,
        Finset.mem_sdiff.mpr ⟨Finset.mem_union_right _ hz0, hz0O⟩⟩
    have e1 := Finset.card_erase_of_mem hz0mem
    have e2 := Finset.card_erase_of_mem hvmem
    have e3 := Finset.card_sdiff_of_subset hOv
    have e4 := Finset.card_union_of_disjoint hdXY
    have e5 : (outN D W v).card = 5 := hout v (hXW hv)
    have hz0le : ic D X z0 ≤ 2 := by
      have := Finset.card_le_card hsubP
      change (X.filter (fun a => D a z0 = true)).card ≤ 2
      omega
    have hsum : ∑ z ∈ Y, ic D X z ≤ 17 := by
      have hs : ic D X z0 + ∑ z ∈ Y.erase z0, ic D X z = ∑ z ∈ Y, ic D X z :=
        Finset.add_sum_erase Y (fun z => ic D X z) hz0
      have hr : ∑ z ∈ Y.erase z0, ic D X z ≤ (Y.erase z0).card * 5 :=
        sum_le_card_mul (fun z _ => by have := ic_le (G := D) X z; omega)
      rw [Finset.card_erase_of_mem hz0, hY4'] at hr
      omega
    have h8 : 8 ≤ ∑ x ∈ X, oc D X x := by omega
    have := hfull8 h8 z0 hz0
    omega
  -- Step 4: in-degree bookkeeping
  have hRXrow : ∀ x ∈ X, ic D X x + ic D R x = 4 := by
    intro x hx
    have h := icW x
    rw [hin x (hXW hx), if_pos (mem_outN.mp hx).2] at h
    have h0 : ic D Y x = 0 :=
      Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr fun v hv => hYX v hv x hx)
    omega
  have hRX : ∑ x ∈ X, oc D X x + ∑ x ∈ X, ic D R x = 20 := by
    have h : ∑ x ∈ X, (ic D X x + ic D R x) = ∑ _x ∈ X, 4 := Finset.sum_congr rfl hRXrow
    rw [Finset.sum_add_distrib, Finset.sum_const, hX5, smul_eq_mul, ← swap D X X] at h
    omega
  have hYrow : ∀ z ∈ Y, ic D X z + (ic D Y z + ic D R z) = 5 := by
    intro z hz
    have h := icW z
    have hyz : ¬ D y z = true := fun h' =>
      Finset.disjoint_left.mp hdXY (mem_outN.mpr ⟨hYW hz, h'⟩) hz
    rw [hin z (hYW hz), if_neg hyz] at h
    omega
  have hYsum : ∑ z ∈ Y, ic D X z + (∑ z ∈ Y, ic D Y z + ∑ z ∈ Y, ic D R z) = 20 := by
    have h : ∑ z ∈ Y, (ic D X z + (ic D Y z + ic D R z)) = ∑ _z ∈ Y, 5 := Finset.sum_congr rfl hYrow
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, hY4', smul_eq_mul] at h
    omega
  have heY : ∑ z ∈ Y, oc D Y z = ∑ z ∈ Y, ic D Y z := swap D Y Y
  -- Step 5: sinks of `D[Y]` and `R'`
  have hYout : ∀ z ∈ Y, 5 ≤ oc D Y z + oc D R z := by
    intro z hz
    have h : oc D W z ≤ oc D Y z + oc D R z := out_split (U := Y) (S := R) (fun b hb hzb => by
      rcases hsplit b hb with rfl | h | h | h
      · exact absurd hzb (hYy z hz)
      · exact absurd hzb (hYX z hz b h)
      · exact Or.inl h
      · exact Or.inr h)
    have := hoc z (hYW hz)
    omega
  set R' := R.filter (fun r => ∃ z ∈ Y, D z r = true) with hR'def
  set R0 := R.filter (fun r => ¬ ∃ z ∈ Y, D z r = true) with hR0def
  have hR'R0 : R'.card + R0.card = 6 := by
    rw [hR'def, hR0def, Finset.card_filter_add_card_filter_not, hR6]
  have hsinkR : ∀ z ∈ Y, oc D Y z = 0 → R.filter (fun v => D z v = true) ⊆ R' ∧
      5 ≤ (R.filter (fun v => D z v = true)).card := by
    intro z hz h0
    refine ⟨fun r hr => ?_, ?_⟩
    · obtain ⟨hrR, hzr⟩ := Finset.mem_filter.mp hr
      exact Finset.mem_filter.mpr ⟨hrR, z, hz, hzr⟩
    · have := hYout z hz
      change 5 ≤ oc D R z
      omega
  -- non-sinks of `D[Y]` number at most `e(Y)`
  set NS := Y.filter (fun z => 1 ≤ oc D Y z) with hNSdef
  set S0 := Y.filter (fun z => ¬ 1 ≤ oc D Y z) with hS0def
  have hNSS0 : NS.card + S0.card = 4 := by
    rw [hNSdef, hS0def, Finset.card_filter_add_card_filter_not, hY4']
  have hNS : NS.card ≤ ∑ z ∈ Y, oc D Y z := by
    have h1 : NS.card * 1 ≤ ∑ z ∈ NS, oc D Y z :=
      card_mul_le_sum (fun z hz => (Finset.mem_filter.mp hz).2)
    have h2 : ∑ z ∈ NS, oc D Y z ≤ ∑ z ∈ Y, oc D Y z :=
      Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    omega
  have hS0 : ∀ z ∈ S0, z ∈ Y ∧ oc D Y z = 0 := by
    intro z hz
    obtain ⟨hzY, h⟩ := Finset.mem_filter.mp hz
    exact ⟨hzY, by omega⟩
  -- `|R'| ≥ 5`
  obtain ⟨z1, hz1⟩ : S0.Nonempty := Finset.card_pos.mp (by omega)
  have hR'5 : 5 ≤ R'.card := by
    obtain ⟨hz1Y, hz10⟩ := hS0 z1 hz1
    obtain ⟨hs, hc⟩ := hsinkR z1 hz1Y hz10
    exact hc.trans (Finset.card_le_card hs)
  -- Step 6
  have hcap : ∀ r ∈ R, ∀ z ∈ Y, D z r = true → oc D X r + ic D X z ≤ 5 := by
    intro r hr z hz hzr
    have hdisj : Disjoint (X.filter (fun v => D r v = true)) (X.filter (fun v => D v z = true)) := by
      refine Finset.disjoint_left.mpr fun _ hx1 hx2 => ?_
      obtain ⟨hx, hrx⟩ := Finset.mem_filter.mp hx1
      exact tri (hRW hr) (hXW hx) (hYW hz) hrx (Finset.mem_filter.mp hx2).2 hzr
    have h := Finset.card_le_card (Finset.union_subset (Finset.filter_subset (fun v => D r v = true) X)
      (Finset.filter_subset (fun v => D v z = true) X))
    rw [Finset.card_union_of_disjoint hdisj, hX5] at h
    exact h
  -- Step 7: `e(R,X) = 20 - e(X)`, split over `R'` and `R0`
  have hRXs : ∑ r ∈ R, oc D X r = ∑ x ∈ X, ic D R x := swap D R X
  have hsplitR : ∑ r ∈ R', oc D X r + ∑ r ∈ R0, oc D X r = ∑ r ∈ R, oc D X r := by
    rw [hR'def, hR0def]; exact Finset.sum_filter_add_sum_filter_not _ _ _
  have hR0s : ∑ r ∈ R0, oc D X r ≤ R0.card * 5 :=
    sum_le_card_mul (fun r _ => by have := oc_le (G := D) X r; omega)
  have hR'mem : ∀ r ∈ R', r ∈ R ∧ ∃ z ∈ Y, D z r = true := fun r hr => Finset.mem_filter.mp hr
  by_cases hA : ∀ z ∈ Y, 4 ≤ ic D X z
  · -- every row of `R'` heads at most one vertex of `X`
    have hR's : ∑ r ∈ R', oc D X r ≤ R'.card * 1 := by
      refine sum_le_card_mul (fun r hr => ?_)
      obtain ⟨hrR, z, hz, hzr⟩ := hR'mem r hr
      have := hcap r hrR z hz hzr
      have := hA z hz
      omega
    omega
  · push Not at hA
    obtain ⟨zs, hzs, hzs3⟩ := hA
    have hle5 : ∀ z ∈ Y, ic D X z ≤ 5 := fun z _ => by have := ic_le (G := D) X z; omega
    have hsumY : ic D X zs + ∑ z ∈ Y.erase zs, ic D X z = ∑ z ∈ Y, ic D X z :=
      Finset.add_sum_erase Y (fun z => ic D X z) hzs
    have hrest : ∑ z ∈ Y.erase zs, ic D X z ≤ (Y.erase zs).card * 5 :=
      sum_le_card_mul (fun z hz => hle5 z (Finset.mem_of_mem_erase hz))
    rw [Finset.card_erase_of_mem hzs, hY4'] at hrest
    -- `e(X) = 7`
    have hne8 : ¬ 8 ≤ ∑ x ∈ X, oc D X x := fun h8 => by have := hfull8 h8 zs hzs; omega
    have heX7 : ∑ x ∈ X, oc D X x = 7 := by omega
    -- the other three vertices of `Y` have all five `X`-parents
    have hother : ∀ z ∈ Y, z ≠ zs → ic D X z = 5 := by
      intro z hz hne
      by_contra h5
      have h1 : ∑ z ∈ Y.erase zs, ic D X z + 1 ≤ ∑ _z ∈ Y.erase zs, 5 :=
        sum_add_one_le (fun z hz => hle5 z (Finset.mem_of_mem_erase hz)) (Finset.mem_erase.mpr ⟨hne, hz⟩)
          (show ic D X z + 1 ≤ 5 by have := hle5 z hz; omega)
      rw [Finset.sum_const, Finset.card_erase_of_mem hzs, hY4', smul_eq_mul] at h1
      omega
    -- every row of `R'` heads at most two vertices of `X`, none if it has a parent `≠ zs`
    have hrow2 : ∀ r ∈ R', oc D X r ≤ 2 := by
      intro r hr
      obtain ⟨hrR, z, hz, hzr⟩ := hR'mem r hr
      have := hcap r hrR z hz hzr
      by_cases hzz : z = zs
      · subst hzz
        omega
      · have := hother z hz hzz
        omega
    have hrow0 : ∀ r ∈ R', ∀ z ∈ Y, z ≠ zs → D z r = true → oc D X r = 0 := by
      intro r hr z hz hne hzr
      have := hcap r (hR'mem r hr).1 z hz hzr
      have := hother z hz hne
      omega
    -- `D[Y]` has at least two sinks
    have hS02 : 2 ≤ S0.card := by omega
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < S0.card)
    obtain ⟨z', hz'S0, hz'ne⟩ : ∃ z' ∈ S0, z' ≠ zs := by
      by_cases haz : a = zs
      · exact ⟨b, hb, fun h => hab (haz.trans h.symm)⟩
      · exact ⟨a, ha, haz⟩
    obtain ⟨hz'Y, hz'0⟩ := hS0 z' hz'S0
    rcases (by omega : R'.card = 5 ∨ R'.card = 6) with h5 | h6
    · -- `z'` heads all of `R'`
      obtain ⟨hs, hc⟩ := hsinkR z' hz'Y hz'0
      have heq := Finset.eq_of_subset_of_card_le hs (by omega)
      have hR's : ∑ r ∈ R', oc D X r ≤ R'.card * 0 := by
        refine sum_le_card_mul (fun r hr => ?_)
        have hr' : r ∈ R.filter (fun v => D z' v = true) := by rw [heq]; exact hr
        exact (hrow0 r hr z' hz'Y hz'ne (Finset.mem_filter.mp hr').2).le
      omega
    · have hR's : ∑ r ∈ R', oc D X r ≤ R'.card * 2 := sum_le_card_mul hrow2
      omega

/-- **`BallSmall 3 5`** (Lemma B1): every `3`-free out-`5` digraph on at most `16` vertices has `|B_2(u)| ≥ 11`. -/
theorem bball35 : BallSmall 3 5 := by
  intro D W hfree hout hcard u hu
  exact ball_two_ge hfree hout (by omega) hu

/-- **`BBall 3 5`**: the boundary form, on `range 16`. -/
theorem bball35_boundary : BBall 3 5 :=
  fun D hf ho u hu => bball35 D _ hf ho (by simp) u hu

end LeanCH.BR.BRsGen35
