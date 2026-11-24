import LeanCH.BR.BR35Master
import LeanCH.BR.BR34

/-!
# Boundary regularity `BR(3,5)`, Lean 4.35.0

Paper source: `checkpoints/boundary_20261111/BR35_attempt_subagent.md` (audited in `STATUS.md`, last section).
The proof follows the paper, restructured so that each case is closed by one count.

Setting (`Root`): `u` has in-degree 6, hence (strict cap) out-degree 5, and `|M| = 4`. Write `a_m = |I(m) ∩ O|`,
`(O→M) = Σ a_m = 20 - σ`. By `five_shape`, `e(D[O]) ≤ 8`, so `(O→M) ≥ 25 - 8 = 17` (σ ≤ 3), and the budget (2.2)
reads `(I→M) + e(D[M]) ≤ 24 - (O→M)`. A row `m` is *full* if `a_m = 5`. `I₀` = vertices of `I` heading nothing in `O`.

* **σ = 3 (`caseE`, paper Theorem E).** Then `e(D[O]) = 8` and `five_shape` gives shape R: `e ∈ O` heads the 4-set
  `C = O ∖ {e}`, each `c ∈ C` has one head in `O` and so heads all of `M`; `e` heads exactly one `m* ∈ M`, the only
  full row. `M` sends nothing into `O`, and `M`-heads in `I` lie in `J = {w ∈ I : w heads nothing in C}`, with
  `p_w ≤ 1` on `J` and `p_w = 0` on `I₀ ⊆ J`. The master inequalities force `|J| ∈ {4,5}` and `|I₀| = 2`, so `m*`
  heads all of `S = M ∖ {m*}` and each `s ∈ S` spends its out-degree in `J ∪ S`. `|J| = 4`: every `s ∈ S` has a head
  in `S` (`small_out`). `|J| = 5`: the caps at `m*` and at `s ∈ S` give `(J→M) ≤ e(D[M]) - 2`, against the budget.
  (The paper's three ways of paying the bracket are not needed: `(J→M) ≥ 3` already follows from `lemmaX`.)
* **σ ≤ 2, at least three full rows (`caseC`, paper Theorems A and C).** Full rows head only `(M∖m) ∪ I₀`. With
  `k₀ = |I₀|`: `k₀ ≤ 3` makes each of three full rows head another full row (`small_out`); `k₀ ≥ 4` uses `lemmaX` on
  `J = I₀` (the paper's (L8), sharpened by one) and the budget: `k₀ = 6` is too expensive, `k₀ = 5` forces
  `e(D[M]) = 0`, `k₀ = 4` forces every full row to head all of `I₀`, and then `BR(3,1)` on `I₀` (`four_regular`)
  gives `(I₀→M) ≥ 4`.
* **σ ≤ 2, at most two full rows (`caseD`, paper Theorem D).** Then σ = 2 and every row misses at most one vertex of
  `O`, so `M` sends nothing into `O` (`noMO`), and `J` = `M`-heads in `I` has `p_w ≤ 1`, with `p_w = 0` on at least
  three vertices (two full rows cannot both head all of `M`). The master inequalities give `k² - 9k + 22 ≤ 0`.

Hence no vertex has in-degree 6; with the cap (in-degree ≤ 6) every in-degree is at most 5, and double counting
(`Σ in = Σ out ≥ 80`) makes every in-degree exactly 5 (as in `LeanCH.BR.BR34.br_of_strict_cap`).
-/

namespace LeanCH.BR.BR35

open CH Compose.Boundary Compose.FloorSix

namespace Root

variable {G : CH.Digraph} {u : Nat} {I O M : Finset Nat} (R : Root G u I O M)
include R

/-- **Paper Theorems A and C**: at least three full rows and `σ ≤ 2` are impossible. -/
theorem caseC {F : Finset Nat} (hF : F ⊆ M) (hFc : F.card = 3) (hfull : ∀ m ∈ F, ∀ x ∈ O, G x m = true)
    (hOM : 18 ≤ ∑ m ∈ M, ic G O m) : False := by
  classical
  have bud := R.budget
  have heM : ∑ m ∈ M, oc G M m = ∑ m ∈ M, ic G M m := swap G M M
  set I0 := I.filter (fun w => ∀ x ∈ O, G w x = false) with hI0
  have hI0I : I0 ⊆ I := Finset.filter_subset _ _
  have hI0O : ∀ w ∈ I0, oc G O w = 0 := fun w hw => oc_eq_zero (Finset.mem_filter.mp hw).2
  have heads : ∀ m ∈ F, 5 ≤ oc G M m + oc G I0 m := fun m hm => R.full_heads (hF hm) (hfull m hm)
  have hk0 : I0.card ≤ 6 := R.cI ▸ Finset.card_le_card hI0I
  have heMF : ∑ m ∈ F, oc G M m ≤ ∑ m ∈ M, oc G M m := Finset.sum_le_sum_of_subset hF
  have hIM : ∑ w ∈ I0, oc G M w ≤ ∑ m ∈ M, ic G I m := by
    rw [← swap G I M]
    exact Finset.sum_le_sum_of_subset hI0I
  -- a vertex of `I₀` headed by all three full rows heads at most one vertex of `M`
  have xle : ∀ w ∈ I0, (∀ m ∈ F, G m w = true) → oc G M w ≤ 1 := by
    intro w hw hall
    have h1 : 3 ≤ ic G M w := hFc ▸ Finset.card_le_card (fun m hm => Finset.mem_filter.mpr ⟨hF hm, hall m hm⟩)
    have h2 := oc_ic_le R.H.loopless R.H.noShort R.subM (R.ltI (hI0I hw)) (B := M) (fun v hv _ => hv)
    rw [R.cM] at h2
    omega
  -- the `M`-part of the out-degree of a vertex of `I₀`
  have rowI0 : ∀ w ∈ I0, 4 ≤ oc G I0 w + (6 - I0.card) + oc G M w := by
    intro w hw
    have h1 := R.I_out (hI0I hw)
    rw [hI0O w hw] at h1
    have h2 := oc_sdiff (G := G) hI0I w
    have h3 := oc_le (G := G) (I \ I0) w
    rw [Finset.card_sdiff_of_subset hI0I, R.cI] at h3
    omega
  by_cases hsmall : I0.card ≤ 3
  · -- every full row heads at least two vertices of `M`, hence another full row
    apply small_out R.H.loopless R.H.noShort (hF.trans R.subM) (by omega) (Finset.card_pos.mp (by omega))
    intro m hm
    have h1 := heads m hm
    have h2 := oc_le (G := G) I0 m
    have h3 := oc_sdiff (G := G) hF m
    have h4 : (M \ F).card = 1 := by rw [Finset.card_sdiff_of_subset hF, R.cM, hFc]
    have h5 := oc_le (G := G) (M \ F) m
    exact exists_of_oc (by omega)
  · have hne : I0.Nonempty := Finset.card_pos.mp (by omega)
    have X := lemmaX R.H.loopless R.H.noShort R.subI R.cI hI0I hne (fun w => oc G M w) (fun w hw => by
      have := R.I_out (hI0I hw)
      rw [hI0O w hw] at this
      omega)
    rcases (by omega : I0.card = 4 ∨ I0.card = 5 ∨ I0.card = 6) with h4 | h5 | h6
    · rw [h4] at X
      have hge1 : ∀ m ∈ F, 1 ≤ oc G M m := fun m hm => by
        have := heads m hm
        have := oc_le (G := G) I0 m
        omega
      -- each full row has exactly one head in `M`, so heads all of `I₀`
      have hFrow : ∀ m ∈ F, ∀ w ∈ I0, G m w = true := by
        intro m hm
        have hsum := Finset.add_sum_erase F (oc G M) hm
        have hrest := card_mul_le_sum (s := F.erase m) (fun m' hm' => hge1 m' (Finset.mem_of_mem_erase hm'))
        rw [Finset.card_erase_of_mem hm, hFc] at hrest
        have h1 := heads m hm
        apply all_of_oc
        omega
      have hx1 : ∀ w ∈ I0, oc G M w ≤ 1 := fun w hw => xle w hw (fun m hm => hFrow m hm w hw)
      -- every vertex of `I₀` keeps a head in `I₀`; `BR(3,1)` makes it exactly one
      have hkeep : ∀ w ∈ I0, 1 ≤ oc G I0 w := fun w hw => by
        have := rowI0 w hw
        have := hx1 w hw
        omega
      have reg := four_regular R.H.loopless R.H.noShort (hI0I.trans R.subI) h4 hkeep
      have hx2 : ∀ w ∈ I0, 1 ≤ oc G M w := fun w hw => by
        have := rowI0 w hw
        have := reg w hw
        omega
      have s1 := card_mul_le_sum hx2
      have s2 := card_mul_le_sum hge1
      rw [h4] at s1
      rw [hFc] at s2
      omega
    · rw [h5] at X
      have hFrow : ∀ m ∈ F, ∀ w ∈ I0, G m w = true := by
        intro m hm
        have h1 := heads m hm
        have h2 : oc G M m ≤ ∑ m ∈ F, oc G M m := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hm
        apply all_of_oc
        omega
      have hx1 : ∀ w ∈ I0, oc G M w ≤ 1 := fun w hw => xle w hw (fun m hm => hFrow m hm w hw)
      have s1 := sum_le_card_mul hx1
      rw [h5] at s1
      omega
    · rw [h6] at X
      omega

/-- **Paper Theorem D**: `σ = 2` with every row missing at most one vertex of `O` and two full rows. -/
theorem caseD (h4 : ∀ m ∈ M, 4 ≤ ic G O m) {m1 m2 : Nat} (hm1 : m1 ∈ M) (hm2 : m2 ∈ M) (h12 : m1 ≠ m2)
    (hf1 : ∀ x ∈ O, G x m1 = true) (hf2 : ∀ x ∈ O, G x m2 = true) (hOM : 18 ≤ ∑ m ∈ M, ic G O m) :
    False := by
  classical
  set I0 := I.filter (fun w => ∀ x ∈ O, G w x = false) with hI0
  set J := I.filter (fun w => ∃ m ∈ M, G m w = true) with hJ
  have hJI : J ⊆ I := Finset.filter_subset _ _
  have hMO : ∀ m ∈ M, ∀ x ∈ O, G m x = false := fun m hm x hx => R.noMO hm (h4 m hm) hx
  have hMJ : ∀ m ∈ M, ∀ w ∈ I, G m w = true → w ∈ J := fun m hm w hw h =>
    Finset.mem_filter.mpr ⟨hw, m, hm, h⟩
  have hp : ∀ w ∈ J, oc G O w ≤ 1 := by
    intro w hw
    obtain ⟨hwI, m, hm, hmw⟩ := Finset.mem_filter.mp hw
    have := R.p_le hm hwI hmw
    have := h4 m hm
    omega
  -- some row of `M` heads at least three vertices of `I₀`: otherwise the two full rows head each other
  have big : ∃ m ∈ M, 3 ≤ oc G I0 m := by
    by_contra hcon
    push Not at hcon
    have rowM : ∀ a ∈ M, ∀ b ∈ M, a ≠ b → (∀ x ∈ O, G x a = true) → G a b = true := by
      intro a ha b hb hab hfa
      have h1 : 5 ≤ oc G M a + oc G I0 a := R.full_heads ha hfa
      have h2 := hcon a ha
      have h3 := oc_erase_eq (G := G) (A := M) (R.H.loopless a (R.ltM ha))
      have h5 : (M.erase a).card = 3 := by rw [Finset.card_erase_of_mem ha, R.cM]
      have hall := all_of_oc (G := G) (A := M.erase a) (w := a) (by omega)
      exact hall b (Finset.mem_erase.mpr ⟨Ne.symm hab, hb⟩)
    exact R.H.n2 (R.ltM hm1) (R.ltM hm2) (rowM m1 hm1 m2 hm2 h12 hf1) (rowM m2 hm2 m1 hm1 (Ne.symm h12) hf2)
  obtain ⟨m, hm, hT⟩ := big
  have hTJ : I0.filter (fun w => G m w = true) ⊆ J := fun w hw =>
    hMJ m hm w (Finset.filter_subset _ _ (Finset.mem_filter.mp hw).1) (Finset.mem_filter.mp hw).2
  have hTO : ∀ w ∈ I0.filter (fun w => G m w = true), oc G O w = 0 := fun w hw =>
    oc_eq_zero (Finset.mem_filter.mp (Finset.mem_filter.mp hw).1).2
  have hPi : ∑ w ∈ J, oc G O w + 3 ≤ J.card := by
    rw [← Finset.sum_sdiff hTJ, Finset.sum_eq_zero hTO]
    have e2 := sum_le_card_mul (s := J \ I0.filter (fun w => G m w = true)) (c := 1)
      (fun w hw => hp w (Finset.sdiff_subset hw))
    rw [Finset.card_sdiff_of_subset hTJ] at e2
    have := Finset.card_le_card hTJ
    have : 3 ≤ (I0.filter (fun w => G m w = true)).card := hT
    omega
  have hne : J.Nonempty := Finset.card_pos.mp (by omega)
  have X := lemmaX R.H.loopless R.H.noShort R.subI R.cI hJI hne (fun w => oc G O w + oc G M w)
    (fun w hw => R.I_out (hJI hw))
  rw [Finset.sum_add_distrib] at X
  have YZ := R.lemmaYZ hJI hMO hMJ
  have B := R.budgetJ hJI
  have hk6 : J.card ≤ 6 := R.cI ▸ Finset.card_le_card hJI
  generalize J.card = k at X YZ hPi hk6
  interval_cases k <;> omega

/-- **Paper Theorem E**: `σ = 3`, shape R. -/
theorem caseE {e : Nat} (he : e ∈ O) (hsh : ∀ c ∈ O, c ≠ e → G e c = true ∧ oc G O c = 1)
    (hOM : ∑ x ∈ O, oc G M x ≤ 17) : False := by
  classical
  set C := O.erase e with hC
  have hCO : C ⊆ O := Finset.erase_subset e O
  have hCc : C.card = 4 := by rw [hC, Finset.card_erase_of_mem he, R.cO]
  -- the cycle rows head all of `M`
  have hCM : ∀ c ∈ C, ∀ m ∈ M, G c m = true := by
    intro c hc
    have hcO := hCO hc
    have h1 := R.O_out hcO
    have h2 := (hsh c hcO (Finset.ne_of_mem_erase hc)).2
    apply all_of_oc
    rw [R.cM]
    omega
  have heC : ∀ c ∈ C, G e c = true := fun c hc => (hsh c (hCO hc) (Finset.ne_of_mem_erase hc)).1
  -- `e` heads exactly one vertex `m*` of `M`
  have hOMe : ∑ x ∈ O, oc G M x = oc G M e + 16 := by
    rw [← Finset.add_sum_erase O (oc G M) he]
    have h4 : ∀ c ∈ O.erase e, oc G M c = 4 := fun c hc => by rw [oc_full (hCM c hc), R.cM]
    rw [Finset.sum_congr rfl h4, Finset.sum_const, smul_eq_mul, ← hC, hCc]
  have hoce : 1 ≤ oc G M e := by
    have h1 := R.O_out he
    have h2 := oc_erase_eq (G := G) (A := O) (R.H.loopless e (R.ltO he))
    have h3 := oc_le (G := G) (O.erase e) e
    rw [← hC, hCc] at h3
    rw [← hC] at h2
    omega
  obtain ⟨ms, hms, hems⟩ := exists_of_oc hoce
  have hfull : ∀ x ∈ O, G x ms = true := by
    intro x hx
    by_cases hxe : x = e
    · rw [hxe]; exact hems
    · exact hCM x (Finset.mem_erase.mpr ⟨hxe, hx⟩) ms hms
  -- Lemma 5.1: `M` sends nothing into `O`
  obtain ⟨c0, hc0⟩ : C.Nonempty := Finset.card_pos.mp (by omega)
  have hMO : ∀ m ∈ M, ∀ x ∈ O, G m x = false := by
    intro m hm x hx
    by_cases hxe : x = e
    · rw [hxe]
      exact R.H.tri (R.ltO he) (R.ltO (hCO hc0)) (R.ltM hm) (heC c0 hc0) (hCM c0 hc0 m hm)
    · exact R.H.back (R.ltO hx) (R.ltM hm) (hCM x (Finset.mem_erase.mpr ⟨hxe, hx⟩) m hm)
  set J := I.filter (fun w => ∀ c ∈ C, G w c = false) with hJ
  set I0 := I.filter (fun w => ∀ x ∈ O, G w x = false) with hI0
  have hJI : J ⊆ I := Finset.filter_subset _ _
  have hI0J : I0 ⊆ J := fun w hw => by
    obtain ⟨hwI, hall⟩ := Finset.mem_filter.mp hw
    exact Finset.mem_filter.mpr ⟨hwI, fun c hc => hall c (hCO hc)⟩
  have hMJ : ∀ m ∈ M, ∀ w ∈ I, G m w = true → w ∈ J := by
    intro m hm w hw hmw
    refine Finset.mem_filter.mpr ⟨hw, fun c hc => ?_⟩
    cases h : G w c
    · rfl
    · have := R.H.tri (R.ltM hm) (R.ltI hw) (R.ltO (hCO hc)) hmw h
      rw [hCM c hc m hm] at this
      exact Bool.noConfusion this
  have hJO : ∀ w ∈ J, oc G O w ≤ 1 := by
    intro w hw
    have h1 : oc G O w ≤ ({e} : Finset Nat).card := oc_le_of_sub (fun x hx hwx => by
      by_contra hxe
      have hxC : x ∈ C := Finset.mem_erase.mpr ⟨by simpa using hxe, hx⟩
      rw [(Finset.mem_filter.mp hw).2 x hxC] at hwx
      exact Bool.false_ne_true hwx)
    simpa using h1
  have hI0O : ∀ w ∈ I0, oc G O w = 0 := fun w hw => oc_eq_zero (Finset.mem_filter.mp hw).2
  have hPi : ∑ w ∈ J, oc G O w + I0.card ≤ J.card := by
    rw [← Finset.sum_sdiff hI0J, Finset.sum_eq_zero hI0O]
    have e2 := sum_le_card_mul (s := J \ I0) (c := 1) (fun w hw => hJO w (Finset.sdiff_subset hw))
    rw [Finset.card_sdiff_of_subset hI0J] at e2
    have := Finset.card_le_card hI0J
    omega
  -- the full row `m*`
  have heads : 5 ≤ oc G M ms + oc G I0 ms := R.full_heads hms hfull
  have hmsM : oc G M ms ≤ 3 := by
    rw [← oc_erase_eq (G := G) (A := M) (R.H.loopless ms (R.ltM hms))]
    have := oc_le (G := G) (M.erase ms) ms
    rw [Finset.card_erase_of_mem hms, R.cM] at this
    exact this
  have hk0 : 2 ≤ I0.card := le_trans (by omega) (oc_le (G := G) I0 ms)
  have hne : J.Nonempty := Finset.card_pos.mp (by have := Finset.card_le_card hI0J; omega)
  have X := lemmaX R.H.loopless R.H.noShort R.subI R.cI hJI hne (fun w => oc G O w + oc G M w)
    (fun w hw => R.I_out (hJI hw))
  rw [Finset.sum_add_distrib] at X
  have YZ := R.lemmaYZ hJI hMO hMJ
  have B := R.budgetJ hJI
  have hswapO : ∑ x ∈ O, oc G M x = ∑ m ∈ M, ic G O m := swap G O M
  have hk6 : J.card ≤ 6 := R.cI ▸ Finset.card_le_card hJI
  -- the master inequalities leave `|J| ∈ {4, 5}` and `|I₀| = 2`
  have hkey : (J.card = 4 ∨ J.card = 5) ∧ I0.card = 2 ∧ (J.card = 5 → 3 ≤ ∑ w ∈ J, oc G M w) := by
    generalize J.card = k at X YZ hPi hk6 ⊢
    interval_cases k <;> omega
  obtain ⟨hk45, hk02, hA3⟩ := hkey
  -- `m*` heads all of `S = M ∖ {m*}`
  have hS : ∀ s ∈ M.erase ms, G ms s = true := by
    apply all_of_oc
    rw [oc_erase_eq (G := G) (A := M) (R.H.loopless ms (R.ltM hms)), Finset.card_erase_of_mem hms, R.cM]
    have := oc_le (G := G) I0 ms
    omega
  have hScard : (M.erase ms).card = 3 := by rw [Finset.card_erase_of_mem hms, R.cM]
  -- each `s ∈ S` spends its out-degree in `J ∪ S`
  have hsrow : ∀ s ∈ M.erase ms, 5 ≤ oc G J s + oc G (M.erase ms) s := by
    intro s hs
    have hsM := Finset.mem_of_mem_erase hs
    have h1 := R.M_out hsM
    have h2 : oc G O s = 0 := oc_eq_zero (hMO s hsM)
    have h3 := oc_I_eq_J (G := G) hJI hMJ hsM
    have h4 := oc_erase_eq (G := G) (A := M) (R.H.back (R.ltM hms) (R.ltM hsM) (hS s hs))
    omega
  rcases hk45 with hk | hk
  · -- `|J| = 4`: every `s ∈ S` heads another vertex of `S`
    apply small_out R.H.loopless R.H.noShort ((Finset.erase_subset ms M).trans R.subM) (by omega)
      (Finset.card_pos.mp (by omega))
    intro s hs
    have h1 := hsrow s hs
    have h2 := oc_le (G := G) J s
    exact exists_of_oc (by omega)
  · -- `|J| = 5`: caps at `m*` and at `S`
    have hA := hA3 hk
    have capms : ic G I ms ≤ 1 := by
      have h1 := R.M_in hms
      have h2 : ic G O ms = 5 := by rw [ic_full hfull, R.cO]
      omega
    have caps : ∀ s ∈ M.erase ms, ic G I s + ic G (M.erase ms) s ≤ 1 := by
      intro s hs
      have hsM := Finset.mem_of_mem_erase hs
      have h1 := R.M_in hsM
      have h2 : 4 ≤ ic G O s := by
        have := ic_mono (G := G) hCO s
        rw [ic_full (fun c hc => hCM c hc s hsM), hCc] at this
        exact this
      have h3 : ic G M s = 1 + ic G (M.erase ms) s := by
        conv_lhs => rw [← Finset.insert_erase hms]
        rw [ic_insert (Finset.notMem_erase ms M), hS s hs]
        rfl
      omega
    have per : ∀ s ∈ M.erase ms, ic G J s ≤ oc G (M.erase ms) s := by
      intro s hs
      have hsM := Finset.mem_of_mem_erase hs
      by_cases h0 : oc G (M.erase ms) s = 0
      · have h1 := hsrow s hs
        have hall := all_of_oc (G := G) (A := J) (w := s) (by omega)
        rw [ic_eq_zero (fun w hw => R.H.back (R.ltM hsM) (R.ltI (hJI hw)) (hall w hw))]
        exact Nat.zero_le _
      · have := caps s hs
        have := ic_mono (G := G) hJI s
        omega
    have hA' : ∑ w ∈ J, oc G M w = ic G J ms + ∑ s ∈ M.erase ms, ic G J s := by
      rw [swap G J M, Finset.add_sum_erase M (ic G J) hms]
    have heM : ∑ m ∈ M, oc G M m = oc G M ms + ∑ s ∈ M.erase ms, oc G M s :=
      (Finset.add_sum_erase M (oc G M) hms).symm
    have h1 : ∑ s ∈ M.erase ms, ic G J s ≤ ∑ s ∈ M.erase ms, oc G (M.erase ms) s := Finset.sum_le_sum per
    have h2 : ∑ s ∈ M.erase ms, oc G (M.erase ms) s ≤ ∑ s ∈ M.erase ms, oc G M s :=
      Finset.sum_le_sum (fun s _ => oc_mono (Finset.erase_subset ms M) s)
    have h3 : ic G J ms ≤ 1 := le_trans (ic_mono hJI ms) capms
    have h4 := oc_le (G := G) I0 ms
    omega

/-- **No vertex of in-degree 6.** -/
theorem no_root : False := by
  classical
  obtain ⟨hle8, hshape⟩ := five_shape R.H.loopless R.H.noShort R.subO R.cO (fun x hx => R.O_inner hx)
  have hsum : O.card * 5 ≤ ∑ x ∈ O, (oc G O x + oc G M x) := card_mul_le_sum (fun x hx => R.O_out hx)
  rw [Finset.sum_add_distrib, R.cO] at hsum
  have hswap : ∑ x ∈ O, oc G M x = ∑ m ∈ M, ic G O m := swap G O M
  by_cases h17 : ∑ x ∈ O, oc G M x ≤ 17
  · obtain ⟨e, he, hsh⟩ := hshape (by omega)
    exact R.caseE he hsh h17
  · have h18 : 18 ≤ ∑ m ∈ M, ic G O m := by omega
    set Fu := M.filter (fun m => 5 ≤ ic G O m) with hFu
    have hFuM : Fu ⊆ M := Finset.filter_subset _ _
    have hfullOf : ∀ m ∈ Fu, ∀ x ∈ O, G x m = true := fun m hm =>
      all_of_ic (by rw [R.cO]; exact (Finset.mem_filter.mp hm).2)
    by_cases h3 : 3 ≤ Fu.card
    · obtain ⟨F, hF, hFc⟩ := Finset.exists_subset_card_eq h3
      exact R.caseC (hF.trans hFuM) hFc (fun m hm => hfullOf m (hF hm)) h18
    · have hpt : ∀ m ∈ M, ic G O m ≤ 4 + (if m ∈ Fu then 1 else 0) := by
        intro m hm
        have := ic_le (G := G) O m
        rw [R.cO] at this
        split_ifs with h
        · omega
        · have : ¬ 5 ≤ ic G O m := fun h' => h (Finset.mem_filter.mpr ⟨hm, h'⟩)
          omega
      have hsumFu : ∑ m ∈ M, (4 + if m ∈ Fu then 1 else 0) = 16 + Fu.card := by
        rw [Finset.sum_add_distrib, Finset.sum_const, R.cM, smul_eq_mul, ← Finset.card_filter,
          Finset.filter_mem_eq_inter, Finset.inter_eq_right.mpr hFuM]
      have hS := Finset.sum_le_sum hpt
      rw [hsumFu] at hS
      have h4 : ∀ m ∈ M, 4 ≤ ic G O m := by
        intro m hm
        by_contra hlt
        have := sum_add_one_le hpt hm (by split_ifs <;> omega)
        rw [hsumFu] at this
        omega
      obtain ⟨m1, hm1, m2, hm2, h12⟩ := Finset.one_lt_card.mp (by omega : 1 < Fu.card)
      exact R.caseD h4 (hFuM hm1) (hFuM hm2) h12 (hfullOf m1 hm1) (hfullOf m2 hm2) h18

end Root

/-- No vertex has in-degree 6 and out-degree 5. -/
theorem no_in_six {G : CH.Digraph} (H : Hyp G) {u : Nat} (hu : u < 16) (hin : ic G V u = 6)
    (hout : oc G V u = 5) : False :=
  (root_of H hu hin hout).no_root

/-- **`BR(3,5)`.** Every loopless digraph on 16 labels with minimum out-degree 5 and no directed cycle of length at
most 3 has every in-degree exactly 5. -/
theorem br_five : BoundaryRegular 3 5 := by
  classical
  intro G loopless deg noShort
  have brs : ∀ t, 1 ≤ t → t < 5 → BoundaryRegular 3 t := fun t h1 h2 => by
    rcases (by omega : t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4) with rfl | rfl | rfl | rfl
    · exact LeanCH.BR.SmallBR.br_one
    · exact LeanCH.BR.SmallBR.br_two
    · exact LeanCH.BR.SmallBR.br_three
    · exact LeanCH.BR.BR34.br_four
  have cap : ∀ v, v < 16 → 5 ≤ ic G V v → 3 * (ic G V v - 5) + 2 * (oc G V v - 5) + 2 ≤ 5 :=
    fun v hv hin => LeanCH.BR.StrictCap.strict_cap (s := 5) (by omega) brs loopless deg noShort hv hin
  have H : Hyp G :=
    { loopless := loopless
      deg := deg
      noShort := noShort
      cap := fun v hv => by
        by_contra h
        have := cap v hv (by omega)
        omega }
  -- every in-degree is at most 5
  have hle : ∀ u ∈ Finset.range 16, (par G 16 u).card ≤ 5 := by
    intro u hu
    have hu' := Finset.mem_range.mp hu
    by_contra hgt
    have hc := H.cap u hu'
    have h6 : ic G V u = 6 := by
      change ¬ ic G V u ≤ 5 at hgt
      omega
    have c := cap u hu' (by omega)
    have h5 : oc G V u = 5 := by
      have := H.out hu'
      omega
    exact no_in_six H hu' h6 h5
  -- double counting: Σ in = Σ out ≥ 16 · 5
  have hge : ∑ _u ∈ Finset.range 16, 5 ≤ ∑ u ∈ Finset.range 16, (par G 16 u).card :=
    calc ∑ _u ∈ Finset.range 16, 5
        ≤ ∑ x ∈ Finset.range 16, ((Finset.range 16).filter (fun w => G x w = true)).card :=
          Finset.sum_le_sum (fun x hx => out_card deg (Finset.mem_range.mp hx))
      _ = ∑ v ∈ Finset.range 16, ((Finset.range 16).filter (fun u => G u v = true)).card :=
          Compose.ThinRigid.sum_out_eq_sum_in G _
      _ = ∑ u ∈ Finset.range 16, (par G 16 u).card := rfl
  have heq := le_antisymm (Finset.sum_le_sum hle) hge
  have each := (Finset.sum_eq_sum_iff_of_le hle).mp heq
  intro v hv
  exact each v (Finset.mem_range.mpr hv)

end LeanCH.BR.BR35
