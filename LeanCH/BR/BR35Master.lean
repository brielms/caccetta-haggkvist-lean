import LeanCH.BR.BR35Shape

/-!
# BR(3,5), part 3: the master inequality (Lean 4.35.0)

Paper source: `checkpoints/boundary_20261111/BR35_attempt_subagent.md`, section 8 (identity (8.2), the bracket lemma
and (★)). The identity is used here as three inequalities, which is all the later steps need.

**`lemmaX` (the bracket lemma).** Let `|I| = 6`, `J ⊆ I` nonempty with `k = |J|`, and suppose every `w ∈ J` has
`4 ≤ out_I(w) + q(w)` (in the application `q(w) = |O(w) ∩ O| + |O(w) ∩ M| = p_w + x_w`, from `out(w) ≥ 5` and
`O(w) ⊆ {u} ∪ I ∪ O ∪ M`). Then `9k + 2 ≤ 2 Σ_J q + k² + 2k(6-k)`, i.e. `Σ_J (p_w + x_w) ≥ (k² - 3k)/2 + 1`.

Proof. `Σ_J out_I = e(D[J]) + e(J → I∖J)`, with `2e(D[J]) + k ≤ k²` (no digon) and `e(J → I∖J) ≤ k(6-k)`. This
gives the bound without the `+ 2`. The extra unit (the paper's "bracket ≥ 2") comes from one of: two non-adjacent
vertices of `J` (`2e(D[J]) + k + 2 ≤ k²`); a non-arc `w ↛ h` with `w ∈ J`, `h ∈ I∖J`; or else `D[J]` is a tournament,
transitive by No3, whose source `t` (`tourn_source`) heads all of `I∖{t}`, so `out_I(t) = 5`.

**`lemmaYZ`.** If `M` sends no arc into `O` and every `M`-head in `I` lies in `J ⊆ I`, then
`20 + (J→M) ≤ 4k + e(D[M])`: the `M`-rows give `(M→J) + e(D[M]) ≥ 20`, and `(M→J) + (J→M) ≤ 4k` (no digon).

**`budgetJ`.** `(J→M) + (O→M) + e(D[M]) ≤ 24`, from the budget (2.2).

Together: `k² - 7k + 18 - σ ≤ 2Π` with `σ = 20 - (O→M)` and `Π = Σ_J p_w`, which is the paper's (★) with
`Ω, β ≥ 0` dropped.
-/

namespace LeanCH.BR.BR35

open CH Compose.Boundary Compose.FloorSix

section generic

variable {G : CH.Digraph} {n : Nat}

/-- **The bracket lemma** (paper section 8). -/
theorem lemmaX (loopless : CH.Loopless G n) (noShort : ¬ CH.HasDirectedCycleAtMost G n 3)
    {I J : Finset Nat} (hI : I ⊆ Finset.range n) (hIc : I.card = 6) (hJI : J ⊆ I) (hne : J.Nonempty)
    (q : Nat → Nat) (hq : ∀ w ∈ J, 4 ≤ oc G I w + q w) :
    9 * J.card + 2 ≤ 2 * ∑ w ∈ J, q w + J.card * J.card + 2 * (J.card * (6 - J.card)) := by
  classical
  have hJ : J ⊆ Finset.range n := hJI.trans hI
  have lt : ∀ x ∈ I, x < n := fun x hx => Finset.mem_range.mp (hI hx)
  have hHc : (I \ J).card = 6 - J.card := by rw [Finset.card_sdiff_of_subset hJI, hIc]
  have hk1 : 1 ≤ J.card := Finset.card_pos.mpr hne
  have hsplit : ∀ w, oc G I w = oc G J w + oc G (I \ J) w := fun w => oc_sdiff hJI w
  have sJ : ∑ w ∈ J, oc G J w = ∑ w ∈ J, ic G J w := swap G J J
  have pv1 : ∀ w ∈ J, oc G J w + ic G J w + 1 ≤ J.card := fun w hw =>
    oc_ic_le_mem loopless noShort hJ hw
  have pv2 : ∀ w ∈ J, oc G (I \ J) w ≤ 6 - J.card := fun w _ => hHc ▸ oc_le (I \ J) w
  have eqf : ∑ w ∈ J, (oc G J w + ic G J w + 1) = 2 * ∑ w ∈ J, oc G J w + J.card := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← sJ, Finset.sum_const, smul_eq_mul, mul_one]
    omega
  have eqg : ∑ _w ∈ J, J.card = J.card * J.card := by rw [Finset.sum_const, smul_eq_mul]
  have S1 := Finset.sum_le_sum pv1
  rw [eqf, eqg] at S1
  have S2 : ∑ w ∈ J, oc G (I \ J) w ≤ J.card * (6 - J.card) := sum_le_card_mul pv2
  have S3 : J.card * 4 ≤ ∑ w ∈ J, (oc G J w + oc G (I \ J) w + q w) :=
    card_mul_le_sum (fun w hw => by rw [← hsplit]; exact hq w hw)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at S3
  by_cases ha : ∃ w ∈ J, ∃ w' ∈ J, w ≠ w' ∧ G w w' = false ∧ G w' w = false
  · -- two non-adjacent vertices of `J`
    obtain ⟨w, hw, w', hw', hww, g1, g2⟩ := ha
    have pa : ∀ a ∈ J, ∀ b ∈ J, a ≠ b → G a b = false → G b a = false →
        oc G J a + ic G J a + 1 + 1 ≤ J.card := by
      intro a ha b hb hab gab gba
      have han : a < n := Finset.mem_range.mp (hJ ha)
      have h1 := oc_ic_le loopless noShort hJ han (B := (J.erase a).erase b) (fun v hv hG => by
        refine Finset.mem_erase.mpr ⟨?_, Finset.mem_erase.mpr ⟨?_, hv⟩⟩
        · rintro rfl
          rcases hG with h | h
          · rw [gab] at h; exact Bool.false_ne_true h
          · rw [gba] at h; exact Bool.false_ne_true h
        · rintro rfl
          rcases hG with h | h <;> (rw [loopless v han] at h; exact Bool.false_ne_true h))
      rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨Ne.symm hab, hb⟩),
        Finset.card_erase_of_mem ha] at h1
      have h2 : 1 < J.card := Finset.one_lt_card.mpr ⟨a, ha, b, hb, hab⟩
      omega
    have h2 := sum_add_two_le (f := fun x => oc G J x + ic G J x + 1) (g := fun _ => J.card) pv1 hw hw' hww
      (pa w hw w' hw' hww g1 g2) (pa w' hw' w hw (Ne.symm hww) g2 g1)
    rw [eqf, eqg] at h2
    omega
  · by_cases hb : ∃ w ∈ J, ∃ h ∈ I \ J, G w h = false
    · -- a missing arc from `J` to `I ∖ J`
      obtain ⟨w, hw, h, hh, g⟩ := hb
      have pb : oc G (I \ J) w + 1 ≤ 6 - J.card := by
        have h1 : oc G (I \ J) w ≤ ((I \ J).erase h).card := oc_le_of_sub (fun v hv hG =>
          Finset.mem_erase.mpr ⟨by rintro rfl; rw [g] at hG; exact Bool.false_ne_true hG, hv⟩)
        rw [Finset.card_erase_of_mem hh, hHc] at h1
        have h2 : 1 ≤ (I \ J).card := Finset.card_pos.mpr ⟨h, hh⟩
        omega
      have h2 := sum_add_one_le (f := fun x => oc G (I \ J) x) (g := fun _ => 6 - J.card) pv2 hw pb
      rw [Finset.sum_const, smul_eq_mul] at h2
      omega
    · -- `D[J]` is a tournament and `J → I ∖ J` is complete: the source has `out_I = 5`
      have tour : ∀ a ∈ J, ∀ b ∈ J, a ≠ b → G a b = true ∨ G b a = true := by
        intro a ha' b hb' hab
        by_contra hcon
        apply ha
        refine ⟨a, ha', b, hb', hab, ?_, ?_⟩
        · cases h : G a b
          · rfl
          · exact absurd (Or.inl h) hcon
        · cases h : G b a
          · rfl
          · exact absurd (Or.inr h) hcon
      have comp : ∀ w ∈ J, ∀ h ∈ I \ J, G w h = true := by
        intro w hw h hh
        cases g : G w h
        · exact absurd ⟨w, hw, h, hh, g⟩ hb
        · rfl
      obtain ⟨t, ht, hsrc⟩ := tourn_source loopless noShort hJ hne tour
      have hocJ : J.card - 1 ≤ oc G J t := by
        have hsub : J.erase t ⊆ J.filter (fun v => G t v = true) := by
          intro v hv
          obtain ⟨hvt, hvJ⟩ := Finset.mem_erase.mp hv
          refine Finset.mem_filter.mpr ⟨hvJ, ?_⟩
          rcases tour t ht v hvJ (Ne.symm hvt) with h | h
          · exact h
          · rw [hsrc v hvJ] at h; exact absurd h Bool.false_ne_true
        have := Finset.card_le_card hsub
        rw [Finset.card_erase_of_mem ht] at this
        exact this
      have hocH : oc G (I \ J) t = 6 - J.card := hHc ▸ oc_full (comp t ht)
      have pc : 4 + 1 ≤ oc G J t + oc G (I \ J) t + q t := by omega
      have h2 := sum_add_one_le (f := fun _ => 4) (g := fun x => oc G J x + oc G (I \ J) x + q x)
        (fun x hx => by rw [← hsplit]; exact hq x hx) ht pc
      rw [Finset.sum_const, smul_eq_mul, Finset.sum_add_distrib, Finset.sum_add_distrib] at h2
      omega

/-- If every `M`-head in `I` lies in `J ⊆ I`, a row of `M` has the same heads in `I` as in `J`. -/
theorem oc_I_eq_J {I J M : Finset Nat} (hJI : J ⊆ I) (hMJ : ∀ m ∈ M, ∀ w ∈ I, G m w = true → w ∈ J)
    {m : Nat} (hm : m ∈ M) : oc G I m = oc G J m := by
  rw [oc_sdiff hJI m]
  have : oc G (I \ J) m = 0 := oc_eq_zero (fun w hw => by
    cases h : G m w
    · rfl
    · exact absurd (hMJ m hm w (Finset.mem_sdiff.mp hw).1 h) (Finset.mem_sdiff.mp hw).2)
  omega

end generic

namespace Root

variable {G : CH.Digraph} {u : Nat} {I O M : Finset Nat} (R : Root G u I O M)
include R

/-- Rows of `M` must spend their out-degree in `J ∪ M`; `J`-rows see `M` without digons. -/
theorem lemmaYZ {J : Finset Nat} (hJI : J ⊆ I) (hMO : ∀ m ∈ M, ∀ x ∈ O, G m x = false)
    (hMJ : ∀ m ∈ M, ∀ w ∈ I, G m w = true → w ∈ J) :
    20 + ∑ w ∈ J, oc G M w ≤ 4 * J.card + ∑ m ∈ M, oc G M m := by
  have hY : ∀ m ∈ M, 5 ≤ oc G J m + oc G M m := by
    intro m hm
    have h1 := R.M_out hm
    have h2 : oc G O m = 0 := oc_eq_zero (hMO m hm)
    have h3 := oc_I_eq_J (G := G) hJI hMJ hm
    omega
  have sY := card_mul_le_sum hY
  rw [Finset.sum_add_distrib, R.cM, swap G M J] at sY
  have hZ : ∀ w ∈ J, ic G M w + oc G M w ≤ 4 := by
    intro w hw
    have := oc_ic_le R.H.loopless R.H.noShort R.subM (R.ltI (hJI hw)) (B := M) (fun v hv _ => hv)
    rw [R.cM] at this
    omega
  have sZ := sum_le_card_mul hZ
  rw [Finset.sum_add_distrib] at sZ
  omega

/-- The budget (2.2) restricted to `J ⊆ I`. -/
theorem budgetJ {J : Finset Nat} (hJI : J ⊆ I) :
    ∑ w ∈ J, oc G M w + ∑ m ∈ M, ic G O m + ∑ m ∈ M, oc G M m ≤ 24 := by
  have h1 := R.budget
  have h2 : ∑ w ∈ J, oc G M w ≤ ∑ m ∈ M, ic G I m := by
    rw [← swap G I M]
    exact Finset.sum_le_sum_of_subset hJI
  have h3 : ∑ m ∈ M, oc G M m = ∑ m ∈ M, ic G M m := swap G M M
  omega

end Root

end LeanCH.BR.BR35
