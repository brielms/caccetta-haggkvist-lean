import LeanCH.BR.BR36Local
import LeanCH.BR.BR35
import LeanCH.BR.Reduce

/-!
# BR(3,6), part 2: reduction to saturated graphs (Lean 4.35.0)

Paper source: `BR36_attempt_subagent.md`, Lemma 5.0 (audited), in a direct unweighted form.

`br_six_of`: if no saturated boundary graph at `s = 6` (structure `Hyp`) has a vertex of in-degree 7, then
`BoundaryRegular 3 6`.

Proof: strong induction on the number of non-arcs. If some non-adjacent pair `a, b` has no path `a → z → b`, then
adding the arc `b → a` creates no loop, digon or triangle (`short_cases`), the supergraph is regular by induction,
and in-degrees can only drop, so the degree sum `Σ in = Σ out ≥ 114` forces regularity. Otherwise the graph is
saturated; the strict cap (`StrictCap.strict_cap`, with `BR(3,1..5)`) gives `in ≤ 7` and `in = 7 ⇒ out = 6`, the
hypothesis excludes in-degree 7, and the degree sum again forces every in-degree to be 6.
-/

namespace LeanCH.BR.BR36

open CH Compose.Boundary Compose.FloorSix
open LeanCH.BR.BR35 hiding V Hyp Root root_of

/-- A cycle of length at most 3 is a digon or a triangle. -/
theorem short_cases {G : CH.Digraph} {n : Nat} (h : CH.HasDirectedCycleAtMost G n 3) :
    (∃ a b, a < n ∧ b < n ∧ G a b = true ∧ G b a = true) ∨
      (∃ a b c, a < n ∧ b < n ∧ c < n ∧ G a b = true ∧ G b c = true ∧ G c a = true) := by
  obtain ⟨l, hc, hlen⟩ := h
  match l, hc, hlen with
  | [], hc, _ => exact hc.elim
  | [_], hc, _ => exact (hc.1 rfl).elim
  | [a, b], hc, _ =>
    left
    obtain ⟨_, _, hlt, he, hcl⟩ := hc
    exact ⟨a, b, hlt a (by simp), hlt b (by simp), he.1, by simpa using hcl⟩
  | [a, b, c], hc, _ =>
    right
    obtain ⟨_, _, hlt, he, hcl⟩ := hc
    exact ⟨a, b, c, hlt a (by simp), hlt b (by simp), hlt c (by simp), he.1, he.2.1, by simpa using hcl⟩
  | _ :: _ :: _ :: _ :: _, _, hlen => exact absurd hlen (by simp)

/-- No loop, digon or triangle gives no short cycle. -/
theorem noShort_of {G : CH.Digraph} {n : Nat}
    (h2 : ∀ a b, a < n → b < n → G a b = true → G b a = true → False)
    (h3 : ∀ a b c, a < n → b < n → c < n → G a b = true → G b c = true → G c a = true → False) :
    ¬ CH.HasDirectedCycleAtMost G n 3 := by
  intro h
  rcases short_cases h with ⟨a, b, ha, hb, e1, e2⟩ | ⟨a, b, c, ha, hb, hc, e1, e2, e3⟩
  · exact h2 a b ha hb e1 e2
  · exact h3 a b c ha hb hc e1 e2 e3

theorem minOut_mono {G G' : CH.Digraph} {n r : Nat} (sub : ∀ x y, G x y = true → G' x y = true)
    (h : CH.MinOutdegreeAtLeast G n r) : CH.MinOutdegreeAtLeast G' n r := by
  intro v hv
  obtain ⟨l, hlen, hnd, hmem⟩ := h v hv
  exact ⟨l, hlen, hnd, fun w hw => ⟨(hmem w hw).1, sub v w (hmem w hw).2⟩⟩

/-- In-degree at most 6 everywhere and minimum out-degree 6 force in-degree exactly 6. -/
theorem reg_of_le {G : CH.Digraph} (deg : CH.MinOutdegreeAtLeast G 19 6)
    (hle : ∀ v, v < 19 → ic G V v ≤ 6) : ∀ v, v < 19 → ic G V v = 6 := by
  have hle' : ∀ v ∈ Finset.range 19, ic G V v ≤ 6 := fun v hv => hle v (Finset.mem_range.mp hv)
  have hge : ∑ _v ∈ Finset.range 19, 6 ≤ ∑ v ∈ Finset.range 19, ic G V v :=
    calc ∑ _v ∈ Finset.range 19, 6
        ≤ ∑ x ∈ Finset.range 19, ((Finset.range 19).filter (fun w => G x w = true)).card :=
          Finset.sum_le_sum (fun x hx => out_card deg (Finset.mem_range.mp hx))
      _ = ∑ v ∈ Finset.range 19, ((Finset.range 19).filter (fun u => G u v = true)).card :=
          Compose.ThinRigid.sum_out_eq_sum_in G _
      _ = ∑ v ∈ Finset.range 19, ic G V v := rfl
  have heq := le_antisymm (Finset.sum_le_sum hle') hge
  have each := (Finset.sum_eq_sum_iff_of_le hle').mp heq
  intro v hv
  exact each v (Finset.mem_range.mpr hv)

theorem brs6 : ∀ t, 1 ≤ t → t < 6 → BoundaryRegular 3 t := fun t h1 h2 => by
  rcases (by omega : t = 1 ∨ t = 2 ∨ t = 3 ∨ t = 4 ∨ t = 5) with rfl | rfl | rfl | rfl | rfl
  · exact LeanCH.BR.SmallBR.br_one
  · exact LeanCH.BR.SmallBR.br_two
  · exact LeanCH.BR.SmallBR.br_three
  · exact LeanCH.BR.BR34.br_four
  · exact LeanCH.BR.BR35.br_five

/-- **Reduction.** -/
theorem br_six_of (main : ∀ G : CH.Digraph, Hyp G → ∀ u, u < 19 → ic G V u = 7 → False) :
    BoundaryRegular 3 6 := by
  classical
  suffices key : ∀ (k : Nat) (G : CH.Digraph), LeanCH.BR.Reduce.miss G 19 = k → CH.Loopless G 19 →
      CH.MinOutdegreeAtLeast G 19 6 → ¬ CH.HasDirectedCycleAtMost G 19 3 → ∀ v, v < 19 → ic G V v = 6 by
    intro G loopless deg noShort v hv
    exact key _ G rfl loopless deg noShort v hv
  intro k
  induction k using Nat.strong_induction_on with
  | _ k IH =>
  intro G hk loopless deg noShort
  have cap : ∀ v, v < 19 → 6 ≤ ic G V v → 3 * (ic G V v - 6) + 2 * (oc G V v - 6) + 2 ≤ 6 :=
    fun v hv hin => LeanCH.BR.StrictCap.strict_cap (s := 6) (by omega) brs6 loopless deg noShort hv hin
  by_cases hsat : ∀ a b, a < 19 → b < 19 → a ≠ b → G a b = false → G b a = false →
      ∃ z, z < 19 ∧ G a z = true ∧ G z b = true
  · have H : Hyp G :=
      { loopless := loopless
        deg := deg
        noShort := noShort
        cap := fun v hv => by
          by_contra h
          have := cap v hv (by omega)
          omega
        cap7 := fun v hv h7 => by
          have := cap v hv (by omega)
          have := out_card deg hv
          change 6 ≤ oc G V v at this
          omega
        sat := hsat }
    apply reg_of_le deg
    intro v hv
    have h1 := H.cap v hv
    by_contra h2
    exact main G H v hv (by omega)
  · push Not at hsat
    obtain ⟨a, b, ha, hb, hab, gab, gba, hno⟩ := hsat
    have hno' : ∀ z, z < 19 → G a z = true → G z b = false := fun z hz h => by simpa using hno z hz h
    -- add the arc `b → a`
    set G' := LeanCH.BR.Reduce.addArc G b a with hG'
    have arc : ∀ x y, G' x y = true → (x = b ∧ y = a) ∨ G x y = true := by
      intro x y h
      simp only [hG', LeanCH.BR.Reduce.addArc] at h
      split_ifs at h with hxy
      · exact Or.inl hxy
      · exact Or.inr h
    have N2 := fun {x y : Nat} => @no2 G 19 loopless noShort x y
    have N3 := fun {x y z : Nat} => @no3 G 19 loopless noShort x y z
    have loop' : CH.Loopless G' 19 := by
      intro w hw
      have : ¬ (w = b ∧ w = a) := fun h => hab (h.2.symm.trans h.1)
      simp only [hG', LeanCH.BR.Reduce.addArc, this]; exact loopless w hw
    have short' : ¬ CH.HasDirectedCycleAtMost G' 19 3 := by
      apply noShort_of
      · intro x y hx hy e1 e2
        rcases arc x y e1 with ⟨h1, h2⟩ | e1
        · rw [h1, h2] at e2
          rcases arc a b e2 with ⟨h, _⟩ | e2
          · exact hab h
          · rw [gab] at e2; exact Bool.false_ne_true e2
        · rcases arc y x e2 with ⟨h1, h2⟩ | e2
          · rw [h1, h2, gab] at e1; exact Bool.false_ne_true e1
          · exact N2 hx hy e1 e2
      · intro x y z hx hy hz e1 e2 e3
        rcases arc x y e1 with ⟨h1, h2⟩ | e1
        · rw [h2] at e2
          rw [h1] at e3
          have e2' : G a z = true := by
            rcases arc a z e2 with ⟨h, _⟩ | e2
            · exact absurd h hab
            · exact e2
          have e3' : G z b = true := by
            rcases arc z b e3 with ⟨_, h⟩ | e3
            · exact absurd h.symm hab
            · exact e3
          rw [hno' z hz e2'] at e3'; exact Bool.false_ne_true e3'
        · rcases arc y z e2 with ⟨h1, h2⟩ | e2
          · rw [h2] at e3
            rw [h1] at e1
            have e3' : G a x = true := by
              rcases arc a x e3 with ⟨h, _⟩ | e3
              · exact absurd h hab
              · exact e3
            rw [hno' x hx e3'] at e1; exact Bool.false_ne_true e1
          · rcases arc z x e3 with ⟨h1, h2⟩ | e3
            · rw [h2] at e1
              rw [h1] at e2
              rw [hno' y hy e1] at e2; exact Bool.false_ne_true e2
            · exact N3 hx hy hz e1 e2 e3
    have deg' := minOut_mono (LeanCH.BR.Reduce.addArc_ge G b a) deg
    have hlt := LeanCH.BR.Reduce.miss_lt hb ha (Ne.symm hab) gba
    have reg' := IH _ (hk ▸ hlt) G' rfl loop' deg' short'
    apply reg_of_le deg
    intro v hv
    rw [← reg' v hv]
    apply Finset.card_le_card
    intro w hw
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hw
    exact Finset.mem_filter.mpr ⟨h1, LeanCH.BR.Reduce.addArc_ge G b a w v h2⟩

end LeanCH.BR.BR36
