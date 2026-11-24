import LeanCH.BR.BR45Base

/-!
# BR(4,5), Lemma 1: saturation (Lean 4.35.0)

Paper: `checkpoints/boundary_20261111/BR45_attempt_subagent.md` §1 (Lemma 1), audited in `BR45_audit_subagent.md` §1.

`Sat E V`: for `v, w ∈ V` with `w ↛ v`, `w ∈ B_3(v)`. (Adding the non-arc `w → v` would close a cycle of length
`≤ 4`; this is the consequence of maximality that the proof uses.)

* `exists_sat` (**Lemma 1(a)**, existence): a `4`-free `D` on `V` has a `4`-free saturated supergraph on `V`
  (an arc set `A ⊆ V × V` of maximal size; if `w ↛ v` and `w ∉ B_3(v)` then `A + (w,v)` is still `4`-free by
  `qfree_insert`, which cuts a closed walk at its first use of the new arc, twice).
* `br45_of_sat` (**Lemma 1(a)**, reduction): if every saturated `4`-free digraph on `range 21` with min out `≥ 5` has
  every in-degree `5`, then `BR(4,5)` holds.
* `inN_eq_of_sat` (**Lemma 1(b)**): `I(v) = V ∖ B_3(v)` in a saturated `4`-free digraph.
* `sat_d1`, `sat_d2` (**Lemma 1(d)**): for `r → u`, no in-neighbour of `r` lies in `B_2(u)`; and if `r ↛ x` for some
  `x ∈ O(u)`, then `r` has an in-neighbour in `B_3(u) ∖ B_2(u)`.
-/

set_option linter.style.longLine false

namespace LeanCH.BR.BR45

open LeanCH.BR.BRq2 LeanCH.BR.BRq3 CH Compose.Boundary Compose.FloorSix

variable {E : CH.Digraph} {V : Finset ℕ}

/-- Saturation on `V` at `q = 4`: every non-arc `w ↛ v` inside `V` has `w ∈ B_3(v)`. -/
def Sat (E : CH.Digraph) (V : Finset ℕ) : Prop :=
  ∀ v ∈ V, ∀ w ∈ V, ¬ E w v = true → w ∈ ball E V v 3

/-- A walk in `E + (w,v)` is a walk in `E`, or splits at its first use of the new arc. -/
theorem walk_split {E E' : CH.Digraph} {w v : ℕ}
    (hE' : ∀ a b, E' a b = true → E a b = true ∨ (a = w ∧ b = v)) {a b m : ℕ} (p : Walk E' V a b m) :
    Walk E V a b m ∨ ∃ m1 m2, m1 + 1 + m2 = m ∧ Walk E V a w m1 ∧ Walk E' V v b m2 := by
  induction p with
  | refl a => exact Or.inl (.refl a)
  | @step a c b k hc hac rest ih =>
    rcases hE' a c hac with h | ⟨h1, h2⟩
    · rcases ih with h' | ⟨m1, m2, hm, w1, w2⟩
      · exact Or.inl (.step hc h h')
      · exact Or.inr ⟨m1 + 1, m2, by omega, .step hc h w1, w2⟩
    · subst h1 h2
      exact Or.inr ⟨0, k, by omega, .refl _, rest⟩

/-- Adding a non-arc `w → v` with `w ∉ B_3(v)` keeps the digraph `4`-free. -/
theorem qfree_insert {E E' : CH.Digraph} {w v : ℕ} (hfree : QFree E V 4) (hw : w ∈ V)
    (hE' : ∀ a b, E' a b = true → E a b = true ∨ (a = w ∧ b = v)) (hnot : w ∉ ball E V v 3) :
    QFree E' V 4 := by
  intro a ℓ h1 h4 p
  rcases walk_split hE' p with h | ⟨m1, m2, hm, w1, w2⟩
  · exact hfree a ℓ h1 h4 h
  · rcases walk_split hE' w2 with h | ⟨m3, m4, hm', w3, _⟩
    · exact hnot (mem_ball.mpr ⟨hw, m2 + m1, by omega, h.append w1⟩)
    · exact hnot (mem_ball.mpr ⟨hw, m3, by omega, w3⟩)

/-- The digraph of an arc set. -/
def gr (A : Finset (ℕ × ℕ)) : CH.Digraph := fun a b => decide ((a, b) ∈ A)

/-- **Lemma 1(a), existence.** A `4`-free digraph on `V` has a saturated `4`-free supergraph on `V`. -/
theorem exists_sat {D : CH.Digraph} (hfree : QFree D V 4) :
    ∃ E : CH.Digraph, (∀ a ∈ V, ∀ b ∈ V, D a b = true → E a b = true) ∧ QFree E V 4 ∧ Sat E V := by
  classical
  let 𝒜 : Finset (Finset (ℕ × ℕ)) := (V ×ˢ V).powerset.filter
    (fun A => (∀ a ∈ V, ∀ b ∈ V, D a b = true → (a, b) ∈ A) ∧ QFree (gr A) V 4)
  have hne : 𝒜.Nonempty := by
    refine ⟨(V ×ˢ V).filter (fun p => D p.1 p.2 = true), Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr (Finset.filter_subset _ _), ?_, ?_⟩⟩
    · intro a ha b hb h
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha, hb⟩, h⟩
    · refine qfree_sub (fun a b h => ?_) hfree
      exact (Finset.mem_filter.mp (of_decide_eq_true h)).2
  obtain ⟨A, hA, hmax⟩ := Finset.exists_max_image 𝒜 Finset.card hne
  obtain ⟨hAsub, hAD, hAfree⟩ := Finset.mem_filter.mp hA
  refine ⟨gr A, fun a ha b hb h => decide_eq_true (hAD a ha b hb h), hAfree, ?_⟩
  intro v hv w hw hnot
  by_contra hball
  have hnA : (w, v) ∉ A := fun h => hnot (decide_eq_true h)
  have hfree' : QFree (gr (insert (w, v) A)) V 4 := by
    refine qfree_insert hAfree hw (fun a b h => ?_) hball
    rcases Finset.mem_insert.mp (of_decide_eq_true h) with h | h
    · right
      exact ⟨(Prod.mk.inj h).1, (Prod.mk.inj h).2⟩
    · left
      exact decide_eq_true h
  have hmem : insert (w, v) A ∈ 𝒜 := Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr (Finset.insert_subset (Finset.mem_product.mpr ⟨hw, hv⟩)
      (Finset.mem_powerset.mp hAsub)),
      fun a ha b hb h => Finset.mem_insert_of_mem (hAD a ha b hb h), hfree'⟩
  have := hmax _ hmem
  rw [Finset.card_insert_of_notMem hnA] at this
  omega

/-- **Lemma 1(b).** In a saturated `4`-free digraph, `I(v) = V ∖ B_3(v)`. -/
theorem inN_eq_of_sat (hfree : QFree E V 4) (hsat : Sat E V) {v : ℕ} (hv : v ∈ V) :
    inN E V v = V \ ball E V v 3 := by
  ext w
  rw [mem_inN, Finset.mem_sdiff]
  constructor
  · rintro ⟨hw, hwv⟩
    exact ⟨hw, fun hb => no_back_arc hfree hv hb (by omega) hwv⟩
  · rintro ⟨hw, hb⟩
    exact ⟨hw, by_contra (fun h => hb (hsat v hv w hw h))⟩

theorem card_inN_of_sat (hfree : QFree E V 4) (hsat : Sat E V) {v : ℕ} (hv : v ∈ V) :
    (inN E V v).card + (ball E V v 3).card = V.card := by
  rw [inN_eq_of_sat hfree hsat hv, Finset.card_sdiff_of_subset ball_subset]
  have := Finset.card_le_card (ball_subset (D := E) (W := V) (u := v) (k := 3))
  omega

/-- **Lemma 1(d), first half.** For `r → u`, no in-neighbour of `r` lies in `B_2(u)`. -/
theorem sat_d1 (hfree : QFree E V 4) {u r p : ℕ} (hu : u ∈ V) (hr : r ∈ inN E V u)
    (hp : p ∈ inN E V r) : p ∉ ball E V u 2 := by
  intro hb
  obtain ⟨hrV, hru⟩ := mem_inN.mp hr
  exact no_back_arc hfree hu (ball_step hb hrV (mem_inN.mp hp).2) (by omega) hru

/-- **Lemma 1(d), second half.** For `r → u` and `x ∈ O(u)` with `r ↛ x`, `r` has an in-neighbour in
`B_3(u) ∖ B_2(u)`. -/
theorem sat_d2 (hfree : QFree E V 4) (hsat : Sat E V) {u r x : ℕ} (hu : u ∈ V) (hr : r ∈ inN E V u)
    (hx : x ∈ outN E V u) (hrx : ¬ E r x = true) :
    ∃ p ∈ inN E V r, p ∈ ball E V u 3 ∧ p ∉ ball E V u 2 := by
  obtain ⟨hrV, hru⟩ := mem_inN.mp hr
  obtain ⟨hxV, hux⟩ := mem_outN.mp hx
  have hb := hsat x hxV r hrV hrx
  have hne : r ≠ x := by
    rintro rfl
    exact n2 hfree hu hrV hux hru
  obtain ⟨p, hp, hpr⟩ := exists_pred (j := 2) hxV hb hne
  have hpin : p ∈ inN E V r := mem_inN.mpr ⟨ball_subset hp, hpr⟩
  exact ⟨p, hpin, ball_trans (ball_of_adj hxV hux) hp, sat_d1 hfree hu hr hpin⟩

/-- **Lemma 1(a), reduction.** Regularity of saturated boundary graphs gives `BR(4,5)`. -/
theorem br45_of_sat
    (h : ∀ E : CH.Digraph, QFree E (Finset.range 21) 4 →
      (∀ v ∈ Finset.range 21, 5 ≤ (outN E (Finset.range 21) v).card) → Sat E (Finset.range 21) →
      ∀ v ∈ Finset.range 21, (inN E (Finset.range 21) v).card = 5) :
    BoundaryRegular 4 5 := by
  intro G loopless deg noShort
  classical
  have loopless' : CH.Loopless G 21 := loopless
  have deg' : CH.MinOutdegreeAtLeast G 21 5 := deg
  have noShort' : ¬ CH.HasDirectedCycleAtMost G 21 4 := noShort
  have hfree : QFree G (Finset.range 21) 4 := qfree_of_noShort loopless' noShort'
  have hout : ∀ v ∈ Finset.range 21, 5 ≤ (outN G (Finset.range 21) v).card :=
    fun v hv => out_card deg' (Finset.mem_range.mp hv)
  obtain ⟨E, hsub, hEfree, hsat⟩ := exists_sat hfree
  have hsubN : ∀ v ∈ Finset.range 21, outN G (Finset.range 21) v ⊆ outN E (Finset.range 21) v :=
    fun v hv z hz => mem_outN.mpr ⟨(mem_outN.mp hz).1, hsub v hv z (mem_outN.mp hz).1 (mem_outN.mp hz).2⟩
  have hEout : ∀ v ∈ Finset.range 21, 5 ≤ (outN E (Finset.range 21) v).card :=
    fun v hv => (hout v hv).trans (Finset.card_le_card (hsubN v hv))
  have hin := h E hEfree hEout hsat
  have hsum : ∑ y ∈ Finset.range 21, (outN E (Finset.range 21) y).card =
      ∑ z ∈ Finset.range 21, (inN E (Finset.range 21) z).card :=
    Compose.ThinRigid.sum_out_eq_sum_in E (Finset.range 21)
  have heq : ∑ _y ∈ Finset.range 21, 5 = ∑ y ∈ Finset.range 21, (outN E (Finset.range 21) y).card := by
    rw [hsum]
    exact (Finset.sum_congr rfl hin).symm
  have hE5 : ∀ v ∈ Finset.range 21, (outN E (Finset.range 21) v).card = 5 :=
    fun v hv => ((Finset.sum_eq_sum_iff_of_le hEout).mp heq v hv).symm
  have hNeq : ∀ v ∈ Finset.range 21, outN G (Finset.range 21) v = outN E (Finset.range 21) v :=
    fun v hv => Finset.eq_of_subset_of_card_le (hsubN v hv) (by rw [hE5 v hv]; exact hout v hv)
  intro v hv
  have hv' : v < 21 := hv
  have hvV : v ∈ Finset.range 21 := Finset.mem_range.mpr hv'
  have hpar : par G (4 * 5 + 1) v = inN E (Finset.range 21) v := by
    ext w
    change w ∈ (Finset.range 21).filter (fun u => G u v = true) ↔ w ∈ inN E (Finset.range 21) v
    rw [Finset.mem_filter, mem_inN]
    constructor
    · rintro ⟨hw, hwv⟩
      exact ⟨hw, hsub w hw v hvV hwv⟩
    · rintro ⟨hw, hwv⟩
      have hmem : v ∈ outN G (Finset.range 21) w := by
        rw [hNeq w hw]
        exact mem_outN.mpr ⟨hvV, hwv⟩
      exact ⟨hw, (mem_outN.mp hmem).2⟩
  rw [hpar]
  exact hin v hvV

end LeanCH.BR.BR45
