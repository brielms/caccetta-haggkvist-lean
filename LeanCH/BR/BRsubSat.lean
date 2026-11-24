import LeanCH.BR.BR45Sat

/-!
# Saturation for every `q` (Lemma 1 of the sub-diagonal note), Lean 4.35.0

Paper: `checkpoints/boundary_20261111/BRsubdiag_attempt_subagent.md` §1 (Lemma 1). Generalises
`LeanCH/BR/BR45Sat.lean` (which is the case `q = 4`) to arbitrary `q`.

`Sat q E V`: for `v, w ∈ V` with `w ↛ v`, `w ∈ B_{q-1}(v)`. For a `q`-free `E` this is exactly "adding any non-arc
`w → v` between distinct vertices closes a cycle of length `≤ q`" (`qfree_insertQ` is the converse direction used for
maximality; the forward direction is the cut at the first use of the new arc).

* `exists_satQ` (**Lemma 1(a)**, existence): a `q`-free `D` on `V` has a `q`-free saturated supergraph on `V`.
* `br_of_satQ` (**Lemma 1(a)**, reduction): regularity of saturated `(q,s)` boundary graphs gives `BR(q,s)`.
* `inN_eq_of_satQ` (**Lemma 1(b)**): `I(v) = V ∖ B_{q-1}(v)`.
* `sat_d1Q`, `sat_d2Q` (**Lemma 1(c)**): for `r → u`, no in-neighbour of `r` lies in `B_{q-2}(u)`; and if `r ↛ x`
  for some `x ∈ O(u)`, then `r` has an in-neighbour in `B_{q-1}(u) ∖ B_{q-2}(u)` (an `N_{q-1}`-parent).
* `descend`: a vertex of `B_k(u) ∖ B_1(u)` (`k ≥ 2`) is within `k - 2` of some vertex of `N_2(u)`.
-/

set_option linter.style.longLine false

namespace LeanCH.BR.BRsub

open LeanCH.BR.BRq2 LeanCH.BR.BRq3 LeanCH.BR.BR45 CH Compose.Boundary Compose.FloorSix

variable {E : CH.Digraph} {V : Finset ℕ}

/-- Saturation on `V` at cycle bound `q`: every non-arc `w ↛ v` inside `V` has `w ∈ B_{q-1}(v)`. -/
def Sat (q : ℕ) (E : CH.Digraph) (V : Finset ℕ) : Prop :=
  ∀ v ∈ V, ∀ w ∈ V, ¬ E w v = true → w ∈ ball E V v (q - 1)

/-- Adding a non-arc `w → v` with `w ∉ B_{q-1}(v)` keeps the digraph `q`-free. -/
theorem qfree_insertQ {E E' : CH.Digraph} {q w v : ℕ} (hfree : QFree E V q) (hw : w ∈ V)
    (hE' : ∀ a b, E' a b = true → E a b = true ∨ (a = w ∧ b = v)) (hnot : w ∉ ball E V v (q - 1)) :
    QFree E' V q := by
  intro a ℓ h1 hℓ p
  rcases walk_split hE' p with h | ⟨m1, m2, hm, w1, w2⟩
  · exact hfree a ℓ h1 hℓ h
  · rcases walk_split hE' w2 with h | ⟨m3, m4, hm', w3, _⟩
    · exact hnot (mem_ball.mpr ⟨hw, m2 + m1, by omega, h.append w1⟩)
    · exact hnot (mem_ball.mpr ⟨hw, m3, by omega, w3⟩)

/-- **Lemma 1(a), existence.** A `q`-free digraph on `V` has a saturated `q`-free supergraph on `V`. -/
theorem exists_satQ {q : ℕ} {D : CH.Digraph} (hfree : QFree D V q) :
    ∃ E : CH.Digraph, (∀ a ∈ V, ∀ b ∈ V, D a b = true → E a b = true) ∧ QFree E V q ∧ Sat q E V := by
  classical
  let 𝒜 : Finset (Finset (ℕ × ℕ)) := (V ×ˢ V).powerset.filter
    (fun A => (∀ a ∈ V, ∀ b ∈ V, D a b = true → (a, b) ∈ A) ∧ QFree (gr A) V q)
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
  have hfree' : QFree (gr (insert (w, v) A)) V q := by
    refine qfree_insertQ hAfree hw (fun a b h => ?_) hball
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

/-- **Lemma 1(b).** In a saturated `q`-free digraph, `I(v) = V ∖ B_{q-1}(v)`. -/
theorem inN_eq_of_satQ {q : ℕ} (hq : 1 ≤ q) (hfree : QFree E V q) (hsat : Sat q E V) {v : ℕ} (hv : v ∈ V) :
    inN E V v = V \ ball E V v (q - 1) := by
  ext w
  rw [mem_inN, Finset.mem_sdiff]
  constructor
  · rintro ⟨hw, hwv⟩
    exact ⟨hw, fun hb => no_back_arc hfree hv hb (by omega) hwv⟩
  · rintro ⟨hw, hb⟩
    exact ⟨hw, by_contra (fun h => hb (hsat v hv w hw h))⟩

theorem card_inN_of_satQ {q : ℕ} (hq : 1 ≤ q) (hfree : QFree E V q) (hsat : Sat q E V) {v : ℕ} (hv : v ∈ V) :
    (inN E V v).card + (ball E V v (q - 1)).card = V.card := by
  rw [inN_eq_of_satQ hq hfree hsat hv, Finset.card_sdiff_of_subset ball_subset]
  have := Finset.card_le_card (ball_subset (D := E) (W := V) (u := v) (k := q - 1))
  omega

/-- **Lemma 1(c), first half.** For `r → u`, no in-neighbour of `r` lies in `B_{q-2}(u)`. -/
theorem sat_d1Q {q : ℕ} (hq : 2 ≤ q) (hfree : QFree E V q) {u r p : ℕ} (hu : u ∈ V) (hr : r ∈ inN E V u)
    (hp : p ∈ inN E V r) : p ∉ ball E V u (q - 2) := by
  intro hb
  obtain ⟨hrV, hru⟩ := mem_inN.mp hr
  exact no_back_arc hfree hu (ball_step hb hrV (mem_inN.mp hp).2) (by omega) hru

/-- **Lemma 1(c), second half.** For `r → u` and `x ∈ O(u)` with `r ↛ x`, `r` has an in-neighbour in
`B_{q-1}(u) ∖ B_{q-2}(u)`. -/
theorem sat_d2Q {q : ℕ} (hq : 2 ≤ q) (hfree : QFree E V q) (hsat : Sat q E V) {u r x : ℕ} (hu : u ∈ V)
    (hr : r ∈ inN E V u) (hx : x ∈ outN E V u) (hrx : ¬ E r x = true) :
    ∃ p ∈ inN E V r, p ∈ ball E V u (q - 1) ∧ p ∉ ball E V u (q - 2) := by
  obtain ⟨hrV, hru⟩ := mem_inN.mp hr
  obtain ⟨hxV, hux⟩ := mem_outN.mp hx
  have hb := hsat x hxV r hrV hrx
  have e1 : q - 1 = q - 2 + 1 := by omega
  rw [e1] at hb
  have hne : r ≠ x := by
    rintro rfl
    exact digonfree hfree hq hu hrV hux hru
  obtain ⟨p, hp, hpr⟩ := exists_pred hxV hb hne
  have hpin : p ∈ inN E V r := mem_inN.mpr ⟨ball_subset hp, hpr⟩
  have hpu := ball_trans (ball_of_adj hxV hux) hp
  have e2 : 1 + (q - 2) = q - 1 := by omega
  rw [e2] at hpu
  exact ⟨p, hpin, hpu, sat_d1Q hq hfree hu hr hpin⟩

/-- A vertex of `B_k(u) ∖ B_1(u)`, `k ≥ 2`, is within `k - 2` of some vertex of `N_2(u) = B_2(u) ∖ B_1(u)`. -/
theorem descend {u : ℕ} (hu : u ∈ V) : ∀ k, 2 ≤ k → ∀ p, p ∈ ball E V u k → p ∉ ball E V u 1 →
    ∃ y, y ∈ ball E V u 2 ∧ y ∉ ball E V u 1 ∧ p ∈ ball E V y (k - 2) := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
    intro p hp hp1
    exact ⟨p, hp, hp1, self_mem_ball (ball_subset hp)⟩
  | succ k hk ih =>
    intro p hp hp1
    by_cases hpk : p ∈ ball E V u k
    · obtain ⟨y, hy2, hy1, hpy⟩ := ih p hpk hp1
      exact ⟨y, hy2, hy1, ball_mono_radius (by omega) hpy⟩
    · obtain ⟨y', hy', hy'p⟩ := ball_succ_pred hu hp hpk
      have hy'1 : y' ∉ ball E V u 1 := by
        intro h
        exact hpk (ball_mono_radius hk (ball_step h (ball_subset hp) hy'p))
      obtain ⟨y, hy2, hy1, hy'y⟩ := ih y' hy' hy'1
      have h := ball_step hy'y (ball_subset hp) hy'p
      have e : k + 1 - 2 = k - 2 + 1 := by omega
      rw [e]
      exact ⟨y, hy2, hy1, h⟩

/-- If `x` heads every vertex of `N_2(u)`, then `x` reaches every vertex of `B_j(u) ∖ B_1(u)` within `j - 1`. -/
theorem reach_of_heads {u x j z : ℕ} (hu : u ∈ V)
    (hxY : ∀ y ∈ ball E V u 2, y ∉ ball E V u 1 → E x y = true) (hj : 2 ≤ j)
    (hz : z ∈ ball E V u j) (hz1 : z ∉ ball E V u 1) : z ∈ ball E V x (j - 1) := by
  obtain ⟨y, hy2, hy1, hzy⟩ := descend hu j hj z hz hz1
  have h := ball_trans (ball_of_adj (ball_subset hy2) (hxY y hy2 hy1)) hzy
  have e : 1 + (j - 2) = j - 1 := by omega
  rw [e] at h
  exact h

/-- **Lemma 1(a), reduction.** Regularity of saturated `(q,s)` boundary graphs gives `BR(q,s)`. -/
theorem br_of_satQ {q s : ℕ}
    (h : ∀ E : CH.Digraph, QFree E (Finset.range (q * s + 1)) q →
      (∀ v ∈ Finset.range (q * s + 1), s ≤ (outN E (Finset.range (q * s + 1)) v).card) →
      Sat q E (Finset.range (q * s + 1)) →
      ∀ v ∈ Finset.range (q * s + 1), (inN E (Finset.range (q * s + 1)) v).card = s) :
    BoundaryRegular q s := by
  intro G loopless deg noShort
  classical
  set n := q * s + 1 with hn
  have hfree : QFree G (Finset.range n) q := qfree_of_noShort loopless noShort
  have hout : ∀ v ∈ Finset.range n, s ≤ (outN G (Finset.range n) v).card :=
    fun v hv => out_card deg (Finset.mem_range.mp hv)
  obtain ⟨E, hsub, hEfree, hsat⟩ := exists_satQ hfree
  have hsubN : ∀ v ∈ Finset.range n, outN G (Finset.range n) v ⊆ outN E (Finset.range n) v :=
    fun v hv z hz => mem_outN.mpr ⟨(mem_outN.mp hz).1, hsub v hv z (mem_outN.mp hz).1 (mem_outN.mp hz).2⟩
  have hEout : ∀ v ∈ Finset.range n, s ≤ (outN E (Finset.range n) v).card :=
    fun v hv => (hout v hv).trans (Finset.card_le_card (hsubN v hv))
  have hin := h E hEfree hEout hsat
  have hsum : ∑ y ∈ Finset.range n, (outN E (Finset.range n) y).card =
      ∑ z ∈ Finset.range n, (inN E (Finset.range n) z).card :=
    Compose.ThinRigid.sum_out_eq_sum_in E (Finset.range n)
  have heq : ∑ _y ∈ Finset.range n, s = ∑ y ∈ Finset.range n, (outN E (Finset.range n) y).card := by
    rw [hsum]
    exact (Finset.sum_congr rfl hin).symm
  have hEs : ∀ v ∈ Finset.range n, (outN E (Finset.range n) v).card = s :=
    fun v hv => ((Finset.sum_eq_sum_iff_of_le hEout).mp heq v hv).symm
  have hNeq : ∀ v ∈ Finset.range n, outN G (Finset.range n) v = outN E (Finset.range n) v :=
    fun v hv => Finset.eq_of_subset_of_card_le (hsubN v hv) (by rw [hEs v hv]; exact hout v hv)
  intro v hv
  have hvV : v ∈ Finset.range n := Finset.mem_range.mpr hv
  have hpar : par G n v = inN E (Finset.range n) v := by
    ext w
    change w ∈ (Finset.range n).filter (fun u => G u v = true) ↔ w ∈ inN E (Finset.range n) v
    rw [Finset.mem_filter, mem_inN]
    constructor
    · rintro ⟨hw, hwv⟩
      exact ⟨hw, hsub w hw v hvV hwv⟩
    · rintro ⟨hw, hwv⟩
      have hmem : v ∈ outN G (Finset.range n) w := by
        rw [hNeq w hw]
        exact mem_outN.mpr ⟨hvV, hwv⟩
      exact ⟨hw, (mem_outN.mp hmem).2⟩
  rw [hpar]
  exact hin v hvV

end LeanCH.BR.BRsub
