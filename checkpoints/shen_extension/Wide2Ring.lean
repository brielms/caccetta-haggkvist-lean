import checkpoints.shen_extension.Wide2Cycle

/-!
# A shortest cycle in a finite set and its windows

`Ring D F C`: `C ⊆ F` carries a closed walk of length `|C|` through all its rows, read
from any row `c` as a sequence `g 0 = c, g 1, …, g |C| = c` (`rot`), and no closed walk
inside `F` is shorter than `|C|` (`short`).

* `exists_ring`: a set `F` with a closed walk has a ring.
* `ring_heads`: a ring is chordless, every row has at most one head on it (`2 ≤ |C|`).
* `ring_children` (window, forward): if `c ∈ C` heads `a ∈ F`, then `a` has at most
  two heads on `C`, namely `g 1` and `g 2` read from `c` (`3 ≤ |C|`).
* `ring_parents` (window, backward): if `a ∈ F` heads `c' ∈ C`, at most two rows of `C`
  head `a`.
* `ring_far`: rows of `C` that `c*` cannot reach along `F` in fewer than `k` steps number
  at most `|C| - k`.

Everything is stated for an arbitrary digraph and arbitrary finite `F`.
-/

namespace LeanCH.BR.Wide2Ring
open Finset BRq2 BRq3

/-- A shortest cycle `C` of `F`. -/
structure Ring (D : CH.Digraph) (F C : Finset ℕ) : Prop where
  sub : C ⊆ F
  pos : 1 ≤ C.card
  rot : ∀ c ∈ C, ∃ g : ℕ → ℕ, g 0 = c ∧ (∀ i < C.card, g (i + 1) ∈ C ∧ D (g i) (g (i + 1)) = true) ∧
    g C.card = c ∧ ∀ c' ∈ C, ∃ t < C.card, g t = c'
  short : ∀ a ℓ, 1 ≤ ℓ → Walk D F a a ℓ → C.card ≤ ℓ

variable {D : CH.Digraph} {F C W : Finset ℕ}

/-- A walk sequence of length `m` in a `q`-free set is injective when `m ≤ q + 1`. -/
theorem fun_inj {f : ℕ → ℕ} {m q : ℕ} (free : QFree D W q) (le : m ≤ q + 1)
    (he : ∀ k, k < m → f (k + 1) ∈ W ∧ D (f k) (f (k + 1)) = true) :
    Set.InjOn f (range m) := by
  intro i hi j hj heq
  simp only [coe_range, Set.mem_Iio] at hi hj
  by_contra hn
  rcases Nat.lt_or_gt_of_ne hn with hij | hji
  · have wc := walk_between he hij.le hj.le
    rw [← heq] at wc
    exact free (f i) (j - i) (by omega) (by omega) wc
  · have wc := walk_between he hji.le hi.le
    rw [heq] at wc
    exact free (f j) (i - j) (by omega) (by omega) wc

/-- **Shortest cycle.** A finite set carrying a closed walk has a ring. -/
theorem exists_ring {a ℓ : ℕ} (one : 1 ≤ ℓ) (cyc : Walk D F a a ℓ) : ∃ C, Ring D F C := by
  classical
  have ex : ∃ L, 1 ≤ L ∧ ∃ b, Walk D F b b L := ⟨ℓ, one, a, cyc⟩
  obtain ⟨L1, b, walk⟩ := Nat.find_spec ex
  set L := Nat.find ex with hL
  have short (a' ℓ') (h1 : 1 ≤ ℓ') (w' : Walk D F a' a' ℓ') : L ≤ ℓ' :=
    Nat.find_min' ex ⟨h1, a', w'⟩
  have freeF : QFree D F (L - 1) := fun a' ℓ' h1 hl w' => by
    have := short a' ℓ' h1 w'; omega
  obtain ⟨f, f0, fL, he⟩ := walk.toFun
  have inj := fun_inj freeF (by omega) he
  let C := (range L).image f
  have fC (k) (kl : k < L) : f (k + 1) ∈ C := by
    by_cases e : k + 1 = L
    · rw [e, fL, ← f0]; exact mem_image.mpr ⟨0, mem_range.mpr (by omega), rfl⟩
    · exact mem_image.mpr ⟨k + 1, mem_range.mpr (by omega), rfl⟩
  have cC : C.card = L := by rw [card_image_of_injOn inj, card_range]
  have walkC : Walk D C b b L := by
    have w := walk_between (W := C) (f := f) (fun k kl => ⟨fC k kl, (he k kl).2⟩) (Nat.zero_le L) le_rfl
    rwa [f0, fL, Nat.sub_zero] at w
  have freeC : QFree D C (L - 1) := freeF.mono_set (by
    intro x hx
    obtain ⟨i, im, rfl⟩ := mem_image.mp hx
    by_cases i0 : i = 0
    · subst i0; rw [f0, ← fL]; exact (he (L - 1) (by omega)).1 |> fun h => by
        rwa [Nat.sub_add_cancel (by omega : 1 ≤ L)] at h
    · have := (he (i - 1) (by have := mem_range.mp im; omega)).1
      rwa [Nat.sub_add_cancel (by omega : 1 ≤ i)] at this)
  refine ⟨C, ⟨?_, by omega, ?_, by rw [cC]; exact short⟩⟩
  · intro x hx
    obtain ⟨i, im, rfl⟩ := mem_image.mp hx
    by_cases i0 : i = 0
    · subst i0; rw [f0, ← fL]
      have := (he (L - 1) (by omega)).1
      rwa [Nat.sub_add_cancel (by omega : 1 ≤ L)] at this
    · have := (he (i - 1) (by have := mem_range.mp im; omega)).1
      rwa [Nat.sub_add_cancel (by omega : 1 ≤ i)] at this
  · intro c cm
    have bC : b ∈ C := by rw [← f0]; exact mem_image.mpr ⟨0, mem_range.mpr (by omega), rfl⟩
    have wc := Wide2Cycle.cycle_at freeC (by omega) (show Walk D C b b (L - 1 + 1) by
      rwa [Nat.sub_add_cancel (by omega : 1 ≤ L)]) cm
    rw [Nat.sub_add_cancel (by omega : 1 ≤ L)] at wc
    obtain ⟨g, g0, gL, ge⟩ := wc.toFun
    have ginj := fun_inj freeC (by omega) ge
    have gsub : (range L).image g ⊆ C := by
      intro x hx
      obtain ⟨i, im, rfl⟩ := mem_image.mp hx
      by_cases i0 : i = 0
      · subst i0; rw [g0]; exact cm
      · have := (ge (i - 1) (by have := mem_range.mp im; omega)).1
        rwa [Nat.sub_add_cancel (by omega : 1 ≤ i)] at this
    have geq := eq_of_subset_of_card_le gsub (by rw [card_image_of_injOn ginj, card_range, cC])
    refine ⟨g, g0, fun i il => ?_, by rw [cC]; exact gL, fun c' c'm => ?_⟩
    · rw [cC] at il; exact ge i il
    · rw [← geq] at c'm
      obtain ⟨t, tm, rfl⟩ := mem_image.mp c'm
      exact ⟨t, by rw [cC]; exact mem_range.mp tm, rfl⟩

/-- Walks along the ring read from `c`. -/
theorem Ring.walk {R : Ring D F C} {g : ℕ → ℕ}
    (ge : ∀ i < C.card, g (i + 1) ∈ C ∧ D (g i) (g (i + 1)) = true) {i j : ℕ} (ij : i ≤ j)
    (jl : j ≤ C.card) : Walk D F (g i) (g j) (j - i) :=
  (walk_between ge ij jl).mono R.sub

/-- **Chordless.** A row of the ring has at most one head on it. -/
theorem ring_heads (R : Ring D F C) (two : 2 ≤ C.card) {c : ℕ} (cm : c ∈ C) :
    (outN D C c).card ≤ 1 := by
  classical
  obtain ⟨g, g0, ge, gL, onto⟩ := R.rot c cm
  have sub : outN D C c ⊆ (Icc 1 1).image g := by
    intro c' hc'
    obtain ⟨c'm, arc⟩ := mem_outN.mp hc'
    obtain ⟨u, ul, rfl⟩ := onto c' c'm
    have w := Ring.walk (R := R) ge (i := u) (j := C.card) ul.le le_rfl
    rw [gL] at w
    have := R.short c (C.card - u + 1) (by omega) (Walk.step (R.sub c'm) arc w)
    by_cases u0 : u = 0
    · subst u0; rw [g0] at arc
      have := R.short c 1 le_rfl (.step (R.sub cm) arc (.refl c)); omega
    · exact mem_image.mpr ⟨u, mem_Icc.mpr ⟨by omega, by omega⟩, rfl⟩
  exact (card_le_card sub).trans (card_image_le.trans (by simp))

/-- **Window, forward.** If `c ∈ C` heads `a ∈ F`, then `a` has at most two heads on
`C`: a head `g u` read from `c` closes `c → a → g u ⇝ c` of length `|C| - u + 2`. -/
theorem ring_children (R : Ring D F C) (three : 3 ≤ C.card) {c a : ℕ} (cm : c ∈ C)
    (aF : a ∈ F) (ca : D c a = true) : (outN D C a).card ≤ 2 := by
  classical
  obtain ⟨g, g0, ge, gL, onto⟩ := R.rot c cm
  have sub : outN D C a ⊆ (Icc 1 2).image g := by
    intro c' hc'
    obtain ⟨c'm, arc⟩ := mem_outN.mp hc'
    obtain ⟨u, ul, rfl⟩ := onto c' c'm
    have w := Ring.walk (R := R) ge (i := u) (j := C.card) ul.le le_rfl
    rw [gL] at w
    have := R.short c (C.card - u + 1 + 1) (by omega) (.step aF ca (.step (R.sub c'm) arc w))
    by_cases u0 : u = 0
    · subst u0; rw [g0] at arc
      have := R.short c 2 (by omega) (.step aF ca (.step (R.sub cm) arc (.refl c))); omega
    · exact mem_image.mpr ⟨u, mem_Icc.mpr ⟨by omega, by omega⟩, rfl⟩
  exact (card_le_card sub).trans (card_image_le.trans (by simp))

/-- **Window, backward.** If `a ∈ F` heads `c' ∈ C`, at most two rows of `C` head `a`:
such a row `g t`, read from `c'`, closes `g t → a → c' ⇝ g t` of length `t + 2`. -/
theorem ring_parents (R : Ring D F C) {c' a : ℕ} (c'm : c' ∈ C) (aF : a ∈ F)
    (ac : D a c' = true) : (C.filter (fun c => D c a = true)).card ≤ 2 := by
  classical
  obtain ⟨g, g0, ge, gL, onto⟩ := R.rot c' c'm
  have sub : C.filter (fun c => D c a = true) ⊆ (Ico (C.card - 2) C.card).image g := by
    intro c hc
    obtain ⟨cm, arc⟩ := mem_filter.mp hc
    obtain ⟨t, tl, rfl⟩ := onto c cm
    have w := Ring.walk (R := R) ge (i := 0) (j := t) (Nat.zero_le t) tl.le
    rw [g0, Nat.sub_zero] at w
    have := R.short (g t) (t + 1 + 1) (by omega) (.step aF arc (.step (R.sub c'm) ac w))
    exact mem_image.mpr ⟨t, mem_Ico.mpr ⟨by omega, tl⟩, rfl⟩
  refine (card_le_card sub).trans (card_image_le.trans ?_)
  simp only [Nat.card_Ico]; omega

/-- **Far rows.** Rows of `C` that `c*` reaches along `F` only in `k` or more steps number
at most `|C| - k`. -/
theorem ring_far (R : Ring D F C) {c k : ℕ} (cm : c ∈ C) {S : Finset ℕ} (sub : S ⊆ C)
    (far : ∀ s ∈ S, ∀ t, Walk D F c s t → k ≤ t) : S.card ≤ C.card - k := by
  classical
  obtain ⟨g, g0, ge, gL, onto⟩ := R.rot c cm
  have sub' : S ⊆ (Ico k C.card).image g := by
    intro s hs
    obtain ⟨t, tl, rfl⟩ := onto s (sub hs)
    have w := Ring.walk (R := R) ge (i := 0) (j := t) (Nat.zero_le t) tl.le
    rw [g0, Nat.sub_zero] at w
    exact mem_image.mpr ⟨t, mem_Ico.mpr ⟨far _ hs t w, tl⟩, rfl⟩
  refine (card_le_card sub').trans (card_image_le.trans ?_)
  simp only [Nat.card_Ico]; omega

#print axioms exists_ring
#print axioms ring_heads
#print axioms ring_children
#print axioms ring_parents
#print axioms ring_far

end LeanCH.BR.Wide2Ring
