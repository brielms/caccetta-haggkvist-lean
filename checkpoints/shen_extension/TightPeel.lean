import checkpoints.shen_extension.BypassRepair

/-!
# A tight peel gives a parent cover, and a parent cover kills a sink

* `parent_cover` (Lemma A): a `q`-free set `A ∪ Y` of `q · t + 1` labels, with `NoHost q t`,
  whose rows of `A` keep `t + 1` heads inside and whose rows of `Y` keep `t` heads inside,
  has an in-neighbour in `Y` at every label: otherwise deleting the label leaves a host of
  degree `t` on `q · t` labels.
* `cover_sink_false` (Lemma B): a nonempty `X` with `|X| ≤ q`, rows of out-degree `r` heading
  only `X ∪ Y`, `|Y| ≤ r + a`, `a + 2 ≤ q`, and every label of `X ∪ Y` with an in-neighbour in
  `Y` is impossible. A sink `s` of `X` heads only `Y`; the parent chain `y₀ → s`,
  `y_{i+1} → y_i` in `Y` has `a + 1` distinct labels that `s` does not head.
-/

namespace LeanCH.BR.TightPeel
open Finset BRq2 BRq3 BypassRepair

/-- **Lemma A: parent cover.** -/
theorem parent_cover {D : CH.Digraph} {V A Y : Finset ℕ} {q t : ℕ}
    (free : QFree D V q) (sub : A ∪ Y ⊆ V) (lower : NoHost q t) (ht : 1 ≤ t) (hq : 1 ≤ q)
    (size : (A ∪ Y).card = q * t + 1)
    (rowsA : ∀ x ∈ A, t + 1 ≤ (outN D (A ∪ Y) x).card)
    (rowsY : ∀ y ∈ Y, t ≤ (outN D (A ∪ Y) y).card) :
    ∀ z ∈ A ∪ Y, ∃ y ∈ Y, D y z = true := by
  intro z hz
  by_contra! none
  have outE : ∀ x, outN D ((A ∪ Y).erase z) x = (outN D (A ∪ Y) x).erase z := by
    intro x
    ext w
    simp only [mem_outN, mem_erase]
    tauto
  have hcard : ((A ∪ Y).erase z).card = q * t := by
    rw [card_erase_of_mem hz, size]; rfl
  have pos : 0 < q * t := Nat.mul_pos (by omega) (by omega)
  apply lower D ((A ∪ Y).erase z) (card_pos.mp (by omega)) hcard.le
    (free.mono_set ((erase_subset _ _).trans sub))
  intro x hx
  rw [outE]
  have xU := mem_of_mem_erase hx
  by_cases xy : x ∈ Y
  · rw [erase_eq_of_notMem (fun m => (none x xy) (mem_outN.mp m).2)]
    exact rowsY x xy
  · have xa : x ∈ A := (mem_union.mp xU).resolve_right xy
    have := pred_card_le_card_erase (s := outN D (A ∪ Y) x) (a := z)
    have := rowsA x xa
    omega

/-- **Lemma B: a parent cover kills a sink.** -/
theorem cover_sink_false {D : CH.Digraph} {V X Y : Finset ℕ} {q r a : ℕ}
    (free : QFree D V q) (xv : X ⊆ V) (yv : Y ⊆ V) (ne : X.Nonempty) (sx : X.card ≤ q)
    (degX : ∀ x ∈ X, r ≤ (outN D V x).card) (headsX : ∀ x ∈ X, outN D V x ⊆ X ∪ Y)
    (cy : Y.card ≤ r + a) (time : a + 2 ≤ q)
    (cover : ∀ v ∈ X ∪ Y, ∃ y ∈ Y, D y v = true) : False := by
  classical
  obtain ⟨s, sm, sink⟩ := exists_sink (free.mono_set xv) ne sx
  choose! par hpar using cover
  have parY : ∀ v ∈ X ∪ Y, par v ∈ Y := fun v hv => (hpar v hv).1
  have parA : ∀ v ∈ X ∪ Y, D (par v) v = true := fun v hv => (hpar v hv).2
  let f : ℕ → ℕ := fun i => par^[i + 1] s
  have f0 : f 0 = par s := rfl
  have fs : ∀ i, f (i + 1) = par (f i) := fun i => Function.iterate_succ_apply' par (i + 1) s
  have mem : ∀ i, f i ∈ Y := by
    intro i
    induction i with
    | zero => rw [f0]; exact parY s (mem_union_left _ sm)
    | succ i ih => rw [fs]; exact parY _ (mem_union_right _ ih)
  have arc0 : D (f 0) s = true := by rw [f0]; exact parA s (mem_union_left _ sm)
  have arc : ∀ i, D (f (i + 1)) (f i) = true := fun i => by
    rw [fs]; exact parA _ (mem_union_right _ (mem i))
  have walk : ∀ i j, Walk D V (f (i + j)) (f i) j := by
    intro i j
    induction j with
    | zero => exact .refl _
    | succ j ih => exact .step (yv (mem _)) (arc _) ih
  have toS : ∀ i, Walk D V (f i) s (i + 1) := by
    intro i
    have w := walk 0 i
    rw [Nat.zero_add] at w
    exact w.snoc (xv sm) arc0
  -- `s` heads none of the chain
  have miss : ∀ i ≤ a, f i ∉ outN D V s := by
    intro i hi m
    exact free s (i + 1 + 1) (by omega) (by omega) (.step (yv (mem i)) (mem_outN.mp m).2 (toS i))
  -- the chain is injective on `0 … a`
  have inj : Set.InjOn f (range (a + 1) : Set ℕ) := by
    intro i hi j hj e
    simp only [coe_range, Set.mem_Iio] at hi hj
    by_contra n
    rcases Nat.lt_or_gt_of_ne n with lt | lt
    · have w := walk i (j - i)
      rw [Nat.add_sub_cancel' lt.le, ← e] at w
      exact free _ (j - i) (by omega) (by omega) w
    · have w := walk j (i - j)
      rw [Nat.add_sub_cancel' lt.le, e] at w
      exact free _ (i - j) (by omega) (by omega) w
  have cT : ((range (a + 1)).image f).card = a + 1 := by
    rw [card_image_of_injOn inj, card_range]
  have heads : outN D V s ⊆ Y := by
    intro z hz
    rcases mem_union.mp (headsX s sm hz) with zx | zy
    · exact (sink z zx (mem_outN.mp hz).2).elim
    · exact zy
  have disj : Disjoint (outN D V s) ((range (a + 1)).image f) := by
    rw [disjoint_right]
    intro z hz
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hz
    exact miss i (by rw [mem_range] at hi; omega)
  have imY : (range (a + 1)).image f ⊆ Y := by
    intro z hz
    obtain ⟨i, -, rfl⟩ := mem_image.mp hz
    exact mem i
  have tot := card_le_card (union_subset heads imY)
  rw [card_union_of_disjoint disj] at tot
  have := degX s sm
  omega

#print axioms parent_cover
#print axioms cover_sink_false
end LeanCH.BR.TightPeel
