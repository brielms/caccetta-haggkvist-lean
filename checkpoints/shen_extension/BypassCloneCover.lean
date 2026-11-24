import checkpoints.shen_extension.BypassBankReplay

namespace LeanCH.BR.BypassCloneCover
open Finset BRq2 BRq3 BypassRepair BypassBankReplay

/-- An old label in S is reused as a copy of its assigned surviving label. -/
def fold (S : Finset ℕ) (f : ℕ → ℕ) (v : ℕ) := if v ∈ S then f v else v

def copies (D : CH.Digraph) (S : Finset ℕ) (f : ℕ → ℕ) : CH.Digraph :=
  fun a b => D (fold S f a) (fold S f b)

/-- The original labels on both sides of the replacement, including repeated choices of f. -/
theorem copy_row {D : CH.Digraph} {U S : Finset ℕ} {f : ℕ → ℕ}
    (sub : S ⊆ U) (a : ℕ) :
    (outN (copies D S f) U a).card =
      (outN D (U \ S) (fold S f a)).card +
      (S.filter (fun j => D (fold S f a) (f j) = true)).card := by
  classical
  have row : outN (copies D S f) U a =
      outN D (U \ S) (fold S f a) ∪ S.filter (fun j => D (fold S f a) (f j) = true) := by
    ext v
    constructor
    · intro hit
      obtain ⟨vu,arc⟩ := mem_outN.mp hit
      change D (fold S f a) (fold S f v) = true at arc
      by_cases vs : v ∈ S
      · exact mem_union_right _ (mem_filter.mpr ⟨vs,by simpa [fold,vs] using arc⟩)
      · exact mem_union_left _ (mem_outN.mpr ⟨mem_sdiff.mpr ⟨vu,vs⟩,by simpa [fold,vs] using arc⟩)
    · intro hit
      apply mem_outN.mpr
      rcases mem_union.mp hit with old | copy
      · obtain ⟨vw,arc⟩ := mem_outN.mp old
        obtain ⟨vu,vs⟩ := mem_sdiff.mp vw
        exact ⟨vu,by simpa [copies,fold,vs] using arc⟩
      · obtain ⟨vs,arc⟩ := mem_filter.mp copy
        exact ⟨sub vs,by simpa [copies,fold,vs] using arc⟩
  rw [row, card_union_of_disjoint]
  exact disjoint_left.mpr fun _ memOld memCopy =>
    (mem_sdiff.mp (outN_subset memOld)).2 (mem_filter.mp memCopy).1

/-- Folding a walk preserves its length, including a walk visiting several different copies. -/
theorem copy_free {D : CH.Digraph} {U S : Finset ℕ} {f : ℕ → ℕ} {q : ℕ}
    (free : QFree D (U \ S) q) (dest : ∀ j ∈ S, f j ∈ U \ S) :
    QFree (copies D S f) U q := by
  have inside (v) (vu : v ∈ U) : fold S f v ∈ U \ S := by
    by_cases vs : v ∈ S
    · simpa [fold, vs] using dest v vs
    · simpa [fold, vs] using mem_sdiff.mpr ⟨vu, vs⟩
  have project {a b k} (w : Walk (copies D S f) U a b k) :
      Walk D (U \ S) (fold S f a) (fold S f b) k := by
    induction w with
    | refl v => exact .refl _
    | step hv edge _ ih => exact .step (inside _ hv) edge ih
  exact fun a k pos bound walk => free (fold S f a) k pos bound (project walk)

/-- A proposed allocation pays precisely when it pays every distinct surviving row. -/
theorem copy_quota_iff {D : CH.Digraph} {U S : Finset ℕ} {f : ℕ → ℕ} {t : ℕ}
    (sub : S ⊆ U) (dest : ∀ j ∈ S, f j ∈ U \ S) :
    (∀ a ∈ U, t ≤ (outN (copies D S f) U a).card) ↔
      ∀ y ∈ U \ S, t ≤ (outN D (U \ S) y).card +
        (S.filter (fun j => D y (f j) = true)).card := by
  constructor
  · intro rows y hy
    have h := rows y (mem_sdiff.mp hy).1
    rw [copy_row sub] at h
    simpa [fold, (mem_sdiff.mp hy).2] using h
  · intro rows a ha
    rw [copy_row sub]
    apply rows
    by_cases mem : a ∈ S
    · simpa [fold, mem] using dest a mem
    · simpa [fold, mem] using mem_sdiff.mpr ⟨ha, mem⟩

/-- At a terminal order every allocation of the freed slots misses a physical row. -/
theorem uncovered_row {D : CH.Digraph} {U S : Finset ℕ} {f : ℕ → ℕ} {t q : ℕ}
    (none : NoHost q t) (small : U.card ≤ q*t) (live : U.Nonempty)
    (free : QFree D (U \ S) q) (sub : S ⊆ U) (dest : ∀ j ∈ S, f j ∈ U \ S) :
    ∃ y ∈ U \ S, (outN D (U \ S) y).card +
      (S.filter (fun j => D y (f j) = true)).card < t := by
  by_contra! allPaid
  exact none _ U live small (copy_free free dest) ((copy_quota_iff sub dest).mpr allPaid)

/-- Put the freed slot at any specific k. Failure identifies a tight parent of x missing k. -/
theorem misses_copy {D : CH.Digraph} {U : Finset ℕ} {q t x k : ℕ}
    (none : NoHost q t) (small : U.card ≤ q*t) (free : QFree D U q)
    (xu : x ∈ U) (ku : k ∈ U) (kx : k ≠ x)
    (other : ∀ a ∈ U, a ≠ x → t ≤ (outN D U a).card) :
    ∃ y ∈ U, y ≠ x ∧ D y x = true ∧ (outN D U y).card = t ∧ D y k ≠ true := by
  have dest : ∀ j ∈ ({x} : Finset ℕ), (fun _ : ℕ => k) j ∈ U \ {x} :=
    fun _ _ => mem_sdiff.mpr ⟨ku, by simpa using kx⟩
  obtain ⟨y, yw, short⟩ := uncovered_row none small ⟨x, xu⟩ (free.mono_set sdiff_subset)
    (singleton_subset_iff.mpr xu) dest
  have yu := (mem_sdiff.mp yw).1
  have yx : y ≠ x := by simpa using (mem_sdiff.mp yw).2
  have low := other y yu yx
  have eraseRow : outN D (U \ {x}) y = (outN D U y).erase x := by
    ext v
    simp only [mem_outN, mem_sdiff, mem_singleton, mem_erase]
    tauto
  rw [eraseRow] at short
  by_cases hit : x ∈ outN D U y
  · have eq := card_erase_add_one hit
    have missed : D y k ≠ true := by
      intro yes
      simp [yes] at short
      omega
    exact ⟨y, yu, yx, (mem_outN.mp hit).2, by omega, missed⟩
  · rw [erase_eq_of_notMem hit] at short
    omega

/-- The earlier unpaid parent can be retained verbatim. Each of its other heads
    separates that parent from another tight parent of the same x. -/
theorem separate_parent {D : CH.Digraph} {U : Finset ℕ} {q t x y : ℕ}
    (none : NoHost q t) (small : U.card ≤ q*t) (free : QFree D U q)
    (xu : x ∈ U) (yx : D y x = true) (exactRow : (outN D U y).card = t)
    (other : ∀ a ∈ U, a ≠ x → t ≤ (outN D U a).card) :
    ((outN D U y).erase x).card + 1 = t ∧
    ∀ k ∈ (outN D U y).erase x, ∃ v ∈ U, v ≠ x ∧ v ≠ y ∧
      D v x = true ∧ (outN D U v).card = t ∧ D v k ≠ true := by
  refine ⟨(card_erase_add_one (mem_outN.mpr ⟨xu, yx⟩)).trans exactRow, ?_⟩
  intro k hk
  obtain ⟨kx, head⟩ := mem_erase.mp hk
  obtain ⟨v, vu, vx, arc, tight, missed⟩ :=
    misses_copy none small free xu (outN_subset head) kx other
  exact ⟨v, vu, vx, fun h => missed (h ▸ (mem_outN.mp head).2), arc, tight, missed⟩

structure CopySeparation (D : CH.Digraph) (U : Finset ℕ) (t x : ℕ) : Prop where
  every_column : ∀ k ∈ U, k ≠ x →
    ∃ y ∈ U, y ≠ x ∧ D y x = true ∧ (outN D U y).card = t ∧ D y k ≠ true

/-- The same physical y is kept for every separating column. -/
theorem another_parent {D U t x y} (sep : CopySeparation D U t x) (xu : x ∈ U)
    (yx : D y x = true) (row : (outN D U y).card = t) (enough : 2 ≤ t) :
    ∃ k ∈ (outN D U y).erase x, ∃ v ∈ U, v ≠ x ∧ v ≠ y ∧
      D v x = true ∧ (outN D U v).card = t ∧ D v k ≠ true := by
  have card := card_erase_add_one (mem_outN.mpr ⟨xu, yx⟩)
  obtain ⟨k,hk⟩ := card_pos.mp (show 0 < ((outN D U y).erase x).card by omega)
  obtain ⟨kx,head⟩ := mem_erase.mp hk
  obtain ⟨v,vu,vx,arc,tight,miss⟩ := sep.every_column k (outN_subset head) kx
  exact ⟨k,hk,v,vu,vx,fun eq => miss (eq ▸ (mem_outN.mp head).2),arc,tight,miss⟩

/-- If only two parents can pay at exactly quota, their rows overlap precisely at x. -/
theorem pair_intersection {D U t x a b} (sep : CopySeparation D U t x) (xu : x ∈ U)
    (ax : D a x = true) (bx : D b x = true)
    (only : ∀ y ∈ U, y ≠ x → D y x = true → (outN D U y).card = t → y = a ∨ y = b) :
    outN D U a ∩ outN D U b = {x} := by
  ext k
  constructor
  · intro both
    obtain ⟨ak,bk⟩ := mem_inter.mp both
    apply mem_singleton.mpr
    by_contra kx
    obtain ⟨y,yu,yx,edge,hc,miss⟩ := sep.every_column k (outN_subset ak) kx
    rcases only y yu yx edge hc with rfl | rfl
    · exact miss (mem_outN.mp ak).2
    · exact miss (mem_outN.mp bk).2
  · intro kx
    rw [mem_singleton.mp kx]
    exact mem_inter.mpr ⟨mem_outN.mpr ⟨xu,ax⟩,mem_outN.mpr ⟨xu,bx⟩⟩

structure AllocationFailure (D : CH.Digraph) (U : Finset ℕ) (t : ℕ) : Prop where
  at_slots : ∀ S ⊆ U, ∀ f : ℕ → ℕ, (∀ j ∈ S, f j ∈ U \ S) →
    ∃ y ∈ U \ S, (outN D (U \ S) y).card + (S.filter (fun j => D y (f j) = true)).card < t

@[aesop safe forward (immediate := [none,small,free,live]) (rule_sets := [CHGraphFamilies])]
theorem allocations {D U q t} (none : NoHost q t) (small : U.card ≤ q*t)
    (free : QFree D U q) (live : U.Nonempty) : AllocationFailure D U t :=
  ⟨fun _ sub _ dest => uncovered_row none small live (free.mono_set sdiff_subset) sub dest⟩

@[aesop safe forward (immediate := [none,cell]) (rule_sets := [CHGraphFamilies])]
theorem marked_allocations {q r} {X : ShenMinimumOrder.Source q r} {m : Cell}
    (none : NoHost q (r-1)) (cell : Marked X m) :
    AllocationFailure X.D (X.V \ m.bank) (r-1) := by
  have size := cell.size
  have card := card_sdiff_add_card_eq_card cell.sub
  exact allocations none (by omega) (X.free.mono_set sdiff_subset) ⟨_,cell.xu⟩

@[aesop safe forward (immediate := [none,small,free,xu,other]) (rule_sets := [CHGraphFamilies])]
theorem separation {D U q t x} (none : NoHost q t) (small : U.card ≤ q*t)
    (free : QFree D U q) (xu : x ∈ U)
    (other : ∀ a ∈ U, a ≠ x → t ≤ (outN D U a).card) : CopySeparation D U t x :=
  ⟨fun _ ku kx => misses_copy none small free xu ku kx other⟩

@[aesop safe forward (immediate := [none,cell,lone]) (rule_sets := [CHGraphFamilies])]
theorem on_lone {q r} {X : ShenMinimumOrder.Source q r} {m : Cell}
    (none : NoHost q (r-1)) (cell : Marked X m) (lone : LoneBlocked X m) :
    CopySeparation X.D (X.V \ m.bank) (r-1) m.x := by
  have size := cell.size
  have card := card_sdiff_add_card_eq_card cell.sub
  exact separation none (by omega) (X.free.mono_set sdiff_subset) cell.xu lone.paid_elsewhere

#print axioms copy_row
#print axioms copy_free
#print axioms copy_quota_iff
#print axioms uncovered_row
#print axioms misses_copy
#print axioms separate_parent
#print axioms another_parent
#print axioms pair_intersection
#print axioms allocations
#print axioms marked_allocations
#print axioms separation
#print axioms on_lone
end LeanCH.BR.BypassCloneCover
