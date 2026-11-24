import LeanCH.BR.BR36Reduce
import LeanCH.BR.ModuleSize
import LeanCH.BR.BRq3Base

/-!
# BBall(3,5), part 1: `BR(3,5)` and the 5-vertex lemma on an arbitrary vertex set (Lean 4.35.0)

Paper: `checkpoints/boundary_20261111/BallQ5b_attempt_subagent.md` §2 (Lemma B1, "Lean inputs"). No existing file is
changed.

`D` is `3`-free with out-degree exactly `5` on a finite `W ⊆ ℕ`. The restriction `resD D W` (arcs of `D` with both
ends in `W`) is loopless and has no cycle of length `≤ 3` on any label range containing `W`, so the label-range
theorems apply to it.

* `card_ge_16`: `|W| ≥ 16` (`ModuleSize.module_size` with `BR35.br_five`; the paper cites `triangle_le_24`).
* `in_eq_five`: if `|W| = 16`, every in-degree inside `W` is `5` (`BR35.br_five`, transported to labels `0..15` as in
  `StrictCap.induced_regular`).
* `five_shape_W`: `BR35.five_shape` for a 5-set `S ⊆ W` (`e(D[S]) ≤ 8`; at equality a source heading the other four,
  each of which has exactly one head in `S`).
-/

set_option linter.style.longLine false

namespace LeanCH.BR.BRsGen35

open LeanCH.BR.BRq2 LeanCH.BR.BRq3 CH Compose.Boundary Compose.FloorSix
open LeanCH.BR.BR35 (oc ic)

variable {D : CH.Digraph} {W : Finset ℕ}

/-- The restriction of `D` to `W`. -/
def resD (D : CH.Digraph) (W : Finset ℕ) : CH.Digraph :=
  fun a b => decide (a ∈ W) && decide (b ∈ W) && D a b

theorem resD_eq {a b : ℕ} : resD D W a b = true ↔ a ∈ W ∧ b ∈ W ∧ D a b = true := by
  simp [resD, and_assoc]

theorem exists_range (W : Finset ℕ) : ∃ n, W ⊆ Finset.range n :=
  ⟨W.sup id + 1, fun _ hx => Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := id) hx))⟩

theorem resD_loopless (hfree : QFree D W 3) (n : ℕ) : CH.Loopless (resD D W) n := by
  intro v _
  cases h : resD D W v v
  · rfl
  · obtain ⟨hv, -, hvv⟩ := resD_eq.mp h
    exact absurd hvv (loopfree hfree (by omega) hv)

theorem resD_noShort (hfree : QFree D W 3) (n : ℕ) : ¬ CH.HasDirectedCycleAtMost (resD D W) n 3 :=
  LeanCH.BR.BR36.noShort_of
    (fun a b _ _ h1 h2 => by
      obtain ⟨ha, hb, h1⟩ := resD_eq.mp h1
      exact digonfree hfree (by omega) ha hb h1 (resD_eq.mp h2).2.2)
    (fun a b c _ _ _ h1 h2 h3 => by
      obtain ⟨ha, hb, h1⟩ := resD_eq.mp h1
      obtain ⟨-, hc, h2⟩ := resD_eq.mp h2
      exact hfree a 3 (by omega) le_rfl (.step hb h1 (.step hc h2 (.step ha (resD_eq.mp h3).2.2 (.refl a)))))

theorem oc_resD {S : Finset ℕ} (hS : S ⊆ W) {x : ℕ} (hx : x ∈ W) : oc (resD D W) S x = oc D S x := by
  unfold oc
  congr 1
  apply Finset.filter_congr
  intro v hv
  rw [resD_eq]
  exact ⟨fun h => h.2.2, fun h => ⟨hx, hS hv, h⟩⟩

theorem ic_resD {S : Finset ℕ} (hS : S ⊆ W) {x : ℕ} (hx : x ∈ W) : ic (resD D W) S x = ic D S x := by
  unfold ic
  congr 1
  apply Finset.filter_congr
  intro v hv
  rw [resD_eq]
  exact ⟨fun h => h.2.2, fun h => ⟨hS hv, hx, h⟩⟩

/-- A nonempty `3`-free out-`5` vertex set has at least `16` vertices. -/
theorem card_ge_16 (hfree : QFree D W 3) (hout : OutEq 5 D W) (hne : W.Nonempty) : 16 ≤ W.card := by
  obtain ⟨n, hn⟩ := exists_range W
  have := LeanCH.BR.ModuleSize.module_size (G := resD D W) (n := n) (q := 3) (c := 5) (by omega)
    LeanCH.BR.BR35.br_five hn (Finset.card_pos.mpr hne) (resD_loopless hfree n) (resD_noShort hfree n)
    (fun x hx => by
      have h := oc_resD (D := D) (S := W) (subset_refl _) hx
      have h5 : oc D W x = 5 := hout x hx
      change 5 ≤ oc (resD D W) W x
      omega)
  omega

/-- **`BR(3,5)` on a vertex set.** A `3`-free out-`5` set of `16` vertices has every in-degree `5`. -/
theorem in_eq_five (hfree : QFree D W 3) (hout : OutEq 5 D W) (hcard : W.card = 16) :
    ∀ y ∈ W, ic D W y = 5 := by
  classical
  obtain ⟨n, hsub⟩ := exists_range W
  have loopless := resD_loopless hfree n
  have noShort := resD_noShort hfree n
  set G := resD D W with hG
  have keep : ∀ x ∈ W, 5 ≤ (W.filter (fun w => G x w = true)).card := by
    intro x hx
    have h := oc_resD (D := D) (S := W) (subset_refl _) hx
    have h5 : oc D W x = 5 := hout x hx
    change 5 ≤ oc (resD D W) W x
    omega
  obtain ⟨e, eB, eI, eM, eS⟩ := CH.Side.sc_finset_enumeration hsub
  set m := W.card with hm
  let H : CH.Digraph := fun a b => if a < m then (if b < m then G (e a) (e b) else false) else false
  have hloop : CH.Loopless H m := by
    intro v hv
    change (if v < m then (if v < m then G (e v) (e v) else false) else false) = false
    rw [if_pos hv, if_pos hv]; exact loopless (e v) (eB v hv)
  have hmin : CH.MinOutdegreeAtLeast H m 5 := by
    intro a ha
    let T : Finset Nat := (Finset.range m).filter (fun i => G (e a) (e i) = true)
    have himage : T.image e = W.filter (fun w => G (e a) w = true) := by
      ext w
      simp only [T, Finset.mem_image, Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro ⟨i, ⟨hi, hG⟩, rfl⟩; exact ⟨eM i hi, hG⟩
      · rintro ⟨hwM, hG⟩; obtain ⟨i, hi, rfl⟩ := eS w hwM; exact ⟨i, ⟨hi, hG⟩, rfl⟩
    have hinj : Set.InjOn e T := by
      intro i hi j hj hij
      have hi' : i ∈ T := hi
      have hj' : j ∈ T := hj
      exact eI i j (Finset.mem_range.mp (Finset.mem_filter.mp hi').1)
        (Finset.mem_range.mp (Finset.mem_filter.mp hj').1) hij
    have hTcard : 5 ≤ T.card := by
      have := Finset.card_image_of_injOn hinj
      rw [himage] at this; rw [← this]; exact keep (e a) (eM a ha)
    refine ⟨(T.sort (· ≤ ·)).take 5, ?_, ?_, ?_⟩
    · rw [List.length_take, Finset.length_sort]; omega
    · exact (Finset.sort_nodup _ _).sublist (List.take_sublist _ _)
    · intro w hw
      have hwT : w ∈ T := (Finset.mem_sort _).mp ((List.take_sublist _ _).subset hw)
      simp only [T, Finset.mem_filter, Finset.mem_range] at hwT
      refine ⟨hwT.1, ?_⟩
      change (if a < m then (if w < m then G (e a) (e w) else false) else false) = true
      rw [if_pos ha, if_pos hwT.1]; exact hwT.2
  have hshort : ¬ CH.HasDirectedCycleAtMost H m 3 := fun h =>
    noShort (CH.Side.sc_induced_subgraph_transport eB eI h)
  rw [hcard] at hloop hmin hshort
  have hreg : ∀ v, v < 3 * 5 + 1 → (par H (3 * 5 + 1) v).card = 5 :=
    LeanCH.BR.BR35.br_five H hloop hmin hshort
  intro y hy
  obtain ⟨a, ha, rfl⟩ := eS y hy
  have h1 := hreg a (by omega)
  have himage : (par H (3 * 5 + 1) a).image e = W.filter (fun u => G u (e a) = true) := by
    ext w
    simp only [par, Finset.mem_image, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨i, ⟨hi, hG⟩, rfl⟩
      have hi' : i < m := by omega
      have hG' : (if i < m then (if a < m then G (e i) (e a) else false) else false) = true := hG
      rw [if_pos hi', if_pos ha] at hG'
      exact ⟨eM i hi', hG'⟩
    · rintro ⟨hwM, hG⟩
      obtain ⟨i, hi, rfl⟩ := eS w hwM
      refine ⟨i, ⟨by omega, ?_⟩, rfl⟩
      change (if i < m then (if a < m then G (e i) (e a) else false) else false) = true
      rw [if_pos hi, if_pos ha]; exact hG
  have hinj : Set.InjOn e (par H (3 * 5 + 1) a) := by
    intro i hi j hj hij
    have hi' : i ∈ par H (3 * 5 + 1) a := hi
    have hj' : j ∈ par H (3 * 5 + 1) a := hj
    have hi'' := Finset.mem_range.mp (Finset.mem_filter.mp hi').1
    have hj'' := Finset.mem_range.mp (Finset.mem_filter.mp hj').1
    exact eI i j (by omega) (by omega) hij
  have hcnt : ic G W (e a) = 5 := by
    change (W.filter (fun u => G u (e a) = true)).card = 5
    rw [← himage, Finset.card_image_of_injOn hinj, h1]
  rw [← ic_resD (D := D) (subset_refl W) hy]
  exact hcnt

/-- **The 5-vertex lemma on a vertex set** (`BR35.five_shape`). -/
theorem five_shape_W (hfree : QFree D W 3) {S : Finset ℕ} (hS : S ⊆ W) (hcard : S.card = 5)
    (pos : ∀ x ∈ S, 1 ≤ oc D S x) :
    ∑ x ∈ S, oc D S x ≤ 8 ∧
      (8 ≤ ∑ x ∈ S, oc D S x → ∃ e ∈ S, ∀ c ∈ S, c ≠ e → D e c = true ∧ oc D S c = 1) := by
  obtain ⟨n, hn⟩ := exists_range W
  have hsum : ∑ x ∈ S, oc (resD D W) S x = ∑ x ∈ S, oc D S x :=
    Finset.sum_congr rfl (fun x hx => oc_resD hS (hS hx))
  obtain ⟨h8, hsh⟩ := LeanCH.BR.BR35.five_shape (G := resD D W) (n := n) (resD_loopless hfree n)
    (resD_noShort hfree n) (hS.trans hn) hcard (fun x hx => by rw [oc_resD hS (hS hx)]; exact pos x hx)
  refine ⟨hsum ▸ h8, fun h => ?_⟩
  obtain ⟨e, he, hc⟩ := hsh (hsum ▸ h)
  refine ⟨e, he, fun c hcS hne => ?_⟩
  obtain ⟨h1, h2⟩ := hc c hcS hne
  exact ⟨(resD_eq.mp h1).2.2, by rw [← oc_resD hS (hS hcS)]; exact h2⟩

end LeanCH.BR.BRsGen35
