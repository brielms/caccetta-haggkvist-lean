import LeanCH.BR.CH.Conjecture
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Weighted boundary graphs and the merge lemma (Lean 4.35.0)

A *weighted boundary graph* for `(q, s)`: a digraph on labels `< n` with weights `ω v ∈ ℕ` (weight `0` means the
vertex is absent), total weight `q s + 1`, every present vertex of out-weight `≥ s`, and no cycle of length `≤ q`
(in the whole label set, which is stronger). It is *regular* when every present vertex has in-weight `s`.
A vertex of weight `w` stands for `w` independent twins, so this is boundary regularity for blow-ups.

**Merge lemma.** Let `a, b` be present, non-adjacent, with `I(b) ⊆ I(a)` among present vertices. If every weighted
boundary graph on the same digraph with smaller support is regular, then so is `ω`. Hence a support-minimal
counterexample is *in-Sperner*: no two non-adjacent present vertices have nested in-neighbourhoods.
-/

namespace LeanCH.BR.Weighted

open Finset

def outW (G : CH.Digraph) (n : Nat) (ω : Nat → Nat) (v : Nat) : Nat :=
  ∑ u ∈ range n, if G v u = true then ω u else 0

def inW (G : CH.Digraph) (n : Nat) (ω : Nat → Nat) (v : Nat) : Nat :=
  ∑ u ∈ range n, if G u v = true then ω u else 0

def supp (n : Nat) (ω : Nat → Nat) : Finset Nat := (range n).filter (fun v => 0 < ω v)

structure WB (G : CH.Digraph) (n q s : Nat) (ω : Nat → Nat) : Prop where
  total : ∑ v ∈ range n, ω v = q * s + 1
  loopless : CH.Loopless G n
  out : ∀ v, v < n → 0 < ω v → s ≤ outW G n ω v
  noShort : ¬ CH.HasDirectedCycleAtMost G n q

def Regular (G : CH.Digraph) (n s : Nat) (ω : Nat → Nat) : Prop :=
  ∀ v, v < n → 0 < ω v → inW G n ω v = s

/-- Two-point exchange: if `f` and `g` agree off `{a, b}` on `S`, the sums differ only at `a` and `b`. -/
theorem sum_two {S : Finset Nat} {a b : Nat} (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b) (f g : Nat → Nat)
    (h : ∀ v ∈ S, v ≠ a → v ≠ b → f v = g v) :
    ∑ v ∈ S, f v + g a + g b = ∑ v ∈ S, g v + f a + f b := by
  have hb' : b ∈ S.erase a := Finset.mem_erase.mpr ⟨fun e => hab e.symm, hb⟩
  have ef : ∑ v ∈ S, f v = ∑ v ∈ (S.erase a).erase b, f v + f b + f a := by
    rw [← Finset.sum_erase_add _ _ ha, ← Finset.sum_erase_add _ _ hb']
  have eg : ∑ v ∈ S, g v = ∑ v ∈ (S.erase a).erase b, g v + g b + g a := by
    rw [← Finset.sum_erase_add _ _ ha, ← Finset.sum_erase_add _ _ hb']
  have mid : ∑ v ∈ (S.erase a).erase b, f v = ∑ v ∈ (S.erase a).erase b, g v := by
    apply Finset.sum_congr rfl
    intro v hv
    simp only [Finset.mem_erase] at hv
    exact h v hv.2.2 hv.2.1 hv.1
  omega

/-- Arc double counting with weights. -/
theorem double_count (G : CH.Digraph) (n : Nat) (ω : Nat → Nat) :
    ∑ v ∈ range n, ω v * outW G n ω v = ∑ v ∈ range n, ω v * inW G n ω v := by
  simp only [outW, inW, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro u _
  apply Finset.sum_congr rfl; intro v _
  split_ifs <;> ring

/-- Regular weighted boundary graphs are out-regular. -/
theorem out_exact {G : CH.Digraph} {n q s : Nat} {ω : Nat → Nat} (hW : WB G n q s ω) (hR : Regular G n s ω) :
    ∀ v, v < n → 0 < ω v → outW G n ω v = s := by
  have hle : ∀ v ∈ range n, ω v * s ≤ ω v * outW G n ω v := by
    intro v hv
    rcases Nat.eq_zero_or_pos (ω v) with h | h
    · simp [h]
    · exact Nat.mul_le_mul_left _ (hW.out v (Finset.mem_range.mp hv) h)
  have heq : ∑ v ∈ range n, ω v * s = ∑ v ∈ range n, ω v * outW G n ω v := by
    rw [double_count]
    apply Finset.sum_congr rfl; intro v hv
    rcases Nat.eq_zero_or_pos (ω v) with h | h
    · simp [h]
    · rw [hR v (Finset.mem_range.mp hv) h]
  have each := (Finset.sum_eq_sum_iff_of_le hle).mp heq
  intro v hv hpos
  have := each v (Finset.mem_range.mpr hv)
  exact (Nat.eq_of_mul_eq_mul_left hpos this).symm

/-- Move the whole weight of `b` onto `a`. -/
def shift (ω : Nat → Nat) (a b : Nat) : Nat → Nat :=
  fun v => if v = b then 0 else if v = a then ω a + ω b else ω v

theorem shift_a {ω : Nat → Nat} {a b : Nat} (hab : a ≠ b) : shift ω a b a = ω a + ω b := by
  simp [shift, hab]

theorem shift_b {ω : Nat → Nat} {a b : Nat} : shift ω a b b = 0 := by simp [shift]

theorem shift_other {ω : Nat → Nat} {a b v : Nat} (hva : v ≠ a) (hvb : v ≠ b) : shift ω a b v = ω v := by
  simp [shift, hva, hvb]

theorem shift_sum {n : Nat} {ω : Nat → Nat} {a b : Nat} (ha : a < n) (hb : b < n) (hab : a ≠ b)
    (c : Nat → Nat) :
    (∑ u ∈ range n, c u * shift ω a b u) + c a * ω a + c b * ω b =
      (∑ u ∈ range n, c u * ω u) + c a * (ω a + ω b) := by
  have := sum_two (Finset.mem_range.mpr ha) (Finset.mem_range.mpr hb) hab
    (fun u => c u * shift ω a b u) (fun u => c u * ω u)
    (fun v _ hva hvb => by simp only [shift_other hva hvb])
  simp only [shift_a hab, shift_b, Nat.mul_zero, Nat.add_zero] at this
  exact this

theorem inW_eq (G : CH.Digraph) (n : Nat) (ω : Nat → Nat) (v : Nat) :
    inW G n ω v = ∑ u ∈ range n, (if G u v = true then 1 else 0) * ω u := by
  simp only [inW]; apply Finset.sum_congr rfl; intro u _; split_ifs <;> simp

theorem outW_eq (G : CH.Digraph) (n : Nat) (ω : Nat → Nat) (v : Nat) :
    outW G n ω v = ∑ u ∈ range n, (if G v u = true then 1 else 0) * ω u := by
  simp only [outW]; apply Finset.sum_congr rfl; intro u _; split_ifs <;> simp

/-- In-weight after shifting `b` onto `a`. -/
theorem inW_shift {G : CH.Digraph} {n : Nat} {ω : Nat → Nat} {a b : Nat} (ha : a < n) (hb : b < n)
    (hab : a ≠ b) (y : Nat) :
    inW G n (shift ω a b) y + (if G a y = true then 1 else 0) * ω a +
      (if G b y = true then 1 else 0) * ω b =
      inW G n ω y + (if G a y = true then 1 else 0) * (ω a + ω b) := by
  rw [inW_eq, inW_eq]
  exact shift_sum ha hb hab (fun u => if G u y = true then 1 else 0)

/-- Out-weight after shifting `b` onto `a`. -/
theorem outW_shift {G : CH.Digraph} {n : Nat} {ω : Nat → Nat} {a b : Nat} (ha : a < n) (hb : b < n)
    (hab : a ≠ b) (x : Nat) :
    outW G n (shift ω a b) x + (if G x a = true then 1 else 0) * ω a +
      (if G x b = true then 1 else 0) * ω b =
      outW G n ω x + (if G x a = true then 1 else 0) * (ω a + ω b) := by
  rw [outW_eq, outW_eq]
  exact shift_sum ha hb hab (fun u => if G x u = true then 1 else 0)

theorem shift_total {n : Nat} {ω : Nat → Nat} {a b : Nat} (ha : a < n) (hb : b < n) (hab : a ≠ b) :
    ∑ v ∈ range n, shift ω a b v = ∑ v ∈ range n, ω v := by
  have := shift_sum (ω := ω) ha hb hab (fun _ => 1)
  simp only [Nat.one_mul] at this
  omega

theorem shift_pos {ω : Nat → Nat} {a b v : Nat} (hab : a ≠ b) (pa : 0 < ω a) (h : 0 < shift ω a b v) :
    v ≠ b ∧ 0 < ω v := by
  by_cases hvb : v = b
  · subst hvb; simp [shift_b] at h
  · refine ⟨hvb, ?_⟩
    by_cases hva : v = a
    · subst hva; exact pa
    · rwa [shift_other hva hvb] at h

theorem shift_supp {n : Nat} {ω : Nat → Nat} {a b : Nat} (hb : b < n) (hab : a ≠ b) (pa : 0 < ω a)
    (pb : 0 < ω b) : (supp n (shift ω a b)).card < (supp n ω).card := by
  apply Finset.card_lt_card
  refine ⟨?_, ?_⟩
  · intro v hv
    have hv' := Finset.mem_filter.mp hv
    exact Finset.mem_filter.mpr ⟨hv'.1, (shift_pos hab pa hv'.2).2⟩
  · intro hsub
    have hbm : b ∈ supp n ω := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hb, pb⟩
    have := (Finset.mem_filter.mp (hsub hbm)).2
    rw [shift_b] at this; omega

/-- Shifting `b` onto `a` keeps a weighted boundary graph when `I(b) ⊆ I(a)` among present vertices. -/
theorem shift_WB {G : CH.Digraph} {n q s : Nat} {ω : Nat → Nat} {a b : Nat} (hW : WB G n q s ω)
    (ha : a < n) (hb : b < n) (hab : a ≠ b) (pa : 0 < ω a)
    (nest : ∀ x, x < n → 0 < ω x → G x b = true → G x a = true) : WB G n q s (shift ω a b) where
  total := by rw [shift_total ha hb hab]; exact hW.total
  loopless := hW.loopless
  noShort := hW.noShort
  out := by
    intro x hx hpos
    have hpx := (shift_pos hab pa hpos).2
    have h0 := hW.out x hx hpx
    have := outW_shift (G := G) (ω := ω) ha hb hab x
    by_cases hGb : G x b = true
    · have hGa := nest x hx hpx hGb
      simp only [hGa, hGb, if_true, Nat.one_mul] at this; omega
    · rw [if_neg hGb] at this
      split_ifs at this <;> omega

/-- **Merge lemma.** Non-adjacent present `a, b` with `I(b) ⊆ I(a)`: if every weighted boundary graph on `G`
with smaller support is regular, then `ω` is regular (and `a, b` are twins among present vertices). -/
theorem merge_regular {G : CH.Digraph} {n q s : Nat} {ω : Nat → Nat} {a b : Nat} (hW : WB G n q s ω)
    (ha : a < n) (hb : b < n) (hab : a ≠ b) (pa : 0 < ω a) (pb : 0 < ω b)
    (nab : G a b = false) (nba : G b a = false)
    (nest : ∀ x, x < n → 0 < ω x → G x b = true → G x a = true)
    (IH : ∀ ω', WB G n q s ω' → (supp n ω').card < (supp n ω).card → Regular G n s ω') :
    Regular G n s ω := by
  have W1 := shift_WB hW ha hb hab pa nest
  have R1 := IH _ W1 (shift_supp hb hab pa pb)
  have E1 := out_exact W1 R1
  -- I(a) ⊆ I(b): otherwise a vertex gains weight in ω1 beyond the exact value s
  have nest' : ∀ x, x < n → 0 < ω x → G x a = true → G x b = true := by
    intro x hx hpx hGa
    by_contra hGb
    have hxb : x ≠ b := by rintro rfl; rw [nba] at hGa; exact Bool.false_ne_true hGa
    have hpos1 : 0 < shift ω a b x := by
      by_cases hxa : x = a
      · subst hxa; rw [shift_a hab]; omega
      · rw [shift_other hxa hxb]; exact hpx
    have e := E1 x hx hpos1
    have o := outW_shift (G := G) (ω := ω) ha hb hab x
    have h0 := hW.out x hx hpx
    rw [if_pos hGa, if_neg hGb] at o
    omega
  have W2 := shift_WB hW hb ha (Ne.symm hab) pb nest'
  have R2 := IH _ W2 (shift_supp ha (Ne.symm hab) pb pa)
  -- O(a) = O(b) among present vertices
  have same : ∀ y, y < n → 0 < ω y → y ≠ a → y ≠ b → G a y = G b y := by
    intro y hy hpy hya hyb
    have i1 := inW_shift (G := G) (ω := ω) ha hb hab y
    have i2 := inW_shift (G := G) (ω := ω) hb ha (Ne.symm hab) y
    rw [R1 y hy (by rw [shift_other hya hyb]; exact hpy)] at i1
    rw [R2 y hy (by rw [shift_other hyb hya]; exact hpy)] at i2
    cases h1 : G a y <;> cases h2 : G b y <;> simp [h1, h2] at i1 i2 ⊢ <;> omega
  intro y hy hpy
  by_cases hya : y = a
  · subst hya
    have i1 := inW_shift (G := G) (ω := ω) ha hb hab y
    rw [R1 y hy (by rw [shift_a hab]; omega), hW.loopless y hy, nba] at i1
    simp at i1; omega
  · by_cases hyb : y = b
    · subst hyb
      have i2 := inW_shift (G := G) (ω := ω) hb ha (Ne.symm hab) y
      rw [R2 y hy (by rw [shift_a (Ne.symm hab)]; omega), hW.loopless y hy, nab] at i2
      simp at i2; omega
    · have i1 := inW_shift (G := G) (ω := ω) ha hb hab y
      rw [R1 y hy (by rw [shift_other hya hyb]; exact hpy), ← same y hy hpy hya hyb] at i1
      cases h1 : G a y <;> simp [h1] at i1 <;> omega

end LeanCH.BR.Weighted
