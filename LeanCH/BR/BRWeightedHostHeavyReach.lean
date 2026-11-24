import LeanCH.BR.BRWeightedOrderCongruence
import LeanCH.BR.BRWeightedTightCut

/-! Reach a deficient row inside a positive weighted host whose order is not
one modulo q. The application uses actual host weights, not a separate core law. -/
namespace LeanCH.BR.WeightedSD
open Finset BRq2 BRq3 BR45 BRsub

theorem small_row_reachable {q : ℕ} {D : CH.Digraph} {E : Finset ℕ}
    (hsmall : ∀ R ⊆ E, SmallRow q D R) (a : ℕ → ℚ) (ha : ∀ x ∈ E, 0 ≤ a x)
    {v : ℕ} (hv : v ∈ E) :
    ∃ b ∈ E, row q D E a b ≤ mass E a ∧ ∃ k, Walk D E v b k := by
  classical
  let R := E.filter (fun x => ∃ k, Walk D E v x k)
  have hRE : R ⊆ E := filter_subset _ _
  have hvR : v ∈ R := mem_filter.mpr ⟨hv,0,.refl v⟩
  obtain ⟨b,hb,hrow⟩ := hsmall R hRE a (fun x hx => ha x (hRE hx)) ⟨v,hvR⟩
  have hz : outW D (E \ R) a b = 0 := by
    apply sum_eq_zero
    intro y hy
    have hn : D b y ≠ true := by
      intro hby
      obtain ⟨k,hw⟩ := (mem_filter.mp hb).2
      exact (mem_sdiff.mp hy).2 (mem_filter.mpr ⟨(mem_sdiff.mp hy).1,
        k+1,hw.snoc (mem_sdiff.mp hy).1 hby⟩)
    simp [hn]
  have heq : row q D E a b = row q D R a b := by
    simp only [row,outW_split hRE a b,hz,add_zero]
  refine ⟨b,hRE hb,?_,(mem_filter.mp hb).2⟩
  rw [heq]
  exact hrow.trans (mass_mono hRE ha)

theorem host_weak_heavy_reachable {q : ℕ} {D : CH.Digraph} {V S : Finset ℕ}
    (hSV : S ⊆ V) (hsmall : ∀ R ⊆ V \ S, SmallRow q D R)
    (a : ℕ → ℚ) (ha : ∀ x ∈ V \ S, 0 ≤ a x) (c : ℚ)
    (hr : ∀ x ∈ V \ S, c ≤ row q D V a x) {v : ℕ} (hv : v ∈ V \ S) :
    ∃ b ∈ V \ S, c - mass (V \ S) a ≤ (q : ℚ)*outW D S a b ∧
      ∃ k, Walk D (V \ S) v b k := by
  obtain ⟨b,hb,hsmallrow,hw⟩ := small_row_reachable hsmall a ha hv
  refine ⟨b,hb,?_,hw⟩
  have hrow := hr b hb
  rw [row,outW_split hSV a b] at hrow
  unfold row at hsmallrow
  linarith

theorem host_strict_heavy_reachable {q : ℕ} {D : CH.Digraph} {V S : Finset ℕ}
    (hSV : S ⊆ V) (hsmall : ∀ R ⊆ V \ S, SmallRow q D R)
    (a : ℕ → ℚ) (ha : ∀ x ∈ V \ S, 0 ≤ a x) (c : ℚ) (hc : mass V a < c)
    (hr : ∀ x ∈ V \ S, c ≤ row q D V a x) {v : ℕ} (hv : v ∈ V \ S) :
    ∃ b ∈ V \ S, mass S a < (q : ℚ)*outW D S a b ∧ ∃ k, Walk D (V \ S) v b k := by
  obtain ⟨b,hb,hheavy,hw⟩ := host_weak_heavy_reachable hSV hsmall a ha c hr hv
  refine ⟨b,hb,?_,hw⟩
  have hm : mass (V \ S) a + mass S a = mass V a := sum_sdiff hSV
  linarith

theorem deficient_row_reachable {q : ℕ} (hq : 2 ≤ q) {D : CH.Digraph} {E : Finset ℕ}
    (hsmall : ∀ R ⊆ E, SmallRow q D R) (a : ℕ → ℚ) (ha : ∀ x ∈ E, 0 < a x)
    (hmod : (E.card : ZMod q) ≠ 1) {v : ℕ} (hv : v ∈ E) :
    ∃ b ∈ E, row q D E a b < mass E a ∧ ∃ k, Walk D E v b k := by
  classical
  by_contra h
  let R := E.filter (fun x => ∃ k, Walk D E v x k)
  have hRE : R ⊆ E := filter_subset _ _
  have hvR : v ∈ R := mem_filter.mpr ⟨hv,0,.refl v⟩
  have hclosed : ∀ x ∈ R, ∀ y ∈ E, D x y = true → y ∈ R := by
    intro x hx y hy hxy
    obtain ⟨k,hw⟩ := (mem_filter.mp hx).2
    exact mem_filter.mpr ⟨hy,k+1,hw.snoc hy hxy⟩
  have hrE : ∀ x ∈ R, mass E a ≤ row q D E a x := by
    intro x hx
    apply le_of_not_gt
    intro hbad
    exact h ⟨x,hRE hx,hbad,(mem_filter.mp hx).2⟩
  have hrow : ∀ x ∈ R, row q D E a x = row q D R a x := by
    intro x hx
    have hz : outW D (E \ R) a x = 0 := by
      apply sum_eq_zero
      intro y hy
      have hn : D x y ≠ true := fun he => (mem_sdiff.mp hy).2 (hclosed x hx y (mem_sdiff.mp hy).1 he)
      simp [hn]
    simp only [row,outW_split hRE a x,hz,add_zero]
  obtain ⟨x,hx,hxsmall⟩ := hsmall R hRE a (fun x hx => (ha x (hRE hx)).le) ⟨v,hvR⟩
  have hmass : mass R a = mass E a := by
    apply le_antisymm (mass_mono hRE (fun x hx => (ha x hx).le))
    exact (hrE x hx).trans (by rw [hrow x hx]; exact hxsmall)
  have heq : R = E := positive_mass_eq_subset hRE ha hmass
  apply hmod (positive_feasible_card_mod hq (hsmall E Subset.rfl) a ha ⟨v,hv⟩ ?_)
  intro x hx
  exact hrE x (heq.symm ▸ hx)

theorem host_heavy_reachable {q : ℕ} (hq : 2 ≤ q) {D : CH.Digraph} {V S : Finset ℕ}
    (hSV : S ⊆ V) (hsmall : ∀ R ⊆ V \ S, SmallRow q D R)
    (a : ℕ → ℚ) (ha : ∀ x ∈ V \ S, 0 < a x)
    (hr : ∀ x ∈ V \ S, mass V a ≤ row q D V a x)
    (hmod : ((V \ S).card : ZMod q) ≠ 1) {v : ℕ} (hv : v ∈ V \ S) :
    ∃ b ∈ V \ S, mass S a < (q : ℚ)*outW D S a b ∧ ∃ k, Walk D (V \ S) v b k := by
  obtain ⟨b,hb,hbad,hw⟩ := deficient_row_reachable hq hsmall a ha hmod hv
  refine ⟨b,hb,?_,hw⟩
  have hm : mass (V \ S) a + mass S a = mass V a := sum_sdiff hSV
  have hrow := hr b hb
  rw [row,outW_split hSV a b] at hrow
  unfold row at hbad
  linarith

theorem host_heavy_reachable_of_proper {q : ℕ} (hq : 2 ≤ q)
    {D : CH.Digraph} {V S : Finset ℕ} (hSV : S ⊆ V) (hS : S.Nonempty)
    (hproper : ∀ R ⊆ V, R ≠ V → SmallRow q D R)
    (a : ℕ → ℚ) (ha : ∀ x ∈ V \ S, 0 < a x)
    (hr : ∀ x ∈ V \ S, mass V a ≤ row q D V a x)
    (hmod : ((V \ S).card : ZMod q) ≠ 1) {v : ℕ} (hv : v ∈ V \ S) :
    ∃ b ∈ V \ S, mass S a < (q : ℚ)*outW D S a b ∧ ∃ k, Walk D (V \ S) v b k := by
  apply host_heavy_reachable hq hSV ?_ a ha hr hmod hv
  intro R hRE
  apply hproper R (hRE.trans sdiff_subset)
  intro heq
  obtain ⟨s,hs⟩ := hS
  have hx := hRE (heq.symm ▸ hSV hs)
  exact (mem_sdiff.mp hx).2 hs

theorem card_mod_ne_one_of_dvd {q n : ℕ} (hq : q ≠ 1) (hd : q ∣ n) : (n : ZMod q) ≠ 1 := by
  intro he
  have hz : (n : ZMod q) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hd
  have hone : ((1 : ℕ) : ZMod q) = 0 := by simpa only [Nat.cast_one] using he.symm.trans hz
  have hd1 : q ∣ 1 := (ZMod.natCast_eq_zero_iff _ _).mp hone
  exact hq (Nat.dvd_one.mp hd1)

theorem host_heavy_reachable_of_divisible {q : ℕ} (hq : 2 ≤ q)
    {D : CH.Digraph} {V S : Finset ℕ} (hSV : S ⊆ V) (hS : S.Nonempty)
    (hproper : ∀ R ⊆ V, R ≠ V → SmallRow q D R)
    (a : ℕ → ℚ) (ha : ∀ x ∈ V \ S, 0 < a x)
    (hr : ∀ x ∈ V \ S, mass V a ≤ row q D V a x)
    (hd : q ∣ (V \ S).card) {v : ℕ} (hv : v ∈ V \ S) :
    ∃ b ∈ V \ S, mass S a < (q : ℚ)*outW D S a b ∧ ∃ k, Walk D (V \ S) v b k :=
  host_heavy_reachable_of_proper hq hSV hS hproper a ha hr (card_mod_ne_one_of_dvd (by omega) hd) hv

end LeanCH.BR.WeightedSD
