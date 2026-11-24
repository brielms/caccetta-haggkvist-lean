import LeanCH.BR.BRWeightedHostHeavyReach

/-! A local single-contact cut pays an actual atom. The cutoff and row level
are parameters; weights outside the cut may be signed. -/
namespace LeanCH.BR.WeightedSD
open Finset BRq2 BRq3 BR45 BRsub

theorem cut_contact_mass {q : ℕ} {D : CH.Digraph} {V R : Finset ℕ}
    (hRV : R ⊆ V) (hR : R.Nonempty) (hsmall : SmallRow q D R)
    (a : ℕ → ℚ) (ha : ∀ x ∈ R, 0 ≤ a x) (c : ℚ)
    (hr : ∀ x ∈ R, c ≤ row q D V a x) :
    ∃ x ∈ R, c - mass R a ≤ (q : ℚ)*outW D (V \ R) a x := by
  obtain ⟨x,hx,hsmallrow⟩ := hsmall a ha hR
  refine ⟨x,hx,?_⟩
  have hold := hr x hx
  have hsplit : row q D V a x = row q D R a x + (q : ℚ)*outW D (V \ R) a x := by
    simp only [row,outW_split hRV a x]; ring
  rw [hsplit] at hold
  linarith

theorem single_contact_cut_atom {q : ℕ} {D : CH.Digraph} {V R S : Finset ℕ}
    (hRV : R ⊆ V) (hR : R.Nonempty) (hsmall : SmallRow q D R)
    (a : ℕ → ℚ) (ha : ∀ x ∈ R, 0 ≤ a x) (c : ℚ)
    (hr : ∀ x ∈ R, c ≤ row q D V a x) (hgap : mass R a < c)
    (hheads : ∀ x ∈ R, outN D (V \ R) x ⊆ S)
    (hcard : ∀ x ∈ R, (outN D (V \ R) x).card ≤ 1) :
    ∃ x ∈ R, ∃ h ∈ V \ R, h ∈ S ∧ outN D (V \ R) x = {h} ∧
      D x h = true ∧ c - mass R a ≤ (q : ℚ)*a h := by
  obtain ⟨x,hx,hload⟩ := cut_contact_mass hRV hR hsmall a ha c hr
  have hne : (outN D (V \ R) x).Nonempty := by
    apply nonempty_iff_ne_empty.mpr
    intro he
    rw [outW_eq_mass,he] at hload
    simp only [mass,sum_empty,mul_zero] at hload
    unfold mass at hgap
    linarith
  have hone : (outN D (V \ R) x).card = 1 := by
    have hp := card_pos.mpr hne
    have hc := hcard x hx
    omega
  obtain ⟨h,he⟩ := card_eq_one.mp hone
  have hh : h ∈ outN D (V \ R) x := by rw [he]; exact mem_singleton_self _
  refine ⟨x,hx,h,(mem_outN.mp hh).1,hheads x hx hh,he,(mem_outN.mp hh).2,?_⟩
  simpa only [outW_eq_mass,he,mass,sum_singleton] using hload

end LeanCH.BR.WeightedSD
