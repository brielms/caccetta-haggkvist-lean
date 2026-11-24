import LeanCH.BR.BRLocalDegreeDrop

/-! Partial funnels suffice to exclude a return from a vertex with enough parents. -/

namespace LeanCH.BR.BRsGen

open BRq2 BRq3 BR45

/-- Degree descent need not reach every exterior label. Enough distinct parents
force one reachable label, which excludes the return arc. -/
theorem no_return_of_many_parents {D : CH.Digraph} {V X Y P : Finset ℕ}
    {q k d s z : ℕ} (hk : 2 ≤ k) (hkq : k + 1 ≤ q) (hb : Ball k d)
    (hf : QFree D V q) (hmin : ∀ v ∈ V, d ≤ (outN D V v).card)
    (hXV : X ⊆ V) (hYV : Y ⊆ V) (hXY : Disjoint X Y)
    (hX : X.card ≤ d * (k - 1))
    (hhigh : ∀ x ∈ X, s ≤ (outN D (X ∪ Y) x).card)
    (hPY : P ⊆ Y) (hz : z ∈ V) (hparents : ∀ p ∈ P, D p z = true)
    (hbudget : d + Y.card ≤ s + P.card) :
    ∀ x ∈ X, ¬ D z x = true := by
  classical
  intro x hx hzx
  obtain ⟨b, hbX, hlow, m, hm, w⟩ := local_degree_drop_reachable hk hb
    (hf.mono_bound (by omega : k ≤ q)) hmin hXV hX hx
  have havoid : outN D Y b ⊆ Y \ P := by
    intro p hp
    obtain ⟨hpY, hbp⟩ := mem_outN.mp hp
    refine Finset.mem_sdiff.mpr ⟨hpY, ?_⟩
    intro hpP
    have path := (((w.mono hXV).snoc (hYV hpY) hbp).snoc hz
      (hparents p hpP)).snoc (hXV hx) hzx
    exact hf x (m + 1 + 1 + 1) (by omega) (by omega) path
  have hcount := Finset.card_le_card havoid
  have hpart := Finset.card_sdiff_add_card_eq_card hPY
  have hh := hhigh b hbX
  rw [card_outN_union hXY] at hh
  omega

end LeanCH.BR.BRsGen
