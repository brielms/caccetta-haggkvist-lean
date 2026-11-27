import checkpoints.shen_extension.BypassDegreeDescent

/-! At the two-label deletion boundary, each prescribed label belongs to a pair
of heads shared by two different rows. -/

namespace LeanCH.BR.BypassBankReplay
open Finset BRq2 BRq3 BR45 BypassRepair

private theorem pair_covered {q s : ℕ} (X : ShenMinimumOrder.Source q s)
    (hr : 2 ≤ s) (hq : 2 ≤ q) (order : X.V.card = q * (s-1) + 2)
    (none : NoHost q (s-1)) {p h : ℕ} (pv : p ∈ X.V) (hv : h ∈ X.V) (ne : p ≠ h) :
    ∃ x ∈ X.V, X.D x p = true ∧ X.D x h = true := by
  classical
  by_contra missing
  let B : Finset ℕ := {p,h}
  have sub : B ⊆ X.V := insert_subset pv (singleton_subset_iff.mpr hv)
  have card : B.card = 2 := card_pair ne
  have size : (X.V \ B).card = q * (s-1) := by rw [card_sdiff_of_subset sub, card, order]; omega
  have pos : 0 < q * (s-1) := Nat.mul_pos (by omega) (by omega)
  apply none X.D (X.V \ B) (card_pos.mp (by omega)) size.le (X.free.mono_set sdiff_subset)
  intro x hx
  have xv := (mem_sdiff.mp hx).1
  have short : (outN X.D B x).card ≤ 1 := by
    by_cases xp : X.D x p = true
    · have xh : X.D x h ≠ true := fun e => missing ⟨x, xv, xp, e⟩
      have incl : outN X.D B x ⊆ {p} := by
        intro y hy
        obtain ⟨yb, xy⟩ := mem_outN.mp hy
        rcases (show y = p ∨ y = h by simpa [B] using yb) with yp | yh
        · exact mem_singleton.mpr yp
        · exact (xh (yh ▸ xy)).elim
      simpa using card_le_card incl
    · have incl : outN X.D B x ⊆ {h} := by
        intro y hy
        obtain ⟨yb, xy⟩ := mem_outN.mp hy
        rcases (show y = p ∨ y = h by simpa [B] using yb) with yp | yh
        · exact (xp (yp ▸ xy)).elim
        · exact mem_singleton.mpr yh
      simpa using card_le_card incl
  have split := card_outN_union (D := X.D) (show Disjoint B (X.V \ B) from disjoint_sdiff) x
  rw [union_sdiff_of_subset sub] at split
  have large := X.degree x xv
  omega

/-- An obstruction to a unique common predecessor for every pair containing a
fixed head: those predecessor rows would partition the other labels into
blocks of size every row's outdegree minus one. -/
theorem shared_pair_at_head {D : CH.Digraph} {V : Finset ℕ} {s p : ℕ}
    (eqdeg : OutEq s D V) (pv : p ∈ V)
    (covered : ∀ h ∈ V, p ≠ h → ∃ x ∈ V, D x p = true ∧ D x h = true)
    (nondiv : ¬ (s-1) ∣ (V.erase p).card) :
    ∃ x ∈ V, ∃ j ∈ V, x ≠ j ∧ p ∈ outN D V x ∧ p ∈ outN D V j ∧
      ∃ h ∈ outN D V x, h ∈ outN D V j ∧ h ≠ p := by
  classical
  let P := inN D V p
  let S (x : ℕ) := (outN D V x).erase p
  have cover : P.biUnion S = V.erase p := by
    ext h
    constructor
    · intro hh
      obtain ⟨x, _, hx⟩ := mem_biUnion.mp hh
      exact mem_erase.mpr ⟨(mem_erase.mp hx).1, outN_subset (mem_erase.mp hx).2⟩
    · intro hh
      obtain ⟨hp, hv⟩ := mem_erase.mp hh
      obtain ⟨x, xv, xp, xh⟩ := covered h hv hp.symm
      exact mem_biUnion.mpr ⟨x, mem_inN.mpr ⟨xv,xp⟩, mem_erase.mpr ⟨hp,mem_outN.mpr ⟨hv,xh⟩⟩⟩
  by_contra unique
  have count : (P.biUnion S).card = ∑ x ∈ P, (S x).card := by
    apply card_biUnion
    intro x hx j hj ne
    apply disjoint_left.mpr
    intro h h1 h2
    obtain ⟨xv,xp⟩ := mem_inN.mp hx
    obtain ⟨jv,jp⟩ := mem_inN.mp hj
    exact unique ⟨x,xv,j,jv,ne,mem_outN.mpr ⟨pv,xp⟩,mem_outN.mpr ⟨pv,jp⟩,
      h,(mem_erase.mp h1).2,(mem_erase.mp h2).2,(mem_erase.mp h1).1⟩
  have sizes (x) (hx : x ∈ P) : (S x).card = s-1 := by
    obtain ⟨xv,xp⟩ := mem_inN.mp hx
    exact (card_erase_of_mem (mem_outN.mpr ⟨pv,xp⟩)).trans (by rw [eqdeg x xv])
  rw [cover, sum_congr rfl sizes] at count
  simp only [sum_const, nsmul_eq_mul] at count
  exact nondiv (count ▸ dvd_mul_left _ _)

/-- At bank size two, a shared pair of successors exists for any choice of
the first head. -/
theorem shared_pair_at_two {q s} (X : ShenMinimumOrder.Source q s) (eqdeg : OutEq s X.D X.V)
    (hr : 4 ≤ s) (order : X.V.card = q * (s-1) + 2) (none : NoHost q (s-1)) (hq : 2 ≤ q) :
    ∃ x ∈ X.V, ∃ j ∈ X.V, x ≠ j ∧
      ∃ p ∈ outN X.D X.V x, p ∈ outN X.D X.V j ∧
      ∃ h ∈ outN X.D X.V x, h ∈ outN X.D X.V j ∧ h ≠ p := by
  obtain ⟨p,pv⟩ := X.nonempty
  have nondiv : ¬ (s-1) ∣ (X.V.erase p).card := by
    have card := card_erase_add_one pv
    have eq : (X.V.erase p).card = q*(s-1)+1 := by omega
    rw [eq]
    intro d
    have one : (s-1) ∣ 1 := by
      simpa using Nat.dvd_sub d (show (s-1) ∣ q*(s-1) from dvd_mul_left _ _)
    have := Nat.le_of_dvd (by decide : 0 < 1) one
    omega
  obtain ⟨x,xv,j,jv,ne,xp,jp,h,xh,jh,hp⟩ := shared_pair_at_head eqdeg pv
    (fun _ hv ne => pair_covered X (by omega) hq order none pv hv ne) nondiv
  exact ⟨x,xv,j,jv,ne,p,xp,jp,h,xh,jh,hp⟩

#print axioms shared_pair_at_two
end LeanCH.BR.BypassBankReplay

