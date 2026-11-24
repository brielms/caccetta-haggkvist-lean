import checkpoints.shen_extension.FeederReceiverMultiplicity

namespace LeanCH.BR.Closure.FeederPrivateHeadDescent
open Finset Function BRq2 BRq3 BR45 WeightedSD ShenCycleSuccessor ShortestCycleWeights

/-- On a proper cycle, two equal exterior row sizes and saturation force
an actual pair of opposite incidences. -/
theorem opposed_exterior {q n} (X : Model q n) (hq : 2 ≤ q) {L}
    (cy : Cycle X.D X.V q L) (proper : L ≠ X.V)
    (same : ∀ x ∈ L, ∀ y ∈ L, (outN X.D X.V x).card = (outN X.D X.V y).card) :
    ∃ x ∈ L, ∃ y ∈ L, ∃ j ∈ X.V \ L, ∃ k ∈ X.V \ L, j ≠ k ∧
      X.D x j = true ∧ X.D y j = false ∧ X.D x k = false ∧ X.D y k = true := by
  classical
  let E (x : ℕ) := outN X.D (X.V \ L) x
  have add (x) (hx : x ∈ L) : (E x).card + 1 = (outN X.D X.V x).card := by
    have sub : outN X.D L x ⊆ outN X.D X.V x :=
      fun t ht => mem_outN.mpr ⟨cy.sub (mem_outN.mp ht).1,(mem_outN.mp ht).2⟩
    have id : E x = outN X.D X.V x \ outN X.D L x := by
      ext t
      simp only [E,mem_outN,mem_sdiff]
      tauto
    rw [id,card_sdiff_of_subset sub]
    have lo := card_le_card sub
    have one := cy.heads x hx
    omega
  have varies : ∃ x ∈ L, ∃ y ∈ L, E x ≠ E y := by
    by_contra! eq
    have out : BRsub.OutUniform X.D X.V L := by
      intro x hx y hy j jv jl
      have iff : j ∈ E x ↔ j ∈ E y := (eq x hx y hy) ▸ Iff.rfl
      apply Bool.eq_iff_iff.mpr
      simpa [E,mem_outN,mem_sdiff,jv,jl] using iff
    exact X.prime L cy.sub (by have := cy.size; omega) proper
      ⟨out,BRsub.outUniform_inUniform X.free X.sat cy.sub out⟩
  obtain ⟨x,hx,y,hy,diff⟩ := varies
  have eq : (E x).card = (E y).card := by
    have := same x hx y hy
    have := add x hx
    have := add y hy
    omega
  obtain ⟨j,jx,jy⟩ := (show ∃ j ∈ E x, j ∉ E y by
    simpa [Finset.Nonempty] using (sdiff_nonempty.mpr (fun sub => diff (eq_of_subset_of_card_le sub eq.ge))))
  obtain ⟨k,ky,kx⟩ := (show ∃ k ∈ E y, k ∉ E x by
    simpa [Finset.Nonempty] using (sdiff_nonempty.mpr (fun sub => diff.symm (eq_of_subset_of_card_le sub eq.le))))
  obtain ⟨jv,xj⟩ := mem_outN.mp jx
  obtain ⟨kv,yk⟩ := mem_outN.mp ky
  exact ⟨x,hx,y,hy,j,jv,k,kv,fun h => jy (h ▸ ky),xj,
    Bool.eq_false_iff.mpr (fun h => jy (mem_outN.mpr ⟨jv,h⟩)),
    Bool.eq_false_iff.mpr (fun h => kx (mem_outN.mpr ⟨kv,h⟩)),yk⟩

/-- At coprime spacing, a failed degree escape forces the common cycle
price onto at least two distinct exterior columns, on opposite incidences. -/
theorem coprime_spill {q n} (X : Model q n) (hq : 2 ≤ q) (small : SmallerSmallRow q X.V.card)
    {w π c} (posw : ∀ i ∈ X.V, 0 < w i) (flat : ∀ i ∈ X.V, WeightedSD.row q X.D X.V w i = c)
    (pos : ∀ i ∈ X.V, 0 < π i) (high : mass X.V π < c)
    (cols : ∀ i ∈ X.V, WeightedSD.col q X.D X.V π i = c)
    {L a b} (cy : Cycle X.D X.V q L) (ha : a ∈ L) (hb : b ∈ L) (ne : a ≠ b)
    (proper : L ≠ X.V) (cop : Nat.Coprime (MandatoryExcursion.span X.D X.V q a b) (q+1)) :
    (∀ ell, ell.Prime → ell ∣ q → SignatureExit X w π c a b ell) ∨
    ((∀ x ∈ L, w x = w a) ∧
     ∃ x ∈ L, ∃ y ∈ L, ∃ j ∈ X.V \ L, ∃ k ∈ X.V \ L, j ≠ k ∧
       X.D x j = true ∧ X.D y j = false ∧ X.D x k = false ∧ X.D y k = true ∧
       w j = w a ∧ w k = w a) := by
  classical
  rcases on_marked_cycle X hq small posw flat pos high cols cy ha hb ne with win | regular
  · exact Or.inl win
  right
  obtain ⟨period,_,_,multiplicity⟩ := regular
  rw [show Nat.gcd (MandatoryExcursion.span X.D X.V q a b) (q+1) = 1 from cop] at period multiplicity
  simp only [Nat.div_one] at multiplicity
  let s := fun i => (nextOn X.D L)^[i] a
  let word := fun i => cycleWord X.D X.V w (s i) (s (i+1))
  have const (i : ℕ) : word i = word 0 := by
    induction i with
    | zero => rfl
    | succ i ih => exact (period i).trans ih
  have allrows (x) (hx : x ∈ L) :
      w x = w a ∧ (outN X.D X.V x).card = (outN X.D X.V a).card := by
    have cover := (cycle_index (by omega : 1 ≤ q) X.free cy ha).2.2.1
    rw [←cover] at hx
    obtain ⟨i,_,rfl⟩ := mem_image.mp hx
    exact ⟨congrArg Prod.fst (const i),congrArg (fun v : ℚ × ℕ × Finset ℕ => v.2.1) (const i)⟩
  obtain ⟨x,hx,y,hy,j,jv,k,kv,ne',xj,yj,xk,yk⟩ :=
    opposed_exterior X hq cy proper (fun x hx y hy => (allrows x hx).2.trans (allrows y hy).2.symm)
  have priced (t) (tv : t ∈ X.V \ L) (u v) (hu : u ∈ L) (hv : v ∈ L)
      (hit : X.D u t = true) (miss : X.D v t = false) : w t = w a := by
    rcases multiplicity t (mem_sdiff.mp tv).1 with ⟨e,he,eq⟩ | div
    · exact eq.trans (allrows e he).1
    have lt : (inN X.D L t).card < L.card := card_lt_card (Finset.ssubset_iff_subset_ne.mpr
      ⟨filter_subset _ _,fun eq => Bool.noConfusion
        ((mem_inN.mp (show v ∈ inN X.D L t from eq.symm ▸ hv)).2.symm.trans miss)⟩)
    have p := card_pos.mpr (show (inN X.D L t).Nonempty from ⟨u,mem_inN.mpr ⟨hu,hit⟩⟩)
    have := Nat.le_of_dvd p div
    have := cy.size
    omega
  exact ⟨fun x hx => (allrows x hx).1,x,hx,y,hy,j,jv,k,kv,ne',xj,yj,xk,yk,
    priced j jv x y hx hy xj yj,priced k kv y x hy hx yk xk⟩

#print axioms opposed_exterior
#print axioms coprime_spill
end LeanCH.BR.Closure.FeederPrivateHeadDescent
