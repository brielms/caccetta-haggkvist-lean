import checkpoints.shen_extension.PhysicalCycleStockReplay

namespace LeanCH.BR.PhysicalCycleStock
open Finset BRq2 BRq3 BR45 BRsGen ExteriorPacking

private theorem exterior_sub {D V C} : exterior D V C ⊆ V := by
  intro x hx
  obtain ⟨_, _, arc⟩ := mem_biUnion.mp (mem_sdiff.mp hx).1
  exact outN_subset arc

private theorem complete_edge {D V C r x y} (rooted : Rooted D V x C)
    (degree : (outN D V x).card = r) (size : (exterior D V C).card = r-1)
    (outside : y ∈ exterior D V C) : D x y = true := by
  have head : y ∈ (outN D V x).erase (internalHead D C x) :=
    (complete_row rooted degree size).symm ▸ outside
  exact (mem_outN.mp (mem_of_mem_erase head)).2

/-- On three successive physical banks, either the first cycle already has
strong stock on every row, or the last bank is another complete cycle.
The new bank is its actual exterior in the original graph. -/
theorem exclusive_step {D V q r A B C} (free : QFree D V q) (hq : 4 ≤ q)
    (hr : 2 ≤ r) (fit : r ≤ q+2) (reg : OutEq r D V)
    (rootA : ∀ a ∈ A, Rooted D V a A) (rootB : ∀ b ∈ B, Rooted D V b B)
    (ab : exterior D V A = B) (bc : exterior D V B = C)
    (bsize : B.card = r-1) (csize : C.card = r-1) :
    (∀ a ∈ A, 3*r+2 ≤ (ball D V a 3).card) ∨
      ((exterior D V C).card = r-1 ∧ ∀ c ∈ C, Rooted D V c C) := by
  classical
  let E := exterior D V C
  have bsub : B ⊆ V := ab ▸ exterior_sub
  have csub : C ⊆ V := bc ▸ exterior_sub
  have esub : E ⊆ V := exterior_sub
  have acard : (exterior D V A).card = r-1 := ab.symm ▸ bsize
  have bcard : (exterior D V B).card = r-1 := bc.symm ▸ csize
  have edgeAB a (ha : a ∈ A) b (hb : b ∈ B) :=
    complete_edge (rootA a ha) (reg a ((rootA a ha).sub ha)) acard (ab.symm ▸ hb)
  have edgeBC b (hb : b ∈ B) c (hc : c ∈ C) :=
    complete_edge (rootB b hb) (reg b (bsub hb)) bcard (bc.symm ▸ hc)
  have aB : Disjoint A B := disjoint_left.mpr (fun z ha hb => (mem_sdiff.mp (ab.symm ▸ hb)).2 ha)
  have bC : Disjoint B C := disjoint_left.mpr (fun z hb hc => (mem_sdiff.mp (bc.symm ▸ hc)).2 hb)
  have cE : Disjoint C E := disjoint_left.mpr (fun _ hc he => (mem_sdiff.mp he).2 hc)
  have bpos : B.Nonempty := card_pos.mp (by omega)
  have cpos : C.Nonempty := card_pos.mp (by omega)
  have aC : Disjoint A C := by
    refine disjoint_left.mpr (fun a ha hc => ?_)
    obtain ⟨b, hb⟩ := bpos
    exact digonfree free (by omega) (csub hc) (bsub hb) (edgeAB a ha b hb) (edgeBC b hb a hc)
  have bE : Disjoint B E := by
    refine disjoint_left.mpr (fun b hb he => ?_)
    obtain ⟨c, hc, initial⟩ := mem_biUnion.mp (mem_sdiff.mp he).1
    exact digonfree free (by omega) (bsub hb) (csub hc) (edgeBC b hb c hc) (mem_outN.mp initial).2
  have aE : Disjoint A E := by
    refine disjoint_left.mpr (fun a ha he => ?_)
    obtain ⟨b, hb⟩ := bpos
    obtain ⟨c, hc, edge⟩ := mem_biUnion.mp (mem_sdiff.mp he).1
    exact free a 3 (by decide) (by omega) (.step (bsub hb) (edgeAB a ha b hb)
      (.step (csub hc) (edgeBC b hb c hc) (.step (esub he) (mem_outN.mp edge).2 (.refl a))))
  have row x (hx : x ∈ C) : outN D V x ⊆ outN D C x ∪ E := by
    intro y hy
    by_cases hit : y ∈ C
    · exact mem_union_left _ (mem_outN.mpr ⟨hit, (mem_outN.mp hy).2⟩)
    · exact mem_union_right _ (mem_sdiff.mpr ⟨mem_biUnion.mpr ⟨x, hx, hy⟩, hit⟩)
  have size : r-1 ≤ E.card := by
    by_contra! small
    have min2 x (hx : x ∈ C) : 2 ≤ (outN D C x).card := by
      have cap := (card_le_card (row x hx)).trans (card_union_le _ _)
      rw [reg x (csub hx)] at cap
      omega
    have lower := corB (by omega : 1≤q) (free.mono_set csub) min2 cpos
    omega
  by_cases equal : E.card = r-1
  · refine Or.inr ⟨equal, ?_⟩
    have min1 x (hx : x ∈ C) : 1 ≤ (outN D C x).card := by
      have cap := (card_le_card (row x hx)).trans (card_union_le _ _)
      rw [reg x (csub hx)] at cap
      omega
    intro c hc
    exact ShellCycleSupply.rooted_on_small_set free (by omega) csub (by omega) min1 hc
  · left
    intro a ha
    let H := ball D A a 3
    have sa : A ⊆ V := (rootA a ha).sub
    have hsize := ball_one_growth (free.mono_set sa)
      (fun x hx => ((rootA x hx).one x hx).ge) ha 3 (by omega)
    have included : H ∪ B ∪ C ∪ E ⊆ ball D V a 3 := by
      have bseen : B ⊆ ball D V a 1 := fun b hb => ball_of_adj (bsub hb) (edgeAB a ha b hb)
      have cseen : C ⊆ ball D V a 2 := by
        intro c hc
        obtain ⟨b, hb⟩ := bpos
        exact ball_step (bseen hb) (csub hc) (edgeBC b hb c hc)
      refine union_subset (union_subset (union_subset (ShellCycleSupply.lift_ball sa)
        (fun _ hb => ball_mono_radius (by decide : 1 ≤ 3) (bseen hb)))
        (fun _ hc => ball_mono_radius (by decide : 2 ≤ 3) (cseen hc))) ?_
      intro e he
      obtain ⟨c, hc, ce⟩ := mem_biUnion.mp (mem_sdiff.mp he).1
      exact ball_step (cseen hc) (esub he) (mem_outN.mp ce).2
    have bill := card_le_card included
    rw [card_union_of_disjoint (disjoint_union_left.mpr
          ⟨disjoint_union_left.mpr ⟨aE.mono_left ball_subset, bE⟩, cE⟩),
      card_union_of_disjoint (disjoint_union_left.mpr ⟨aC.mono_left ball_subset, bC⟩),
      card_union_of_disjoint (aB.mono_left ball_subset)] at bill
    change H.card+B.card+C.card+E.card ≤ (ball D V a 3).card at bill
    change 4 ≤ H.card at hsize
    omega

def bankIteration (D : CH.Digraph) (V A : Finset ℕ) : ℕ → Finset ℕ
  | 0 => A
  | i+1 => exterior D V (bankIteration D V A i)

/-- A finite sequence of complete banks cannot stay weak when its first
q+1 banks would exceed the physical carrier. The output retains the actual
terminal and all of its predecessor banks. -/
theorem exclusive_terminal {D V q r A} (free : QFree D V q) (hq : 4 ≤ q)
    (hr : 2 ≤ r) (fit : r ≤ q+2) (reg : OutEq r D V)
    (order : V.card < (q+1)*(r-1))
    (s0 : A.card = r-1) (s1 : (exterior D V A).card = r-1)
    (s2 : (exterior D V (exterior D V A)).card = r-1)
    (rootA : ∀ a ∈ A, Rooted D V a A)
    (rootB : ∀ b ∈ exterior D V A, Rooted D V b (exterior D V A)) :
    let B := bankIteration D V A
    ∃ k, k+2≤q ∧ (∀ j≤k+1, (B j).card = r-1 ∧ ∀ x ∈ B j, Rooted D V x (B j)) ∧
      ∀ x ∈ B k, 3*r+2 ≤ (ball D V x 3).card := by
  classical
  let B := bankIteration D V A
  let valid := fun j => (B j).card=r-1 ∧ ∀ x ∈ B j, Rooted D V x (B j)
  change ∃ k, k+2≤q ∧ (∀ j≤k+1, valid j) ∧ ∀ x ∈ B k, 3*r+2 ≤ (ball D V x 3).card
  by_contra no
  have filled (k) (hk : k+2≤q) : (∀ j≤k+1, valid j) ∧ (B (k+2)).card = r-1 := by
    induction k with
    | zero =>
      refine ⟨fun j hj => ?_, s2⟩
      rcases show j=0 ∨ j=1 by omega with rfl | rfl
      · exact ⟨s0, rootA⟩
      · exact ⟨s1, rootB⟩
    | succ k ih =>
      obtain ⟨prior, last⟩ := ih (by omega)
      have l := prior k (by omega)
      have m := prior (k+1) le_rfl
      obtain strong | ⟨next, rooted⟩ :=
        exclusive_step free hq hr fit reg l.2 m.2 (rfl : exterior D V (B k) = B (k+1))
          (rfl : exterior D V (B (k+1)) = B (k+2)) m.1 last
      · exact (no ⟨k, by omega, prior, strong⟩).elim
      refine ⟨fun j hj => ?_, next⟩
      by_cases early : j≤k+1
      · exact prior j early
      · obtain rfl : j=k+2 := by omega
        exact ⟨last, rooted⟩
  obtain ⟨upto, last⟩ := filled (q-2) (by omega)
  have eq : q-2+2=q := by omega
  rw [eq] at last
  have everySize j (hj : j≤q) : (B j).card = r-1 := by
    by_cases end' : j=q
    · exact end'.symm ▸ last
    · exact (upto j (by omega)).1
  have everySub j (hj : j≤q) : B j ⊆ V := by
    cases j with
    | zero =>
      obtain ⟨a, ha⟩ := card_pos.mp (show 0<A.card by omega)
      exact (rootA a ha).sub
    | succ j => exact exterior_sub
  have everyEdge i (hi : i<q) x (hx : x ∈ B i) y (hy : y ∈ B (i+1)) : D x y = true :=
    complete_edge ((upto i (by omega)).2 x hx) (reg x (everySub i (by omega) hx))
      (everySize (i+1) (by omega)) hy
  have everyWalk n i (hi : i+n+1≤q) x (hx : x ∈ B i) y (hy : y ∈ B (i+n+1)) :
      Walk D V x y (n+1) := by
    induction n generalizing y with
    | zero =>
      exact .step (everySub (i+1) (by omega) hy) (everyEdge i (by omega) x hx y hy) (.refl y)
    | succ n ih =>
      have size := everySize (i+n+1) (by omega)
      obtain ⟨z, hz⟩ := card_pos.mp (show 0 < (B (i+n+1)).card by omega)
      have loc : i+n.succ+1=i+n+1+1 := by omega
      rw [loc] at hy
      exact (ih (by omega) z hz).snoc (everySub _ (by omega) hy)
        (everyEdge (i+n+1) (by omega) z hz y hy)
  have apart {i j} (hi : i<j) (hj : j≤q) : Disjoint (B i) (B j) := by
    refine disjoint_left.mpr (fun x xi xj => ?_)
    have eq : i+(j-i-1)+1=j := by omega
    have walk := everyWalk (j-i-1) i (by omega) x xi x (eq.symm ▸ xj)
    exact free x _ (by omega) (by omega) walk
  let I := range (q+1)
  have parts : (I : Set ℕ).PairwiseDisjoint B := by
    intro i hi j hj different
    have hi' := mem_range.mp (show i ∈ I from hi)
    have hj' := mem_range.mp (show j ∈ I from hj)
    rcases lt_or_gt_of_ne different with lt | gt
    · exact apart lt (by omega)
    · exact (apart gt (by omega)).symm
  have sub : I.biUnion B ⊆ V := by
    intro x hx
    obtain ⟨i, hi, xi⟩ := mem_biUnion.mp hx
    exact everySub i (by have := mem_range.mp hi; omega) xi
  have budget := card_le_card sub
  rw [card_biUnion parts, sum_congr rfl (fun j hj => everySize j (by have := mem_range.mp hj; omega)),
    sum_const_nat (fun _ _ => rfl), show I.card=q+1 from card_range _] at budget
  omega

#print axioms exclusive_step
#print axioms exclusive_terminal
end LeanCH.BR.PhysicalCycleStock
