import checkpoints.shen_extension.MixedRadiusCompletion
import checkpoints.shen_extension.FifthStripEndpoints
import checkpoints.shen_extension.FifthStripCommonSuccessors

/-! Finite comparison tests for the family of cutoffs q = 2r − 7.
The prefix advances and the endpoint argument come from the reach-ledger handoff.
The catalog can evaluate the same predicate at any degree. -/
set_option linter.style.longLine false
set_option maxRecDepth 100000
namespace LeanCH.BR.FifthStripLedger
open Finset BRq2 BRq3 BR45 BypassRepair ReachLedger MixedRadiusCompletion
open DotTwoPassShellTransport (shell layer holes fullColumns full_columns_bound)

/-! ### Checked suppliers on the fifth strip, generic in `a` -/

section Strip
variable {a : ℕ}

private theorem inner (k : ℕ) (hk : k ≤ a + 1) : Floor (2*a+7) (a+7) k ((a+7)*k+1) :=
  fun _ _ free deg _ hu => ShenFifthStrip.inner_growth free deg hu k hk

private theorem mid3 : Floor (2*a+7) (a+7) (a+3) ((a+7)*(a+3)-1) := fun _ _ free deg _ hu => by
  have := (ShenFifthStrip.middle_growth free deg hu).2.1
  omega

private theorem mid4 : Floor (2*a+7) (a+7) (a+4) ((a+7)*(a+4)-3) := fun _ _ free deg _ hu => by
  have := (ShenFifthStrip.middle_growth free deg hu).2.2
  omega

private theorem out5 : Floor (2*a+7) (a+7) (a+5) ((a+7)*(a+5)-5) := fun _ _ free deg _ hu => by
  have := (ShenFifthStrip.outer_growth free deg hu).1
  omega

private theorem order_top : Order (2*a+7) (a+7) ((2*a+7)*(a+7)-3) := fun _ _ free deg ne => by
  have := ShenFifthStrip.order_to_three free deg ne
  omega

private theorem low3 : Floor (2*a+7) (a+6) (a+3) ((a+6)*(a+3)) :=
  fun _ _ free deg _ hu => ShenThirdStrip.radius_R_growth free deg hu

private theorem low4 : Floor (2*a+7) (a+6) (a+4) ((a+6)*(a+4)-1) := fun _ _ free deg _ hu => by
  have := ShenThirdStrip.radius_R1_growth free deg hu
  omega

private theorem low_order (ha : 1 ≤ a) : Order (2*a+7) (a+6) ((2*a+7)*(a+6)+1) :=
  fun _ _ free deg ne => DotTwoPassShellTransport.order_third_strip_closed ha free deg ne

/-- Test one rise of the radius floor. A smaller comparison degree or the
current degree may pay for any fixed row profile. -/
private abbrev Window (a lo hi prev order pair : ℕ) : Prop :=
  ∀ x ∈ Icc lo hi, ∀ c ∈ range (x - prev + 1),
    Pass x c hi (a+7) (a+6) ((2*a+7)*(a+6)+1) ((a+6)*(a+3) + ((a+6)*(a+4)-1)) ∨
    Pass x c hi (a+7) (a+7) order pair

/-- Seven finite arithmetic checks indexed by the strip parameter. -/
def Checks (a : ℕ) : Prop :=
  let r := a+7
  let n := (2*a+7)*r
  let pair := r*(a+3) + (r*(a+4)-1)
  Window a (r*(a+1)+1) (r*(a+2)) (r*a+1) (n-3) ((r*(a+3)-1) + (r*(a+4)-3)) ∧
  Window a (r*(a+2)+1) (r*(a+3)-1) (r*(a+1)+1) (n-3) ((r*(a+3)-1) + (r*(a+4)-3)) ∧
  Window a (r*(a+3)) (r*(a+4)-3) (r*(a+2)+1) (n-3) (r*(a+3) + (r*(a+4)-3)) ∧
  Window a (r*(a+3)) (r*(a+4)-2) (r*(a+2)+1) (n-3) (r*(a+3) + (r*(a+4)-2)) ∧
  Window a (r*(a+4)-1) (r*(a+5)-5) (r*(a+3)) (pair-1) pair ∧
  Window a (r*(a+4)-1) (r*(a+5)-4) (r*(a+3)) (pair-1) pair ∧
  ∀ x ∈ Icc (r*(a+2)+1) (r*(a+3)), ∀ c ∈ range (x - (r*(a+1)+1) + 1),
    Pass x c (r*(a+3)) r (a+6) ((2*a+7)*(a+6)+1) ((a+6)*(a+3) + ((a+6)*(a+4)-1)) ∨
    Pass x c (r*(a+3)) r r (pair-1) pair ∨
    ColumnPass x c (r*(a+3)-x) (pair-1) (r*(a+1)+1) (r*(a+5)-3) (a+5) (2*a+7) pair (pair-1)

instance (a : ℕ) : Decidable (Checks a) := by unfold Checks; infer_instance

theorem strip_regime (ha : 1 ≤ a) (checks : Checks a)
    {D : CH.Digraph} {V : Finset ℕ} (free : QFree D V (2*a+7))
    (degree : ∀ v ∈ V, a+7 ≤ (outN D V v).card) (ne : V.Nonempty)
    (small : V.card + 2 ≤ (2*a+7)*(a+7)) : False := by
  obtain ⟨s1,s2,s3,s4,s5,s6,col⟩ := checks
  have e1 : (a+7)*(a+2) = (a+7)*(a+1) + (a+7) := by ring
  have e2 : (a+7)*(a+3) = (a+7)*(a+2) + (a+7) := by ring
  have e3 : (a+7)*(a+4) = (a+7)*(a+3) + (a+7) := by ring
  have e4 : (a+7)*(a+5) = (a+7)*(a+4) + (a+7) := by ring
  have e5 : (2*a+7)*(a+7) = (a+7)*(a+3) + (a+7)*(a+4) := by ring
  have p1 : 1 ≤ (a+7)*(a+1) := Nat.mul_pos (by omega) (by omega)
  have F2 : Floor (2*a+7) (a+7) (a+2) ((a+7)*(a+2)+1) :=
    advance (k := a) (inner a (by omega)) (inner (a+1) le_rfl) (by omega) (by omega)
      (by omega) (by omega) (low_order ha) low3 low4 le_rfl (by omega) order_top mid3 mid4 s1
  have F3 : Floor (2*a+7) (a+7) (a+3) ((a+7)*(a+3)) :=
    (advance (k := a+1) (inner (a+1) le_rfl) F2 (by omega) (by omega)
      (by omega) (by omega) (low_order ha) low3 low4 le_rfl (by omega) order_top mid3 mid4 s2).weaken
      (by omega)
  have F4a : Floor (2*a+7) (a+7) (a+4) ((a+7)*(a+4)-2) :=
    (advance (k := a+2) F2 F3 (by omega) (by omega)
      (by omega) (by omega) (low_order ha) low3 low4 le_rfl (by omega) order_top F3 mid4 s3).weaken
      (by omega)
  have F4 : Floor (2*a+7) (a+7) (a+4) ((a+7)*(a+4)-1) :=
    (advance (k := a+2) F2 F3 (by omega) (by omega)
      (by omega) (by omega) (low_order ha) low3 low4 le_rfl (by omega) order_top F3 F4a s4).weaken
      (by omega)
  have ord : Order (2*a+7) (a+7) ((a+7)*(a+3) + ((a+7)*(a+4)-1) - 1) :=
    order_of_floors (by omega) F3 F4
  have F5a : Floor (2*a+7) (a+7) (a+5) ((a+7)*(a+5)-4) :=
    (advance (k := a+3) F3 F4 (by omega) (by omega)
      (by omega) (by omega) (low_order ha) low3 low4 le_rfl (by omega) ord F3 F4 s5).weaken
      (by omega)
  have F5 : Floor (2*a+7) (a+7) (a+5) ((a+7)*(a+5)-3) :=
    (advance (k := a+3) F3 F4 (by omega) (by omega)
      (by omega) (by omega) (low_order ha) low3 low4 le_rfl (by omega) ord F3 F4 s6).weaken
      (by omega)
  have pos : 0 < V.card := card_pos.mpr ne
  by_cases top : V.card + 2 = (2*a+7)*(a+7)
  · exact column_endpoint (k := a+1) (j := a+4) free degree
      (show V.card = (a+7)*(a+3) + ((a+7)*(a+4)-1) - 1 by omega) (by omega) (by omega) F3 F4
      (by omega) (inner (a+1) le_rfl) F2 F5 (by omega) (by omega)
      (by omega : a+6 ≤ a+7) (by omega : (a+3)+(a+4) ≤ 2*a+7) (low_order ha) low3 low4 col
  · exact capacity_regime free degree rfl pos (by omega : (a+3)+(a+4) ≤ 2*a+7) F3 F4 (by omega)

end Strip

/-- A numerical lower bound using only the same decidable profile tests
at the input degree, for any nonempty free carrier at the stated quota. -/
def orderFloor (q r : ℕ) : ℕ :=
  if 8 ≤ r ∧ q+7 = 2*r ∧ Checks (r-7) then q*r-1 else 0

theorem order_floor {D : CH.Digraph} {V : Finset ℕ} {q r : ℕ}
    (free : QFree D V q) (degree : ∀v∈V, r ≤ (outN D V v).card) (live : V.Nonempty) :
    orderFloor q r ≤ V.card := by
  unfold orderFloor
  split
  · rename_i ok
    obtain ⟨hr,hq,tests⟩ := ok
    let a := r-7
    have er : a+7=r := by dsimp [a]; omega
    have eq : 2*a+7=q := by omega
    by_contra! small
    apply strip_regime (a := a) (by omega) tests (D := D) (V := V)
    · rwa [eq]
    · rwa [er]
    · exact live
    · rw [eq,er]
      omega
  · exact Nat.zero_le _

#print axioms order_floor

set_option maxHeartbeats 0 in
/-- The existing common-successor theorem covers all shifts from 25 on.
Only this bounded arithmetic obligation is needed to join the two proofs. -/
private theorem comparison_window : ∀ a ∈ Icc 2 24, Checks a := by decide +kernel

/-- On the fifth strip the two orders just below the diagonal are now
separated uniformly: every nonempty free graph has at least qr−1 vertices. -/
theorem fifth_order {D : CH.Digraph} {V : Finset ℕ} {q r : ℕ}
    (free : QFree D V q) (degree : ∀v∈V,r≤(outN D V v).card) (live : V.Nonempty)
    (rank : 9≤r) (strip : q+7=2*r) : q*r≤V.card+1 := by
  let a := r-7
  have er : a+7=r := by dsimp [a]; omega
  have eq : 2*a+7=q := by omega
  have hf : QFree D V (2*a+7) := eq ▸ free
  have hd : ∀v∈V,a+7≤(outN D V v).card := er ▸ degree
  by_cases large : 25≤a
  · simpa only [eq,er] using ShenFifthStrip.order_to_one large hf hd live
  · have tests := comparison_window a (mem_Icc.mpr ⟨by omega,by omega⟩)
    by_contra! small
    exact strip_regime (by omega : 1≤a) tests hf hd live (by rw [eq,er]; omega)

#print axioms fifth_order
end LeanCH.BR.FifthStripLedger
