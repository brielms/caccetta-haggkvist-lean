import LeanCH.BR.Compose.DeletionPays
import LeanCH.BR.Compose.BankPays

/-!
Incoming floor six at the deficit-one triangle order, from graph axioms and lower-degree CH only.

Paper source: `PairParentThreeOmissionsAndIncomingSixFloor.md` (11 Nov 2026, audited in
`ThreeMissingParents_IndependentAudit.md`). Hypotheses: loopless, minimum outdegree `R ≥ 3`,
no directed cycle of length at most three, order `3R-1`, and CH at degrees `R-1` and `R-2`.
No marker, clock, defect, certificate or order induction.

Small sharpening of the paper: in-degree 3 and 4 are paid at degree `R-1` (rows keep at least `R-1`
heads on at most `3(R-1)` labels); degree `R-2` is needed only for in-degree 5.
-/

namespace Compose.FloorSix

open CH

variable {G : CH.Digraph} {n : Nat}

theorem no2 (loopless : CH.Loopless G n) (noShort : ¬ CH.HasDirectedCycleAtMost G n 3)
    {a b : Nat} (ha : a < n) (hb : b < n) (hab : G a b = true) (hba : G b a = true) : False := by
  have hne : a ≠ b := by
    rintro rfl; rw [loopless a ha] at hab; exact Bool.false_ne_true hab
  apply noShort
  refine ⟨[a, b], ⟨by simp, by simp [hne], ?_, ?_, ?_⟩, by simp⟩
  · intro v hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl <;> assumption
  · exact ⟨hab, trivial⟩
  · simpa using hba

theorem no3 (loopless : CH.Loopless G n) (noShort : ¬ CH.HasDirectedCycleAtMost G n 3)
    {a b c : Nat} (ha : a < n) (hb : b < n) (hc : c < n)
    (hab : G a b = true) (hbc : G b c = true) (hca : G c a = true) : False := by
  have hab' : a ≠ b := by rintro rfl; rw [loopless a ha] at hab; exact Bool.false_ne_true hab
  have hbc' : b ≠ c := by rintro rfl; rw [loopless b hb] at hbc; exact Bool.false_ne_true hbc
  have hac' : a ≠ c := by rintro rfl; exact no2 loopless noShort ha hb hab hbc
  apply noShort
  refine ⟨[a, b, c], ⟨by simp, by simp [hab', hbc', hac'], ?_, ?_, ?_⟩, by simp⟩
  · intro v hv; simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl | rfl <;> assumption
  · exact ⟨hab, hbc, trivial⟩
  · simpa using hca

/-- In-neighbours of `v`. -/
def par (G : CH.Digraph) (n v : Nat) : Finset Nat := (Finset.range n).filter (fun u => G u v = true)

theorem out_card (deg : CH.MinOutdegreeAtLeast G n R) {x : Nat} (hx : x < n) :
    R ≤ ((Finset.range n).filter (fun w => G x w = true)).card := by
  classical
  obtain ⟨nbrs, hlen, hnd, hmem⟩ := deg x hx
  have hsub : nbrs.toFinset ⊆ (Finset.range n).filter (fun w => G x w = true) := by
    intro w hw
    have := hmem w (List.mem_toFinset.mp hw)
    simp [this.1, this.2]
  have := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup hnd, hlen] at this
  exact this

/-- Three omissions (paper eq. (1)): for `x ≠ v`, at least three in-neighbours of `v` are not
out-neighbours of `x`. Uses only the pair-common-parent law. -/
theorem three_omissions
    (loopless : CH.Loopless G n) (noShort : ¬ CH.HasDirectedCycleAtMost G n 3)
    (P : ∀ i j, i < n → j < n → i ≠ j → ∃ w, w < n ∧ w ≠ i ∧ w ≠ j ∧ G w i = true ∧ G w j = true)
    {v x : Nat} (hv : v < n) (hx : x < n) (hxv : x ≠ v) :
    3 ≤ ((par G n v).filter (fun u => ¬ G x u = true)).card := by
  classical
  have N2 := fun {a b : Nat} => @no2 G n loopless noShort a b
  have N3 := fun {a b c : Nat} => @no3 G n loopless noShort a b c
  -- c : common parent of v and x
  obtain ⟨c, hc, hcv', hcx', hcv, hcx⟩ := P v x hv hx (Ne.symm hxv)
  -- d : common parent of v and c
  obtain ⟨d, hd, hdv', hdc', hdv, hdc⟩ := P v c hv hc (Ne.symm hcv')
  -- y : common parent of x and d
  have hdx : d ≠ x := by rintro rfl; exact N2 hc hd hcx hdc
  obtain ⟨y, hy, hyx', hyd', hyx, hyd⟩ := P x d hx hd (Ne.symm hdx)
  have hyv : y ≠ v := by rintro rfl; exact N2 hd hv hdv hyd
  -- a : common parent of v and y
  obtain ⟨a, ha, hav', hay', hav, hay⟩ := P v y hv hy (Ne.symm hyv)
  let A := (par G n v).filter (fun u => ¬ G x u = true)
  have memA : ∀ u, u < n → G u v = true → ¬ G x u = true → u ∈ A := by
    intro u hu h1 h2; simp [A, par, hu, h1, h2]
  have cA : c ∈ A := memA c hc hcv (fun h => N2 hx hc h hcx)
  have dA : d ∈ A := memA d hd hdv (fun h => N3 hd hc hx hdc hcx h)
  have aA : a ∈ A := memA a ha hav (fun h => N3 ha hy hx hay hyx h)
  have hcd : c ≠ d := by rintro rfl; rw [loopless c hc] at hdc; exact Bool.false_ne_true hdc
  have had : a ≠ d := by rintro rfl; exact N2 ha hy hay hyd
  have hac : a ≠ c := by rintro rfl; exact N3 ha hy hd hay hyd hdc
  have hsub : ({a, c, d} : Finset Nat) ⊆ A := by
    intro u hu; simp only [Finset.mem_insert, Finset.mem_singleton] at hu
    rcases hu with rfl | rfl | rfl <;> assumption
  have hcard : ({a, c, d} : Finset Nat).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hac, had]), Finset.card_pair hcd]
  have := Finset.card_le_card hsub
  rw [hcard] at this
  exact this

/-- Incoming floor six at order `3R-1`. -/
theorem incoming_floor_six
    {R v : Nat} (hR : 3 ≤ R)
    (ih1 : CH.Research.FixedDegreeCH (R - 1)) (ih2 : CH.Research.FixedDegreeCH (R - 2))
    (loopless : CH.Loopless G (3 * R - 1)) (deg : CH.MinOutdegreeAtLeast G (3 * R - 1) R)
    (noShort : ¬ CH.HasDirectedCycleAtMost G (3 * R - 1) 3) (hv : v < 3 * R - 1) :
    6 ≤ (par G (3 * R - 1) v).card := by
  classical
  set n := 3 * R - 1 with hn
  have P : ∀ i j, i < n → j < n → i ≠ j → ∃ w, w < n ∧ w ≠ i ∧ w ≠ j ∧ G w i = true ∧ G w j = true :=
    fun i j hi hj hij =>
      Compose.DeletionPays.deficit_one_pair_common_parent (by omega) ih1 loopless deg noShort hi hj hij
  by_contra hlt
  push Not at hlt
  set i := (par G n v).card with hi
  -- at least three in-neighbours, from the omission bound at any other vertex
  have hge3 : 3 ≤ i := by
    let x := if v = 0 then 1 else 0
    have hx : x < n := by simp only [x]; split <;> omega
    have hxv : x ≠ v := by simp only [x]; split <;> omega
    exact (three_omissions loopless noShort P hv hx hxv).trans (Finset.card_filter_le _ _)
  -- delete the bank D = {v} ∪ I(v)
  let D := insert v (par G n v)
  let K := Finset.range n \ D
  have hvpar : v ∉ par G n v := by simp [par, loopless v hv]
  have hDsub : D ⊆ Finset.range n := by
    intro u hu; simp only [D, Finset.mem_insert] at hu
    rcases hu with rfl | hu
    · exact Finset.mem_range.mpr hv
    · exact (Finset.mem_filter.mp hu).1
  have hKcard : K.card = n - (i + 1) := by
    simp only [K]
    rw [Finset.card_sdiff_of_subset hDsub, Finset.card_range, Finset.card_insert_of_notMem hvpar]
  have hKsub : K ⊆ Finset.range n := Finset.sdiff_subset
  -- each retained row keeps at least R - (i - 3) heads inside K
  have hrow : ∀ x ∈ K, R - (i - 3) ≤ (K.filter (fun w => G x w = true)).card := by
    intro x hxK
    have hxn : x < n := Finset.mem_range.mp (hKsub hxK)
    have hxD : x ∉ D := (Finset.mem_sdiff.mp hxK).2
    have hxv : x ≠ v := fun h => hxD (by simp [D, h])
    have hxpar : ¬ G x v = true := fun h => hxD (by simp [D, par, hxn, h])
    have hout := out_card deg hxn
    have hsplit : (Finset.range n).filter (fun w => G x w = true) ⊆
        K.filter (fun w => G x w = true) ∪ (par G n v).filter (fun u => G x u = true) := by
      intro w hw
      obtain ⟨hwn, hG⟩ := Finset.mem_filter.mp hw
      by_cases hwD : w ∈ D
      · refine Finset.mem_union_right _ ?_
        simp only [D, Finset.mem_insert] at hwD
        rcases hwD with rfl | hwpar
        · exact absurd hG hxpar
        · exact Finset.mem_filter.mpr ⟨hwpar, hG⟩
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hwn, hwD⟩, hG⟩)
    have hle := (Finset.card_le_card hsplit).trans (Finset.card_union_le _ _)
    have hom := three_omissions loopless noShort P hv hxn hxv
    have hpart := Finset.card_filter_add_card_filter_not
      (s := par G n v) (fun u => G x u = true)
    omega
  have hn8 : n = 3 * R - 1 := rfl
  by_cases h45 : i ≤ 4
  · -- pay at degree R - 1
    apply noShort
    refine Compose.BankPays.bank_pays hKsub (by omega) (by omega) (by omega) loopless ?_ ih1
    intro x hx; have := hrow x hx; omega
  · -- i = 5: pay at degree R - 2
    apply noShort
    refine Compose.BankPays.bank_pays hKsub (by omega) (by omega) (by omega) loopless ?_ ih2
    intro x hx; have := hrow x hx; omega

end Compose.FloorSix
