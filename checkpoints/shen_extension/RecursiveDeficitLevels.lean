import checkpoints.shen_extension.TransitionClosure
import LeanCH.BR.BRDeficiencyCompletion
import LeanCH.BR.BRNearBoundaryRows
import checkpoints.shen_extension.WeightedHost

/-! Bounds on all deficit levels of a state, at arbitrary cutoff.
The lower-degree order bound is a hypothesis. The original state's graph
can be any valid state, regardless of the edits by which it was reached. -/
namespace LeanCH.BR.Closure.DeficitLevels
open BRq2 BRq3 Finset

def cost (s : ℕ) (D : CH.Digraph) (U : Finset ℕ) (v : ℕ) :=
  s - (outN D U v).card

def total (s : ℕ) (D : CH.Digraph) (U : Finset ℕ) :=
  ∑ v ∈ U, cost s D U v

def OrderLaw (q j lower : ℕ) : Prop :=
  ∀ D U, QFree D U q → (∀ v ∈ U, j ≤ (outN D U v).card) → U.Nonempty → lower ≤ U.card

/-- After deleting a set R, retain the links to the individual deleted labels. -/
theorem set_price {D : CH.Digraph} {U R : Finset ℕ} {s q L : ℕ}
    (free : QFree D U q) (sub : R ⊆ U) (law : OrderLaw q (s-R.card) L)
    (live : (U \ R).Nonempty) (heads : ∀ u ∈ U \ R, 1 ≤ (outN D (U \ R) u).card) :
    L + R.card ≤ U.card + ∑ u ∈ U \ R, (cost s D U u - (R \ outN D U u).card) := by
  have price (u : ℕ) : s-R.card-(outN D (U \ R) u).card =
        cost s D U u - (R \ outN D U u).card := by
    have er : outN D (U \ R) u = outN D U u \ R := by
      ext z; simp only [mem_outN, mem_sdiff]; tauto
    rw [er]
    have a := card_sdiff_add_card_inter (outN D U u) R
    have b := card_sdiff_add_card_inter R (outN D U u)
    rw [inter_comm R] at b
    unfold cost
    omega
  have b := BRsGen.deficiency_bound_of_size law (free.mono_set sdiff_subset) heads live
  have sumEq := Finset.sum_congr (s₁:=U \ R) rfl (fun u _ => price u)
  rw [sumEq] at b
  have sz := card_sdiff_add_card_eq_card sub
  omega

/-- The removed short row costs its entire deficit, and each other short
row missing it saves a further unit in a degree-(s-1) completion. -/
theorem short_row_price {D : CH.Digraph} {U B : Finset ℕ} {s q L v : ℕ}
    (free : QFree D U q) (law : OrderLaw q (s-1) L) (hq : 1 ≤ q)
    (small : total s D U < s) (hv : v∈U) (short : 0 < cost s D U v)
    (sub : B ⊆ U.erase v)
    (miss : ∀ u ∈ B, 0 < cost s D U u ∧ D u v ≠ true) :
    L + 1 + cost s D U v + B.card ≤ U.card + total s D U := by
  classical
  let V := U.erase v
  let a := cost s D U
  have sumDel : (∑ u ∈ V, a u) + a v = total s D U := sum_erase_add _ _ hv
  have av : 0 < a v := short
  have degV (u : ℕ) : outN D V u = (outN D U u).erase v := by
    ext z; simp only [V, mem_outN,mem_erase]; tauto
  have pos (u) (hu : u∈V) : 1 ≤ (outN D V u).card := by
    have le := single_le_sum (f:=a) (fun _ _ => Nat.zero_le _) hu
    have paid : a u + a v ≤ total s D U := by omega
    change s - (outN D U u).card + a v ≤ total s D U at paid
    rw [degV]
    have er := pred_card_le_card_erase (s:=outN D U u) (a:=v)
    omega
  have live : V.Nonempty := by
    have le := single_le_sum (f:=a) (fun _ _ => Nat.zero_le _) hv
    change a v ≤ total s D U at le
    change s-(outN D U v).card ≤ total s D U at le
    obtain ⟨u,hu⟩ := card_pos.mp (show 0 < (outN D U v).card by omega)
    refine ⟨u, mem_erase.mpr ⟨?_, (mem_outN.mp hu).1⟩⟩
    intro e
    exact loopfree free hq hv (e ▸ (mem_outN.mp hu).2)
  have base := BRsGen.deficiency_bound_of_size law (free.mono_set (erase_subset v U)) pos live
  have row (u) (_hu : u∈V) : s-1-(outN D V u).card + (if u∈B then 1 else 0) ≤ a u := by
    rw [degV]
    change _ ≤ s-(outN D U u).card
    split_ifs with hit
    · obtain ⟨positive,no⟩ := miss u hit
      change 0 < s-(outN D U u).card at positive
      rw [erase_eq_of_notMem (fun h => no (mem_outN.mp h).2)]
      omega
    · have := pred_card_le_card_erase (s:=outN D U u) (a:=v)
      omega
  have budget := sum_le_sum row
  rw [sum_add_distrib] at budget
  have num : (∑ u ∈ V, (if u∈B then 1 else 0 : ℕ)) = B.card := by
    rw [← card_filter]
    congr 1
    ext u
    simp only [mem_filter]
    exact ⟨And.right, fun h => ⟨sub h,h⟩⟩
  rw [num] at budget
  have sz : V.card = U.card-1 := card_erase_of_mem hv
  have up := card_pos.mpr (show U.Nonempty from ⟨v,hv⟩)
  change L ≤ V.card + ∑ u ∈ V, (s-1-(outN D V u).card) at base
  change L + 1 + a v + B.card ≤ U.card + total s D U
  omega

/-- Test any nonempty group of at most q rows missing at least j heads each. -/
theorem level_price {D : CH.Digraph} {U S : Finset ℕ} {s q L j : ℕ}
    (free : QFree D U q) (law : OrderLaw q (s-1) L) (small : total s D U < s)
    (sub : S ⊆ U) (live : S.Nonempty) (few : S.card ≤ q)
    (hj : 0 < j) (level : ∀ v ∈ S, j ≤ cost s D U v) :
    L + j + S.card ≤ U.card + total s D U := by
  obtain ⟨v,hv,no⟩ := exists_sink (free.reverse.mono_set sub) live few
  have pos := card_pos.mpr live
  have use := short_row_price free law (by omega) small (sub hv) (by have := level v hv; omega)
    (erase_subset_erase v sub) (fun u hu => ⟨by have := level u (mem_of_mem_erase hu); omega,
      no _ (mem_of_mem_erase hu)⟩)
  rw [card_erase_of_mem hv] at use
  have := level v hv
  omega

/-- The same constraint at every node reached by the capstone rules. -/
theorem reachable_level_price {q s L j : ℕ} (O : Origin q s) {st : State}
    (reached : Reach (Step q s) O.init st) (law : OrderLaw q (s-1) L)
    (small : total s st.H st.U < s) {S : Finset ℕ} (sub : S ⊆ st.U)
    (live : S.Nonempty) (few : S.card ≤ q) (hj : 0<j)
    (level : ∀ v ∈ S, j ≤ cost s st.H st.U v) :
    L+j+S.card ≤ st.U.card + total s st.H st.U :=
  level_price (reach_valid O reached).2.2 law small sub live few hj level

#print axioms set_price
#print axioms short_row_price
#print axioms level_price
#print axioms reachable_level_price
/-- A single clone of a head pays one unit simultaneously to every short
parent of that head. All residual units can be paid on the same blow-up. -/
theorem column_price {D : CH.Digraph} {U P : Finset ℕ} {s q N c : ℕ}
    (free : QFree D U q) (law : OrderLaw q s N) (live : U.Nonempty)
    (small : total s D U < s) (hc : c∈U) (sub : P ⊆ U)
    (parents : ∀ u∈P, 0 < cost s D U u ∧ D u c=true) :
    N + P.card ≤ U.card + total s D U + 1 := by
  classical
  let a := cost s D U
  have choices (u : ℕ) : ∃ z, u∈U → z∈outN D U u := by
    by_cases hu : u∈U
    · have le := single_le_sum (s:=U) (f:=a) (fun _ _ => Nat.zero_le _) hu
      change s-(outN D U u).card ≤ total s D U at le
      obtain ⟨z,hz⟩ := card_pos.mp (show 0 < (outN D U u).card by omega)
      exact ⟨z,fun _ => hz⟩
    · exact ⟨0,fun h => (hu h).elim⟩
  choose f hf using choices
  let rem (u : ℕ) := a u - (if u∈P then 1 else 0)
  let clones (z : ℕ) := (if z=c then 1 else 0) + ∑ u∈U, (if f u=z then rem u else 0)
  have paid (u) (hu : u∈U) : s ≤ (outN D U u).card + ∑ z∈outN D U u, clones z := by
    have fu := hf u hu
    have costLe : s ≤ (outN D U u).card + a u := by dsimp [a,cost]; omega
    simp only [clones, sum_add_distrib]
    have own : rem u ≤ ∑ z∈outN D U u, ∑ v∈U, (if f v=z then rem v else 0) := by
      apply le_trans _ (single_le_sum (f:=fun z => ∑ v∈U, (if f v=z then rem v else 0))
        (fun _ _ => Nat.zero_le _) fu)
      simpa using single_le_sum (f:=fun v => if f v=f u then rem v else 0)
        (fun _ _ => Nat.zero_le _) hu
    by_cases up : u∈P
    · have huc := mem_outN.mpr ⟨hc,(parents u up).2⟩
      have contrib := single_le_sum (f:=fun z => if z=c then 1 else (0:ℕ))
        (fun _ _ => Nat.zero_le _) huc
      simp only [ite_true] at contrib
      have eq : rem u = a u-1 := by simp [rem,up]
      omega
    · have eq : rem u = a u := by simp [rem,up]
      omega
  have out := WeightedHost.cover_bound law clones free live paid
  have sumClones : (∑ z∈U, clones z) = 1 + ∑ u∈U, rem u := by
    simp only [clones,sum_add_distrib]
    rw [Finset.sum_comm (s:=U) (t:=U)]
    have first : (∑ z∈U, if z=c then 1 else (0:ℕ))=1 := by simp [hc]
    rw [first]
    congr 1
    apply sum_congr rfl
    intro u hu
    have := outN_subset (hf u hu)
    simp [this]
  have num : (∑ u ∈ U, (if u∈P then 1 else 0 : ℕ)) = P.card := by
    rw [← card_filter]
    congr 1
    ext u
    simp only [mem_filter]
    exact ⟨And.right, fun h => ⟨sub h,h⟩⟩
  have split : (∑ u∈U, rem u) + P.card = total s D U := by
    rw [← num, ← sum_add_distrib]
    apply sum_congr rfl
    intro u _
    change rem u + (if u∈P then 1 else 0) = a u
    by_cases up : u∈P
    · have pos : 0<a u := (parents u up).1
      simp [rem,up]; omega
    · simp [rem,up]
  omega

#print axioms column_price
/-- The row deletion and shared clone use the same parent incidence in
opposite directions. Keeping that label gives a bound for every short row. -/
theorem row_and_column {D : CH.Digraph} {U T : Finset ℕ} {d q n g e v : ℕ}
    (free : QFree D U q) (native : OrderLaw q (d+1) n)
    (lower : OrderLaw q d (q*d+1)) (hq : 1≤q) (size : n+e=q*(d+1))
    (gap : n+g=U.card+total (d+1) D U) (small : total (d+1) D U < d+1)
    (sub : T ⊆ U) (short : ∀ u∈T, 0<cost (d+1) D U u) (hv : v∈T) :
    cost (d+1) D U v + T.card + e ≤ q+2*g := by
  classical
  let P := (T.erase v).filter (fun u => D u v=true)
  let B := T.erase v \ P
  have ps : P ⊆ T.erase v := filter_subset _ _
  have bv : B ⊆ U.erase v := sdiff_subset.trans (erase_subset_erase v sub)
  have cut := short_row_price (s:=d+1) free (by simpa using lower) hq small (sub hv) (short _ hv) bv (by
    intro u hu
    obtain ⟨h,no⟩ := mem_sdiff.mp hu
    exact ⟨short _ (mem_of_mem_erase h), fun a => no (mem_filter.mpr ⟨h,a⟩)⟩)
  have col := column_price free native ⟨v,sub hv⟩ small (sub hv) (ps.trans ((erase_subset _ _).trans sub)) (by
    intro u hu
    exact ⟨short _ (mem_of_mem_erase (ps hu)), (mem_filter.mp hu).2⟩)
  have parts : B.card + P.card = (T.erase v).card := card_sdiff_add_card_eq_card ps
  rw [card_erase_of_mem hv] at parts
  have tpos := card_pos.mpr (show T.Nonempty from ⟨v,hv⟩)
  rw [Nat.mul_add, Nat.mul_one] at size
  omega

/-- A rectangle bound on the entire shortfall of a valid recursive state.
It holds for every cutoff and every admissible arc history. -/
theorem valid_budget {q d g e : ℕ} (O : Origin q (d+1)) {st : State}
    (valid : Valid O st) (lower : OrderLaw q d (q*d+1)) (hq : 1≤q)
    (size : O.V.card+e=q*(d+1)) (gap : O.V.card+g=st.U.card+total (d+1) st.H st.U)
    (small : total (d+1) st.H st.U < d+1) :
    let t := (st.U.filter (fun u => 0<cost (d+1) st.H st.U u)).card
    total (d+1) st.H st.U + t*t + t*e ≤ t*(q+2*g) := by
  classical
  let T := st.U.filter (fun u => 0<cost (d+1) st.H st.U u)
  change total _ _ _ + T.card*T.card + T.card*e ≤ T.card*(q+2*g)
  have sumT : (∑ u ∈ T, cost (d+1) st.H st.U u) = total (d+1) st.H st.U := by
    unfold T total
    rw [sum_filter]
    apply sum_congr rfl
    intro u _
    split_ifs <;> omega
  have atRow (v) (hv : v∈T) := row_and_column valid.2.2 O.least lower hq size gap small
    (filter_subset _ _) (fun _ hu => (mem_filter.mp hu).2) hv
  have sumRows := sum_le_sum atRow
  simp only [sum_add_distrib, sumT, sum_const, Nat.nsmul_eq_mul] at sumRows
  simpa only [Nat.mul_add] using sumRows

#print axioms row_and_column
#print axioms valid_budget
/-- Arc maximality on W, expressed by a short return at every missing arc. -/
def MaximalReturns (q : ℕ) (D : CH.Digraph) (W : Finset ℕ) : Prop :=
  ∀ u∈W, ∀ z∈W, D u z ≠ true → ∃ k, k+1≤q ∧ Walk D W z u k

/-- A short return ending at u cannot pass through any head of u. -/
theorem return_off_heads {D : CH.Digraph} {W R : Finset ℕ} {q k u z : ℕ}
    (free : QFree D W q) (sub : R ⊆ outN D W u) (short : k+1≤q)
    (w : Walk D W z u k) : Walk D (W \ R) z u k := by
  induction w with
  | refl => exact .refl _
  | @step a b c l hb ab tail ih =>
    have missed : b∉R := by
      intro hit
      exact free c (l+1) (by omega) (by omega) (.step hb (mem_outN.mp (sub hit)).2 tail)
    exact .step (mem_sdiff.mpr ⟨hb,missed⟩) ab (ih sub (by omega))

private theorem lift_kept {D E : CH.Digraph} {V : Finset ℕ} {a b k : ℕ}
    (keep : ∀ x∈V, ∀ y∈V, D x y=true → E x y=true)
    (w : Walk D V a b k) (ha : a∈V) : Walk E V a b k := by
  induction w with
  | refl => exact .refl _
  | step hb e _ ih => exact .step hb (keep _ ha _ hb e) (ih hb)

/-- Any valid extension preserving the surviving original arcs has exactly
the original surviving heads at each common parent of the deleted set. -/
theorem common_parent_fixed {D E : CH.Digraph} {W R : Finset ℕ} {u q : ℕ}
    (free : QFree D W q) (maximal : MaximalReturns q D W) (hu : u∈W \ R)
    (sub : R ⊆ outN D W u) (safe : QFree E (W \ R) q)
    (keep : ∀ a∈W \ R, ∀ b∈W \ R, D a b=true → E a b=true) :
    outN E (W \ R) u = outN D (W \ R) u := by
  ext z
  constructor
  · intro hit
    obtain ⟨hz,uz⟩ := mem_outN.mp hit
    refine mem_outN.mpr ⟨hz,?_⟩
    by_contra missing
    obtain ⟨k,kq,back⟩ := maximal u (mem_sdiff.mp hu).1 z (mem_sdiff.mp hz).1 missing
    exact safe u (k+1) (by omega) kq (.step hz uz
      (lift_kept keep (return_off_heads free sub kq back) hz))
  · intro hit
    obtain ⟨hz,uz⟩ := mem_outN.mp hit
    exact mem_outN.mpr ⟨hz,keep _ hu _ hz uz⟩

/-- On a one-label puncture the entire shortfall is invariant, even for
valid extensions that need not be reachable by the recursive rules. -/
theorem one_hole_exact {D E : CH.Digraph} {W : Finset ℕ} {v q s : ℕ}
    (free : QFree D W q) (maximal : MaximalReturns q D W) (hv : v∈W)
    (degrees : ∀ u∈W, s≤(outN D W u).card) (safe : QFree E (W \ {v}) q)
    (keep : ∀ a∈W \ {v}, ∀ b∈W \ {v}, D a b=true → E a b=true) :
    total s E (W \ {v}) = total s D (W \ {v}) := by
  apply sum_congr rfl
  intro u hu
  by_cases hit : D u v=true
  · have sub : {v} ⊆ outN D W u := singleton_subset_iff.mpr (mem_outN.mpr ⟨hv,hit⟩)
    unfold cost
    rw [common_parent_fixed free maximal hu sub safe keep]
  · have eq : outN D (W \ {v}) u = outN D W u := by
      ext z
      simp only [mem_outN, mem_sdiff, mem_singleton]
      constructor
      · exact fun h => ⟨h.1.1,h.2⟩
      · rintro ⟨hz,uz⟩
        exact ⟨⟨hz,fun e => hit (e ▸ uz)⟩,uz⟩
    have inc : outN D (W \ {v}) u ⊆ outN E (W \ {v}) u := by
      intro z hz
      exact mem_outN.mpr ⟨(mem_outN.mp hz).1,keep _ hu _ (mem_outN.mp hz).1 (mem_outN.mp hz).2⟩
    have le := card_le_card inc
    have deg := degrees u (mem_sdiff.mp hu).1
    unfold cost
    rw [eq] at le ⊢
    omega

#print axioms common_parent_fixed
#print axioms one_hole_exact
end LeanCH.BR.Closure.DeficitLevels
