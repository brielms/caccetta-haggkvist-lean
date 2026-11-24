import checkpoints.shen_extension.AcyclicClaimPayment

namespace LeanCH.BR.LowShellCycleSelection
open Finset BRq2 BRq3 BR45 BRsGen ExteriorPacking PhysicalCycleStock

/-- Heads of the source outside the bank that no row of the bank reaches directly. -/
def privateHeads (D : CH.Digraph) (V C : Finset ℕ) (u : ℕ) :=
  (outN D V u \ C) \ exterior D V C

theorem exterior_subset_menu {D V q u C} (free : QFree D V q) (hq : 4≤q)
    (uv : u∈V) (first : C⊆outN D V u) :
    exterior D V C ⊆ (outN D V u\C) ∪ N2 D V u := by
  intro z zm
  obtain ⟨hit,off⟩ := mem_sdiff.mp zm
  obtain ⟨v,vm,vz⟩ := mem_biUnion.mp hit
  rcases mem_union.mp (headX (free.mono_bound hq) uv (first vm) (outN_subset vz) (mem_outN.mp vz).2) with x|y
  · exact mem_union_left _ (mem_sdiff.mpr ⟨x,off⟩)
  · exact mem_union_right _ y

/-- Exact accounting of both uncovered parts of the two-layer menu. -/
theorem gate_balance {D V q u C} (free : QFree D V q) (hq : 4≤q) (uv : u∈V)
    (first : C⊆outN D V u) :
    (privateHeads D V C u).card + (N2 D V u\exterior D V C).card + (exterior D V C).card =
    (outN D V u\C).card + (N2 D V u).card := by
  classical
  let A := outN D V u\C
  let Y := N2 D V u
  let E := exterior D V C
  have dis : Disjoint A Y := disjXY.mono_left sdiff_subset
  have rest : (A\E)∪(Y\E)=(A∪Y)\E := by ext; simp; tauto
  have intact := card_sdiff_add_card_eq_card (exterior_subset_menu free hq uv first)
  change ((A∪Y)\E).card + E.card = (A∪Y).card at intact
  rw [←rest,card_union_of_disjoint (dis.mono sdiff_subset sdiff_subset),card_union_of_disjoint dis] at intact
  exact intact

/-- A walk back to a root heading the bank cannot pass through the bank or
its exterior when the remaining length leaves room for the two return arcs. -/
theorem avoids_columns {D V C v x l q} (free : QFree D V q)
    (common : C⊆outN D V v) (road : Walk D V x v l) (time : l+2≤q) :
    x∉C∪exterior D V C := by
  intro hit
  rcases mem_union.mp hit with c|e
  · exact free v _ (by omega) (by omega) (.step (outN_subset (common c)) (mem_outN.mp (common c)).2 road)
  · obtain ⟨seen,_⟩ := mem_sdiff.mp e
    obtain ⟨a,am,ax⟩ := mem_biUnion.mp seen
    exact free v _ (by omega) (by omega) (.step (outN_subset (common am)) (mem_outN.mp (common am)).2
      (.step (outN_subset ax) (mem_outN.mp ax).2 road))

/-- If the second shell is covered, every short route to another root
heading the same bank must end at one of the literal private first heads. -/
theorem contact_in_gate {D V q u v C k} (free : QFree D V q) (hq : 4≤q)
    (uv : u∈V) (ne : u≠v) (common : C⊆outN D V v)
    (covered : N2 D V u⊆exterior D V C) (time : k+1≤q) (hit : v∈ball D V u k) :
    v∈privateHeads D V C u := by
  obtain ⟨_,l,lk,road⟩ := mem_ball.mp hit
  have fromHead {a m} (path : Walk D V a v m) (am : a∈outN D V u) (lim : m+2≤q) :
      v∈privateHeads D V C u := by
    induction m generalizing a with
    | zero =>
      cases path
      have outside := avoids_columns free common (Walk.refl (D:=D) (W:=V) v) lim
      exact mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨am,fun h=>outside (mem_union_left _ h)⟩,
        fun h=>outside (mem_union_right _ h)⟩
    | succ m ih =>
      cases path with
      | step zm edge tail =>
        have menu := headX (free.mono_bound hq) uv am zm edge
        have avoid := avoids_columns free common tail (by omega)
        exact ih tail ((mem_union.mp menu).resolve_right (fun hy=>avoid (mem_union_right _ (covered hy)))) (by omega)
  cases road with
  | refl => exact (ne rfl).elim
  | step xm ux tail => exact fromHead tail (mem_outN.mpr ⟨xm,ux⟩) (by omega)

/-- With a single available slot, a reachable competing origin determines
both the unique private head and the source's entire second shell. -/
theorem single_slot_collision {D V q u v C k} (free : QFree D V q) (hq : 4≤q)
    (uv : u∈V) (ne : u≠v) (first : C⊆outN D V u) (common : C⊆outN D V v)
    (slots : (outN D V u\C).card≤1) (wide : (N2 D V u).card≤(exterior D V C).card)
    (time : k+1≤q) (hit : v∈ball D V u k) :
    privateHeads D V C u={v} ∧ N2 D V u=exterior D V C := by
  classical
  have bal := gate_balance free hq uv first
  obtain ⟨_,l,lk,rd⟩ := mem_ball.mp hit
  have visited : (privateHeads D V C u).Nonempty := by
    cases rd with
    | refl => exact (ne rfl).elim
    | step av ua tail =>
      have avd := avoids_columns free common tail (by omega)
      exact ⟨_,mem_sdiff.mpr ⟨mem_sdiff.mpr ⟨mem_outN.mpr ⟨av,ua⟩,fun h=>avd (mem_union_left _ h)⟩,
        fun h=>avd (mem_union_right _ h)⟩⟩
  have positive := card_pos.mpr visited
  have same : N2 D V u=exterior D V C := by
    have empty : N2 D V u\exterior D V C=∅ := card_eq_zero.mp (by omega)
    exact eq_of_subset_of_card_le (sdiff_eq_empty_iff_subset.mp empty) (by omega)
  have vm := contact_in_gate free hq uv ne common same.subset time hit
  obtain ⟨a,ha⟩ := card_eq_one.mp (show (privateHeads D V C u).card=1 by omega)
  have va : v=a := mem_singleton.mp (ha ▸ vm)
  exact ⟨va.symm ▸ ha,same⟩


/-- Directed contacts between distinct representatives within the allowed horizon. -/
noncomputable def contacts (D : CH.Digraph) (V U : Finset ℕ) (k : ℕ) :=
  U.offDiag.filter (fun p=>p.2∈ball D V p.1 k)

/-- The only possible origin of a contact has exactly the cycle exterior as
its second shell. Its unique private head fixes the other endpoint as well. -/
theorem at_most_one_contact {D V q U C k} (free : QFree D V q) (hq : 4≤q)
    (sub : U⊆V) (distinct : Set.InjOn (N2 D V) (U : Set ℕ))
    (first : ∀u∈U,C⊆outN D V u) (slots : ∀u∈U,(outN D V u\C).card≤1)
    (wide : ∀u∈U,(N2 D V u).card≤(exterior D V C).card) (time : k+1≤q) :
    (contacts D V U k).card≤1 := by
  classical
  have identify (p : ℕ×ℕ) (pm : p∈contacts D V U k) := by
    obtain ⟨pair,hit⟩ := mem_filter.mp pm
    obtain ⟨a,b,ab⟩ := mem_offDiag.mp pair
    exact single_slot_collision free hq (sub a) ab (first _ a) (first _ b) (slots _ a) (wide _ a) time hit
  apply card_le_one.mpr
  intro p pm t tm
  obtain ⟨pv,py⟩ := identify p pm
  obtain ⟨tv,ty⟩ := identify t tm
  have same := distinct (mem_offDiag.mp (mem_filter.mp pm).1).1
    (mem_offDiag.mp (mem_filter.mp tm).1).1 (py.trans ty.symm)
  have tail : p.1=t.1 := same
  rw [tail] at pv
  exact Prod.ext tail (singleton_injective (pv.symm.trans tv))

/-- All ordered pairs except at most two are genuine ledger receipts. -/
theorem holes_of_contacts {D V U k} (sub : U⊆V) :
    U.offDiag.card ≤ (U.offDiag∩DotClonePairCompletion.orderedIncomparable D V k).card +
      2*(contacts D V U k).card := by
  classical
  let R := contacts D V U k
  let H := U.offDiag∩DotClonePairCompletion.orderedIncomparable D V k
  have cover : U.offDiag ⊆ H ∪ (R ∪ R.image Prod.swap) := by
    intro p pm
    obtain ⟨a,b,ab⟩ := mem_offDiag.mp pm
    by_cases f : p.2∈ball D V p.1 k
    · exact mem_union_right _ (mem_union_left _ (mem_filter.mpr ⟨pm,f⟩))
    by_cases g : p.1∈ball D V p.2 k
    · have rev : p.swap∈R := mem_filter.mpr ⟨mem_offDiag.mpr ⟨b,a,Ne.symm ab⟩,g⟩
      exact mem_union_right _ (mem_union_right _ (mem_image.mpr ⟨_,rev,Prod.swap_swap p⟩))
    exact mem_union_left _ (mem_inter.mpr ⟨pm,mem_filter.mpr ⟨mem_offDiag.mpr ⟨sub a,sub b,ab⟩,f,g⟩⟩)
  have c := (card_le_card cover).trans (card_union_le _ _)
  have d := card_union_le R (R.image Prod.swap)
  have i : (R.image Prod.swap).card≤R.card := card_image_le
  change U.offDiag.card≤H.card+2*R.card
  omega

/-- Residual unit debt after charging actual missed pairs within one
first-layer cohort. This remains valid in a mixed family of physical cycles. -/
theorem first_cohort_debt {D V q U C k} (free : QFree D V q) (hq : 4≤q) (sub : U⊆V)
    (distinct : Set.InjOn (N2 D V) (U : Set ℕ)) (first : ∀u∈U,C⊆outN D V u)
    (slots : ∀u∈U,(outN D V u\C).card≤1)
    (wide : ∀u∈U,(N2 D V u).card≤(exterior D V C).card) (time : k+1≤q) :
    U.card ≤ (U.offDiag∩DotClonePairCompletion.orderedIncomparable D V k).card+2 := by
  have bound := at_most_one_contact free hq sub distinct first slots wide time
  have card := holes_of_contacts (D:=D) (k:=k) sub
  by_cases little : U.card≤2
  · omega
  have square := Nat.mul_le_mul_left U.card (show 3≤U.card by omega)
  rw [offDiag_card] at card
  omega

#print axioms first_cohort_debt

#print axioms single_slot_collision
end LeanCH.BR.LowShellCycleSelection
