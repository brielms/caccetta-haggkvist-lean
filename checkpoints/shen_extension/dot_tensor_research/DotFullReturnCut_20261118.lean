import checkpoints.shen_extension.DeleteRepairUnlock

/-!
# Full last-return cut on the CURRENT graph

For distinct current vertices p,w with p→w absent, recompute ALL donors
Z={z: w reaches z within q-2 CURRENT steps and z→p}. Cut every donor arc z→p,
then add p→w. Safety and the exact debit vector are proved for every q>=2.
No donor is assumed paid; this is not a source contradiction or CH closure.
-/
namespace LeanCH.BR.DotFullReturnCut
open LeanCH.BR.BRq2 LeanCH.BR.BRq3

noncomputable def donors (D : CH.Digraph) (V : Finset ℕ) (q p w : ℕ) : Finset ℕ :=
  (ball D V w (q-2)).filter (fun z => D z p = true)

@[simp] theorem mem_donors {D : CH.Digraph} {V : Finset ℕ} {q p w z : ℕ} :
    z ∈ donors D V q p w ↔ z ∈ ball D V w (q-2) ∧ D z p = true := by
  simp [donors]

/-- Remove precisely the old arcs whose tail lies in Z and whose head is p. -/
def cut (D : CH.Digraph) (Z : Finset ℕ) (p : ℕ) : CH.Digraph :=
  fun a b => D a b && decide (a ∉ Z ∨ b ≠ p)

@[simp] theorem cut_edge {D : CH.Digraph} {Z : Finset ℕ} {p a b : ℕ} :
    cut D Z p a b = true ↔ D a b = true ∧ (a ∉ Z ∨ b ≠ p) := by
  simp [cut]

theorem cut_sub {D : CH.Digraph} {Z : Finset ℕ} {p a b : ℕ}
    (h : cut D Z p a b = true) : D a b = true := (cut_edge.mp h).1

noncomputable def transition (D : CH.Digraph) (V : Finset ℕ) (q p w : ℕ) : CH.Digraph :=
  DeleteRepair.repair (cut D (donors D V q p w) p) {p} (fun _ => {w})

theorem donor_subset {D : CH.Digraph} {V : Finset ℕ} {q p w : ℕ} :
    donors D V q p w ⊆ V := fun _ hz => ball_subset (mem_donors.mp hz).1

theorem receiver_not_donor {D : CH.Digraph} {V : Finset ℕ} {q p w : ℕ}
    (hq : 2 ≤ q) (hf : QFree D V q) (hp : p ∈ V) : p ∉ donors D V q p w := by
  intro hz
  exact loopfree hf (by omega) hp (mem_donors.mp hz).2

/-- ALL short returns are cut: the final predecessor of any surviving return
would itself be in the recomputed donor set, contradicting its retained last arc. -/
theorem no_short_return_after_cut {D : CH.Digraph} {V : Finset ℕ} {q p w m : ℕ}
    (hq : 2 ≤ q) (hw : w ∈ V) (hne : p ≠ w) (hm : m+1 ≤ q) :
    ¬ Walk (cut D (donors D V q p w) p) V w p m := by
  intro path
  cases m with
  | zero =>
      cases path
      exact hne rfl
  | succ m =>
      obtain ⟨z, prewalk, _, last⟩ := path.unsnoc
      have native : Walk D V w z m := walk_sub (fun _ _ h => cut_sub h) prewalk
      have hzV : z ∈ V := by
        rcases native.end_mem_or with he | hz
        · simpa only [he] using hw
        · exact hz
      have hz : z ∈ donors D V q p w := mem_donors.mpr
        ⟨mem_ball.mpr ⟨hzV, m, by omega, native⟩, cut_sub last⟩
      obtain ⟨_, keep⟩ := cut_edge.mp last
      exact keep.elim (fun hn => hn hz) (fun hn => hn rfl)

/-- Joint safety of the actual cut-plus-add transition, recomputed from D. -/
theorem transition_qfree {D : CH.Digraph} {V : Finset ℕ} {q p w : ℕ}
    (hq : 2 ≤ q) (hf : QFree D V q) (hw : w ∈ V) (hne : p ≠ w) :
    QFree (transition D V q p w) V q := by
  have base : QFree (cut D (donors D V q p w) p) V q := by
    intro a m hm hmq path
    exact hf a m hm hmq (walk_sub (fun _ _ h => cut_sub h) path)
  apply DeleteRepair.repair_qfree_half base
  · intro u hu z hz m hm
    have hu' : u = p := Finset.mem_singleton.mp hu
    have hz' : z = w := Finset.mem_singleton.mp hz
    subst u
    subst z
    exact no_short_return_after_cut hq hw hne hm
  · intro u _ z hz u' hu' m hm
    have hz' : z = w := Finset.mem_singleton.mp hz
    have hu'' : u' = p := Finset.mem_singleton.mp hu'
    subst z
    subst u'
    exact no_short_return_after_cut hq hw hne (by omega)

theorem cut_outside_row {D : CH.Digraph} {V Z : Finset ℕ} {p x : ℕ}
    (hx : x ∉ Z) : outN (cut D Z p) V x = outN D V x := by
  ext y
  simp [mem_outN, cut, hx]

theorem cut_donor_row {D : CH.Digraph} {V Z : Finset ℕ} {p x : ℕ}
    (hx : x ∈ Z) : outN (cut D Z p) V x = (outN D V x).erase p := by
  ext y
  simp only [mem_outN, cut_edge, Finset.mem_erase]
  simp only [hx, not_true_eq_false, false_or]
  tauto

theorem transition_other_row {D : CH.Digraph} {V : Finset ℕ} {q p w x : ℕ}
    (hx : x ≠ p) :
    outN (transition D V q p w) V x = outN (cut D (donors D V q p w) p) V x := by
  ext y
  simp [mem_outN, transition, DeleteRepair.repair, hx]

theorem transition_receiver_row {D : CH.Digraph} {V : Finset ℕ} {q p w : ℕ}
    (hq : 2 ≤ q) (hf : QFree D V q) (hp : p ∈ V) (hw : w ∈ V) :
    outN (transition D V q p w) V p = insert w (outN D V p) := by
  have hpZ := receiver_not_donor hq hf hp (w := w)
  ext y
  by_cases hy : y = w
  · subst y
    simp [mem_outN, transition, DeleteRepair.repair, cut, hpZ, hw]
  · simp [mem_outN, transition, DeleteRepair.repair, cut, hpZ, hy]

/-- Exact debit vector in three disjoint row classes. The receiver gains one,
each physical donor loses one, every remaining row is literally unchanged. -/
theorem exact_row_debits {D : CH.Digraph} {V : Finset ℕ} {q p w : ℕ}
    (hq : 2 ≤ q) (hf : QFree D V q) (hp : p ∈ V) (hw : w ∈ V)
    (missing : D p w ≠ true) :
    (outN (transition D V q p w) V p).card = (outN D V p).card+1 ∧
    (∀ z ∈ donors D V q p w,
      (outN (transition D V q p w) V z).card+1 = (outN D V z).card) ∧
    (∀ x, x ≠ p → x ∉ donors D V q p w →
      outN (transition D V q p w) V x = outN D V x) := by
  have hpZ := receiver_not_donor hq hf hp (w := w)
  refine ⟨?_, ?_, ?_⟩
  · rw [transition_receiver_row hq hf hp hw, Finset.card_insert_of_notMem]
    exact fun h => missing (mem_outN.mp h).2
  · intro z hz
    have hzp : z ≠ p := by intro he; subst z; exact hpZ hz
    rw [transition_other_row hzp, cut_donor_row hz]
    exact Finset.card_erase_add_one (mem_outN.mpr ⟨hp, (mem_donors.mp hz).2⟩)
  · intro x hxp hxZ
    rw [transition_other_row hxp, cut_outside_row hxZ]

/-- Signed version of the same exact native row accounting. No buffer or
minimum-degree payment is asserted by this equality. -/
theorem exact_signed_debit {D : CH.Digraph} {V : Finset ℕ} {q p w : ℕ}
    (hq : 2 ≤ q) (hf : QFree D V q) (hp : p ∈ V) (hw : w ∈ V)
    (missing : D p w ≠ true) (x : ℕ) :
    ((outN (transition D V q p w) V x).card : ℤ) =
      ((outN D V x).card : ℤ) + (if x=p then 1 else 0) -
        (if x ∈ donors D V q p w then 1 else 0) := by
  obtain ⟨gain, loss, same⟩ := exact_row_debits hq hf hp hw missing
  have hpZ := receiver_not_donor hq hf hp (w := w)
  by_cases hxp : x=p
  · subst x
    simp [hpZ, gain]
  · by_cases hxZ : x ∈ donors D V q p w
    · have hl := loss x hxZ
      simp only [ite_eq_right hxp, ite_eq_left hxZ]
      omega
    · rw [same x hxp hxZ]
      simp [hxp, hxZ]

/-- At the q=2 boundary, the only possible donor is w itself, precisely when
the old reverse arc w→p exists. Closed radius zero must not be omitted. -/
theorem donors_at_two {D : CH.Digraph} {V : Finset ℕ} {p w : ℕ} (hw : w ∈ V) :
    donors D V 2 p w = if D w p = true then {w} else ∅ := by
  ext z
  constructor
  · intro hz
    obtain ⟨reach, arc⟩ := mem_donors.mp hz
    obtain ⟨_, m, hm, path⟩ := mem_ball.mp reach
    have hm0 : m = 0 := by omega
    subst m
    cases path
    simp [arc]
  · intro hz
    split_ifs at hz with arc
    · have he : z = w := Finset.mem_singleton.mp hz
      subst z
      exact mem_donors.mpr ⟨self_mem_ball hw, arc⟩
    · simp at hz

/-- Complete current-graph transition package. No minimum degree, donor buffer,
source leastness, original-state saturation, or repair-existence premise is hidden. -/
theorem current_graph_transition {D : CH.Digraph} {V : Finset ℕ} {q p w : ℕ}
    (hq : 2 ≤ q) (hf : QFree D V q) (hp : p ∈ V) (hw : w ∈ V)
    (hne : p ≠ w) (missing : D p w ≠ true) :
    QFree (transition D V q p w) V q ∧
    ∀ x, ((outN (transition D V q p w) V x).card : ℤ) =
      ((outN D V x).card : ℤ) + (if x=p then 1 else 0) -
        (if x ∈ donors D V q p w then 1 else 0) :=
  ⟨transition_qfree hq hf hw hne, fun x => exact_signed_debit hq hf hp hw missing x⟩

end LeanCH.BR.DotFullReturnCut

open LeanCH.BR.DotFullReturnCut in
#print axioms no_short_return_after_cut
open LeanCH.BR.DotFullReturnCut in
#print axioms transition_qfree
open LeanCH.BR.DotFullReturnCut in
#print axioms exact_row_debits
open LeanCH.BR.DotFullReturnCut in
#print axioms exact_signed_debit
open LeanCH.BR.DotFullReturnCut in
#print axioms donors_at_two
open LeanCH.BR.DotFullReturnCut in
#print axioms current_graph_transition