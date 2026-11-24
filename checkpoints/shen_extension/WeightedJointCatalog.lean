import checkpoints.shen_extension.WeightedJoint
import checkpoints.shen_extension.LoneRowCatalog

/-!
Typed forward rules for the weighted joint test and the remaining lone-row facts.
Importing this module is the registration; nothing else is changed.
-/

namespace LeanCH.BR.WeightedJointCatalog
open Finset BRq2 BRq3 FundedCascade BypassRepair BypassBankReplay BypassTwoStepRow JointShortcut
  JointShortcutReplay LoneRow WeightedJoint

attribute [aesop safe forward (immediate := [none,safe,pos,mass,paid]) (rule_sets := [CHGraphFamilies])]
  weighted_exit
attribute [aesop safe forward (immediate := [none,old,inW,pos,mass,paid]) (rule_sets := [CHGraphFamilies])]
  weighted_cycle
ch_family_split_result weighted_cycle

/-- The copy-and-bypass law for every surviving label and every affordable cut. -/
structure CloneBypass (D : CH.Digraph) (U : Finset ℕ) (q t x : ℕ) : Prop where
  at_copy : ∀ k ∈ U, k ≠ x → ∀ C : ℕ → Finset ℕ,
    (∀ c ∈ U.erase x, (C c).card ≤ spare D (U.erase x) t c) →
    ∃ y, TightParent D U t x y ∧ D y k ≠ true ∧
      ∀ a ∈ U, D x a = true → D y a ≠ true → Walk (cut D C) (U.erase x) a y (q-1)

@[aesop safe forward (immediate := [hq,none,cell,lone]) (rule_sets := [CHGraphFamilies])]
theorem clone_packet {q r} {X : ShenMinimumOrder.Source q r} {m : Cell} (hq : 2 ≤ q)
    (none : NoHost q (r-1)) (cell : Marked X m) (lone : LoneBlocked X m) :
    CloneBypass X.D (X.V \ m.bank) q (r-1) m.x :=
  ⟨fun _ ku kx C budget => marked_clone_bypass hq none cell lone ku kx C budget⟩

/-- Copy a named candidate column, with no further cut: one tight parent misses that column and
has a native return of exactly `q-1` arcs, avoiding `x`, from every head of `x` it misses. -/
@[aesop safe forward (immediate := [packet,kc]) (rule_sets := [CHGraphFamilies])]
theorem copy_column {D : CH.Digraph} {U : Finset ℕ} {q t x k : ℕ}
    (packet : CloneBypass D U q t x) (kc : k ∈ cols D U x) :
    ∃ y, TightParent D U t x y ∧ D y k ≠ true ∧
      ∀ a ∈ U, D x a = true → D y a ≠ true → Walk D (U.erase x) a y (q-1) := by
  obtain ⟨ku, kx, _⟩ := mem_cols.mp kc
  obtain ⟨y, tight, miss, back⟩ := packet.at_copy k ku kx (fun _ => ∅) (fun _ _ => by simp)
  exact ⟨y, tight, miss, fun a au xa ya => walk_sub cut_sub (back a au xa ya)⟩

ch_family_split_result copy_column

/-- Each candidate column of the live cell: its table entry and an erased label of the blocking
parent that misses the column. -/
@[aesop safe forward (immediate := [none,cell,lone,kc]) (rule_sets := [CHGraphFamilies])]
theorem column_bank_entry {q r} {X : ShenMinimumOrder.Source q r} {m : Cell}
    (none : NoHost q (r-1)) (cell : Marked X m) (lone : LoneBlocked X m) {k : ℕ}
    (kc : k ∈ cols X.D (X.V \ m.bank) m.x) :
    ∃ v l, Blocks X.D X.V (X.V \ m.bank) q (r-1) m.x v k l ∧
      ∃ h ∈ m.bank, X.D v h = true ∧ X.D h k ≠ true := by
  have deg : ∀ v ∈ X.V, r-1 < (outN X.D X.V v).card := fun v hv => by
    have := X.degree v hv
    have := cell.deficit
    omega
  obtain ⟨v, l, blk, h, hw, arc, miss⟩ := column_bank (on_cell none cell lone) deg kc
  refine ⟨v, l, blk, h, ?_, arc, miss⟩
  obtain ⟨hv, off⟩ := mem_sdiff.mp hw
  by_contra hb
  exact off (mem_sdiff.mpr ⟨hv, hb⟩)

ch_family_split_result column_bank_entry

/-- The marked target is a candidate head of the marked erased parent: its entry has depth exactly
`q-2`, and its blocking parent misses the marked parent. -/
@[aesop safe forward (immediate := [hq,none,cell,lone]) (rule_sets := [CHGraphFamilies])]
theorem target_entry {q r} {X : ShenMinimumOrder.Source q r} {m : Cell} (hq : 2 ≤ q)
    (none : NoHost q (r-1)) (cell : Marked X m) (lone : LoneBlocked X m) :
    ∃ v l, Blocks X.D X.V (X.V \ m.bank) q (r-1) m.x v m.target l ∧ l + 2 = q ∧
      X.D v m.parent ≠ true := by
  have L := on_cell none cell lone
  obtain ⟨v, l, blk⟩ := column L (LoneRowCatalog.target_column hq cell)
  exact ⟨v, l, blk, blk.deep L.uv L.xu (cell.sub cell.erased) cell.xp cell.pz,
    fun vp => blk.no_route L.uv (cell.sub cell.erased) vp cell.pz⟩

ch_family_split_result target_entry

#print axioms clone_packet
#print axioms copy_column
#print axioms column_bank_entry
#print axioms target_entry
end LeanCH.BR.WeightedJointCatalog
