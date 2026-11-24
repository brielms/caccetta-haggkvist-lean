import checkpoints.shen_extension.RootRegularBridge
import checkpoints.shen_extension.MinimalPowerDescent

namespace LeanCH.BR.ShortfallBankReplay
open Finset BRq2 BRq3 BypassRepair BypassBankReplay CHRuleCatalog BypassDegreeDescent

/-- The second deletion in a unit graph uses the same minimal counterexample
    as the first deletion. Both lower quotas are positive on this input. -/
@[aesop safe forward (immediate := [bad,least]) (rule_sets := [CHGraphFamilies])]
theorem next_lower_host {p : Input} (bad : Bad p) (least : MinimalChild p) :
    NoHost (cutoff p) (p.s-2) := by
  obtain ⟨hq,hr,_⟩ := remaining_from_run p bad
  exact MinimalPowerDescent.lower_host least (by omega) (by omega) (by omega)

/-- Mark the entire survivor set and original deficient row. Each proposed
    further deletion can be tested on these labels, including deletions
    that contain no outgoing head of the deficient row. -/
structure SecondDeletion (D : CH.Digraph) (U : Finset ℕ) (q d x : ℕ) : Prop where
  inspect : ∀ Z : Finset ℕ, (U \ Z).Nonempty → (U \ Z).card ≤ q*d →
    (x ∉ Z ∧ ∃ z∈Z, D x z = true) ∨
      ∃ y∈U \ Z, y ≠ x ∧ 2 ≤ (outN D Z y).card

@[aesop safe forward (immediate := [lower,hr,cell,lone]) (rule_sets := [CHGraphFamilies])]
theorem second_deletion {q r} {X : ShenMinimumOrder.Source q r} {m : Cell}
    (lower : NoHost q (r-2)) (hr : 2≤r) (cell : Marked X m) (lone : LoneBlocked X m) :
    SecondDeletion X.D (X.V \ m.bank) q (r-2) m.x :=
  ⟨ShortfallBridge.lone_second_bank lower hr cell lone⟩

@[aesop safe forward (immediate := [rule,live,room]) (rule_sets := [CHGraphFamilies])]
theorem inspect {D U q d x} (rule : SecondDeletion D U q d x) {Z : Finset ℕ}
    (live : (U \ Z).Nonempty) (room : (U \ Z).card ≤ q*d) :
    (x ∉ Z ∧ ∃ z∈Z, D x z = true) ∨
      ∃ y∈U \ Z, y ≠ x ∧ 2 ≤ (outN D Z y).card :=
  rule.inspect Z live room

ch_family_split_result inspect

/-- For a bank of missed columns, the first disjunct of the actual
    second-deletion law is impossible. Keep the witnessing row and
    the two different columns to which that row points. -/
@[aesop safe forward (immediate := [rule,inside,room,xu]) (rule_sets := [CHGraphFamilies])]
theorem two_heads {D U q d x} (rule : SecondDeletion D U q d x) {Z : Finset ℕ}
    (inside : Z⊆LoneRow.cols D U x) (room : (U \ Z).card ≤ q*d) (xu : x∈U) :
    ∃ y∈U \ Z, y≠x ∧ ∃ a∈Z, ∃ b∈Z, a≠b ∧ D y a=true ∧ D y b=true := by
  have xc : x∉Z := fun xz => (LoneRow.mem_cols.mp (inside xz)).2.1 rfl
  rcases rule.inspect Z ⟨x,mem_sdiff.mpr ⟨xu,xc⟩⟩ room with ⟨_,a,az,xa⟩ | ⟨y,yr,ne,two⟩
  · exact False.elim ((LoneRow.mem_cols.mp (inside az)).2.2 xa)
  · obtain ⟨a,ay,b,by',ab⟩ := Finset.one_lt_card.mp two
    exact ⟨y,yr,ne,a,outN_subset ay,b,outN_subset by',ab,(mem_outN.mp ay).2,(mem_outN.mp by').2⟩

ch_family_split_result two_heads

/-- Complete any already specified set of missed columns to the desired
    bank size. The budget only counts how many survivors are left. -/
theorem choose_bank {D U q d x} (rule : SecondDeletion D U q d x) (xu : x∈U)
    {A : Finset ℕ} {b : ℕ} (marks : A⊆LoneRow.cols D U x) (fit : A.card≤b)
    (supply : b≤(LoneRow.cols D U x).card) (budget : U.card≤q*d+b) :
    ∃ Z : Finset ℕ, A⊆Z ∧ Z⊆LoneRow.cols D U x ∧ Z.card=b ∧
      ∃ y∈U \ Z, y≠x ∧ ∃ a∈Z, ∃ b∈Z, a≠b ∧ D y a=true ∧ D y b=true := by
  obtain ⟨Z,az,zc,size⟩ := exists_subsuperset_card_eq marks fit supply
  exact ⟨Z,az,zc,size,two_heads rule zc
    (by rw [card_sdiff_of_subset (zc.trans LoneRow.cols_subset),size]; omega) xu⟩

/-- Keep the two weak numeric premises needed by the unit-boundary and
    column-count consumers in their ordinary forward-matching form. -/
@[aesop safe forward (immediate := [bad]) (rule_sets := [CHGraphFamilies])]
theorem applicable_quota {p : Input} (bad : Bad p) : 1≤cutoff p ∧ 3≤p.s := by
  obtain ⟨hq,hr,_⟩ := remaining_from_run p bad
  exact ⟨by omega,by omega⟩

ch_family_split_result applicable_quota

/-- There are enough missed columns to delete q while keeping both the
    deficient row and the prescribed target's identity. -/
@[aesop safe forward (immediate := [rule,hr,hq,cell,kc]) (rule_sets := [CHGraphFamilies])]
theorem marked_choice {q r} {X : ShenMinimumOrder.Source q r} {m : Cell}
    (rule : SecondDeletion X.D (X.V \ m.bank) q (r-2) m.x)
    (hr : 3≤r) (hq : 2≤q) (cell : Marked X m)
    (kc : m.target∈LoneRow.cols X.D (X.V \ m.bank) m.x) :
    ∃ Z : Finset ℕ, m.target∈Z ∧ Z⊆LoneRow.cols X.D (X.V \ m.bank) m.x ∧ Z.card=q ∧
      ∃ y∈(X.V \ m.bank) \ Z, y≠m.x ∧
        ∃ a∈Z, ∃ b∈Z, a≠b ∧ X.D y a=true ∧ X.D y b=true := by
  let U := X.V \ m.bank
  have order : U.card=q*(r-1) := ShortfallBridge.survivors_card cell
  have rc : r-1=(r-2)+1 := by omega
  have budget : U.card=q*(r-2)+q := by rw [order,rc,Nat.mul_add,Nat.mul_one]
  have paid := cell.deficit
  change (outN X.D U m.x).card+1=r-1 at paid
  have eq : LoneRow.cols X.D U m.x=U \ insert m.x (outN X.D U m.x) := by
    ext a
    simp only [LoneRow.mem_cols,mem_sdiff,mem_insert,mem_outN]
    tauto
  have cut := card_le_card_sdiff_add_card (s:=U) (t:=insert m.x (outN X.D U m.x))
  have lost := card_insert_le m.x (outN X.D U m.x)
  have ub : r-1≤q*(r-2) := by
    have := Nat.mul_le_mul_right (r-2) hq
    omega
  have supply : q≤(LoneRow.cols X.D U m.x).card := by rw [eq]; omega
  obtain ⟨Z,mark,zc,size,rest⟩ := choose_bank rule cell.xu (singleton_subset_iff.mpr kc)
    (by simpa using (show 1≤q by omega)) supply budget.le
  exact ⟨Z,singleton_subset_iff.mp mark,zc,size,rest⟩

ch_family_split_result marked_choice

#print axioms next_lower_host
#print axioms second_deletion
#print axioms inspect
#print axioms two_heads
#print axioms choose_bank
#print axioms applicable_quota
#print axioms marked_choice
end LeanCH.BR.ShortfallBankReplay
