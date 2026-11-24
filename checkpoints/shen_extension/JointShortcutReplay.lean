import checkpoints.shen_extension.JointShortcut
import checkpoints.shen_extension.BypassCloneCover
import checkpoints.shen_extension.BypassTwoStepRow

namespace LeanCH.BR.JointShortcutReplay
open Finset BRq2 BRq3 FundedCascade BypassRepair BypassBankReplay JointShortcut

attribute [aesop safe forward (immediate := [none,cell,joint]) (rule_sets := [CHGraphFamilies])]
  joint_blocked
attribute [aesop safe forward (immediate := [none,live,size,safe]) (rule_sets := [CHGraphFamilies])]
  residual_debt
attribute [aesop safe forward (immediate := [none,bank,inU,fresh,pays,safe]) (rule_sets := [CHGraphFamilies])]
  bank_exit
attribute [aesop safe forward (immediate := [budget,cover]) (rule_sets := [CHGraphFamilies])]
  pays_of_spare
attribute [aesop safe forward (immediate := [inU,old,own,down]) (rule_sets := [CHGraphFamilies])]
  ranked_safe
attribute [aesop safe forward (immediate := [h₁,h₂,old,own₁,own₂,back]) (rule_sets := [CHGraphFamilies])]
  one_way

@[aesop safe forward (immediate := [inU,old,clear]) (rule_sets := [CHGraphFamilies])]
theorem safe_of_no_trail {K U F q} (inU : ∀ j ∈ F, Prod.snd j ∈ U) (old : QFree K U q)
    (clear : ∀ i ∈ F, ∀ c, 0 < c → c ≤ q → ¬ Trail K U F i i c) : QFree (install K F) U q :=
  (install_iff inU).mpr ⟨old,clear⟩

@[aesop safe forward (immediate := [in₁,in₂,old,own₁,own₂,cross]) (rule_sets := [CHGraphFamilies])]
theorem safe_pair {K U q} {a b : Arc} (in₁ : a.2 ∈ U) (in₂ : b.2 ∈ U) (old : QFree K U q)
    (own₁ : ∀ d, d+1 ≤ q → ¬ Walk K U a.2 a.1 d)
    (own₂ : ∀ d, d+1 ≤ q → ¬ Walk K U b.2 b.1 d)
    (cross : ∀ i j, i+j+2 ≤ q → Walk K U a.2 b.1 i → ¬ Walk K U b.2 a.1 j) :
    QFree (install K {a,b}) U q := (pair_iff in₁ in₂).mpr ⟨old,own₁,own₂,cross⟩

@[aesop safe forward (immediate := [free,hq,uv,sub,inU,pv,feeds,kin,own]) (rule_sets := [CHGraphFamilies])]
theorem safe_of_parent_order {D K V U F q} {par ρ : Arc → ℕ} (free : QFree D V q) (hq : 1 ≤ q)
    (uv : U ⊆ V) (sub : ∀ a b, K a b = true → D a b = true) (inU : ∀ j ∈ F, Prod.snd j ∈ U)
    (pv : ∀ j ∈ F, par j ∈ V) (feeds : ∀ j ∈ F, D (par j) j.2 = true)
    (kin : ∀ j ∈ F, ∀ j' ∈ F, ρ j' ≤ ρ j → D j'.1 (par j) = true)
    (own : ∀ j ∈ F, ¬ Walk K U j.2 j.1 (q-1)) : QFree (install K F) U q :=
  (kin_iff free hq uv sub inU par ρ pv feeds kin).mpr own

open Classical in
noncomputable def usable (D : CH.Digraph) (U : Finset ℕ) (q t u : ℕ) : Finset ℕ :=
  let P := U.filter (fun a => (outN D U a).card < t)
  let e := spare D U t
  U.filter (fun z => z ∉ active D U P e (q-2) ∧ D u z ≠ true ∧
    ¬ Walk (cut D (fun a => bill D U P e a (q-1))) U z u (q-1))

structure LastStepDebt (D : CH.Digraph) (U : Finset ℕ) (q t : ℕ) : Prop where
  witness : ∃ u ∈ U, (outN D U u).card < t ∧ (usable D U q t u).card + (outN D U u).card < t

@[aesop safe forward (immediate := [free,none,bank]) (rule_sets := [CHGraphFamilies])]
theorem last_step {D V B q t} (free : QFree D V q) (none : NoHost q t)
    (bank : Eligible V B q t) : LastStepDebt D (V \ B) q t :=
  ⟨last_step_row free none bank⟩

attribute [aesop safe forward (rule_sets := [CHGraphFamilies])] LastStepDebt.witness
ch_family_split_result LastStepDebt.witness

structure SharedParent (D : CH.Digraph) (U : Finset ℕ) (t p : ℕ) : Prop where
  all_short : ∀ u ∈ U, (outN D U u).card < t → D u p = true

structure MissedParent (D : CH.Digraph) (U : Finset ℕ) (t p : ℕ) : Prop where
  witness : ∃ u ∈ U, (outN D U u).card < t ∧ D u p ≠ true

/-- A pivot already used by one deficient row can be tested against the others. -/
structure ParentQuery (D : CH.Digraph) (U : Finset ℕ) (t p : ℕ) : Prop where
  marked : ∃ x ∈ U, (outN D U x).card < t ∧ D x p = true ∧
    ∃ j ∈ U, j ≠ x ∧ (outN D U j).card < t

@[aesop safe forward (immediate := [cell,joint]) (rule_sets := [CHGraphFamilies])]
theorem query {q r} {X : ShenMinimumOrder.Source q r} {m : Cell}
    (cell : Marked X m) (joint : JointBlocked X m) : ParentQuery X.D (X.V \ m.bank) (r-1) m.parent :=
  ⟨m.x,cell.xu,by have := cell.deficit; omega,cell.xp,joint.second⟩

@[aesop safe forward (immediate := [site]) (rule_sets := [CHGraphFamilies])]
theorem inspect {D U t p} (site : ParentQuery D U t p) : SharedParent D U t p ∨ MissedParent D U t p := by
  classical
  obtain ⟨_,_,_,_,_⟩ := site.marked
  by_cases yes : ∀ u ∈ U, (outN D U u).card < t → D u p = true
  · exact Or.inl ⟨yes⟩
  · push Not at yes
    exact Or.inr ⟨yes⟩

ch_family_split_result inspect
attribute [aesop safe forward (rule_sets := [CHGraphFamilies])] MissedParent.witness
ch_family_split_result MissedParent.witness

@[aesop safe forward (immediate := [cell,lone]) (rule_sets := [CHGraphFamilies])]
theorem lone_shared {q r} {X : ShenMinimumOrder.Source q r} {m : Cell}
    (cell : Marked X m) (lone : LoneBlocked X m) : SharedParent X.D (X.V \ m.bank) (r-1) m.parent := by
  refine ⟨fun u uu short => ?_⟩
  have eq : u = m.x := by
    by_contra ne
    exact (not_lt_of_ge (lone.paid_elsewhere u uu ne)) short
  exact eq ▸ cell.xp

structure OwnReturnDebt (D : CH.Digraph) (U : Finset ℕ) (q t p : ℕ) : Prop where
  at_cut : ∀ C : ℕ → Finset ℕ, (∀ c ∈ U, (C c).card ≤ spare D U t c) →
    ∃ u ∈ U, (outN D U u).card < t ∧
      (JointShortcut.clear D (cut D C) U q p u).card + (outN D U u).card < t

@[aesop safe forward (immediate := [free,hq,none,bank,pv,shared]) (rule_sets := [CHGraphFamilies])]
theorem shared_debt {D V B q t p} (free : QFree D V q) (hq : 1 ≤ q) (none : NoHost q t)
    (bank : Eligible V B q t) (pv : p ∈ V) (shared : SharedParent D (V \ B) t p) :
    OwnReturnDebt D (V \ B) q t p := ⟨fun _ budget =>
  common_parent_row free hq none bank pv shared.all_short budget⟩

@[aesop safe forward (immediate := [hq,none,cell,shared]) (rule_sets := [CHGraphFamilies])]
theorem marked_debt {q r} {X : ShenMinimumOrder.Source q r} {m : Cell}
    (hq : 2 ≤ q) (none : NoHost q (r-1)) (cell : Marked X m)
    (shared : SharedParent X.D (X.V \ m.bank) (r-1) m.parent) :
    OwnReturnDebt X.D (X.V \ m.bank) q (r-1) m.parent :=
  shared_debt X.free (by omega) none (marked_bank cell) (cell.sub cell.erased) shared

/-- Each missed bank label uses a slot in addition to the heads actually
    lost by u. No bound on the number of missing labels is assumed. -/
theorem missed_slots {D : CH.Digraph} {V B : Finset ℕ} (u : ℕ) (sub : B ⊆ V) :
    (B \ outN D B u).card + (outN D V u).card =
      B.card + (outN D (V \ B) u).card := by
  have row : outN D V u = outN D (V \ B) u ∪ outN D B u := by
    ext k
    simp only [mem_outN,mem_union,mem_sdiff]
    grind
  have dis : Disjoint (outN D (V \ B) u) (outN D B u) := disjoint_left.mpr
    (fun _ h k => (mem_sdiff.mp (outN_subset h)).2 (outN_subset k))
  have count := card_sdiff_add_card_eq_card (outN_subset : outN D B u ⊆ B)
  rw [row,card_union_of_disjoint dis]
  omega

/-- A deficient row must use every slot of a small enough bank. The bound
    uses the actual lower degree d and the proposed survivor quota t. -/
@[aesop safe forward (immediate := [sub,min,hb,room]) (rule_sets := [CHGraphFamilies])]
theorem shared_from_slots {D V B d t p} (sub : B ⊆ V)
    (min : ∀ u ∈ V, d ≤ (outN D V u).card) (hb : p ∈ B)
    (room : B.card+t ≤ d+1) : SharedParent D (V \ B) t p := by
  refine ⟨fun u uu short => ?_⟩
  by_contra off
  have pos := card_pos.mpr (show (B \ outN D B u).Nonempty from
    ⟨p,mem_sdiff.mpr ⟨hb,fun hit => off (mem_outN.mp hit).2⟩⟩)
  have eq := missed_slots (D:=D) u sub
  have deg := min u (mem_sdiff.mp uu).1
  omega

@[aesop safe forward (immediate := [common,miss]) (rule_sets := [CHGraphFamilies])]
theorem shared_excludes_miss {D U t p} (common : SharedParent D U t p)
    (miss : MissedParent D U t p) : False := by
  obtain ⟨u,uu,short,off⟩ := miss.witness
  exact off (common.all_short u uu short)

@[aesop safe forward (immediate := [cell,band]) (rule_sets := [CHGraphFamilies])]
theorem shared_at_floor {q r} {X : ShenMinimumOrder.Source q r} {m : Cell}
    (cell : Marked X m) (band : X.V.card = q*(r-1)+2) :
    SharedParent X.D (X.V \ m.bank) (r-1) m.parent := by
  have size := cell.size
  have row := cell.deficit
  exact shared_from_slots cell.sub X.degree cell.erased (by omega)

@[aesop safe forward (immediate := [none,cell,order,atFloor]) (rule_sets := [CHGraphFamilies])]
theorem source_at_floor {q r n} {X : ShenMinimumOrder.Source q r} {m : Cell}
    (none : NoHost q (r-1)) (cell : Marked X m) (order : X.V.card ≤ n)
    (atFloor : n=q*(r-1)+2) : X.V.card=q*(r-1)+2 := by
  have row := cell.deficit
  exact le_antisymm (order.trans atFloor.le)
    (order_floor none (by omega) X.free X.nonempty X.degree)

@[aesop safe forward (immediate := [cell,miss]) (rule_sets := [CHGraphFamilies])]
theorem native_order_if_missed {q r} {X : ShenMinimumOrder.Source q r} {m : Cell}
    (cell : Marked X m) (miss : MissedParent X.D (X.V \ m.bank) (r-1) m.parent) :
    q*(r-1)+3 ≤ X.V.card := by
  obtain ⟨u,uu,low,off⟩ := miss.witness
  have pos := card_pos.mpr (show (m.bank \ outN X.D m.bank u).Nonempty from
    ⟨m.parent,mem_sdiff.mpr ⟨cell.erased,fun hit => off (mem_outN.mp hit).2⟩⟩)
  have eq := missed_slots (D:=X.D) u cell.sub
  have min := X.degree u (mem_sdiff.mp uu).1
  have size := cell.size
  omega

@[aesop safe forward (immediate := [cell,miss,order]) (rule_sets := [CHGraphFamilies])]
theorem descendant_order_if_missed {q r n} {X : ShenMinimumOrder.Source q r} {m : Cell}
    (cell : Marked X m) (miss : MissedParent X.D (X.V \ m.bank) (r-1) m.parent)
    (order : X.V.card ≤ n) : q*(r-1)+3 ≤ n := (native_order_if_missed cell miss).trans order

open BypassTwoStepRow

/-- Preserve the particular return parent and its lost head when testing the
    two-step alternative; both marks survive either outcome. -/
structure LostAt (D : CH.Digraph) (U B : Finset ℕ) (t x y h : ℕ) : Prop where
  parent : TightParent D U t x y
  erased : h ∈ B
  lost : D y h = true

@[aesop safe forward (immediate := [yu,yx,arc,tight,hb,lost]) (rule_sets := [CHGraphFamilies])]
theorem marked_loss {D V B t x y h}
    (yu : y ∈ V \ B) (yx : y ≠ x) (arc : D y x = true)
    (tight : (outN D (V \ B) y).card = t) (hb : h ∈ B) (lost : D y h = true) :
    LostAt D (V \ B) B t x y h := ⟨⟨yu,yx,arc,tight⟩,hb,lost⟩

theorem inspect_loss {q r} {X : ShenMinimumOrder.Source q r} {m : Cell} {y h}
    (cell : Marked X m) (rec : Reconstructed X.D X.V (X.V \ m.bank) (r-1) m.x)
    (mark : LostAt X.D (X.V \ m.bank) m.bank (r-1) m.x y h) :
    2 ≤ (outN X.D m.bank h).card + (if X.D h m.x = true then 1 else 0) ∨
    ∃ v, TightParent X.D (X.V \ m.bank) (r-1) m.x v ∧ v ≠ y ∧ X.D v h ≠ true :=
  marked_lost_head cell rec mark.erased mark.lost

/-- Choose the bill when it holds. Its negation is kept on the complementary
child so a stronger return theorem can reuse the same lost head. -/
@[aesop safe forward (immediate := [cell,rec,mark]) (rule_sets := [CHGraphFamilies])]
theorem inspect_loss_partition {q r} {X : ShenMinimumOrder.Source q r} {m : Cell} {y h}
    (cell : Marked X m) (rec : Reconstructed X.D X.V (X.V \ m.bank) (r-1) m.x)
    (mark : LostAt X.D (X.V \ m.bank) m.bank (r-1) m.x y h) :
    2 ≤ (outN X.D m.bank h).card + (if X.D h m.x = true then 1 else 0) ∨
    (¬ 2 ≤ (outN X.D m.bank h).card + (if X.D h m.x = true then 1 else 0)) ∧
      ∃ v, TightParent X.D (X.V \ m.bank) (r-1) m.x v ∧ v ≠ y ∧ X.D v h ≠ true := by
  by_cases bill : 2 ≤ (outN X.D m.bank h).card + (if X.D h m.x = true then 1 else 0)
  · exact Or.inl bill
  · exact Or.inr ⟨bill, (inspect_loss cell rec mark).resolve_left bill⟩

ch_family_split_result inspect_loss_partition

attribute [aesop safe forward (immediate := [cell,band]) (rule_sets := [CHGraphFamilies])] band_all
attribute [aesop safe forward (immediate := [hq,none,cell,band,budget]) (rule_sets := [CHGraphFamilies])] band_row
attribute [aesop safe forward (immediate := [hq,none,cell,band]) (rule_sets := [CHGraphFamilies])] band_unpaid
ch_family_split_result band_unpaid

#print axioms safe_of_no_trail
#print axioms safe_pair
#print axioms safe_of_parent_order
#print axioms last_step
#print axioms inspect
#print axioms marked_debt
#print axioms missed_slots
#print axioms shared_from_slots
#print axioms shared_excludes_miss
#print axioms shared_at_floor
#print axioms source_at_floor
#print axioms native_order_if_missed
#print axioms descendant_order_if_missed
#print axioms inspect_loss
end LeanCH.BR.JointShortcutReplay
