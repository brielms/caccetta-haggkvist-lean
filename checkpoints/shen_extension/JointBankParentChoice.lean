import checkpoints.shen_extension.JointBankChoice
import checkpoints.shen_extension.JointBankPrivateHeads
import checkpoints.shen_extension.JointShortcutReplay

namespace LeanCH.BR.BypassBankReplay
open Finset BRq2 BRq3 BR45 BypassRepair JointShortcutReplay

private def PrivateFork.swap {D V} (f : PrivateFork D V) : PrivateFork D V :=
  ⟨f.j,f.x,f.h,f.g,f.p,f.jv,f.xv,f.jh,f.xh,f.jg,f.xg,f.gx,f.xp,f.jp,f.pj⟩

private theorem private_bank {q s} {X : ShenMinimumOrder.Source q s}
    (reg : OutEq s X.D X.V) (hq : 3 ≤ q) (hs : 4 ≤ s) (room : X.V.card ≤ q*s)
    {b} (size : b = X.V.card-q*(s-1)) (lower : 3 ≤ b) (space : b+s+1 ≤ X.V.card)
    (f : PrivateFork X.D X.V) (clear : X.D f.p f.g ≠ true) :
    ∃ m, Marked X m ∧ JointShort X m ∧ MissedParent X.D (X.V \ m.bank) (s-1) m.parent := by
  classical
  obtain ⟨pv,axp⟩ := mem_outN.mp f.xp
  obtain ⟨z,zkeep,pz,xz⟩ := candidate_exists (B:=∅) X.free (by omega) pv axp
    ((reg _ f.xv).trans (reg _ pv).symm).le (by simp)
  have gz : f.g ≠ z := fun e => clear (e ▸ pz)
  have gj : f.g ≠ f.j := fun e => loopfree X.free (by omega) f.jv (e ▸ (mem_outN.mp f.jg).2)
  have hj : f.h ≠ f.j := fun e => loopfree X.free (by omega) f.jv (e ▸ (mem_outN.mp f.jh).2)
  have hp : f.h ≠ f.p := fun e => f.jp (e ▸ f.jh)
  have hg : f.h ≠ f.g := fun e => f.xg (e ▸ f.xh)
  have jx : f.j ≠ f.x := fun e => f.jp (e ▸ f.xp)
  let T : Finset ℕ := {f.p,f.h}
  let K : Finset ℕ := {f.g}
  have head : T ⊆ outN X.D X.V f.x := insert_subset_iff.mpr ⟨f.xp,singleton_subset_iff.mpr f.xh⟩
  have count : T.card = 2 := card_pair hp.symm
  have jt : f.j ∉ T := by simp [T,f.pj.symm,hj.symm]
  have keep : K ⊆ X.V \ (outN X.D X.V f.x ∪ {f.x,z,f.j}) := by
    apply singleton_subset_iff.mpr
    exact mem_sdiff.mpr ⟨outN_subset f.jg,by simp [f.xg,f.gx,gz,gj]⟩
  have hgsub : ({f.h,f.g}:Finset ℕ) ⊆ outN X.D (T∪K) f.j := by
    apply insert_subset_iff.mpr
    refine ⟨mem_outN.mpr ⟨by simp [T],(mem_outN.mp f.jh).2⟩,singleton_subset_iff.mpr ?_⟩
    exact mem_outN.mpr ⟨by simp [K],(mem_outN.mp f.jg).2⟩
  have paid := card_le_card hgsub
  rw [card_pair hg] at paid
  obtain ⟨B,marked,jb,short⟩ := extend_joint_bank_at (by omega : 2 ≤ q) hs reg room size
    (by omega) space f.xv f.jv (mem_sdiff.mp zkeep).1 pz xz head count (by simp [T]) jt keep
    (by simp only [K,card_singleton]; omega) paid
  exact ⟨⟨B,f.x,f.p,z⟩,marked,⟨f.j,jb,jx,short⟩,⟨f.j,jb,short,fun edge => f.jp (mem_outN.mpr ⟨pv,edge⟩)⟩⟩

/-- A bank of size at least three can be marked with a second short row
which misses the marked parent. -/
theorem exists_missed_mark {q s} (X : ShenMinimumOrder.Source q s) (reg : OutEq s X.D X.V)
    (hq : 3 ≤ q) (hs : 4 ≤ s) (room : X.V.card ≤ q*s)
    (places : 3 ≤ X.V.card-q*(s-1)) :
    ∃ m, Marked X m ∧ JointShort X m ∧ MissedParent X.D (X.V \ m.bank) (s-1) m.parent := by
  let b := X.V.card-q*(s-1)
  have exactOrder : X.V.card = q*(s-1)+b := by dsimp [b]; omega
  have low := Nat.mul_le_mul_right (s-1) hq
  have space : b+s+1 ≤ X.V.card := by omega
  obtain ⟨f⟩ := exists_privateFork X.free X.nonempty reg (by omega) hq room
  by_cases arc : X.D f.p f.g=true
  · have clear : X.D f.swap.p f.swap.g ≠ true :=
      digonfree X.free (by omega) (outN_subset f.xp) (outN_subset f.jg) arc
    exact private_bank reg hq hs room (rfl : b = _) places space f.swap clear
  · exact private_bank reg hq hs room (rfl : b = _) places space f arc

/-- With two erased labels every short row points to the marked parent. -/
theorem shared_at_two {q s} {X : ShenMinimumOrder.Source q s} {m}
    (reg : OutEq s X.D X.V) (cell : Marked X m) (two : m.bank.card=2) :
    SharedParent X.D (X.V \ m.bank) (s-1) m.parent := by
  refine ⟨?_⟩
  intro u uv short
  by_contra absent
  have sub : outN X.D X.V u ∩ m.bank ⊆ m.bank.erase m.parent := by
    intro a ha
    obtain ⟨ah,ab⟩ := mem_inter.mp ha
    exact mem_erase.mpr ⟨fun e => absent (e ▸ (mem_outN.mp ah).2),ab⟩
  have bound := card_le_card sub
  rw [card_erase_of_mem cell.erased,two] at bound
  have counts := card_sdiff_add_card_inter (outN X.D X.V u) m.bank
  rw [reg u (mem_sdiff.mp uv).1] at counts
  have row : outN X.D (X.V \ m.bank) u = outN X.D X.V u \ m.bank := by
    ext a; simp only [mem_outN,mem_sdiff]; tauto
  rw [row] at short
  omega

/-- A single choice realizes both the two-short-row condition and the exact
parent alternative prescribed by the order. -/
theorem exists_classified_joint_mark {q s} (X : ShenMinimumOrder.Source q s)
    (reg : OutEq s X.D X.V) (hq : 3 ≤ q) (hs : 4 ≤ s)
    (room : X.V.card ≤ q*s) (none : NoHost q (s-1)) :
    ∃ m, Marked X m ∧ JointShort X m ∧
      (SharedParent X.D (X.V \ m.bank) (s-1) m.parent ↔ X.V.card=q*(s-1)+2) ∧
      (MissedParent X.D (X.V \ m.bank) (s-1) m.parent ↔ q*(s-1)+3≤X.V.card) := by
  have lo := order_floor none (by omega : 2≤s) X.free X.nonempty X.degree
  have clash {m : Cell} (shared : SharedParent X.D (X.V \ m.bank) (s-1) m.parent)
      (miss : MissedParent X.D (X.V \ m.bank) (s-1) m.parent) : False := by
    obtain ⟨u,uv,short,no⟩ := miss.witness
    exact no (shared.all_short u uv short)
  by_cases small : X.V.card=q*(s-1)+2
  · obtain ⟨m,marked,joint⟩ := exists_joint_mark X reg hq hs room none
    have sz := marked.size
    have shared := shared_at_two reg marked (by omega)
    exact ⟨m,marked,joint,⟨fun _ => small,fun _ => shared⟩,
      ⟨fun h => False.elim (clash shared h),fun h => False.elim (by omega)⟩⟩
  · obtain ⟨m,marked,joint,miss⟩ := exists_missed_mark X reg hq hs room (by omega)
    exact ⟨m,marked,joint,⟨fun h => False.elim (clash h miss),fun h => False.elim (small h)⟩,
      ⟨fun _ => by omega,fun _ => miss⟩⟩

#print axioms exists_missed_mark
#print axioms exists_classified_joint_mark
end LeanCH.BR.BypassBankReplay

