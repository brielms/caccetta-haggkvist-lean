import checkpoints.shen_extension.JointPairCounting
import checkpoints.shen_extension.JointBankConstruction

namespace LeanCH.BR.BypassBankReplay
open Finset BRq2 BRq3 BR45 BypassRepair

/-- In a regular minimum-order source the bank may be chosen with two
distinct surviving short rows, including the designated one. -/
theorem exists_joint_mark {q s} (X : ShenMinimumOrder.Source q s)
    (reg : OutEq s X.D X.V) (hq : 3 ≤ q) (hs : 4 ≤ s)
    (room : X.V.card ≤ q*s) (none : NoHost q (s-1)) :
    ∃ m, Marked X m ∧ JointShort X m := by
  let b := X.V.card-q*(s-1)
  have order := order_floor none (by omega : 2 ≤ s) X.free X.nonempty X.degree
  have exactOrder : X.V.card=q*(s-1)+b := by dsimp [b]; omega
  have lower : 2 ≤ b := by omega
  have wide := Nat.mul_le_mul_right (s-1) hq
  have space : b+s+1 ≤ X.V.card := by omega
  by_cases two : b=2
  · obtain ⟨x,xv,j,jv,xj,p,xp,jp,h,xh,jh,hp⟩ :=
      shared_pair_at_two X reg hs (by omega) none (by omega)
    exact bank_of_shared_heads reg (by omega) hs room (rfl : b = _) lower space
      xv jv xj xp jp xh jh hp
  · exact bank_of_three_places reg (by omega) hs room (rfl : b = _) (by omega) space

theorem joint_excludes_lone {q s} {X : ShenMinimumOrder.Source q s} {m}
    (joint : JointShort X m) (lone : LoneBlocked X m) : False := by
  obtain ⟨j,jv,jx,poor⟩ := joint
  exact poor.not_ge (lone.paid_elsewhere j jv jx)

#print axioms exists_joint_mark
#print axioms joint_excludes_lone
end LeanCH.BR.BypassBankReplay

