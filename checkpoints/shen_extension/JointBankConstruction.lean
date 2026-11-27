import checkpoints.shen_extension.JointBankGeometry

namespace LeanCH.BR.BypassBankReplay
open Finset BRq2 BRq3 BR45 BypassRepair

private theorem some_common_head {q s} (X : ShenMinimumOrder.Source q s) (hs : 2 ≤ s) :
    ∃ p ∈ X.V, ∃ x ∈ X.V, ∃ j ∈ X.V, x ≠ j ∧ X.D x p = true ∧ X.D j p = true := by
  classical
  have enough : ∃ p ∈ X.V, 1 < (inN X.D X.V p).card := by
    by_contra! small
    have ins : (∑ p ∈ X.V, (inN X.D X.V p).card) ≤ ∑ _p ∈ X.V, 1 :=
      sum_le_sum small
    have outs : (∑ _p ∈ X.V, s) ≤ ∑ p ∈ X.V, (outN X.D X.V p).card :=
      sum_le_sum X.degree
    have eq : (∑ p ∈ X.V, (outN X.D X.V p).card) = ∑ p ∈ X.V, (inN X.D X.V p).card :=
      Compose.ThinRigid.sum_out_eq_sum_in X.D X.V
    have both := outs.trans (eq.le.trans ins)
    simp only [sum_const,smul_eq_mul,mul_one] at both
    have pos := card_pos.mpr X.nonempty
    nlinarith [Nat.mul_le_mul_left X.V.card hs]
  obtain ⟨p,pv,pair⟩ := enough
  obtain ⟨x,xp,j,jp,xj⟩ := one_lt_card.mp pair
  exact ⟨p,pv,x,(mem_inN.mp xp).1,j,(mem_inN.mp jp).1,xj,(mem_inN.mp xp).2,(mem_inN.mp jp).2⟩

/-- If two rows share two heads, an exact-size marked bank can keep both rows
and the fresh target while deleting the two shared heads. -/
theorem bank_of_shared_heads {q s} {X : ShenMinimumOrder.Source q s}
    (reg : OutEq s X.D X.V) (hq : 2 ≤ q) (hs : 4 ≤ s) (room : X.V.card ≤ q*s)
    {b} (size : b = X.V.card-q*(s-1)) (lower : 2 ≤ b) (space : b+s+1 ≤ X.V.card)
    {x j p h} (xv : x ∈ X.V) (jv : j ∈ X.V) (xj : x ≠ j)
    (xp : p ∈ outN X.D X.V x) (jp : p ∈ outN X.D X.V j)
    (xh : h ∈ outN X.D X.V x) (jh : h ∈ outN X.D X.V j) (hp : h ≠ p) :
    ∃ m, Marked X m ∧ JointShort X m := by
  classical
  obtain ⟨pv,axp⟩ := mem_outN.mp xp
  obtain ⟨z,zkeep,pz,xz⟩ := candidate_exists (B:=∅) X.free (by omega) pv axp
    ((reg x xv).trans (reg p pv).symm).le (by simp)
  let T : Finset ℕ := {p,h}
  have head : T ⊆ outN X.D X.V x := insert_subset_iff.mpr ⟨xp,singleton_subset_iff.mpr xh⟩
  have jhead : T ⊆ outN X.D X.V j := insert_subset_iff.mpr ⟨jp,singleton_subset_iff.mpr jh⟩
  have jt : j ∉ T := fun hj => loopfree X.free (by omega) jv (mem_outN.mp (jhead hj)).2
  have count : T.card=2 := card_pair hp.symm
  have inside : T ⊆ outN X.D (T ∪ ∅) j := fun a ha =>
    mem_outN.mpr ⟨mem_union_left _ ha,(mem_outN.mp (jhead ha)).2⟩
  exact extend_joint_bank hq hs reg room size lower space xv jv xj.symm
    (mem_sdiff.mp zkeep).1 pz xz head count (by simp [T]) jt (empty_subset _)
    (by simp) (count ▸ card_le_card inside)

private theorem exists_off_small {S F : Finset ℕ} (lt : F.card < S.card) :
    ∃ a ∈ S, a ∉ F := by
  by_contra! all
  exact lt.not_ge (card_le_card all)

/-- With at least three places in the bank, two rows with a common head
suffice. In the single-common-head case the third place pays the second row. -/
theorem bank_of_three_places {q s} {X : ShenMinimumOrder.Source q s}
    (reg : OutEq s X.D X.V) (hq : 2 ≤ q) (hs : 4 ≤ s) (room : X.V.card ≤ q*s)
    {b} (size : b = X.V.card-q*(s-1)) (lower : 3 ≤ b) (space : b+s+1 ≤ X.V.card) :
    ∃ m, Marked X m ∧ JointShort X m := by
  classical
  obtain ⟨p,pv,x,xv,j,jv,xj,axp,ajp⟩ := some_common_head X (by omega)
  have xp : p ∈ outN X.D X.V x := mem_outN.mpr ⟨pv,axp⟩
  have jp : p ∈ outN X.D X.V j := mem_outN.mpr ⟨pv,ajp⟩
  by_cases shared : ∃ h ∈ outN X.D X.V x, h ∈ outN X.D X.V j ∧ h ≠ p
  · obtain ⟨h,xh,jh,hp⟩ := shared
    exact bank_of_shared_heads reg hq hs room size (by omega) space xv jv xj xp jp xh jh hp
  obtain ⟨z,zkeep,pz,xz⟩ := candidate_exists (B:=∅) X.free (by omega) pv axp
    ((reg x xv).trans (reg p pv).symm).le (by simp)
  have card3 : ({p,x,z} : Finset ℕ).card ≤ 3 := by
    have := card_insert_le p ({x,z}:Finset ℕ)
    have : ({x,z}:Finset ℕ).card ≤ 2 := card_le_two
    omega
  obtain ⟨g,jg,gclear⟩ := exists_off_small (S:=outN X.D X.V j) (F:={p,x,z})
    (by rw [reg j jv]; omega)
  have gp : g ≠ p := fun e => gclear (by simp [e])
  have gx : g ≠ x := fun e => gclear (by simp [e])
  have gz : g ≠ z := fun e => gclear (by simp [e])
  have gj : g ≠ j := fun e => loopfree X.free (by omega) jv (e ▸ (mem_outN.mp jg).2)
  have gn : g ∉ outN X.D X.V x := fun xg => shared ⟨g,xg,jg,gp⟩
  have card2 : ({p,j}:Finset ℕ).card ≤ 2 := card_le_two
  obtain ⟨h,xh,hclear⟩ := exists_off_small (S:=outN X.D X.V x) (F:={p,j})
    (by rw [reg x xv]; omega)
  have hp : h ≠ p := fun e => hclear (by simp [e])
  have hj : h ≠ j := fun e => hclear (by simp [e])
  have pj : p ≠ j := fun e => loopfree X.free (by omega) jv (e ▸ ajp)
  let T : Finset ℕ := {p,h}
  let K : Finset ℕ := {g}
  have head : T ⊆ outN X.D X.V x := insert_subset_iff.mpr ⟨xp,singleton_subset_iff.mpr xh⟩
  have count : T.card = 2 := card_pair hp.symm
  have jt : j ∉ T := by simp [T,pj.symm,hj.symm]
  have keep : K ⊆ X.V \ (outN X.D X.V x ∪ {x,z,j}) := by
    apply singleton_subset_iff.mpr
    exact mem_sdiff.mpr ⟨outN_subset jg,by simp [gn,gx,gz,gj]⟩
  have pg : ({p,g}:Finset ℕ) ⊆ outN X.D (T ∪ K) j := by
    apply insert_subset_iff.mpr
    refine ⟨mem_outN.mpr ⟨by simp [T],ajp⟩, singleton_subset_iff.mpr ?_⟩
    exact mem_outN.mpr ⟨by simp [K],(mem_outN.mp jg).2⟩
  have pc : ({p,g}:Finset ℕ).card = 2 := card_pair gp.symm
  apply extend_joint_bank hq hs reg room size (by omega) space xv jv xj.symm
    (mem_sdiff.mp zkeep).1 pz xz head count (by simp [T]) jt keep
  · simp only [K,card_singleton]; omega
  · exact pc ▸ card_le_card pg

end LeanCH.BR.BypassBankReplay

