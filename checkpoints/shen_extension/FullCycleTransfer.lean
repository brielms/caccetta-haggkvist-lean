import checkpoints.shen_extension.JointCycleFamilyBarrier
import Mathlib.Logic.Equiv.Fintype

namespace LeanCH.BR.Closure.FullCycleTransfer
open Finset BRq2 BRq3 BR45 ShenPrimeTransition ShenCycleSuccessor ShortestCycleWeights
open FirstPacketBarrier MarkedCyclePeeling TwoCycleTransfer

/-- A bijection of the two cycles that fixes their intersection and respects
the outgoing edge at every shared tail. -/
structure Pairing (E : CH.Digraph) (A M : Finset ℕ) where
  equiv : ↥A ≃ ↥M
  fixed : ∀ y : A, (y : ℕ) ∈ M → (equiv y : ℕ) = y
  successor : ∀ u ∈ A ∩ M, ∀ y : A, E u y = true → E u (equiv y) = true

def Pairing.label {E A M} (P : Pairing E A M) (y : ℕ) : ℕ :=
  if h : y ∈ A then P.equiv ⟨y,h⟩ else y

theorem Pairing.label_apply {E A M} (P : Pairing E A M) {y} (hy : y ∈ A) :
    P.label y = (P.equiv ⟨y,hy⟩ : ℕ) := dite_eq_left hy

theorem Pairing.destination {E A M} (P : Pairing E A M) {y} (hy : y ∈ A \ M) :
    P.label y ∈ M \ A := by
  obtain ⟨ya,ym⟩ := mem_sdiff.mp hy
  rw [P.label_apply ya]
  let r := P.equiv ⟨y,ya⟩
  refine mem_sdiff.mpr ⟨r.property,?_⟩
  intro ra
  have f := P.fixed ⟨r,ra⟩ r.property
  have eq : P.equiv ⟨r,ra⟩ = P.equiv ⟨y,ya⟩ := Subtype.ext f
  have ry : (r : ℕ) = y := congrArg Subtype.val (P.equiv.injective eq)
  exact ym (ry ▸ r.property)

private theorem succ_mem {E V q C u} (c : Cycle E V q C) (uc : u ∈ C) :
    succHead E C u ∈ outN E C u := by
  have pos : (outN E C u).Nonempty := card_pos.mp (by rw [c.heads u uc]; decide)
  simpa only [succHead,dite_eq_left pos] using (outN E C u).min'_mem pos

private theorem succ_inj {E V q C u v} (c : Cycle E V q C) (uc : u ∈ C) (vc : v ∈ C)
    (same : succHead E C u = succHead E C v) : u = v := by
  obtain ⟨yc,uy⟩ := mem_outN.mp (succ_mem c uc)
  have vy := (mem_outN.mp (succ_mem c vc)).2
  rw [←same] at vy
  exact card_le_one.mp (c.incoming _ yc).le _ (mem_inN.mpr ⟨uc,uy⟩) _ (mem_inN.mpr ⟨vc,vy⟩)

/-- Combine distinct shared labels and distinct prescribed heads disjoint from them. -/
private def prescribed {H B C : Finset ℕ} (sub : H ⊆ C) (f : ↥B → ℕ)
    (inside : ∀ b, f b ∈ C) : ↥H ⊕ ↥B → ↥C :=
  Sum.elim (fun h => ⟨h,sub h.property⟩) (fun b => ⟨f b,inside b⟩)

private theorem prescribed_injective {H B C : Finset ℕ} (sub : H ⊆ C) (f : ↥B → ℕ)
    (inside : ∀ b, f b ∈ C) (apart : ∀ b, f b ∉ H) (inj : Function.Injective f) :
    Function.Injective (prescribed sub f inside) := by
  intro s t eq
  have same := congrArg Subtype.val eq
  cases s with
  | inl a =>
    cases t with
    | inl b => exact congrArg Sum.inl (Subtype.ext same)
    | inr b =>
      have ab : (a : ℕ) = f b := same
      exact (apart b (ab ▸ a.property)).elim
  | inr a =>
    cases t with
    | inl b =>
      have ab : f a = (b : ℕ) := same
      exact (apart a (ab ▸ b.property)).elim
    | inr b => exact congrArg Sum.inr (inj same)

/-- The constrained bijection always exists, even for disjoint cycles. -/
theorem exists_pairing {E V q A M} (a : Cycle E V q A) (m : Cycle E V q M) :
    Nonempty (Pairing E A M) := by
  classical
  let H := A ∩ M
  let B := crossing E A M
  let d (u : ↥B) := succHead E A u
  let r (u : ↥B) := succHead E M u
  have shared (u : ↥B) : (u : ℕ) ∈ A ∩ M := (mem_filter.mp u.property).1
  have donor (u : ↥B) : d u ∈ A \ M := (mem_filter.mp u.property).2
  have dest (u : ↥B) : r u ∈ M \ A := recipient_location a m u.property
  let left := prescribed (H:=H) (inter_subset_left : A ∩ M ⊆ A) d
    (fun u => (mem_sdiff.mp (donor u)).1)
  let right := prescribed (H:=H) (inter_subset_right : A ∩ M ⊆ M) r
    (fun u => (mem_sdiff.mp (dest u)).1)
  have li : Function.Injective left := prescribed_injective _ _ _
    (fun u hu => (mem_sdiff.mp (donor u)).2 (mem_inter.mp hu).2)
    (fun u v eq => Subtype.ext (succ_inj a (mem_inter.mp (shared u)).1 (mem_inter.mp (shared v)).1 eq))
  have ri : Function.Injective right := prescribed_injective _ _ _
    (fun u hu => (mem_sdiff.mp (dest u)).2 (mem_inter.mp hu).1)
    (fun u v eq => Subtype.ext (succ_inj m (mem_inter.mp (shared u)).2 (mem_inter.mp (shared v)).2 eq))
  let e : ↥A ≃ ↥M := Finset.equivOfCardEq (a.size.trans m.size.symm)
  obtain ⟨s,rule⟩ := Equiv.Perm.exists_extending_pair (e ∘ left) right (e.injective.comp li) ri
  let phi := e.trans s
  have maps (i : ↥H ⊕ ↥B) : phi (left i) = right i := rule i
  have fixed (y : ↥A) (ym : (y : ℕ) ∈ M) : (phi y : ℕ) = y :=
    congrArg Subtype.val (maps (.inl ⟨y,mem_inter.mpr ⟨y.property,ym⟩⟩))
  refine ⟨⟨phi,fixed,?_⟩⟩
  intro u hu y uy
  by_cases ym : (y : ℕ) ∈ M
  · simpa only [fixed y ym] using uy
  have eq : succHead E A u = y := card_le_one.mp (a.heads u (mem_inter.mp hu).1).le _
    (succ_mem a (mem_inter.mp hu).1) _ (mem_outN.mpr ⟨y.property,uy⟩)
  have ub : u ∈ B := mem_filter.mpr ⟨hu,eq ▸ mem_sdiff.mpr ⟨y.property,ym⟩⟩
  have x : left (.inr ⟨u,ub⟩) = y := Subtype.ext eq
  have mapped := congrArg Subtype.val (maps (.inr ⟨u,ub⟩))
  rw [x] at mapped
  rw [mapped]
  exact (mem_outN.mp (succ_mem m (mem_inter.mp hu).2)).2

/-- All removed labels send their old weight to their paired recipient. -/
def Pairing.deposit {R : Type*} [AddCommMonoid R] {E A M} (P : Pairing E A M) (w : ℕ → R) (v : ℕ) : R :=
  ∑ y ∈ A \ M, if P.label y = v then w y else 0

theorem Pairing.receipts {R : Type*} [AddCommMonoid R] {E A M} (P : Pairing E A M)
    (w : ℕ → R) (S : Finset ℕ) :
    (∑ v ∈ S, P.deposit w v) = ∑ y ∈ A \ M, if P.label y ∈ S then w y else 0 := by
  classical
  unfold Pairing.deposit
  rw [sum_comm]
  apply sum_congr rfl
  intro y _
  simp

theorem Pairing.mass_balance {R : Type*} [AddCommMonoid R] {E V q A M}
    (P : Pairing E A M) (a : Cycle E V q A) (m : Cycle E V q M) (w : ℕ → R) :
    (∑ v ∈ V \ (A \ M), (w v + P.deposit w v)) = ∑ v ∈ V, w v := by
  classical
  have keep {r} (rm : r ∈ M) : r ∈ V \ (A \ M) :=
    mem_sdiff.mpr ⟨m.sub rm,fun gone => (mem_sdiff.mp gone).2 rm⟩
  rw [sum_add_distrib,P.receipts]
  have all : (∑ y ∈ A \ M, if P.label y ∈ V \ (A \ M) then w y else 0) =
      ∑ y ∈ A \ M, w y := sum_congr rfl fun y hy => ite_eq_left (keep (mem_sdiff.mp (P.destination hy)).1)
  rw [all]
  exact sum_sdiff (sdiff_subset.trans a.sub)

/-- Head mass cannot drop when the row sees the recipient of each lost head. -/
theorem Pairing.covered_heads {R : Type*} [AddCommMonoid R] [PartialOrder R] [IsOrderedAddMonoid R]
    {E V q A M} (P : Pairing E A M) (a : Cycle E V q A) (m : Cycle E V q M)
    (w : ℕ → R) (nonneg : ∀ y ∈ A \ M, 0 ≤ w y) (b : ℕ)
    (cover : ∀ y ∈ A \ M, E b y = true → E b (P.label y) = true) :
    (∑ y ∈ V, if E b y = true then w y else 0) ≤
      ∑ y ∈ V \ (A \ M), if E b y = true then w y + P.deposit w y else 0 := by
  classical
  let Z := A \ M
  let U := V \ Z
  have split := sum_sdiff (sdiff_subset.trans a.sub : Z ⊆ V) (f:=fun y => if E b y = true then w y else 0)
  have covered : (∑ y ∈ Z, if E b y = true then w y else 0) ≤ ∑ y ∈ outN E U b,P.deposit w y := by
    rw [P.receipts]
    apply sum_le_sum
    intro y hy
    by_cases yes : E b y = true
    · have rm := (mem_sdiff.mp (P.destination hy)).1
      have ru : P.label y ∈ U := mem_sdiff.mpr ⟨m.sub rm,fun gone => (mem_sdiff.mp gone).2 rm⟩
      have head := mem_outN.mpr ⟨ru,cover y hy yes⟩
      simp [yes,head]
    · rw [ite_eq_right yes]
      by_cases seen : P.label y ∈ outN E U b
      · rw [ite_eq_left seen]
        exact nonneg y hy
      · rw [ite_eq_right seen]
  have add : (∑ y ∈ U, if E b y = true then w y + P.deposit w y else 0) =
      (∑ y ∈ U, if E b y = true then w y else 0) + ∑ y ∈ outN E U b,P.deposit w y := by
    simp only [outN,sum_filter,←sum_add_distrib]
    apply sum_congr rfl
    intro y _
    by_cases yes : E b y = true <;> simp [yes]
  rw [←split,add]
  exact add_le_add le_rfl covered

/-- If a row sees the recipient of each of its deleted heads, its score
after the full transfer is at least its old score. -/
theorem Pairing.covered_score {E V q A M} (P : Pairing E A M) (a : Cycle E V q A)
    (m : Cycle E V q M) (w : ℕ → ℕ) (b : ℕ)
    (cover : ∀ y ∈ A \ M, E b y = true → E b (P.label y) = true) :
    score q E V w b ≤ score q E (V \ (A \ M)) (fun v => w v + P.deposit w v) b := by
  exact Nat.add_le_add (Nat.le_add_right _ _) (Nat.mul_le_mul_left q
    (P.covered_heads a m w (fun _ _ => Nat.zero_le _) b cover))

/-- The protected cycle survives, all surviving rows of A remain strict,
and a failed exterior row sees a specific deleted head and misses its paired label. -/
theorem transfer {q n} (X : Model q n) {E A M w} (P : Pairing E A M)
    (free : QFree E X.V q) (wp : ∀ v ∈ X.V, 0 < w v) (budget : (∑ v ∈ X.V, w v) ≤ n)
    (strict : Strict q E X.V w) (a : Cycle E X.V q A) (m : Cycle E X.V q M) (ne : A ≠ M) :
    let U := X.V \ (A \ M)
    let w' := fun v => w v + P.deposit w v
    Cycle E U q M ∧ (∑ v ∈ U, w' v) = (∑ v ∈ X.V, w v) ∧
      (∀ b ∈ U, b ∈ A → (∑ v ∈ U,w' v) < score q E U w' b) ∧
      ∃ b ∈ X.V \ A, score q E U w' b ≤ (∑ v ∈ U,w' v) ∧
        ∃ y ∈ A \ M, E b y = true ∧ E b (P.label y) = false := by
  classical
  intro U w'
  have keep : M ⊆ U := fun v vm => mem_sdiff.mpr ⟨m.sub vm,fun gone => (mem_sdiff.mp gone).2 vm⟩
  have mass : (∑ v ∈ U,w' v) = ∑ v ∈ X.V,w v := P.mass_balance a m w
  have paid (b) (bu : b ∈ U) (ba : b ∈ A) : (∑ v ∈ U,w' v) < score q E U w' b := by
    have bm : b ∈ M := by_contra fun h => (mem_sdiff.mp bu).2 (mem_sdiff.mpr ⟨ba,h⟩)
    rw [mass]
    apply (nat_strict.mp strict b (a.sub ba)).trans_le (P.covered_score a m w b ?_)
    intro y hy edge
    have ya := (mem_sdiff.mp hy).1
    rw [P.label_apply ya]
    exact P.successor b (mem_inter.mpr ⟨ba,bm⟩) ⟨y,ya⟩ edge
  have nz : (A \ M).Nonempty := sdiff_nonempty.mpr fun sub =>
    ne (eq_of_subset_of_card_le sub (m.size.trans a.size.symm).le)
  have len := card_sdiff_add_card_eq_card (sdiff_subset.trans a.sub : A \ M ⊆ X.V)
  have fewer : U.card < X.V.card := by have := card_pos.mpr nz; dsimp [U]; omega
  obtain ⟨z,zm⟩ := card_pos.mp (show 0 < M.card by rw [m.size]; omega)
  have fail : ¬Strict q E U w' := fun h => fewer.not_ge
    (X.minimal E U w' ⟨z,keep zm⟩ (free.mono_set sdiff_subset)
      (fun v vu => (wp v (mem_sdiff.mp vu).1).trans_le (Nat.le_add_right _ _))
      (mass.le.trans budget) h)
  rw [nat_strict] at fail
  push Not at fail
  obtain ⟨b,bu,low⟩ := fail
  have bv := (mem_sdiff.mp bu).1
  refine ⟨⟨keep,m.size,m.heads,m.incoming⟩,mass,paid,b,
    mem_sdiff.mpr ⟨bv,fun ba => low.not_gt (paid b bu ba)⟩,low,?_⟩
  by_contra! none
  have cover (y) (hy : y ∈ A \ M) (hit : E b y = true) : E b (P.label y) = true :=
    Bool.eq_true_of_not_eq_false (none y hy hit)
  rw [mass] at low
  exact low.not_gt ((nat_strict.mp strict b bv).trans_le (P.covered_score a m w b cover))

/-- The losing row and its uncompensated arc lie on a named third family member. -/
theorem on_family {q n} (X : Model q n) {F w A M} (sub : F ⊆ family X)
    (wp : ∀ v ∈ X.V, 0 < w v) (budget : (∑ v ∈ X.V, w v) ≤ n)
    (strict : Strict q (graph X.D F) X.V w) (af : A ∈ F) (mf : M ∈ F) (ne : A ≠ M)
    (P : Pairing (graph X.D F) A M) :
    let E := graph X.D F
    let U := X.V \ (A \ M)
    let w' := fun v => w v + P.deposit w v
    ∃ L ∈ F, L ≠ A ∧ L ≠ M ∧ ∃ b ∈ L \ A, ∃ y ∈ L ∩ (A \ M),
      E b y = true ∧ E b (P.label y) = false ∧ score q E U w' b ≤ ∑ v ∈ U, w' v := by
  classical
  intro E U w'
  have actual (C) (cf : C ∈ F) : Cycle E X.V q C :=
    retain_cycle (show Cycle X.D X.V q C from (mem_filter.mp (sub cf)).2) cf
  obtain ⟨_,_,_,b,ba,low,y,ym,hit,miss⟩ := transfer X P (PrivateArcEndpoints.graph_free X F)
    wp budget strict (actual A af) (actual M mf) ne
  obtain ⟨L,used⟩ := active.mp hit
  obtain ⟨lf,bl,yl,_⟩ := mem_col.mp used
  exact ⟨L,lf,fun eq => (mem_sdiff.mp ba).2 (eq ▸ bl),
    fun eq => (mem_sdiff.mp ym).2 (eq ▸ yl),b,mem_sdiff.mpr ⟨bl,(mem_sdiff.mp ba).2⟩,
    y,mem_inter.mpr ⟨yl,ym⟩,hit,miss,low⟩

/-- The same full transfer works directly at rational weights when the proper
child satisfies SmallRow. This version uses the given weights without scaling. -/
theorem rational_step {q E V A M} (P : Pairing E A M) (a : Cycle E V q A) (m : Cycle E V q M)
    (x : ℕ → ℚ) (nonneg : ∀ v ∈ V, 0 ≤ x v)
    (strict : ∀ b ∈ V, WeightedSD.mass V x < WeightedSD.row q E V x b)
    (small : WeightedSD.SmallRow q E (V \ (A \ M))) :
    let U := V \ (A \ M)
    let x' := fun v => x v + P.deposit x v
    ∃ b ∈ V \ A, WeightedSD.row q E U x' b ≤ WeightedSD.mass U x' ∧
      ∃ y ∈ A \ M, E b y = true ∧ E b (P.label y) = false := by
  classical
  intro U x'
  have keep : M ⊆ U := fun v vm => mem_sdiff.mpr ⟨m.sub vm,fun gone => (mem_sdiff.mp gone).2 vm⟩
  obtain ⟨z,zm⟩ := card_pos.mp (show 0 < M.card by rw [m.size]; omega)
  have positive (v) : 0 ≤ P.deposit x v := by
    apply sum_nonneg
    intro y hy
    split_ifs
    · exact nonneg y (a.sub (mem_sdiff.mp hy).1)
    · exact le_rfl
  obtain ⟨b,bu,low⟩ := small x' (fun v vu => add_nonneg (nonneg v (mem_sdiff.mp vu).1) (positive v))
    ⟨z,keep zm⟩
  have mass : WeightedSD.mass U x' = WeightedSD.mass V x := P.mass_balance a m x
  have cannot (cover : ∀ y ∈ A \ M, E b y = true → E b (P.label y) = true) : False := by
    have heads := P.covered_heads a m x (fun y hy => nonneg y (a.sub (mem_sdiff.mp hy).1)) b cover
    have nondec : WeightedSD.row q E V x b ≤ WeightedSD.row q E U x' b :=
      add_le_add (le_add_of_nonneg_right (positive b)) (mul_le_mul_of_nonneg_left heads (Nat.cast_nonneg q))
    exact (strict b (mem_sdiff.mp bu).1).not_ge (nondec.trans (low.trans mass.le))
  have outside : b ∉ A := by
    intro ba
    have bm : b ∈ M := by_contra fun h => (mem_sdiff.mp bu).2 (mem_sdiff.mpr ⟨ba,h⟩)
    apply cannot
    intro y hy hit
    have ya := (mem_sdiff.mp hy).1
    rw [P.label_apply ya]
    exact P.successor b (mem_inter.mpr ⟨ba,bm⟩) ⟨y,ya⟩ hit
  refine ⟨b,mem_sdiff.mpr ⟨(mem_sdiff.mp bu).1,outside⟩,low,?_⟩
  by_contra! none
  exact cannot (fun y hy hit => Bool.eq_true_of_not_eq_false (none y hy hit))

#print axioms exists_pairing
#print axioms Pairing.mass_balance
#print axioms transfer
#print axioms on_family
#print axioms rational_step
end LeanCH.BR.Closure.FullCycleTransfer
