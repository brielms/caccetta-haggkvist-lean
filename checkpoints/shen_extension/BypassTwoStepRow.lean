import checkpoints.shen_extension.BypassBankReplay
import checkpoints.shen_extension.dot_tensor_research.DotFullReturnCut_20261118

namespace LeanCH.BR.BypassTwoStepRow
open Finset BRq2 BRq3 BypassRepair BypassBankReplay

/-- A tight parent is counted on the surviving carrier, even when routes are tested
    in the full native graph. -/
def TightParent (D : CH.Digraph) (U : Finset ℕ) (t x y : ℕ) : Prop :=
  y ∈ U ∧ y ≠ x ∧ D y x = true ∧ (outN D U y).card = t

private theorem trim_context {D : CH.Digraph} {U : Finset ℕ} {t x : ℕ}
    (low : (outN D U x).card ≤ t) (other : ∀ a ∈ U, a ≠ x → t ≤ (outN D U a).card) :
    ∃ K : CH.Digraph, (∀ a b, K a b = true → D a b = true) ∧
      outN K U x = outN D U x ∧ (∀ a ∈ U, a ≠ x → t ≤ (outN K U a).card) ∧
      ∀ y ∈ U, y ≠ x → K y x = true → TightParent D U t x y := by
  classical
  let A := U.filter (fun a => t < (outN D U a).card)
  let K := DotFullReturnCut.cut D A x
  refine ⟨K,fun _ _ arc => DotFullReturnCut.cut_sub arc,
    DotFullReturnCut.cut_outside_row (show x ∉ A from fun h => (not_lt_of_ge low) (mem_filter.mp h).2), ?_, ?_⟩
  · intro a au ax
    by_cases hit : a ∈ A
    · have high := (mem_filter.mp hit).2
      change t ≤ (outN (DotFullReturnCut.cut D A x) U a).card
      rw [DotFullReturnCut.cut_donor_row hit]
      by_cases arc : x ∈ outN D U a
      · have := card_erase_add_one arc
        omega
      · rw [erase_eq_of_notMem arc]
        omega
    · rw [show outN K U a = outN D U a from DotFullReturnCut.cut_outside_row hit]
      exact other a au ax
  · intro y yu yx last
    have off : y ∉ A := (DotFullReturnCut.cut_edge.mp last).2.resolve_right (not_not.mpr rfl)
    have bound : (outN D U y).card ≤ t := Nat.le_of_not_gt (fun high => off (mem_filter.mpr ⟨yu,high⟩))
    exact ⟨yu,yx,DotFullReturnCut.cut_sub last,le_antisymm bound (other y yu yx)⟩

/-- Remove all spare parents' arcs into x once. Every forbidden extra head then
    leads to an actual tight parent. The same return excludes every positive
    reverse route that would fit in the remaining native length budget. -/
theorem blocked_return {D : CH.Digraph} {V U : Finset ℕ} {q t x k : ℕ}
    (none : NoHost q t) (small : U.card ≤ q*t) (free : QFree D V q) (uv : U ⊆ V)
    (xu : x ∈ U) (row : (outN D U x).card + 1 = t)
    (other : ∀ a ∈ U, a ≠ x → t ≤ (outN D U a).card)
    (ku : k ∈ U) (kx : k ≠ x) (fresh : D x k ≠ true) :
    ∃ y, TightParent D U t x y ∧ ∃ l, l+2 ≤ q ∧ Walk D U k y l ∧
      ∀ i, 0 < i → i+l ≤ q → ¬ Walk D V y k i := by
  classical
  obtain ⟨K,sub,keep,paid,lastTight⟩ := trim_context (by omega : (outN D U x).card ≤ t) other
  have freeK : QFree K U q := fun a i pos cap w =>
    free a i pos cap ((walk_sub sub w).mono uv)
  obtain ⟨a, au, short, alternatives⟩ := DeleteRepair.common_recipient freeK ku
    (fun E => none E U ⟨x,xu⟩ small)
  have ax : a = x := by
    by_contra ne
    have := paid a au ne
    omega
  subst a
  rcases alternatives with deep | same | old | ⟨m, cap, path⟩
  · rw [keep] at deep
    omega
  · exact False.elim (kx same.symm)
  · exact False.elim (fresh (sub _ _ old))
  · cases m with
    | zero => cases path; exact False.elim (kx rfl)
    | succ l =>
      obtain ⟨y, first, _, last⟩ := path.unsnoc
      have yu : y ∈ U := first.end_mem_or.elim (fun eq => eq ▸ ku) id
      have edge : D y x = true := sub _ _ last
      have yx : y ≠ x := by
        rintro rfl
        exact loopfree free (by omega) (uv xu) edge
      have route := walk_sub sub first
      refine ⟨y, lastTight y yu yx last, l, by omega, route, ?_⟩
      intro i pos budget back
      exact free y (i+l) (by omega) budget (back.append (route.mono uv))

/-- One literal edit pays any size deficit on x. For each proposed target
    k, each tight parent's own route to k may use a different intermediary,
    including a deleted label. All proposed arcs can be installed together. -/
theorem joint_targets_host {D : CH.Digraph} {V U F : Finset ℕ} {q t x : ℕ}
    (free : QFree D V q) (uv : U ⊆ V) (xu : x ∈ U)
    (low : (outN D U x).card ≤ t) (other : ∀ a ∈ U, a ≠ x → t ≤ (outN D U a).card)
    (targets : F ⊆ U.erase x)
    (returns : ∀ k ∈ F, ∀ y, TightParent D U t x y → Walk D V y k 2)
    (enough : t ≤ (outN D U x ∪ F).card) :
    ∃ E : CH.Digraph, QFree E U q ∧ (∀ a ∈ U, t ≤ (outN E U a).card) ∧
      outN E U x = outN D U x ∪ F := by
  obtain ⟨K,sub,keep,paid,lastTight⟩ := trim_context low other
  let E := DeleteRepair.repair K {x} (fun _ => F)
  have safe : QFree E U q := by
    apply DeleteRepair.repair_qfree (show QFree K U q from fun a i pos cap w =>
      free a i pos cap ((walk_sub sub w).mono uv))
    intro _ _ k kf b bx m cap path
    rw [mem_singleton.mp bx] at path
    obtain ⟨kx,ku⟩ := mem_erase.mp (targets kf)
    cases m with
    | zero => cases path; exact kx rfl
    | succ l =>
      obtain ⟨y,first,_,last⟩ := path.unsnoc
      have yu : y ∈ U := first.end_mem_or.elim (fun eq => eq ▸ ku) id
      have yx : y ≠ x := by
        rintro rfl
        exact loopfree free (by omega) (uv xu) (sub _ _ last)
      have back := returns k kf y (lastTight y yu yx last)
      exact free y (2+l) (by omega) (by omega) (back.append ((walk_sub sub first).mono uv))
  have row : outN E U x = outN D U x ∪ F := by
    rw [← keep]
    ext k
    simp only [E,mem_outN,DeleteRepair.repair,Bool.or_eq_true,Bool.and_eq_true,
      decide_eq_true_eq,mem_singleton_self,true_and,mem_union]
    have live (kf : k ∈ F) : k ∈ U := mem_of_mem_erase (targets kf)
    tauto
  refine ⟨E,safe,?_,row⟩
  intro a au
  by_cases ax : a = x
  · simpa [ax,row] using enough
  · exact (paid a au ax).trans (card_le_card (fun k hk =>
      mem_outN.mpr ⟨outN_subset hk,DeleteRepair.repair_old (mem_outN.mp hk).2⟩))

/-- In a terminal source the common two-step columns can fill strictly
    fewer slots than the row needs, even with an arbitrary shortage. -/
@[aesop safe forward (immediate := [none,small,free,uv,xu,low,other,targets,returns]) (rule_sets := [CHGraphFamilies])]
theorem joint_targets_cap {D V U F q t x} (none : NoHost q t) (small : U.card ≤ q*t)
    (free : QFree D V q) (uv : U ⊆ V) (xu : x ∈ U)
    (low : (outN D U x).card ≤ t) (other : ∀ a ∈ U, a ≠ x → t ≤ (outN D U a).card)
    (targets : F ⊆ U.erase x)
    (returns : ∀ k ∈ F, ∀ y, TightParent D U t x y → Walk D V y k 2) :
    (outN D U x ∪ F).card < t := by
  by_contra! enough
  obtain ⟨E,safe,paid,_⟩ := joint_targets_host free uv xu low other targets returns enough
  exact none E U ⟨x,xu⟩ small safe paid

/-- On surviving labels distinct from x, its native row is exactly the
    intersection of the exact two-step rows of its tight parents. -/
structure Reconstructed (D : CH.Digraph) (V U : Finset ℕ) (t x : ℕ) : Prop where
  at_label : ∀ k ∈ U, k ≠ x → (D x k = true ↔ ∀ y, TightParent D U t x y → Walk D V y k 2)

@[aesop safe forward (immediate := [rec,ku,kx,fresh,routes]) (rule_sets := [CHGraphFamilies])]
theorem extra_head_exit {D V U t x k} (rec : Reconstructed D V U t x)
    (ku : k ∈ U) (kx : k ≠ x) (fresh : D x k ≠ true)
    (routes : ∀ y, TightParent D U t x y → Walk D V y k 2) : False :=
  fresh ((rec.at_label k ku kx).mpr routes)

@[aesop safe forward (immediate := [none,small,free,uv,xu,row,other]) (rule_sets := [CHGraphFamilies])]
theorem reconstruct {D V U q t x} (none : NoHost q t) (small : U.card ≤ q*t)
    (free : QFree D V q) (uv : U ⊆ V) (xu : x ∈ U)
    (row : (outN D U x).card + 1 = t) (other : ∀ a ∈ U, a ≠ x → t ≤ (outN D U a).card) :
    Reconstructed D V U t x := by
  refine ⟨fun k ku kx => ⟨fun hit y hy => .step (uv xu) hy.2.2.1 (.step (uv ku) hit (.refl k)), ?_⟩⟩
  intro all
  by_contra fresh
  obtain ⟨y, tight, l, cap, _, block⟩ := blocked_return none small free uv xu row other ku kx fresh
  exact block 2 (by decide) (by omega) (all y tight)

@[aesop safe forward (immediate := [none,cell,lone]) (rule_sets := [CHGraphFamilies])]
theorem on_lone {q r} {X : ShenMinimumOrder.Source q r} {m : Cell}
    (none : NoHost q (r-1)) (cell : Marked X m) (lone : LoneBlocked X m) :
    Reconstructed X.D X.V (X.V \ m.bank) (r-1) m.x := by
  have size := cell.size
  have card := card_sdiff_add_card_eq_card cell.sub
  exact reconstruct none (by omega) X.free sdiff_subset cell.xu cell.deficit lone.paid_elsewhere

/-- Every intermediate label hit by all the tight parents has its surviving
    heads confined to the row of x, apart from x itself. This also applies
    to intermediate labels in the erased bank. -/
theorem intermediate_heads {D V U t x h} (rec : Reconstructed D V U t x)
    (uv : U ⊆ V) (hv : h ∈ V) (feeds : ∀ y, TightParent D U t x y → D y h = true) :
    (outN D U h).erase x ⊆ outN D U x := by
  intro k hk
  obtain ⟨kx,head⟩ := mem_erase.mp hk
  obtain ⟨ku,hk⟩ := mem_outN.mp head
  exact mem_outN.mpr ⟨ku,(rec.at_label k ku kx).mpr
    (fun y yt => .step hv (feeds y yt) (.step (uv ku) hk (.refl k)))⟩

/-- The same erased h is charged. If every tight parent feeds h, all h's
    native heads beyond x's row are erased, except possibly x itself. -/
theorem intermediate_bill {D V U t x h} (rec : Reconstructed D V U t x)
    (uv : U ⊆ V) (xu : x ∈ U) (hv : h ∈ V)
    (feeds : ∀ y, TightParent D U t x y → D y h = true) :
    (outN D V h).card ≤ (outN D (V \ U) h).card +
      (if D h x = true then 1 else 0) + (outN D U x).card := by
  have row : outN D V h = outN D (V \ U) h ∪ outN D U h := by
    ext k
    simp only [mem_outN, mem_union, mem_sdiff]
    grind
  have le := card_le_card (intermediate_heads rec uv hv feeds)
  have parts := card_union_le (outN D (V \ U) h) (outN D U h)
  rw [row]
  by_cases hx : D h x = true
  · have := card_erase_add_one (mem_outN.mpr ⟨xu,hx⟩)
    simp only [hx, ↓reduceIte]
    omega
  · simp only [hx]
    rw [erase_eq_of_notMem (show x ∉ outN D U h from fun hit => hx (mem_outN.mp hit).2)] at le
    omega

/-- The two units in the native one-debtor case are the difference between
    h's native degree and the debtor's surviving degree. This version keeps
    that difference symbolic and preserves the earlier unpaid parent y. -/
theorem lost_head_alternative {D V U t x y h} (rec : Reconstructed D V U t x)
    (uv : U ⊆ V) (xu : x ∈ U) (hv : h ∈ V) (lost : D y h = true) :
    (outN D V h).card ≤ (outN D (V \ U) h).card +
      (if D h x = true then 1 else 0) + (outN D U x).card ∨
    ∃ v, TightParent D U t x v ∧ v ≠ y ∧ D v h ≠ true := by
  classical
  by_cases all : ∀ v, TightParent D U t x v → D v h = true
  · exact Or.inl (intermediate_bill rec uv xu hv all)
  · push Not at all
    obtain ⟨v,tight,miss⟩ := all
    exact Or.inr ⟨v,tight,fun eq => miss (eq ▸ lost),miss⟩

/-- On the actual marked bank, an erased head shared by all tight parents
    owes at least two heads to the bank together with the possible arc to x. -/
theorem marked_lost_head {q r} {X : ShenMinimumOrder.Source q r} {m : Cell}
    (cell : Marked X m) (rec : Reconstructed X.D X.V (X.V \ m.bank) (r-1) m.x)
    {y h} (hb : h ∈ m.bank) (lost : X.D y h = true) :
    2 ≤ (outN X.D m.bank h).card + (if X.D h m.x = true then 1 else 0) ∨
    ∃ v, TightParent X.D (X.V \ m.bank) (r-1) m.x v ∧ v ≠ y ∧ X.D v h ≠ true := by
  rcases lost_head_alternative rec sdiff_subset cell.xu (cell.sub hb) lost with bill | sep
  · have same : X.V \ (X.V \ m.bank) = m.bank := by
      ext k
      simp only [mem_sdiff]
      exact ⟨fun p => by tauto, fun b => ⟨cell.sub b,fun n => n.2 b⟩⟩
    rw [same] at bill
    have lower := X.degree h (cell.sub hb)
    have short := cell.deficit
    exact Or.inl (by omega)
  · exact Or.inr sep

#print axioms blocked_return
#print axioms joint_targets_host
#print axioms joint_targets_cap
#print axioms reconstruct
#print axioms extra_head_exit
#print axioms on_lone
#print axioms intermediate_heads
#print axioms intermediate_bill
#print axioms lost_head_alternative
#print axioms marked_lost_head
end LeanCH.BR.BypassTwoStepRow
