import checkpoints.shen_extension.JointBankFreeTargets

/-! A simultaneous certificate on the original carrier. Each row may have
several different new heads. All degree counts are on surviving labels. -/
namespace LeanCH.BR.TripleBank
open Finset BRq2 BRq3 BR45 JointFreeTargets

def patch (D : CH.Digraph) (A C : ℕ → Finset ℕ) : CH.Digraph :=
  fun x y => decide (y ∈ A x ∨ D x y = true ∧ y ∉ C x)

/-- A check on one-new-edge returns and on consecutive new edges covers
every short cycle of a multi-head edit. Deleted old arcs are counted once. -/
theorem patch_certificate {D : CH.Digraph} {U : Finset ℕ} {A C : ℕ → Finset ℕ}
    (safe : QFree D U 3)
    (fresh : ∀ a ∈ U, ∀ b ∈ A a, b ∈ U ∧ b ≠ a ∧ D a b ≠ true ∧ D b a ≠ true)
    (returns : ∀ a ∈ U, ∀ b ∈ A a, ∀ w ∈ U, D b w = true → D w a = true →
      w ∈ C b ∨ a ∈ C w)
    (consecutive : ∀ a ∈ U, ∀ b ∈ A a, ∀ w ∈ A b,
      w ≠ a ∧ patch D A C w a ≠ true) :
    QFree (patch D A C) U 3 ∧ ∀ a ∈ U,
      (outN (patch D A C) U a).card = ((outN D U a) \ C a).card + (A a).card := by
  classical
  let E := patch D A C
  have edges {a b} (ed : E a b = true) : b ∈ A a ∨ D a b = true ∧ b ∉ C a := of_decide_eq_true ed
  have tri {a b w} (au : a ∈ U) (bu : b ∈ U) (wu : w ∈ U) (ab : b ∈ A a)
      (bw : E b w = true) (wa : E w a = true) : False := by
    rcases edges bw with new | ⟨old,kept⟩
    · exact (consecutive a au b ab w new).2 wa
    rcases edges wa with new | ⟨old',kept'⟩
    · exact (consecutive w wu a new b ab).2 bw
    · exact (returns a au b ab w wu old old').elim kept kept'
  constructor
  · apply DotOriginalStarReturn.qfree_three_of_tests
    · intro a au aa
      rcases edges aa with new | old
      · exact (fresh a au a new).2.1 rfl
      · exact loopfree safe (by decide) au old.1
    · intro a au b bu ab ba
      rcases edges ab with new | old
      · rcases edges ba with new' | old'
        · exact (consecutive a au b new a new').1 rfl
        · exact (fresh a au b new).2.2.2 old'.1
      · rcases edges ba with new' | old'
        · exact (fresh b bu a new').2.2.2 old.1
        · exact digonfree safe (by decide) au bu old.1 old'.1
    · intro a au b bu w wu ab bw wa
      rcases edges ab with new | old
      · exact tri au bu wu new bw wa
      rcases edges bw with new | old'
      · exact tri bu wu au new wa ab
      rcases edges wa with new | old''
      · exact tri wu au bu new ab bw
      · exact safe a 3 (by decide) (by decide)
          (.step bu old.1 (.step wu old'.1 (.step au old''.1 (.refl _))))
  · intro a au
    have row : outN E U a = (outN D U a \ C a) ∪ A a := by
      ext b
      simp only [E,patch,mem_outN,decide_eq_true_eq,mem_union,mem_sdiff]
      have := fun h : b ∈ A a => (fresh a au b h).1
      tauto
    have dis : Disjoint (outN D U a \ C a) (A a) := disjoint_left.mpr (fun _ old new =>
      (fresh a au _ new).2.2.1 (mem_outN.mp (mem_sdiff.mp old).1).2)
    rw [row,card_union_of_disjoint dis]

noncomputable def available (D : CH.Digraph) (U R : Finset ℕ) (a : ℕ) : Finset ℕ := by
  classical
  exact (U \ R).filter (FreeTarget D U a)

/-- Add every available head to every selected row across one cut. -/
theorem free_menus {D : CH.Digraph} {U R : Finset ℕ} (safe : QFree D U 3) :
    ∃ E : CH.Digraph, QFree E U 3 ∧ ∀ a ∈ U, (outN E U a).card =
      (outN D U a).card + if a ∈ R then (available D U R a).card else 0 := by
  classical
  let A (a : ℕ) := if a ∈ R then available D U R a else ∅
  have spec {a b} (ed : b ∈ A a) : a ∈ R ∧ b ∉ R ∧ FreeTarget D U a b := by
    by_cases ar : a ∈ R
    · have h : b ∈ available D U R a := by simpa [A,ar] using ed
      exact ⟨ar,(mem_sdiff.mp (mem_filter.mp h).1).2,(mem_filter.mp h).2⟩
    · simp [A,ar] at ed
  obtain ⟨ok,rows⟩ := patch_certificate (A := A) (C := fun _ => ∅) safe
    (fun _ _ _ ed => by
      have f := (spec ed).2.2
      exact ⟨f.1,f.2.1,f.2.2.1,f.2.2.2.1⟩)
    (fun _ _ _ ed w wu bw wa => False.elim ((spec ed).2.2.2.2.2.2 w wu bw wa))
    (fun _ _ _ ed _ next => False.elim ((spec ed).2.1 (spec next).1))
  exact ⟨_,ok,fun a au => by simpa [A,apply_ite Finset.card] using rows a au⟩

/-- Any deletion with a forbidden repaired host leaves a short row whose
available heads do not pay its entire deficit. -/
theorem unpaid_row {D : CH.Digraph} {U : Finset ℕ} {t : ℕ}
    (safe : QFree D U 3) (noFloor : ∀ E, QFree E U 3 → ¬ ∀ a ∈ U, t ≤ (outN E U a).card) :
    let R := U.filter (fun a => (outN D U a).card < t)
    ∃ a ∈ R, (outN D U a).card + (available D U R a).card < t := by
  classical
  intro R
  obtain ⟨E,ok,rows⟩ := free_menus (R := R) safe
  by_contra! paid
  apply noFloor E ok
  intro a au
  rw [rows a au]
  by_cases ar : a ∈ R
  · simpa [ar] using paid a ar
  · have floor : t ≤ (outN D U a).card := by
      by_contra! short
      exact ar (mem_filter.mpr ⟨au,short⟩)
    simpa [ar] using floor

/-- Minimum order at the original quota supplies a shared head over each
label. The proof uses no upper bound on the order or lower-quota induction. -/
theorem singleton_covered {s : ℕ} (X : ShenMinimumOrder.Source 3 s) (hs : 0 < s)
    {v : ℕ} (vv : v ∈ X.V) :
    ∃ r ∈ X.V, (outN X.D X.V r).card = s ∧ v ∈ sharedHeads X.D X.V r ∧
      ∀ y, FreeTarget X.D X.V r y → (outN X.D X.V y).card = s := by
  classical
  let U := X.V.erase v
  let R := U.filter (fun c => (outN X.D U c).card < s)
  have pos : U.Nonempty := by
    obtain ⟨w,hw⟩ := card_pos.mp (hs.trans_le (X.degree v vv))
    obtain ⟨wv,vw⟩ := mem_outN.mp hw
    exact ⟨w,mem_erase.mpr ⟨fun eq => loopfree X.free (by decide) vv (eq ▸ vw),wv⟩⟩
  have split (a : ℕ) : outN X.D U a = (outN X.D X.V a).erase v := by
    ext b; simp only [U,mem_outN,mem_erase]; tauto
  obtain ⟨c,cr,low⟩ := unpaid_row (U := U) (t := s) (X.free.mono_set (erase_subset _ _))
    (fun E ok floor => by
      have lower := X.least E U ok floor pos
      have eq : U.card = X.V.card-1 := card_erase_of_mem vv
      have hi := card_pos.mpr X.nonempty
      omega)
  have cu := (mem_filter.mp cr).1
  have cv := (mem_erase.mp cu).2
  have edge (a) (ar : a ∈ R) : X.D a v = true := by
    obtain ⟨au,short⟩ := mem_filter.mp ar
    by_contra miss
    have absent : v ∉ outN X.D X.V a := fun h => miss (mem_outN.mp h).2
    rw [split,erase_eq_of_notMem absent] at short
    exact short.not_ge (X.degree a (mem_erase.mp au).2)
  have ev := edge c cr
  have drop := card_erase_of_mem (mem_outN.mpr ⟨vv,ev⟩)
  change (outN X.D U c).card + (available X.D U R c).card < s at low
  rw [split,drop] at low
  have floor := X.degree c cv
  have tight (a) (ar : a ∈ R) : (outN X.D X.V a).card = s := by
    obtain ⟨au,short⟩ := mem_filter.mp ar
    have degree := X.degree a (mem_erase.mp au).2
    rw [split,card_erase_of_mem (mem_outN.mpr ⟨vv,edge a ar⟩)] at short
    omega
  have allRows (b) (fb : FreeTarget X.D X.V c b) : b ∈ R := by
    by_contra off
    have bu : b ∈ U := mem_erase.mpr ⟨fun eq => fb.2.2.1 (eq ▸ ev),fb.1⟩
    have localFree : FreeTarget X.D U c b := ⟨bu,fb.2.1,fb.2.2.1,fb.2.2.2.1,
      fun w wu => fb.2.2.2.2 w (mem_erase.mp wu).2⟩
    have am : b ∈ available X.D U R c := mem_filter.mpr ⟨mem_sdiff.mpr ⟨bu,off⟩,localFree⟩
    have count := card_pos.mpr (show (available X.D U R c).Nonempty from ⟨b,am⟩)
    omega
  exact ⟨c,cv,tight c cr,mem_filter.mpr ⟨mem_outN.mpr ⟨vv,ev⟩,fun y fy => edge y (allRows y fy)⟩,
    fun y fy => tight y (allRows y fy)⟩

/-- Triple obstruction on the survivor set. Free targets newly opened by
deletion are included, and a deleted label is never counted as a target. -/
theorem triple_obstruction {D : CH.Digraph} {V B : Finset ℕ} {s : ℕ}
    (free : QFree D V 3) (reg : OutEq s D V) (hs : 2 ≤ s)
    (room : V.card = 3*s) (none : BypassRepair.NoHost 3 (s-1))
    (bv : B ⊆ V) (three : B.card = 3) :
    let U := V \ B
    let S := U.filter (fun c => 2 ≤ (outN D B c).card)
    ∃ c ∈ S, ((outN D B c).card = 2 ∧ available D U S c = ∅) ∨
      ((outN D B c).card = 3 ∧ (available D U S c).card ≤ 1) := by
  classical
  let U := V \ B
  let S := U.filter (fun c => 2 ≤ (outN D B c).card)
  have size : U.card = 3*(s-1) := by
    change (V \ B).card = _
    rw [card_sdiff_of_subset bv,room,three]; omega
  have split (c) (cu : c ∈ U) : (outN D U c).card + (outN D B c).card = s := by
    have h := card_outN_union (D := D) (show Disjoint B U from disjoint_sdiff) c
    rw [union_sdiff_of_subset bv,reg c (mem_sdiff.mp cu).1] at h
    omega
  have eq : U.filter (fun c => (outN D U c).card < s-1) = S := by
    ext c; by_cases cu : c ∈ U
    · have := split c cu
      simp [S,cu]; omega
    · simp [S,cu]
  obtain ⟨c,cm,low⟩ := unpaid_row (U := U) (t := s-1) (free.mono_set sdiff_subset)
    (fun E ok => none E U (card_pos.mp (by omega)) size.le ok)
  rw [eq] at cm low
  have cs := mem_filter.mp cm
  have gap := split c cs.1
  have maxHits := (card_le_card (outN_subset : outN D B c ⊆ B)).trans three.le
  change ∃ c ∈ S, ((outN D B c).card = 2 ∧ available D U S c = ∅) ∨
    ((outN D B c).card = 3 ∧ (available D U S c).card ≤ 1)
  refine ⟨c,cm,?_⟩
  by_cases hit : (outN D B c).card = 2
  · exact Or.inl ⟨hit,card_eq_zero.mp (by omega)⟩
  · exact Or.inr ⟨by omega,by omega⟩

#print axioms patch_certificate
#print axioms free_menus
#print axioms unpaid_row
#print axioms singleton_covered
#print axioms triple_obstruction
end LeanCH.BR.TripleBank

