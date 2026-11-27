import checkpoints.shen_extension.TripleBankSelection

/-! Many new heads can be paid at the same row with just one outgoing cut
per blocker. Apply this to one fixed targetable triple at the top order. -/
namespace LeanCH.BR.TripleBank
open Finset BRq2 BRq3 BR45 JointFreeTargets

/-- Available heads for one row comprise the missed common targets and
every individually free surviving label. The union counts an overlap once. -/
noncomputable def rowMenu (D : CH.Digraph) (U P : Finset ℕ) (c : ℕ) : Finset ℕ := by
  classical
  exact (P \ outN D U c) ∪ U.filter (FreeTarget D U c)

/-- Add the entire menu at one row. A blocker of several return paths loses
only its edge to c. Every other row keeps its degree up to the required floor. -/
theorem single_menu {D : CH.Digraph} {V B P : Finset ℕ} {s c : ℕ}
    (safe : QFree D V 3) (reg : OutEq s D V) (sub : B ⊆ V) (pv : P ⊆ V)
    (common : ∀ b ∈ B, P ⊆ outN D V b) (cu : c ∈ V \ B)
    (hit : (outN D B c).Nonempty) :
    let U := V \ B
    ∃ E : CH.Digraph, QFree E U 3 ∧
      (outN E U c).card = (outN D U c).card + (rowMenu D U P c).card ∧
      ∀ a ∈ U, a ≠ c → min (s-1) (outN E U a).card = min (s-1) (outN D U a).card := by
  classical
  let U := V \ B
  let M := rowMenu D U P c
  let A (a : ℕ) : Finset ℕ := if a = c then M else ∅
  let C (a : ℕ) : Finset ℕ := if ∃ z ∈ P, D z a = true then {c} else ∅
  obtain ⟨b,bm⟩ := hit
  obtain ⟨bB,cb⟩ := mem_outN.mp bm
  have cv := (mem_sdiff.mp cu).1
  have inside {z} (zp : z ∈ P) : z ∈ U := mem_sdiff.mpr ⟨pv zp,fun zb =>
    loopfree safe (by decide) (pv zp) (mem_outN.mp (common z zb zp)).2⟩
  have noBack {z} (zp : z ∈ P) : D z c ≠ true := fun zc => safe c 3 (by decide) (by decide)
    (.step (sub bB) cb (.step (pv zp) (mem_outN.mp (common b bB zp)).2 (.step cv zc (.refl _))))
  have spec {a z} (new : z ∈ A a) : a = c ∧ z ∈ U ∧ z ≠ c ∧ D c z ≠ true ∧ D z c ≠ true := by
    by_cases ac : a = c
    · subst a
      have zm : z ∈ rowMenu D U P c := by simpa [A,M] using new
      rcases mem_union.mp zm with general | unpaid
      · obtain ⟨zp,old⟩ := mem_sdiff.mp general
        have zc : z ≠ c := fun eq => digonfree safe (by decide) (sub bB) cv
          (eq ▸ (mem_outN.mp (common b bB zp)).2) cb
        exact ⟨rfl,inside zp,zc,fun ed => old (mem_outN.mpr ⟨inside zp,ed⟩),noBack zp⟩
      · obtain ⟨zu,fv⟩ := mem_filter.mp unpaid
        exact ⟨rfl,zu,fv.2.1,fv.2.2.1,fv.2.2.2.1⟩
    · simp [A,ac] at new
  obtain ⟨ok,rows⟩ := patch_certificate (U := U) (A := A) (C := C) (safe.mono_set sdiff_subset)
    (fun _ _ _ new => by obtain ⟨rfl,h⟩ := spec new; exact h)
    (fun a _ z new w wu zw wc => by
      obtain ⟨rfl,_⟩ := spec new
      have zm : z ∈ rowMenu D U P a := by simpa [A,M] using new
      rcases mem_union.mp zm with general | unpaid
      · exact Or.inr (by simp [C,show ∃ t ∈ P, D t w = true from ⟨z,(mem_sdiff.mp general).1,zw⟩])
      · exact False.elim ((mem_filter.mp unpaid).2.2.2.2.2 w wu zw wc))
    (fun _ _ _ new _ next => False.elim ((spec new).2.2.1 (spec next).1))
  have noCut : ¬ ∃ z ∈ P, D z c = true := fun ⟨_,zp,zc⟩ => noBack zp zc
  refine ⟨_,ok,by simpa [A,C,M,noCut] using rows c cu,?_⟩
  intro a au ac
  rw [rows a au]
  by_cases active : ∃ z ∈ P, D z a = true
  · obtain ⟨z,zp,za⟩ := active
    have av := (mem_sdiff.mp au).1
    have noneOld : ∀ b ∈ B, D a b ≠ true := fun b bb ab => safe b 3 (by decide) (by decide)
      (.step (pv zp) (mem_outN.mp (common b bb zp)).2 (.step av za (.step (sub bb) ab (.refl _))))
    have same : outN D U a = outN D V a := by
      ext v; simp only [U,mem_outN,mem_sdiff]
      constructor
      · rintro ⟨⟨vv,_⟩,ed⟩; exact ⟨vv,ed⟩
      · rintro ⟨vv,ed⟩; exact ⟨⟨vv,fun vb => noneOld _ vb ed⟩,ed⟩
    have active' : ∃ z ∈ P, D z a = true := ⟨z,zp,za⟩
    simp only [C,ite_eq_left active',A,ite_eq_right ac,card_empty,add_zero,sdiff_singleton_eq_erase]
    by_cases edge : c ∈ outN D U a
    · rw [card_erase_of_mem edge,same,reg a av]; omega
    · rw [erase_eq_of_notMem edge]
  · simp [A,C,active,ac,U]

/-- On the chosen triple all short rows can recover a degree unit, while a
lone short row must lose three heads and have a one-element repair menu. -/
theorem top_repair_frontier {D : CH.Digraph} {V : Finset ℕ} {s : ℕ}
    (safe : QFree D V 3) (reg : OutEq s D V) (hs : 7 ≤ s) (room : V.card = 3*s)
    (none : BypassRepair.NoHost 3 (s-1)) :
    ∃ P ⊆ V, 2 ≤ P.card ∧ ∃ B ⊆ V, B.card = 3 ∧ (∀ b ∈ B, P ⊆ outN D V b) ∧
      let U := V \ B
      let S := U.filter (fun c => 2 ≤ (outN D B c).card)
      (∀ c ∈ S, ∃ z ∈ P, D c z ≠ true) ∧
      (∀ c ∈ S, ∃ E : CH.Digraph, QFree E U 3 ∧
        (outN E U c).card = (outN D U c).card + (rowMenu D U P c).card ∧
        ∀ a ∈ U, a ≠ c → min (s-1) (outN E U a).card = min (s-1) (outN D U a).card) ∧
      (2 ≤ S.card ∨ ∃ c, S = {c} ∧ (outN D B c).card = 3 ∧ (rowMenu D U P c).card = 1) := by
  classical
  obtain ⟨P,pv,pc,B,bv,bc,common,miss⟩ := top_triple safe reg hs room
  let U := V \ B
  let S := U.filter (fun c => 2 ≤ (outN D B c).card)
  have each (c) (cs : c ∈ S) := single_menu safe reg bv pv common (mem_filter.mp cs).1
    (card_pos.mp (lt_of_lt_of_le (by decide : 0 < 2) (mem_filter.mp cs).2))
  refine ⟨P,pv,pc,B,bv,bc,common,fun c cs => miss c (mem_filter.mp cs).1 (mem_filter.mp cs).2,each,?_⟩
  change 2 ≤ S.card ∨ ∃ c, S = {c} ∧ (outN D B c).card = 3 ∧ (rowMenu D U P c).card = 1
  by_cases many : 2 ≤ S.card
  · exact Or.inl many
  right
  obtain ⟨c,cs,_⟩ := triple_obstruction safe reg (by omega) room none bv bc
  change c ∈ S at cs
  have single : S = {c} := (eq_of_subset_of_card_le (singleton_subset_iff.mpr cs)
    (by rw [card_singleton]; omega)).symm
  have size : U.card = 3*(s-1) := by change (V \ B).card = _; rw [card_sdiff_of_subset bv,room,bc]; omega
  have split (a) (au : a ∈ U) : (outN D U a).card + (outN D B a).card = s := by
    have h := card_outN_union (D := D) (show Disjoint B U from disjoint_sdiff) a
    rw [union_sdiff_of_subset bv,reg a (mem_sdiff.mp au).1] at h
    omega
  obtain ⟨E,ok,gain,others⟩ := each c cs
  have short : (outN D U c).card + (rowMenu D U P c).card < s-1 := by
    by_contra! enough
    apply none E U (card_pos.mp (by omega)) size.le ok
    intro a au
    by_cases ac : a = c
    · subst a
      change (outN E U c).card = (outN D U c).card + (rowMenu D U P c).card at gain
      rw [gain]; exact enough
    · have off : a ∉ S := fun am => ac (mem_singleton.mp (single ▸ am))
      have hits : (outN D B a).card ≤ 1 := by by_contra! h; exact off (mem_filter.mpr ⟨au,by omega⟩)
      have old := split a au
      have keep := others a au ac
      change min (s-1) (outN E U a).card = min (s-1) (outN D U a).card at keep
      omega
  have cu := (mem_filter.mp cs).1
  obtain ⟨z,zp,fresh⟩ := miss c cu (mem_filter.mp cs).2
  have zm : z ∈ rowMenu D U P c := mem_union_left _ (mem_sdiff.mpr
    ⟨zp,fun edge => fresh (mem_outN.mp edge).2⟩)
  have pos := card_pos.mpr (show (rowMenu D U P c).Nonempty from ⟨z,zm⟩)
  have cnt := split c cu
  have limit := (card_le_card (outN_subset : outN D B c ⊆ B)).trans bc.le
  exact ⟨c,single,by omega,by omega⟩

#print axioms single_menu
#print axioms top_repair_frontier
end LeanCH.BR.TripleBank

