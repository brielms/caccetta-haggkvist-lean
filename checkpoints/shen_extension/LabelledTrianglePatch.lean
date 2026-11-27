import checkpoints.shen_extension.RotatedThreeRows

/-! Pay for a patch on any finite set of distinct named vertices. -/
namespace LeanCH.BR.LabelledTrianglePatch
open Finset BRq2 BRq3 BR45 JointFreeTargets TripleBank TwoRowShared
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Return legs that an exterior middle m must cut, for a table of gains. -/
def chargesOf (gains : ι → Finset ι) (D : CH.Digraph) (v : ι ↪ ℕ) (m : ℕ) :
    Finset ι :=
  univ.filter (fun i => D m (v i) = true ∧ ∃ h ∈ gains i, D (v h) m = true)

private noncomputable def liftRow (v : ι ↪ ℕ) (f : ι → Finset ι) (m : ℕ) : Finset ℕ := by
  classical
  exact if hm : ∃ i, v i = m then (f hm.choose).map v else ∅

omit [DecidableEq ι] in
@[simp] private theorem lift_at (v : ι ↪ ℕ) (f : ι → Finset ι) (i : ι) :
    liftRow v f (v i) = (f i).map v := by
  classical
  have hi : ∃ k, v k = v i := ⟨i,rfl⟩
  rw [liftRow,dite_eq_left hi,v.injective hi.choose_spec]

omit [DecidableEq ι] in
@[simp] private theorem lift_off {v : ι ↪ ℕ} {m : ℕ} (off : ∀ i, m ≠ v i)
    (f : ι → Finset ι) : liftRow v f m = ∅ := by
  classical
  exact dite_eq_right (by rintro ⟨i,hi⟩; exact off i hi.symm)

omit [DecidableEq ι] in
private theorem from_label {v : ι ↪ ℕ} {m h : ℕ} {f : ι → Finset ι}
    (hit : h ∈ liftRow v f m) : ∃ i k, m = v i ∧ h = v k ∧ k ∈ f i := by
  classical
  by_cases eq : ∃ i, v i = m
  · obtain ⟨i,rfl⟩ := eq
    rw [lift_at] at hit
    obtain ⟨k,km,rfl⟩ := mem_map.mp hit
    exact ⟨i,k,rfl,rfl,km⟩
  · rw [liftRow,dite_eq_right eq] at hit
    exact False.elim (notMem_empty _ hit)

/-- An edit of a residual graph prescribed on the named vertices by tables of
new heads and cut heads. The three conditions on the tables say that new arcs
are fresh, every internal return is cut, and every label keeps its quota. -/
theorem repair_of_shape {D : CH.Digraph} {U : Finset ℕ} {t : ℕ} (v : ι ↪ ℕ)
    (shortRows : Finset ι) (gains cuts : ι → Finset ι) (allowed : ι → ι → Bool)
    (s1 : ∀ i, ∀ h ∈ gains i, h ≠ i ∧ allowed i h = false ∧
      (allowed h i = false ∨ i ∈ cuts h) ∧ gains h = ∅)
    (s2 : ∀ i, ∀ h ∈ gains i, ∀ m, allowed h m = true → allowed m i = true →
      m ∈ cuts h ∨ i ∈ cuts m)
    (s3 : ∀ i, if i ∈ shortRows then (cuts i).card + 1 ≤ (gains i).card
      else (cuts i).card ≤ 1 + (gains i).card)
    (free : QFree D U 3) (inside : ∀ i, v i ∈ U)
    (internal : ∀ i k, D (v i) (v k) = true → allowed i k = true)
    (need : ∀ i ∈ shortRows, t ≤ (outN D U (v i)).card + 1)
    (spare : ∀ i ∉ shortRows, t+1 ≤ (outN D U (v i)).card)
    (pay : ∀ m ∈ U, (∀ i, m ≠ v i) → t + (chargesOf gains D v m).card ≤ (outN D U m).card) :
    ∃ E : CH.Digraph, QFree E U 3 ∧ (∀ i, ∀ h ∈ gains i, E (v i) (v h) = true) ∧
      ∀ m ∈ U, t ≤ (outN E U m).card := by
  classical
  let H : CH.Digraph := fun m n => decide (D m n = true ∧ n ∉ liftRow v cuts m)
  have kept {m n} (hit : H m n = true) : D m n = true ∧ n ∉ liftRow v cuts m :=
    of_decide_eq_true hit
  have safe : QFree H U 3 := SignatureRestoration.free_sub free (fun _ _ hit => (kept hit).1)
  have row (m) : outN H U m = outN D U m \ liftRow v cuts m := by ext n; simp [H,mem_outN]; tauto
  let C (m : ℕ) := if ∃ i, v i = m then ∅ else (chargesOf gains D v m).map v
  have empty (i) : C (v i) = ∅ := ite_eq_left ⟨i,rfl⟩
  let A := liftRow v gains
  obtain ⟨ok,deg⟩ := patch_certificate (D:=H) (A:=A) (C:=C) safe
    (fun _ _ _ h => by
      obtain ⟨i,k,rfl,rfl,hk⟩ := from_label h
      obtain ⟨ki,old,rev,_⟩ := s1 i k hk
      refine ⟨inside k,fun eq => ki (v.injective eq),fun e => ?_,fun e => ?_⟩
      · exact Bool.noConfusion (old.symm.trans (internal i k (kept e).1))
      · rcases rev with bad | cut
        · exact Bool.noConfusion (bad.symm.trans (internal k i (kept e).1))
        · exact (kept e).2 (by simp [cut]))
    (fun _ _ _ h m _ hm mi => by
      obtain ⟨i,k,rfl,rfl,hk⟩ := from_label h
      by_cases tagged : ∃ l, v l = m
      · obtain ⟨l,rfl⟩ := tagged
        rcases s2 i k hk l (internal k l (kept hm).1) (internal l i (kept mi).1) with cut | cut
        · exact False.elim ((kept hm).2 (by simp [cut]))
        · exact False.elim ((kept mi).2 (by simp [cut]))
      · right
        have due : i ∈ chargesOf gains D v m :=
          mem_filter.mpr ⟨mem_univ _,(kept mi).1,k,hk,(kept hm).1⟩
        simp [C,tagged,due])
    (fun _ _ _ h _ next => by
      obtain ⟨i,k,rfl,rfl,hk⟩ := from_label h
      simp [A,(s1 i k hk).2.2.2] at next)
  refine ⟨_,ok,fun i k hk => by simp [patch,A,hk],?_⟩
  intro m mu
  rw [deg m mu,row]
  by_cases tagged : ∃ i, v i = m
  · obtain ⟨i,rfl⟩ := tagged
    simp only [empty,sdiff_empty,A,lift_at,card_map]
    have bound := card_le_card_sdiff_add_card (s:=outN D U (v i)) (t:=(cuts i).map v)
    rw [card_map] at bound
    have cost := s3 i
    by_cases short : i ∈ shortRows
    · rw [ite_eq_left short] at cost
      have h := need i short
      omega
    · rw [ite_eq_right short] at cost
      have h := spare i short
      omega
  · have off : ∀ i, m ≠ v i := fun i e => tagged ⟨i,e.symm⟩
    simp only [lift_off off,sdiff_empty,A,card_empty,Nat.add_zero,C,ite_eq_right tagged]
    have bound := card_le_card_sdiff_add_card (s:=outN D U m) (t:=(chargesOf gains D v m).map v)
    rw [card_map] at bound
    have budget := pay m mu off
    omega

#print axioms repair_of_shape
end LeanCH.BR.LabelledTrianglePatch

