import checkpoints.shen_extension.RecipientBalance
import Mathlib.Dynamics.PeriodicPts.Lemmas

namespace LeanCH.BR.Closure.CycleSlotOrbit
open Function

theorem recurrent {α : Type*} [Finite α] (go : α → α) (seed : α) :
    ∃ t, go^[t] seed ∈ periodicPts go := by
  classical
  obtain ⟨i,j,eq,ne⟩ : ∃ i j, go^[i] seed = go^[j] seed ∧ i≠j := by
    simpa [Injective] using not_injective_infinite_finite (go^[·] seed)
  have loop {a b : ℕ} (lt : a<b) (same : go^[a] seed = go^[b] seed) :
      go^[a] seed ∈ periodicPts go := by
    refine mk_mem_periodicPts (n:=b-a) (by omega) ?_
    change go^[b-a] (go^[a] seed) = _
    rw [← iterate_add_apply,show b-a+a=b by omega,same]
  rcases lt_or_gt_of_ne ne with lt|lt
  · exact ⟨i,loop lt eq⟩
  · exact ⟨j,loop lt eq.symm⟩

/-- The states on which the chosen transition recurs have a genuine inverse. -/
noncomputable def base {α : Type*} (go : α → α) : Equiv.Perm (periodicPts go) :=
  Set.BijOn.equiv go (bijOn_periodicPts go)

abbrev Slot {α : Type*} (go : α → α) (bag : α → Finset ℕ) :=
  (a : periodicPts go) × ↥(bag a.val)

/-- Actual labelled occurrences, with separate copies of a label at different
states. Bijections between consecutive fibers lift to a permutation. -/
noncomputable def lift {α : Type*} (go : α → α) (bag : α → Finset ℕ)
    (send : ∀ a, ↥(bag a) ≃ ↥(bag (go a))) : Equiv.Perm (Slot go bag) :=
  Equiv.sigmaCongr (base go) (fun a => send a.val)

theorem next_label {α : Type*} {go : α → α} {bag : α → Finset ℕ}
    (send : ∀ a, ↥(bag a) ≃ ↥(bag (go a))) (s : Slot go bag) :
    ((lift go bag send s).2 : ℕ) = (send s.1.val s.2 : ℕ) := rfl

/-- A losing edge in any marked row forces an opposite switch on that very
slot orbit, before its first return. The row predicate stays fixed. -/
theorem switch {α : Type*} [Finite α] (step : Equiv.Perm α) (sees : α → Bool) {s : α}
    (before : sees s = true) (afterStep : sees (step s) = false) :
    ∃ k, 0<k ∧ k<minimalPeriod step s ∧ sees (step^[k] s)=false ∧
      sees (step^[k+1] s)=true := by
  classical
  let len := minimalPeriod step s
  have pos : 0<len := minimalPeriod_pos_of_mem_periodicPts (step.injective.mem_periodicPts s)
  have close : step^[len] s=s := isPeriodicPt_minimalPeriod step s
  let Seen (i : ℕ) := sees (step^[i+1] s)=true
  have last : Seen (len-1) := by
    unfold Seen
    rw [show len-1+1=len by omega,close,before]
  have found : ∃i,Seen i := ⟨_,last⟩
  let k := Nat.find found
  have hit : Seen k := Nat.find_spec found
  have bound : k ≤ len-1 := Nat.find_min' found last
  have nonzero : k ≠ 0 := by
    intro h
    change sees (step^[k+1] s)=true at hit
    simp [h,afterStep] at hit
  have prev := Nat.find_min found (show k-1<k by omega)
  change ¬sees (step^[k-1+1] s)=true at prev
  rw [show k-1+1=k by omega] at prev
  exact ⟨k,by omega,by change k<len; omega,Bool.eq_false_iff.mpr prev,hit⟩

#print axioms recurrent
#print axioms lift
#print axioms switch
end LeanCH.BR.Closure.CycleSlotOrbit
