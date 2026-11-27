import checkpoints.shen_extension.BankKernelSAT
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.NormNum

namespace LeanCH.BR.TripleBank.CleanSwap

abbrev Slot := Fin 9

def bankSlot (b : Fin 3) : Slot := ⟨b.val, by omega⟩
def outerSlot (u : Fin 6) : Slot := ⟨u.val + 3, by omega⟩

def reachable (R : Slot → Slot → Bool) (u : Fin 6) : Prop :=
  u = 0 ∨ R (outerSlot u) (outerSlot 0) = true ∨
    ∃ v : Fin 6, R (outerSlot u) (outerSlot v) = true ∧ R (outerSlot v) (outerSlot 0) = true

def outside (u : Fin 6) (b : Fin 3) (y : Slot) : Prop :=
  y ≠ outerSlot u ∧ (∀ j : Fin 3, y = bankSlot j → j = b)

def clean (R : Slot → Slot → Bool) (u : Fin 6) (b : Fin 3) : Prop :=
  ∀ y : Slot, outside u b y →
    (∀ i j : Fin 3, i < j → i ≠ b → j ≠ b →
      R y (bankSlot i) = true → R y (bankSlot j) = false) ∧
    (∀ i : Fin 3, i ≠ b → R y (outerSlot u) = true → R y (bankSlot i) = false)

set_option maxHeartbeats 80000000 in
set_option maxRecDepth 200000 in
/-- There are three old bank labels and at most six outside rows with a
bank head. Unused outside slots are represented by empty rows. -/
theorem nine_slots (R : Slot → Slot → Bool)
    (loops : ∀ i, R i i = false)
    (digons : ∀ i j, i < j → R i j = true → R j i = false)
    (triangles : ∀ i j k, i < j → i < k → j ≠ k →
      R i j = true → R j k = true → R k i = false)
    (incoming : ∀ b : Fin 3, ∀ i j k : Slot, i < j → j < k →
      R i (bankSlot b) = true → R j (bankSlot b) = true → R k (bankSlot b) = false)
    (colors : ∀ u : Fin 6, ∀ i j : Fin 3, i < j →
      R (outerSlot u) (bankSlot i) = true → R (outerSlot u) (bankSlot j) = false)
    (root : ∃ j : Fin 3, R (outerSlot 0) (bankSlot j) = true)
    (noRoot : ∀ j : Fin 3, R (bankSlot j) (outerSlot 0) = false) :
    ∃ u : Fin 6, (∃ j : Fin 3, R (outerSlot u) (bankSlot j) = true) ∧
      reachable R u ∧ ∃ b : Fin 3, clean R u b := by
  simp only [reachable, clean, outside, Fin.forall_fin_succ, Fin.exists_fin_succ,
    Fin.forall_fin_zero, Fin.exists_fin_zero] at *
  norm_num [bankSlot, outerSlot, Fin.lt_def, Fin.ext_iff, Fin.succ] at *
  simp only [Bool.eq_false_iff, ne_eq] at *
  by_contra missing
  bank_kernel_sat

#print axioms nine_slots

end LeanCH.BR.TripleBank.CleanSwap
