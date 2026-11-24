module

public import LeanCH.CompromiseMultiplier
public import LeanCH.CompromiseApex
public import LeanCH.CompromiseFair

set_option linter.style.header false

/-! The fixed eight-vertex graph C4[T2]. Even a nonnegative, nonzero
head-average multiplier need not exist, although GK* has a witness. -/

open Finset CH.CompromiseSeven CH.CompromiseWeighted CH.CompromiseMultiplier
public section

namespace CH.CompromiseMultiplierObstruction

abbrev Vertex := Fin 4 × Bool

@[expose] def next (i : Fin 4) : Fin 4 := ⟨(i.val + 1) % 4, Nat.mod_lt _ (by decide)⟩
@[expose] def edge (v a : Vertex) : Prop :=
  a.1 = next v.1 ∨ (a.1 = v.1 ∧ v.2 = false ∧ a.2 = true)
instance : DecidableRel edge := fun v a => by unfold edge; infer_instance

@[expose] def outs (v : Vertex) : Finset Vertex := univ.filter (edge v ·)
@[expose] def ins (v : Vertex) : Finset Vertex := univ.filter (edge · v)
@[expose] def seconds (v : Vertex) : Finset Vertex :=
  univ.filter (fun a => a ≠ v ∧ ¬ edge v a ∧ ∃ b, edge v b ∧ edge b a)

theorem outs_eq (v : Vertex) : outs v = outN edge v := by ext; simp [outs]
theorem ins_eq (v : Vertex) : ins v = inN edge v := by ext; simp [ins]
theorem seconds_eq (v : Vertex) : seconds v = second edge v := by ext; simp [seconds]

theorem oriented_triangle_free :
    (∀ v, ¬ edge v v) ∧ (∀ v a, edge v a → ¬ edge a v) ∧
      (∀ v a b, edge v a → edge a b → ¬ edge b v) := by decide

theorem apex : ∀ v : Vertex, CH.CompromiseApex.IsApex edge v (next v.1, true) := by
  unfold CH.CompromiseApex.IsApex
  decide

theorem rows : ∀ i : Fin 4,
    outs (i, false) = {(i, true), (next i, false), (next i, true)} ∧
    outs (i, true) = {(next i, false), (next i, true)} := by decide

theorem counts : ∀ v : Vertex,
    (outs v).card = (if v.2 then 2 else 3) ∧
    (ins v).card = (if v.2 then 3 else 2) ∧ (seconds v).card = 2 := by decide

theorem weights (v : Vertex) :
    outWeight edge (fun _ => 1) v = (if v.2 then 2 else 3) ∧
    inWeight edge (fun _ => 1) v = (if v.2 then 3 else 2) ∧
    secondWeight edge (fun _ => 1) v = 2 := by
  obtain ⟨ho, hi, hs⟩ := counts v
  rw [outs_eq] at ho
  rw [ins_eq] at hi
  rw [seconds_eq] at hs
  simp only [outWeight, inWeight, secondWeight, mass, sum_const]
  rw [ho, hi, hs]
  cases v.2 <;> norm_num

theorem upper_geometric (i : Fin 4) :
    (outWeight edge (fun _ => 1) (i, true)) ^ 2 ≤
      inWeight edge (fun _ => 1) (i, true) * secondWeight edge (fun _ => 1) (i, true) := by
  obtain ⟨ho, hi, hs⟩ := weights (i, true)
  rw [ho, hi, hs]
  norm_num

theorem head_rows (f : Vertex → ℝ) (i : Fin 4) :
    headAverage edge (fun _ => 1) f (i, false) =
      f (i, true) + f (next i, false) + f (next i, true) ∧
    headAverage edge (fun _ => 1) f (i, true) =
      f (next i, false) + f (next i, true) := by
  have hn : next i ≠ i := by
    have h : ∀ j : Fin 4, next j ≠ j := by decide
    exact h i
  obtain ⟨hl, hu⟩ := rows i
  rw [outs_eq] at hl hu
  simp only [headAverage, hl, hu, one_mul]
  simp [Ne.symm hn, add_assoc]

theorem sum_next (f : Vertex → ℝ) (b : Bool) :
    (∑ i : Fin 4, f (next i, b)) = ∑ i : Fin 4, f (i, b) := by
  simp only [Fin.sum_univ_succ]
  norm_num [next]
  ring

/-- In fact the additive head-average certificate already forces f=0. -/
theorem additive_forces_zero (f : Vertex → ℝ) (hf : ∀ v, 0 ≤ f v)
    (cert : ∀ v, (2 * outWeight edge (fun _ => 1) v - secondWeight edge (fun _ => 1) v) *
      f v ≤ headAverage edge (fun _ => 1) f v) : ∀ v, f v = 0 := by
  have low (i : Fin 4) : 4 * f (i, false) ≤
      f (i, true) + f (next i, false) + f (next i, true) := by
    have h := cert (i, false)
    rw [(weights (i, false)).1, (weights (i, false)).2.2, (head_rows f i).1] at h
    norm_num at h
    exact h
  have high (i : Fin 4) : 2 * f (i, true) ≤ f (next i, false) + f (next i, true) := by
    have h := cert (i, true)
    rw [(weights (i, true)).1, (weights (i, true)).2.2, (head_rows f i).2] at h
    norm_num at h
    exact h
  have hl := sum_le_sum (s := (univ : Finset (Fin 4))) (fun i _ => low i)
  have hu := sum_le_sum (s := (univ : Finset (Fin 4))) (fun i _ => high i)
  simp only [sum_add_distrib, ← mul_sum, sum_next] at hl hu
  have hL : 0 ≤ ∑ i : Fin 4, f (i, false) := sum_nonneg fun i _ => hf (i, false)
  have hU : 0 ≤ ∑ i : Fin 4, f (i, true) := sum_nonneg fun i _ => hf (i, true)
  have hL0 : (∑ i : Fin 4, f (i, false)) = 0 := by linarith
  have hU0 : (∑ i : Fin 4, f (i, true)) = 0 := by linarith
  rintro ⟨i, b⟩
  cases b
  · have h := single_le_sum (fun j (_ : j ∈ (univ : Finset (Fin 4))) => hf (j, false)) (mem_univ i)
    linarith [hf (i, false)]
  · have h := single_le_sum (fun j (_ : j ∈ (univ : Finset (Fin 4))) => hf (j, true)) (mem_univ i)
    linarith [hf (i, true)]

theorem geometric_forces_zero (f : Vertex → ℝ) (hf : ∀ v, 0 ≤ f v)
    (cert : ∀ v, (outWeight edge (fun _ => 1) v) ^ 2 * f v ≤
      secondWeight edge (fun _ => 1) v * headAverage edge (fun _ => 1) f v) :
    ∀ v, f v = 0 := by
  apply additive_forces_zero f hf
  intro v
  have hc := cert v
  obtain ⟨ho, _, hs⟩ := weights v
  rw [ho, hs] at hc ⊢
  cases hb : v.2 <;> simp [hb] at hc ⊢ <;> nlinarith [hf v]

@[expose] def upperWeight (v : Vertex) : ℝ := if v.2 then 1 else 0
@[expose] def backwards (v : Vertex) : Finset Vertex :=
  univ.filter (fun a => a ≠ v ∧ ¬ edge a v ∧ ∃ b, edge a b ∧ edge b v)

theorem backwards_eq (v : Vertex) : backwards v = CH.CompromiseFair.secondIn edge v := by
  ext a
  simp [backwards]

theorem upper_fair : CH.CompromiseFair.Fair edge upperWeight := by
  refine ⟨?_, ⟨(0, true), by norm_num [upperWeight]⟩, ?_⟩
  · intro v
    simp [upperWeight]
    split <;> norm_num
  · intro u
    have hc : ∀ v : Vertex,
        2 * ((ins v).filter (fun a => a.2 = true)).card ≤
          ((outs v).filter (fun a => a.2 = true)).card +
            ((backwards v).filter (fun a => a.2 = true)).card := by decide
    have hr := hc u
    rw [outs_eq, ins_eq, backwards_eq] at hr
    simp only [mass, upperWeight, sum_boole]
    exact_mod_cast hr

theorem all_weights_compromise (w : Vertex → ℝ) (hw : ∀ v, 0 ≤ w v) :
    ∃ v, 0 < upperWeight v ∧
      2 * outWeight edge w v ≤ inWeight edge w v + secondWeight edge w v :=
  CH.CompromiseFair.compromise_of_fair edge upperWeight w upper_fair hw

end CH.CompromiseMultiplierObstruction

#print axioms CH.CompromiseMultiplierObstruction.oriented_triangle_free
#print axioms CH.CompromiseMultiplierObstruction.apex
#print axioms CH.CompromiseMultiplierObstruction.upper_geometric
#print axioms CH.CompromiseMultiplierObstruction.additive_forces_zero
#print axioms CH.CompromiseMultiplierObstruction.geometric_forces_zero
#print axioms CH.CompromiseMultiplierObstruction.upper_fair
#print axioms CH.CompromiseMultiplierObstruction.all_weights_compromise
