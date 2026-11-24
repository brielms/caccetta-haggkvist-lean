module

public import LeanCH.CompromiseFair
public import LeanCH.CompromiseApex

set_option linter.style.header false

/-! The report's seven-vertex mixed graph, with weight two at t and one
elsewhere. Its proposed funnel scaling has no nonzero nonnegative solution,
although every designated cycle visits the independent branch vertex x. -/

open Finset CH.CompromiseSeven CH.CompromiseWeighted
public section

namespace CH.CompromiseFunnelExample

-- 0=x, 1=t, 2=b, 3=a, 4=q, 5=q', 6=y.
abbrev Vertex := Fin 7
@[expose] def edge (v a : Vertex) : Prop :=
  (v = 0 ∧ (a = 1 ∨ a = 4)) ∨ (v = 1 ∧ (a = 2 ∨ a = 3)) ∨
  (v = 2 ∧ a = 3) ∨ (v = 3 ∧ a = 6) ∨ (v = 4 ∧ a = 5) ∨
  (v = 5 ∧ a = 6) ∨ (v = 6 ∧ a = 0)
instance : DecidableRel edge := fun v a => by unfold edge; infer_instance

@[expose] def designated (v a : Vertex) : Prop := edge v a ∧ ¬ (v = 1 ∧ a = 2)
instance : DecidableRel designated := fun v a => by unfold designated; infer_instance
@[expose] def weight (v : Vertex) : ℕ := if v = 1 then 2 else 1
@[expose] def outs (v : Vertex) : Finset Vertex := univ.filter (edge v ·)
@[expose] def ins (v : Vertex) : Finset Vertex := univ.filter (edge · v)
@[expose] def backwards (v : Vertex) : Finset Vertex :=
  univ.filter (fun a => a ≠ v ∧ ¬ edge a v ∧ ∃ b, edge a b ∧ edge b v)

theorem oriented_triangle_free :
    (∀ v, ¬ edge v v) ∧ (∀ v a, edge v a → ¬ edge a v) ∧
      (∀ v a b, edge v a → edge a b → ¬ edge b v) := by decide

theorem independent_elsewhere : ∀ v : Vertex, v ≠ 1 →
    ∀ a b, edge v a → edge v b → ¬ edge a b := by decide

theorem apex_at_t : CH.CompromiseApex.IsApex edge 1 3 := by
  unfold CH.CompromiseApex.IsApex
  decide

@[expose] def rank (v : Vertex) : ℕ :=
  if v = 0 then 4 else if v = 6 then 3 else if v = 3 ∨ v = 5 then 2 else 0

theorem rank_increases : ∀ v a : Vertex, v ≠ 0 → designated v a → rank v < rank a := by decide

/-- In particular every directed cycle contains x, an independent-type vertex.
This stronger set statement avoids any dependence on a cycle representation. -/
theorem every_closed_set_contains_x (S : Finset Vertex) (hn : S.Nonempty)
    (closed : ∀ v ∈ S, ∃ a ∈ S, designated v a) : 0 ∈ S := by
  obtain ⟨v, hv, hmax⟩ := exists_max_image S rank hn
  by_contra h
  have hv0 : v ≠ 0 := fun he => h (he ▸ hv)
  obtain ⟨a, ha, hva⟩ := closed v hv
  have hr := rank_increases v a hv0 hva
  have hm := hmax a ha
  omega

@[expose] def outMass (v : Vertex) : ℕ := ∑ a ∈ outs v, weight a
@[expose] def inMass (v : Vertex) : ℕ := ∑ a ∈ ins v, weight a

/-- The coefficient of t(v) in the incoming funnel flow at a, exactly as in
Section 12.4: the t-row sends its whole out-mass to its apex. -/
@[expose] def funnelCoeff (v a : Vertex) : ℕ :=
  if designated v a then
    if v = 1 then weight v * outMass v else weight v * weight a
  else 0
@[expose] def capacity (a : Vertex) : ℕ := weight a * inMass a

theorem no_nonzero_scaling (t : Vertex → ℝ) (ht : ∀ v, 0 ≤ t v)
    (scaling : ∀ a, (∑ v, (funnelCoeff v a : ℝ) * t v) ≤ (capacity a : ℝ) * t a) :
    ∀ v, t v = 0 := by
  have h0 := scaling 0
  have h1 := scaling 1
  have h3 := scaling 3
  have h4 := scaling 4
  have h5 := scaling 5
  have h6 := scaling 6
  norm_num [sum_filter, Fin.sum_univ_succ, funnelCoeff, capacity, designated, edge, weight,
    outMass, inMass, outs, ins] at h0 h1 h3 h4 h5 h6
  have z0 : t 0 = 0 := by linarith [ht 0, ht 2]
  have z6 : t 6 = 0 := by linarith [ht 6]
  have z3 : t 3 = 0 := by linarith [ht 3, ht 5]
  have z5 : t 5 = 0 := by linarith [ht 3, ht 5]
  have z4 : t 4 = 0 := by linarith [ht 4]
  have z1 : t 1 = 0 := by linarith [ht 1, ht 2]
  have z2 : t 2 = 0 := by linarith [ht 1, ht 2]
  intro v
  fin_cases v <;> assumption

@[expose] def certificate (v : Vertex) : ℕ :=
  if v = 2 then 0 else if v = 5 then 1 else if v = 6 then 3 else 2
@[expose] def certMass (S : Finset Vertex) : ℕ := ∑ a ∈ S, certificate a
@[expose] def fairWeight (v : Vertex) : ℝ := certificate v

theorem fair_counts : ∀ v : Vertex,
    2 * certMass (ins v) ≤ certMass (outs v) + certMass (backwards v) := by decide

theorem mass_cast (S : Finset Vertex) : mass fairWeight S = (certMass S : ℝ) := by
  simp [mass, certMass, fairWeight]

theorem fair_certificate : CH.CompromiseFair.Fair edge fairWeight := by
  refine ⟨fun v => by simp [fairWeight], ⟨0, by norm_num [fairWeight, certificate]⟩, ?_⟩
  intro v
  have ho : outs v = outN edge v := by ext; simp [outs]
  have hi : ins v = inN edge v := by ext; simp [ins]
  have hs : backwards v = CH.CompromiseFair.secondIn edge v := by ext; simp [backwards]
  rw [← ho, ← hi, ← hs, mass_cast, mass_cast, mass_cast]
  exact_mod_cast fair_counts v

theorem all_weights_compromise (w : Vertex → ℝ) (hw : ∀ v, 0 ≤ w v) :
    ∃ v, 0 < fairWeight v ∧ 2 * outWeight edge w v ≤
      inWeight edge w v + secondWeight edge w v :=
  CH.CompromiseFair.compromise_of_fair edge fairWeight w fair_certificate hw

end CH.CompromiseFunnelExample

#print axioms CH.CompromiseFunnelExample.oriented_triangle_free
#print axioms CH.CompromiseFunnelExample.independent_elsewhere
#print axioms CH.CompromiseFunnelExample.apex_at_t
#print axioms CH.CompromiseFunnelExample.every_closed_set_contains_x
#print axioms CH.CompromiseFunnelExample.no_nonzero_scaling
#print axioms CH.CompromiseFunnelExample.fair_certificate
#print axioms CH.CompromiseFunnelExample.all_weights_compromise
