module

public import LeanCH.CompromiseWeighted

set_option linter.style.header false

/-! Weighted compromise for the report's apex class, using a maximum potential. -/

open Finset CH.CompromiseSeven CH.CompromiseWeighted
public section

namespace CH.CompromiseApex

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (adj : V → V → Prop) [DecidableRel adj]

@[expose] def IsApex (v a : V) : Prop := adj v a ∧
  (∀ b, adj v b → ¬ adj a b) ∧ (∀ b, adj v b → b ≠ a → adj b a)

@[expose] def potential (w : V → ℝ) (v : V) : ℝ :=
  inWeight adj w v - outWeight adj w v + w v

theorem apex_out_capture (w : V → ℝ) (hw : ∀ v, 0 ≤ w v)
    (noDigon : ∀ u v, adj u v → ¬ adj v u)
    (v a : V) (h : IsApex adj v a) : outWeight adj w a ≤ secondWeight adj w v := by
  apply weight_mono w hw
  intro b hb
  have hab : adj a b := by simpa using hb
  refine (mem_second adj v b).mpr ⟨?_, ?_, a, h.1, hab⟩
  · intro he
    subst b
    exact noDigon v a h.1 hab
  · exact fun hvb => h.2.1 b hvb hab

omit [DecidableEq V] in
theorem apex_in_capture (w : V → ℝ) (hw : ∀ v, 0 ≤ w v)
    (noDigon : ∀ u v, adj u v → ¬ adj v u)
    (v a : V) (h : IsApex adj v a) :
    outWeight adj w v + w v ≤ inWeight adj w a + w a := by
  classical
  have hs : insert v ((outN adj v).erase a) ⊆ inN adj a := by
    intro b hb
    rcases mem_insert.mp hb with hb | hb
    · subst b
      simpa using h.1
    · simpa using h.2.2 b (by simpa using (mem_erase.mp hb).2) (mem_erase.mp hb).1
  have hvnot : v ∉ (outN adj v).erase a := by
    intro hh
    have hvv : adj v v := by simpa using (mem_erase.mp hh).2
    exact noDigon v v hvv hvv
  have hc := weight_mono w hw _ _ hs
  change (∑ b ∈ insert v ((outN adj v).erase a), w b) ≤ inWeight adj w a at hc
  rw [sum_insert hvnot] at hc
  have he := sum_erase_add (outN adj v) w (show a ∈ outN adj v by simpa using h.1)
  change (∑ b ∈ (outN adj v).erase a, w b) + w a = outWeight adj w v at he
  linarith

/-- At an apex vertex, the compromise surplus dominates the drop in potential. -/
theorem apex_potential_bound (w : V → ℝ) (hw : ∀ v, 0 ≤ w v)
    (noDigon : ∀ u v, adj u v → ¬ adj v u)
    (v a : V) (h : IsApex adj v a) :
    potential adj w v - potential adj w a ≤
      secondWeight adj w v + inWeight adj w v - 2 * outWeight adj w v := by
  have ho := apex_out_capture adj w hw noDigon v a h
  have hi := apex_in_capture adj w hw noDigon v a h
  dsimp [potential]
  linarith

theorem compromise_apex [Nonempty V] (w : V → ℝ) (hw : ∀ v, 0 ≤ w v)
    (noDigon : ∀ u v, adj u v → ¬ adj v u)
    (apex : ∀ v, (outN adj v).Nonempty → ∃ a, IsApex adj v a) :
    ∃ v, 2 * outWeight adj w v ≤ inWeight adj w v + secondWeight adj w v := by
  obtain ⟨v, _, hmax⟩ := exists_max_image univ (potential adj w) univ_nonempty
  refine ⟨v, ?_⟩
  by_cases hn : (outN adj v).Nonempty
  · obtain ⟨a, ha⟩ := apex v hn
    have hp := apex_potential_bound adj w hw noDigon v a ha
    have hm := hmax a (mem_univ _)
    linarith
  · have he := not_nonempty_iff_eq_empty.mp hn
    have ho : outWeight adj w v = 0 := by simp [outWeight, mass, he]
    have hi : 0 ≤ inWeight adj w v := weight_nonneg w hw _
    have hs : 0 ≤ secondWeight adj w v := weight_nonneg w hw _
    linarith

end CH.CompromiseApex

#print axioms CH.CompromiseApex.apex_potential_bound
#print axioms CH.CompromiseApex.compromise_apex
