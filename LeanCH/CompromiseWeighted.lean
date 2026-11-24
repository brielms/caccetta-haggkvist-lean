module

public import LeanCH.CompromiseSeven

set_option linter.style.header false

/-!
Weighted geometric compromise by reciprocal-degree double counting.
The graph conclusions below are unconditional for independent out-neighbourhoods.
Neither a stationary distribution nor CH/Seymour hypotheses are used.
-/

open Finset CH.CompromiseSeven
public section

namespace CH.CompromiseWeighted

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (adj : V → V → Prop) [DecidableRel adj]

@[expose] def mass (w : V → ℝ) (S : Finset V) : ℝ := ∑ v ∈ S, w v
@[expose] def outWeight (w : V → ℝ) (v : V) : ℝ := mass w (outN adj v)
@[expose] def inWeight (w : V → ℝ) (v : V) : ℝ := mass w (inN adj v)
@[expose] def secondWeight (w : V → ℝ) (v : V) : ℝ := mass w (second adj v)
@[expose] noncomputable def reciprocalHeads (w : V → ℝ) (v : V) : ℝ :=
  ∑ a ∈ outN adj v, w a / outWeight adj w a

omit [DecidableEq V] in
theorem weighted_double_count (f g : V → ℝ) :
    ∑ v, f v * (∑ a ∈ outN adj v, g a) =
      ∑ a, g a * (∑ v ∈ inN adj a, f v) := by
  have ho (v : V) : outN adj v = univ.filter (adj v ·) := by ext; simp
  have hi (a : V) : inN adj a = univ.filter (adj · a) := by ext; simp
  calc
    _ = ∑ v, ∑ a, if adj v a then f v * g a else 0 := by
      simp_rw [ho, sum_filter, mul_sum, mul_ite, mul_zero]
    _ = ∑ a, ∑ v, if adj v a then f v * g a else 0 := sum_comm
    _ = _ := by
      simp_rw [hi, sum_filter, mul_sum, mul_ite, mul_zero]
      congr 1
      funext a
      apply sum_congr rfl
      intro v _
      split_ifs <;> ring

omit [DecidableEq V] in
theorem reciprocal_balance (w : V → ℝ) :
    ∑ v, w v * reciprocalHeads adj w v =
      ∑ v, w v * (inWeight adj w v / outWeight adj w v) := by
  have h := weighted_double_count adj w (fun v => w v / outWeight adj w v)
  change (∑ v, w v * reciprocalHeads adj w v) =
    ∑ v, (w v / outWeight adj w v) * inWeight adj w v at h
  rw [h]
  apply sum_congr rfl
  intro v _
  ring

omit [Fintype V] [DecidableEq V] in
theorem weight_nonneg (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) (S : Finset V) :
    0 ≤ mass w S := sum_nonneg (fun v _ => hw v)

omit [Fintype V] [DecidableEq V] in
theorem weight_mono (w : V → ℝ) (hw : ∀ v, 0 ≤ w v)
    (S T : Finset V) (hst : S ⊆ T) : mass w S ≤ mass w T :=
  sum_le_sum_of_subset_of_nonneg hst (fun v _ _ => hw v)

omit [DecidableEq V] in
/-- The local reciprocal condition suffices for geometric compromise.
It is a sufficient condition, not an assertion about arbitrary second neighbourhoods. -/
theorem geometric_of_harmonic [Nonempty V] (w s : V → ℝ)
    (hw : ∀ v, 0 ≤ w v) (hs : ∀ v, 0 ≤ s v)
    (hc : ∀ v, 0 < outWeight adj w v →
      outWeight adj w v ≤ s v * reciprocalHeads adj w v) :
    ∃ v, (outWeight adj w v) ^ 2 ≤ inWeight adj w v * s v := by
  by_contra hn
  have bad (v : V) : inWeight adj w v * s v < (outWeight adj w v) ^ 2 := by
    have hh : ¬ (outWeight adj w v) ^ 2 ≤ inWeight adj w v * s v := fun h => hn ⟨v, h⟩
    linarith
  have outpos (v : V) : 0 < outWeight adj w v := by
    have ho : 0 ≤ outWeight adj w v := weight_nonneg w hw _
    have hi : 0 ≤ inWeight adj w v := weight_nonneg w hw _
    have hb := bad v
    have hp := mul_nonneg hi (hs v)
    nlinarith
  have strict (v : V) : inWeight adj w v / outWeight adj w v < reciprocalHeads adj w v := by
    apply (div_lt_iff₀ (outpos v)).mpr
    by_contra hnlt
    have hrev : reciprocalHeads adj w v * outWeight adj w v ≤ inWeight adj w v := by
      linarith
    have h1 := mul_le_mul_of_nonneg_left (hc v (outpos v)) (le_of_lt (outpos v))
    have h2 := mul_le_mul_of_nonneg_left hrev (hs v)
    have hb := bad v
    nlinarith
  have hpos : ∃ v, 0 < w v := by
    by_contra h
    push Not at h
    have hz (v : V) : w v = 0 := le_antisymm (h v) (hw v)
    have hh := outpos (Classical.arbitrary V)
    simp [outWeight, mass, hz] at hh
  obtain ⟨v, hv⟩ := hpos
  have hsum : (∑ v, w v * (inWeight adj w v / outWeight adj w v)) <
      ∑ v, w v * reciprocalHeads adj w v := by
    apply sum_lt_sum
    · intro a _
      exact mul_le_mul_of_nonneg_left (le_of_lt (strict a)) (hw a)
    · exact ⟨v, mem_univ _, mul_lt_mul_of_pos_left (strict v) hv⟩
  have heq := reciprocal_balance adj w
  linarith

omit [DecidableEq V] in
/-- Capturing each head's full out-neighbourhood implies the reciprocal condition. -/
theorem harmonic_of_capture (w s : V → ℝ) (hw : ∀ v, 0 ≤ w v)
    (outpos : ∀ v, 0 < outWeight adj w v)
    (capture : ∀ v a, adj v a → outWeight adj w a ≤ s v) (v : V) :
    outWeight adj w v ≤ s v * reciprocalHeads adj w v := by
  have sp : 0 < s v := by
    have hn : (outN adj v).Nonempty := by
      by_contra h
      have he : outN adj v = ∅ := not_nonempty_iff_eq_empty.mp h
      have hp := outpos v
      simp [outWeight, mass, he] at hp
    obtain ⟨a, ha⟩ := hn
    exact (outpos a).trans_le (capture v a (by simpa using ha))
  have hterm (a : V) (ha : a ∈ outN adj v) : w a / s v ≤ w a / outWeight adj w a :=
    div_le_div_of_nonneg_left (hw a) (outpos a) (capture v a (by simpa using ha))
  have hsum := sum_le_sum hterm
  rw [← sum_div] at hsum
  change outWeight adj w v / s v ≤ reciprocalHeads adj w v at hsum
  have hh := (div_le_iff₀ sp).mp hsum
  nlinarith

omit [DecidableEq V] in
theorem geometric_of_capture [Nonempty V] (w s : V → ℝ)
    (hw : ∀ v, 0 ≤ w v) (hs : ∀ v, 0 ≤ s v)
    (capture : ∀ v a, adj v a → outWeight adj w a ≤ s v) :
    ∃ v, (outWeight adj w v) ^ 2 ≤ inWeight adj w v * s v := by
  by_cases hz : ∃ v, outWeight adj w v = 0
  · obtain ⟨v, hv⟩ := hz
    refine ⟨v, ?_⟩
    rw [hv, zero_pow (by omega)]
    exact mul_nonneg (weight_nonneg w hw _) (hs v)
  have outpos (v : V) : 0 < outWeight adj w v := by
    have hne : outWeight adj w v ≠ 0 := fun h => hz ⟨v, h⟩
    have := weight_nonneg w hw (outN adj v)
    change 0 ≤ outWeight adj w v at this
    positivity
  exact geometric_of_harmonic adj w s hw hs
    (fun v _ => harmonic_of_capture adj w s hw outpos capture v)

omit [DecidableEq V] in
/-- An elementary weighted arc inequality; no connectivity assumption is needed. -/
theorem arc_geometric [Nonempty V] (w : V → ℝ) (hw : ∀ v, 0 ≤ w v)
    (outpos : ∀ v, 0 < outWeight adj w v) :
    ∃ v a, adj v a ∧ (outWeight adj w v) ^ 2 ≤ inWeight adj w v * outWeight adj w a := by
  have hn (v : V) : (outN adj v).Nonempty := by
    by_contra h
    have he : outN adj v = ∅ := not_nonempty_iff_eq_empty.mp h
    have hp := outpos v
    simp [outWeight, mass, he] at hp
  have hm (v : V) : ∃ a ∈ outN adj v,
      ∀ b ∈ outN adj v, outWeight adj w b ≤ outWeight adj w a :=
    exists_max_image (outN adj v) (outWeight adj w) (hn v)
  choose a ha hmax using hm
  obtain ⟨v, hv⟩ := geometric_of_capture adj w (fun v => outWeight adj w (a v)) hw
    (fun v => (outpos (a v)).le) (fun v b hvb => hmax v b (by simpa using hvb))
  exact ⟨v, a v, by simpa using ha v, hv⟩

/-- Independent out-neighbourhoods may coexist with directed triangles. -/
theorem geometric_independent [Nonempty V] (w : V → ℝ) (hw : ∀ v, 0 ≤ w v)
    (noDigon : ∀ u v, adj u v → ¬ adj v u)
    (independent : ∀ v a b, adj v a → adj v b → ¬ adj a b) :
    ∃ v, (outWeight adj w v) ^ 2 ≤ inWeight adj w v * secondWeight adj w v := by
  apply geometric_of_capture adj w (secondWeight adj w) hw (fun v => weight_nonneg w hw _)
  intro v a hva
  apply weight_mono w hw
  intro b hb
  have hab : adj a b := by simpa using hb
  refine (mem_second adj v b).mpr ⟨?_, ?_, a, hva, hab⟩
  · intro h
    subst b
    exact noDigon v a hva hab
  · exact fun hvb => independent v a b hva hvb hab

theorem compromise_independent [Nonempty V] (w : V → ℝ) (hw : ∀ v, 0 ≤ w v)
    (noDigon : ∀ u v, adj u v → ¬ adj v u)
    (independent : ∀ v a b, adj v a → adj v b → ¬ adj a b) :
    ∃ v, 2 * outWeight adj w v ≤ inWeight adj w v + secondWeight adj w v := by
  obtain ⟨v, hv⟩ := geometric_independent adj w hw noDigon independent
  refine ⟨v, ?_⟩
  have hi : 0 ≤ inWeight adj w v := weight_nonneg w hw _
  have hs : 0 ≤ secondWeight adj w v := weight_nonneg w hw _
  have ho : 0 ≤ outWeight adj w v := weight_nonneg w hw _
  nlinarith [sq_nonneg (inWeight adj w v - secondWeight adj w v)]

/-- In particular, the weighted directed-four-cycle-homomorphic case is settled. -/
theorem geometric_four_cycle [Nonempty V] (w : V → ℝ) (hw : ∀ v, 0 ≤ w v)
    (color : V → Fin 4)
    (step : ∀ u v, adj u v → (color v).val = ((color u).val + 1) % 4) :
    ∃ v, (outWeight adj w v) ^ 2 ≤ inWeight adj w v * secondWeight adj w v := by
  apply geometric_independent adj w hw
  · intro u v huv hvu
    have h1 := step u v huv
    have h2 := step v u hvu
    have hu := (color u).isLt
    have hv := (color v).isLt
    omega
  · intro v a b hva hvb hab
    have h1 := step v a hva
    have h2 := step v b hvb
    have h3 := step a b hab
    have hv := (color v).isLt
    have ha := (color a).isLt
    have hb := (color b).isLt
    omega

end CH.CompromiseWeighted

#print axioms CH.CompromiseWeighted.reciprocal_balance
#print axioms CH.CompromiseWeighted.geometric_of_harmonic
#print axioms CH.CompromiseWeighted.geometric_independent
#print axioms CH.CompromiseWeighted.compromise_independent
#print axioms CH.CompromiseWeighted.arc_geometric
#print axioms CH.CompromiseWeighted.geometric_four_cycle
