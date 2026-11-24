module

public import LeanCH.CompromiseWeighted

set_option linter.style.header false

/-! Fair-weighting certificates and deletion of a dominated vertex. The
induced-graph certificate uses only paths whose middle vertex is retained. -/

open Finset CH.CompromiseSeven CH.CompromiseWeighted
public section

namespace CH.CompromiseFair

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (adj : V → V → Prop) [DecidableRel adj]

@[expose] def secondIn (u : V) : Finset V := second (fun a b => adj b a) u

@[simp] theorem mem_secondIn (u v : V) :
    v ∈ secondIn adj u ↔ v ≠ u ∧ ¬ adj v u ∧ ∃ a, adj v a ∧ adj a u := by
  simp only [secondIn, mem_second]
  constructor
  · rintro ⟨h1, h2, a, ha, hb⟩
    exact ⟨h1, h2, a, hb, ha⟩
  · rintro ⟨h1, h2, a, ha, hb⟩
    exact ⟨h1, h2, a, hb, ha⟩

@[expose] def restrictedSecondIn (S : Finset V) (u : V) : Finset V :=
  S.filter (fun v => v ≠ u ∧ ¬ adj v u ∧ ∃ a ∈ S, adj v a ∧ adj a u)

@[expose] def Fair (p : V → ℝ) : Prop :=
  (∀ v, 0 ≤ p v) ∧ (∃ v, 0 < p v) ∧
    ∀ u, 2 * mass p (inN adj u) ≤ mass p (outN adj u) + mass p (secondIn adj u)

@[expose] def FairOn (S : Finset V) (p : V → ℝ) : Prop :=
  (∀ v, 0 ≤ p v) ∧ (∀ v, v ∉ S → p v = 0) ∧ (∃ v ∈ S, 0 < p v) ∧
    ∀ u ∈ S, 2 * mass p (inN adj u ∩ S) ≤
      mass p (outN adj u ∩ S) + mass p (restrictedSecondIn adj S u)

omit [Fintype V] in
theorem mass_inter_support (p : V → ℝ) (S T : Finset V)
    (support : ∀ v, v ∉ S → p v = 0) : mass p (T ∩ S) = mass p T := by
  apply sum_subset inter_subset_left
  intro v hv hn
  exact support v (fun h => hn (mem_inter.mpr ⟨hv, h⟩))

theorem restrictedSecondIn_subset (S : Finset V) (u : V) :
    restrictedSecondIn adj S u ⊆ secondIn adj u := by
  intro v hv
  obtain ⟨_, hne, hnon, a, _, hva, hau⟩ := mem_filter.mp hv
  exact (mem_secondIn adj u v).mpr ⟨hne, hnon, a, hva, hau⟩

/-- Extending an induced fair weighting by zero preserves all retained rows. -/
theorem retained_row (S : Finset V) (p : V → ℝ) (h : FairOn adj S p)
    (u : V) (hu : u ∈ S) :
    2 * mass p (inN adj u) ≤ mass p (outN adj u) + mass p (secondIn adj u) := by
  have hr := h.2.2.2 u hu
  rw [mass_inter_support p S _ h.2.1, mass_inter_support p S _ h.2.1] at hr
  have hs := weight_mono p h.1 _ _ (restrictedSecondIn_subset adj S u)
  linarith

theorem extension_iff (S : Finset V) (p : V → ℝ) (h : FairOn adj S p) :
    Fair adj p ↔ ∀ u, u ∉ S →
      2 * mass p (inN adj u) ≤ mass p (outN adj u) + mass p (secondIn adj u) := by
  constructor
  · exact fun hh u _ => hh.2.2 u
  · intro outside
    refine ⟨h.1, ?_, ?_⟩
    · obtain ⟨v, _, hv⟩ := h.2.2.1
      exact ⟨v, hv⟩
    · intro u
      by_cases hu : u ∈ S
      · exact retained_row adj S p h u hu
      · exact outside u hu

/-- The deleted row is dominated by the retained row at u. Equality of the
incoming sets is literal, including removal of x. No triangle hypothesis is used. -/
theorem domination_extension (x u : V) (hne : u ≠ x) (p : V → ℝ)
    (incoming : ∀ a, adj a x ↔ a ≠ x ∧ adj a u)
    (outgoing : ∀ a, a ≠ x → adj u a → adj x a)
    (h : FairOn adj (univ.erase x) p) : Fair adj p := by
  apply (extension_iff adj _ p h).mpr
  intro z hz
  have hzx : z = x := by simpa using hz
  subst z
  have hu : u ∈ univ.erase x := by simp [hne]
  have hin : inN adj u ∩ univ.erase x = inN adj x := by
    ext a
    simp only [mem_inter, mem_inN, mem_erase, mem_univ, and_true]
    exact (and_comm.trans (incoming a).symm)
  have hout : outN adj u ∩ univ.erase x ⊆ outN adj x := by
    intro a ha
    exact (mem_outN adj x a).mpr
      (outgoing a (mem_erase.mp (mem_inter.mp ha).2).1
        (by simpa using (mem_inter.mp ha).1))
  have hsecond : restrictedSecondIn adj (univ.erase x) u ⊆ secondIn adj x := by
    intro v hv
    obtain ⟨hvS, _, hnon, a, haS, hva, hau⟩ := mem_filter.mp hv
    have hvx : v ≠ x := (mem_erase.mp hvS).1
    have hax : a ≠ x := (mem_erase.mp haS).1
    refine (mem_secondIn adj x v).mpr ⟨hvx, ?_, a, hva, ?_⟩
    · exact fun hhit => hnon ((incoming v).mp hhit).2
    · exact (incoming a).mpr ⟨hax, hau⟩
  have hr := h.2.2.2 u hu
  rw [hin] at hr
  have ho := weight_mono p h.1 _ _ hout
  have hs := weight_mono p h.1 _ _ hsecond
  linarith

theorem second_double_count (p w : V → ℝ) :
    ∑ v, p v * secondWeight adj w v = ∑ u, w u * mass p (secondIn adj u) := by
  let rel (v u : V) : Prop := u ∈ second adj v
  have ho (v : V) : outN rel v = second adj v := by ext; simp [rel]
  have hi (u : V) : inN rel u = secondIn adj u := by
    ext v
    simp only [mem_inN, rel, mem_second, mem_secondIn]
    exact and_congr_left fun _ => ne_comm
  have hc := weighted_double_count rel p w
  simpa only [ho, hi, secondWeight, mass] using hc

/-- Soundness of the dual certificate. The witness belongs to the positive
support of p, which is useful after deletion or extension. -/
theorem compromise_of_fair (p w : V → ℝ) (hp : Fair adj p) (hw : ∀ v, 0 ≤ w v) :
    ∃ v, 0 < p v ∧ 2 * outWeight adj w v ≤ inWeight adj w v + secondWeight adj w v := by
  have ho := weighted_double_count adj p w
  have hi := weighted_double_count adj w p
  have hs := second_double_count adj p w
  change (∑ v, p v * outWeight adj w v) = ∑ u, w u * mass p (inN adj u) at ho
  change (∑ u, w u * mass p (outN adj u)) = ∑ v, p v * inWeight adj w v at hi
  have hr := sum_le_sum (s := (univ : Finset V)) (fun u _ =>
    mul_le_mul_of_nonneg_left (hp.2.2 u) (hw u))
  have total : 2 * (∑ v, p v * outWeight adj w v) ≤
      (∑ v, p v * inWeight adj w v) + ∑ v, p v * secondWeight adj w v := by
    simp_rw [mul_add] at hr
    rw [sum_add_distrib, hi, ← hs] at hr
    have hl : (∑ u, w u * (2 * mass p (inN adj u))) =
        2 * (∑ u, w u * mass p (inN adj u)) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro u _
      ring
    rw [hl, ← ho] at hr
    exact hr
  by_contra hn
  have weak (v : V) : p v * (inWeight adj w v + secondWeight adj w v) ≤
      p v * (2 * outWeight adj w v) := by
    by_cases hv : 0 < p v
    · have hb : inWeight adj w v + secondWeight adj w v < 2 * outWeight adj w v := by
        have hh : ¬ 2 * outWeight adj w v ≤ inWeight adj w v + secondWeight adj w v :=
          fun h => hn ⟨v, hv, h⟩
        linarith
      exact mul_le_mul_of_nonneg_left hb.le (hp.1 v)
    · have hz : p v = 0 := by linarith [hp.1 v]
      simp [hz]
  obtain ⟨v, hv⟩ := hp.2.1
  have hb : inWeight adj w v + secondWeight adj w v < 2 * outWeight adj w v := by
    have hh : ¬ 2 * outWeight adj w v ≤ inWeight adj w v + secondWeight adj w v :=
      fun h => hn ⟨v, hv, h⟩
    linarith
  have strict := sum_lt_sum (fun u (_ : u ∈ (univ : Finset V)) => weak u)
    ⟨v, mem_univ _, mul_lt_mul_of_pos_left hb hv⟩
  simp_rw [mul_add] at strict
  rw [sum_add_distrib] at strict
  have he : (∑ u, p u * (2 * outWeight adj w u)) =
      2 * (∑ u, p u * outWeight adj w u) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro u _
    ring
  rw [he] at strict
  linarith

end CH.CompromiseFair

#print axioms CH.CompromiseFair.extension_iff
#print axioms CH.CompromiseFair.domination_extension
#print axioms CH.CompromiseFair.compromise_of_fair
