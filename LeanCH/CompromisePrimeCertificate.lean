module

public import LeanCH.CompromisePrimeExample

set_option linter.style.header false

/-! A module-closure certificate for the single graph in CompromisePrimeExample.
The finite certificate checks pairs in this one graph; it does not search graphs. -/

open Finset CH.CompromisePrimeExample
public section

namespace CH.CompromisePrimeCertificate

@[expose] def IsModule (M : Finset Vertex) : Prop :=
  ∀ x, x ∉ M → ∀ a ∈ M, ∀ b ∈ M,
    (edge x a ↔ edge x b) ∧ (edge a x ↔ edge b x)

@[expose] def distinguishes (x a b : Vertex) : Prop :=
  ¬ ((edge x a ↔ edge x b) ∧ (edge a x ↔ edge b x))

instance (x a b : Vertex) : Decidable (distinguishes x a b) := by
  unfold distinguishes
  infer_instance

@[expose] def extend (a : Vertex) (S : Finset Vertex) : Finset Vertex :=
  S ∪ univ.filter (fun x => ∃ b ∈ S, distinguishes x a b)

@[expose] def closure (a : Vertex) : ℕ → Finset Vertex → Finset Vertex
  | 0, S => S
  | n + 1, S => extend a (closure a n S)

theorem extend_subset (a : Vertex) (M S : Finset Vertex)
    (hm : IsModule M) (ha : a ∈ M) (hs : S ⊆ M) : extend a S ⊆ M := by
  intro x hx
  rcases mem_union.mp hx with hx | hx
  · exact hs hx
  · obtain ⟨b, hb, hdist⟩ := (mem_filter.mp hx).2
    by_contra hxm
    exact hdist (hm x hxm a ha b (hs hb))

theorem closure_subset (a : Vertex) (M S : Finset Vertex)
    (hm : IsModule M) (ha : a ∈ M) (hs : S ⊆ M) : ∀ n, closure a n S ⊆ M := by
  intro n
  induction n with
  | zero => exact hs
  | succ n ih => exact extend_subset a M (closure a n S) hm ha ih

@[expose] def shift (i j : Fin 4) : Vertex ≃ Vertex where
  toFun v := (v.1 + i, v.2.1 + j, v.2.2)
  invFun v := (v.1 - i, v.2.1 - j, v.2.2)
  left_inv := by intro v; ext <;> simp
  right_inv := by intro v; ext <;> simp

theorem shift_edge : ∀ i j : Fin 4, ∀ u v : Vertex,
    edge (shift i j u) (shift i j v) ↔ edge u v := by decide +kernel

@[expose] def origin (t : Bool) : Vertex := (0, 0, t)

theorem shift_origin : ∀ a : Vertex, shift (-a.1) (-a.2.1) a = origin a.2.2 := by
  decide +kernel

theorem image_module (i j : Fin 4) (M : Finset Vertex) (hm : IsModule M) :
    IsModule (M.image (shift i j)) := by
  intro x hx a ha b hb
  obtain ⟨a', ha', rfl⟩ := mem_image.mp ha
  obtain ⟨b', hb', rfl⟩ := mem_image.mp hb
  let x' := (shift i j).symm x
  have hx' : x' ∉ M := by
    intro hh
    have hh' := mem_image_of_mem (shift i j) hh
    apply hx
    simpa [x'] using hh'
  have h := hm x' hx' a' ha' b' hb'
  have he : x = shift i j x' := by simp [x']
  rw [he, shift_edge, shift_edge, shift_edge, shift_edge]
  exact h

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
-- Translations reduce the fixed-graph pair certificate to two starting vertices.
theorem origin_certificate : ∀ t : Bool, ∀ b : Vertex,
    origin t ≠ b → closure (origin t) 6 {origin t, b} = univ := by
  decide +kernel

theorem prime : ∀ M : Finset Vertex, IsModule M → M.card ≤ 1 ∨ M = univ := by
  intro M hm
  by_cases hsmall : M.card ≤ 1
  · exact Or.inl hsmall
  · obtain ⟨a, ha, b, hb, hne⟩ := one_lt_card.mp (show 1 < M.card by omega)
    let e := shift (-a.1) (-a.2.1)
    let M' := M.image e
    have hm' : IsModule M' := image_module _ _ M hm
    have hea : e a = origin a.2.2 := shift_origin a
    have ha' : origin a.2.2 ∈ M' := by rw [← hea]; exact mem_image_of_mem e ha
    have hb' : e b ∈ M' := mem_image_of_mem e hb
    have hne' : origin a.2.2 ≠ e b := by
      intro h
      apply hne
      exact e.injective (hea.trans h)
    have hs : ({origin a.2.2, e b} : Finset Vertex) ⊆ M' :=
      insert_subset ha' (singleton_subset_iff.mpr hb')
    have hc := closure_subset (origin a.2.2) M' {origin a.2.2, e b} hm' ha' hs 6
    rw [origin_certificate a.2.2 (e b) hne'] at hc
    apply Or.inr
    apply eq_univ_of_forall
    intro x
    have hx : e x ∈ M' := hc (mem_univ _)
    obtain ⟨y, hy, heq⟩ := mem_image.mp hx
    exact e.injective heq ▸ hy

end CH.CompromisePrimeCertificate

#print axioms CH.CompromisePrimeCertificate.prime
