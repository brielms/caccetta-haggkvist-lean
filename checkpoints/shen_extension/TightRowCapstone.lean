import checkpoints.shen_extension.TightRowLink

/-!
# Integration: the tight-row statement in the capstone's literal shape

Lean 4.35.0. `TightRowLink.tightLaw_implies_CH` excludes a `q`-free digraph on exactly `q*s` vertices with minimum
outdegree `s`. The capstone's input is `n ≤ q*s`. This file closes that gap by source padding: add a new vertex
with `s` heads among the old vertices and no parents; nothing can return to it, so `q`-freeness and the degree
bound survive, and the order grows by one.

`capstone_of_tightLaw`: under the supplied hypothesis `TightLaw q (s-1)`, every loopless digraph on `n ≤ q*s`
vertices with minimum outdegree `s` has a directed cycle of length at most `q` — the literal capstone statement
at `(q, s)`. `TightLaw` is conjectural; this is a compiled conditional rule.
-/

set_option linter.style.longLine false

namespace LeanCH.BR.TightRow

open LeanCH.BR.BRq2 LeanCH.BR.BRq3

/-- `D` on the old vertices, plus a new source `z` pointing to `S`. -/
def pad (D : CH.Digraph) (z : ℕ) (S : Finset ℕ) : CH.Digraph :=
  fun a b => (decide (a ≠ z) && decide (b ≠ z) && D a b) || (decide (a = z) && decide (b ∈ S))

theorem pad_cases {D : CH.Digraph} {z a b : ℕ} {S : Finset ℕ} (h : pad D z S a b = true) :
    (a ≠ z ∧ b ≠ z ∧ D a b = true) ∨ (a = z ∧ b ∈ S) := by
  simp only [pad, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨⟨h1, h2⟩, h3⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨h1, h2, h3⟩
  · exact Or.inr ⟨h1, h2⟩

theorem pad_walk {D : CH.Digraph} {V S : Finset ℕ} {z a b m : ℕ}
    (w : Walk (pad D z S) (insert z V) a b m) (ha : a ≠ z) : Walk D V a b m := by
  induction w with
  | refl a => exact .refl a
  | @step a b' c k hb hab w' ih =>
    rcases pad_cases hab with ⟨_, hbz, arc⟩ | ⟨haz, _⟩
    · have hbV : b' ∈ V := (Finset.mem_insert.mp hb).resolve_left hbz
      exact .step hbV arc (ih hbz)
    · exact absurd haz ha

theorem pad_qfree {D : CH.Digraph} {V S : Finset ℕ} {q z : ℕ} (hf : QFree D V q) (hzV : z ∉ V) (hS : S ⊆ V) :
    QFree (pad D z S) (insert z V) q := by
  intro a ℓ h1 hq w
  by_cases ha : a = z
  · rw [ha] at w
    obtain ⟨k, hk⟩ : ∃ k, ℓ = k + 1 := ⟨ℓ - 1, by omega⟩
    rw [hk] at w
    obtain ⟨y, _, _, arc⟩ := w.unsnoc
    rcases pad_cases arc with ⟨_, h, _⟩ | ⟨_, h⟩
    · exact h rfl
    · exact hzV (hS h)
  · exact hf a ℓ h1 hq (pad_walk w ha)

theorem pad_deg {D : CH.Digraph} {V S : Finset ℕ} {s z : ℕ} (deg : ∀ x ∈ V, s ≤ (outN D V x).card)
    (hzV : z ∉ V) (hS : S ⊆ V) (hc : S.card = s) :
    ∀ x ∈ insert z V, s ≤ (outN (pad D z S) (insert z V) x).card := by
  intro x hx
  rcases Finset.mem_insert.mp hx with hxz | hxV
  · have sub : S ⊆ outN (pad D z S) (insert z V) x := by
      intro b hb
      exact mem_outN.mpr ⟨Finset.mem_insert_of_mem (hS hb), by simp [pad, hxz, hb]⟩
    have := Finset.card_le_card sub
    omega
  · have xz : x ≠ z := fun h => hzV (h ▸ hxV)
    have sub : outN D V x ⊆ outN (pad D z S) (insert z V) x := by
      intro b hb
      obtain ⟨bV, arc⟩ := mem_outN.mp hb
      have bz : b ≠ z := fun h => hzV (h ▸ bV)
      exact mem_outN.mpr ⟨Finset.mem_insert_of_mem bV, by simp [pad, xz, bz, arc]⟩
    exact (deg x hxV).trans (Finset.card_le_card sub)

/-- Pad a `q`-free digraph with minimum outdegree `s` by `g` new sources. -/
theorem pad_to {q s : ℕ} : ∀ g (D : CH.Digraph) (V : Finset ℕ), QFree D V q → V.Nonempty →
    (∀ x ∈ V, s ≤ (outN D V x).card) →
    ∃ D' V', QFree D' V' q ∧ V'.card = V.card + g ∧ ∀ x ∈ V', s ≤ (outN D' V' x).card := by
  intro g
  induction g with
  | zero => intro D V hf _ deg; exact ⟨D, V, hf, rfl, deg⟩
  | succ g ih =>
    intro D V hf hne deg
    obtain ⟨x0, hx0⟩ := hne
    obtain ⟨S, hS, hc⟩ := Finset.exists_subset_card_eq (deg x0 hx0)
    have hSV : S ⊆ V := hS.trans outN_subset
    have hz : V.sup id + 1 ∉ V := by
      intro h
      have := Finset.le_sup (f := id) h
      simp only [id] at this
      omega
    obtain ⟨D', V', f', c', d'⟩ := ih (pad D (V.sup id + 1) S) (insert (V.sup id + 1) V)
      (pad_qfree hf hz hSV) ⟨_, Finset.mem_insert_self _ V⟩ (pad_deg deg hz hSV hc)
    exact ⟨D', V', f', by rw [c', Finset.card_insert_of_notMem hz]; omega, d'⟩

/-- **The capstone statement at `(q, s)` from the tight-row statement at `(q, s-1)`.** -/
theorem capstone_of_tightLaw {q n s : ℕ} {D : CH.Digraph} (hn : 0 < n) (hs : 1 ≤ s) (order : n ≤ q * s)
    (loop : CH.Loopless D n) (degree : CH.MinOutdegreeAtLeast D n s) (T : TightLaw q (s - 1)) :
    CH.HasDirectedCycleAtMost D n q := by
  by_contra no
  have hf := qfree_of_noShort loop no
  have deg : ∀ v ∈ Finset.range n, s ≤ (outN D (Finset.range n) v).card :=
    fun v hv => Compose.FloorSix.out_card degree (Finset.mem_range.mp hv)
  obtain ⟨D', V', f', c', d'⟩ := pad_to (q := q) (s := s) (q * s - n) D (Finset.range n) hf
    (Finset.nonempty_range_iff.mpr (by omega)) deg
  have ss : s - 1 + 1 = s := by omega
  have card : V'.card = q * (s - 1 + 1) := by rw [c', Finset.card_range, ss]; omega
  exact tightLaw_implies_CH T f' card (by rw [c', Finset.card_range]; omega)
    (fun v hv => by have := d' v hv; omega)

end LeanCH.BR.TightRow

open LeanCH.BR.TightRow in
#print axioms capstone_of_tightLaw
