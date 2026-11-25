import checkpoints.shen_extension.CollarLedger
import checkpoints.shen_extension.ShapeClimbMono

/-!
# The collar bound: an order bound at degree `q + 1` from floors for fat roots

`CollarLedger.no_thin` excludes thin roots from an out-regular digraph of degree `q + 1` once
the floors pay for it. Here that is turned into an order bound for every digraph of minimum
out-degree `q + 1`.

* `exists_regular`: a digraph of minimum out-degree `r` keeps a spanning subdigraph with every
  out-degree exactly `r`, and no new closed walk.
* `boundOf_local`: `ShapeClimbMono.boundOf` from floors that hold on one digraph.
* `CollarOK q fs g m`: the arithmetic test at order `m`, with `fs` the floors of every root and
  `g` the floors of fat roots (second layer of at least `q + 1` labels), at the middle radii
  `i = q/2`, `j = q - q/2`.
* `collar_bound`: if `CollarOK q fs g m` and `m ≤ boundOf q (q+1) g`, every `q`-free digraph of
  minimum out-degree `q + 1` has more than `m` labels.

The floors are hypotheses here; `fatFloors` is stated for out-regular digraphs only, which is
all a climb restricted to fat roots has to prove. Everything is generic in `q`.
-/

set_option linter.style.longLine false
namespace LeanCH.BR.CollarBound
open Finset BRq2 BRq3 FifthStripAll RigidHost
open DotTwoPassShellTransport (layer)
open MixedRadiusCompletion (Floor)

/-- **Thinning to exact out-degree.** -/
theorem exists_regular {D : CH.Digraph} {V : Finset ℕ} {q r : ℕ} (free : QFree D V q)
    (deg : ∀ v ∈ V, r ≤ (outN D V v).card) :
    ∃ E : CH.Digraph, QFree E V q ∧ ∀ v ∈ V, (outN E V v).card = r := by
  classical
  have pick : ∀ v, ∃ S : Finset ℕ, v ∈ V → S ⊆ outN D V v ∧ S.card = r := by
    intro v
    by_cases hv : v ∈ V
    · obtain ⟨S, sub, card⟩ := exists_subset_card_eq (deg v hv)
      exact ⟨S, fun _ => ⟨sub, card⟩⟩
    · exact ⟨∅, fun h => (hv h).elim⟩
  choose S hS using pick
  refine ⟨fun v w => decide (v ∈ V ∧ w ∈ S v), ?_, ?_⟩
  · have below : ∀ a b, (fun v w => decide (v ∈ V ∧ w ∈ S v)) a b = true → D a b = true := by
      intro a b h
      obtain ⟨aV, bS⟩ := of_decide_eq_true h
      exact (mem_outN.mp ((hS a aV).1 bS)).2
    exact fun a ℓ h1 hq w => free a ℓ h1 hq (walk_sub below w)
  · intro v hv
    have eq : outN (fun v w => decide (v ∈ V ∧ w ∈ S v)) V v = S v := by
      ext w
      simp only [mem_outN, decide_eq_true_eq]
      constructor
      · exact fun h => h.2.2
      · exact fun h => ⟨outN_subset ((hS v hv).1 h), hv, h⟩
    rw [eq]
    exact (hS v hv).2

/-- `ShapeClimbMono.boundOf` from floors that hold on one digraph. -/
theorem boundOf_local {q r : ℕ} {fs : List ℕ} {D : CH.Digraph} {V : Finset ℕ} (hq : 2 ≤ q)
    (free : QFree D V q) (ne : V.Nonempty) (deg : ∀ v ∈ V, r ≤ (outN D V v).card)
    (floors : ∀ i, ∀ v ∈ V, fs.getD i 0 ≤ (ball D V v i).card) :
    ShapeClimbMono.boundOf q r fs < V.card := by
  have left := floors (q / 2)
  have right := floors (q - q / 2)
  have pos := card_pos.mpr ne
  unfold ShapeClimbMono.boundOf
  by_cases strict : 2 * (q / 2 / 2) = q / 2 ∧ fs.getD (q / 2) 0 + 2 ≤ 2 * fs.getD (q / 2 / 2) 0
  · obtain ⟨eq, more⟩ := strict
    have size := SharedBankOrderTransfer.strict_order (k := q / 2 / 2) free ne
      (by omega : 2 * (q / 2 / 2) + (q - q / 2) ≤ q) (floors (q / 2 / 2))
      (eq.symm ▸ left) right more
    simp only [eq, more, and_self, ↓reduceIte, not_true_eq_false, false_and]
    omega
  · have size := card_ge_of_two_balls free (by omega : q / 2 + (q - q / 2) ≤ q) left right ne
    simp only [strict, ↓reduceIte, not_false_eq_true, true_and]
    split
    next h =>
      obtain ⟨⟨odd, gain⟩, two⟩ := h
      by_contra small
      exact TightPair.tight_pair_false free (by omega : 2 * (q / 2) ≤ q) ne left right
        (c := r + 1)
        (fun v hv => by
          have one : q - 2 * (q / 2) = 1 := by omega
          rw [one, ReachLedger.ball_one free (by omega) hv]
          have := deg v hv
          omega)
        (by omega) (by omega)
    next => omega

/-- The arithmetic test of the collar ledger at order `m`, at the middle radii. `fs` are the
floors of every root, `g` the floors of fat roots. -/
def CollarOK (q : ℕ) (fs g : List ℕ) (m : ℕ) : Prop :=
  let i := q / 2
  let j := q - q / 2
  let top := fs.getD (i+1) 0 + fs.getD (j+1) 0 + i + j
  let π := top - 2*(q+1) - (m+1)
  let δ := m + 1 - (fs.getD i 0 + fs.getD j 0)
  m + 1 ≤ g.getD i 0 + g.getD j 0 ∧ m + 1 + π + 2*(q+1) ≤ top ∧
    ∀ k ∈ range (δ + 2), k * (δ + 1) < k * k + (q+1) * π

instance {q fs g m} : Decidable (CollarOK q fs g m) := by unfold CollarOK; infer_instance

/-- **The collar bound.** -/
theorem collar_bound {q m : ℕ} {fs g : List ℕ} (hq : 2 ≤ q)
    (floors : ∀ i, Floor q (q+1) i (fs.getD i 0))
    (fatFloors : ∀ i, ∀ (E : CH.Digraph) (U : Finset ℕ), QFree E U q →
      (∀ v ∈ U, (outN E U v).card = q + 1) → ∀ u ∈ U, q + 1 ≤ (layer E U 2 u).card →
      g.getD i 0 ≤ (ball E U u i).card)
    (ok : CollarOK q fs g m) (le : m ≤ ShapeClimbMono.boundOf q (q+1) g)
    {D : CH.Digraph} {V : Finset ℕ} (free : QFree D V q) (ne : V.Nonempty)
    (deg : ∀ v ∈ V, q + 1 ≤ (outN D V v).card) : m < V.card := by
  by_contra small
  obtain ⟨E, freeE, regE⟩ := exists_regular free deg
  have degE : ∀ v ∈ V, q + 1 ≤ (outN E V v).card := fun v hv => (regE v hv).ge
  obtain ⟨fatpay, heads, pay⟩ := ok
  have payAll : ∀ k, k * (m + 1 - (fs.getD (q/2) 0 + fs.getD (q - q/2) 0) + 1) <
      k * k + (q+1) * (fs.getD (q/2+1) 0 + fs.getD (q - q/2 + 1) 0 + q/2 + (q - q/2)
        - 2*(q+1) - (m+1)) := by
    intro k
    by_cases hk : k ∈ range (m + 1 - (fs.getD (q/2) 0 + fs.getD (q - q/2) 0) + 2)
    · exact pay k hk
    · have big : m + 1 - (fs.getD (q/2) 0 + fs.getD (q - q/2) 0) + 1 < k := by
        have := mem_range.not.mp hk
        omega
      have : k * (m + 1 - (fs.getD (q/2) 0 + fs.getD (q - q/2) 0) + 1) < k * k :=
        (Nat.mul_lt_mul_left (by omega : 0 < k)).mpr big
      omega
  have fat := CollarLedger.no_thin (i := q/2) (j := q - q/2) freeE hq regE (by omega)
    (fun v hv => floors (q/2) E V freeE degE v hv)
    (fun v hv => floors (q - q/2) E V freeE degE v hv)
    (fun v hv => floors (q/2+1) E V freeE degE v hv)
    (fun v hv => floors (q - q/2 + 1) E V freeE degE v hv)
    (A := g.getD (q/2) 0) (B := g.getD (q - q/2) 0)
    (fun v hv hfat => Nat.add_le_add (fatFloors (q/2) E V freeE regE v hv hfat)
      (fatFloors (q - q/2) E V freeE regE v hv hfat))
    (by omega) (by omega) (by omega) payAll
  have bound := boundOf_local (fs := g) hq freeE ne degE
    (fun k v hv => fatFloors k E V freeE regE v hv (fat v hv))
  omega

#print axioms exists_regular
#print axioms boundOf_local
#print axioms collar_bound
end LeanCH.BR.CollarBound
